module

public import Metrology.Code.LeakyRR
public import Metrology.Couplings.Divergences.DpAvoid
public import Metrology.Micrometer.Examples.RandomizedResponse
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Algebra.Regular.Prod

@[expose] public section

/-! # Approximate DP: randomized response that leaks its input with probability `1/N`

The two first draws are coupled along the identity, avoiding the leak `0` for `↯b (0, 1/N)`;
the leak releases the input outright, so no multiplicative factor bounds it and it is paid in
`δ`, not `ε`. Randomized response then spends `↯b (ln 3, 0)`, so `leakyRR N` is
`(ln 3, 1/N)`-DP. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp codensity codensity_dp_avoid)
open scoped ENNReal

namespace ProbLang
namespace LeakyRR

open RandomizedResponse (rr_refines lrel_bool_eq)

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

theorem unifInt_singleton_zero {N : Int} (hN : 0 < N) :
    unifInt N hN {0} = (N.toNat : ℝ≥0∞)⁻¹ := by
  rw [unifInt, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.uniformOfFinset_apply_of_mem _ (Finset.mem_Ico.2 ⟨le_rfl, hN⟩), Int.card_Ico, sub_zero]

/-- `leakyRR N b` refines `leakyRR N b'` at equal reports, spending `(ln 3, 1/N)`. -/
theorem leakyRR_refines {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (N : Int) (hN : 0 < N) (b b' : Bool) :
    ⊢@{IProp GF} ↯b (ENNReal.ofReal (Real.log 3), (N.toNat : ℝ≥0∞)⁻¹) -∗
      REL[codensity dp] (leakyRR (rT := rT) N b) << leakyRR N b' : lrel_bool := by
  rw [show (ENNReal.ofReal (Real.log 3), (N.toNat : ℝ≥0∞)⁻¹) =
    (0, (N.toNat : ℝ≥0∞)⁻¹) + RandomizedResponse.budget by simp]
  iintro Hb
  ihave ⟨Hδ, Hε⟩ := BudgetCredit.split $$ Hb
  rel_couple_UU_spend (fun r r' ↦ r = r' ∧ r ∉ ({0} : Set Int)) (0, (N.toNat : ℝ≥0∞)⁻¹)
    (by simp [hN]) (unifInt_singleton_zero hN ▸ codensity_dp_avoid _ (.singleton 0))
  iframe Hδ
  iintro %r %_ %⟨rfl, hr⟩
  rel_pures
  iapply rr_refines b b' $$ Hε

/-- `leakyRR N` on private bits, started from state `σ`. -/
noncomputable def leakyRRMech (N : Int) (σ : State rT) : Mechanism Bool (Exp rT) :=
  progMech (leakyRR N) σ

/-- `leakyRR N` is `(ln 3, 1/N)`-differentially private for any two bits (Def. 2.1). -/
theorem leakyRR_DP (N : Int) (hN : 0 < N) (σ : State rT) :
    (leakyRRMech N σ).DP ⊤ (ENNReal.ofReal (Real.log 3)) (N.toNat : ℝ≥0∞)⁻¹ :=
  progMech_isPrivate (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) (L := codensity dp) (leakyRR N) σ _
    (fun _ _ ↦ lrel_bool) (fun _ _ ↦ lrel_bool_eq) fun b b' _ _ _ ↦ leakyRR_refines N hN b b'

end LeakyRR
end ProbLang
