module

public import Metrology.Code.LeakyRR
public import Metrology.Couplings.Divergences.DpAvoid
public import Metrology.Micrometer.Examples.RandomizedResponse.Dp
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Algebra.Regular.Prod
import Metrology.Iris.LocalBI

@[expose] public section

/-! # LeakyRR: spending `δ`

Randomized response that leaks its input with probability `1/N` is `(ln 3, 1/N)`-DP (`leakyRR_DP`).
No factor bounds the leak, so avoiding it costs `↯b (0, 1/N)`; `rr` costs `↯b (ln 3, 0)`. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp codensity codensity_dp_avoid)
open scoped ENNReal

namespace ProbLang
namespace LeakyRR

open RandomizedResponse (rr_refines budget)

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

section Refines

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF]
local bi IProp GF

/-- `leakyRR N b` refines `leakyRR N b'` at equal reports, spending `(ln 3, 1/N)`. -/
theorem leakyRR_refines (N : Int) (hN : 0 < N) (b b' : Bool) :
    ⊢ ↯b (ENNReal.ofReal (Real.log 3), (N.toNat : ℝ≥0∞)⁻¹) -∗
      REL[codensity dp] (leakyRR (rT := rT) N b) << leakyRR N b' : lrel_bool := by
  -- split the budget: `(0, 1/N)` pays to avoid the leak, `(ln 3, 0)` pays for `rr`
  rw [show (ENNReal.ofReal (Real.log 3), (N.toNat : ℝ≥0∞)⁻¹) =
    (0, (N.toNat : ℝ≥0∞)⁻¹) + budget by simp]
  iintro Hb
  ihave ⟨Hδ, Hε⟩ := BudgetCredit.split $$ Hb
  -- couple the two draws along "equal and not `0`" at `(0, μ{0}) = (0, 1/N)`
  rel_couple_UU_spend (fun r r' ↦ r = r' ∧ r ∉ ({0} : Set Int)) (0, (N.toNat : ℝ≥0∞)⁻¹)
    (by simp [hN]) (unifInt_singleton_zero hN ▸ codensity_dp_avoid _ (.singleton 0))
  iframe Hδ
  iintro %r %_ %⟨rfl, hr⟩
  -- `hr` rules out the leaking branch on both sides
  rel_pures
  iapply rr_refines b b' $$ Hε

end Refines

/-- `leakyRR N` on private bits, started from state `σ`. -/
noncomputable abbrev leakyRRMech (N : Int) (σ : State rT) : Mechanism Bool (Exp rT) :=
  progMech (leakyRR N) σ

/-- `leakyRR N` is `(ln 3, 1/N)`-differentially private for any two bits (Def. 2.1). -/
theorem leakyRR_DP (N : Int) (hN : 0 < N) (σ : State rT) :
    (leakyRRMech N σ).DP ⊤ (ENNReal.ofReal (Real.log 3)) (N.toNat : ℝ≥0∞)⁻¹ :=
  progMech_isPrivate (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) (L := codensity dp) (leakyRR N) σ _
    (fun _ _ ↦ lrel_bool) (fun _ _ ↦ lrel_bool_car_eq) fun b b' _ _ _ ↦ leakyRR_refines N hN b b'

end LeakyRR
end ProbLang
