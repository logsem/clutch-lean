module

public import Metrology.Code.Retry
public import Metrology.Micrometer.SpecAdvRules
public import Metrology.Micrometer.AdequacyTV
public import Metrology.Micrometer.RelTactics
public import Metrology.Couplings.Divergences.Tv
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Amplification: flipping a coin until heads returns `0` almost surely

Amplification (`refines_ind_amp`) turns any positive credit into `↯b 1`, so `retry` returns `0`
almost surely. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace Retry

open ENNReal (div_le_of_le_mul add_halves)
open OrderAddMonoidHom (coe_id)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

variable (ε : ℝ≥0∞)

/-- Credits on the two flips: nothing on heads, `2ε` on tails. -/
noncomputable def flipCredit (n : Int) : ℝ≥0∞ :=
  -- written as the cast of `k = (2 : ℝ≥0)` to match `refines_ind_amp`'s `↯b ((k : ℝ≥0∞) * ε)`
  if n = 0 then 0 else ((2 : NNReal) : ℝ≥0∞) * ε

/-- The flip credits average to `ε`, as `refines_randU_r_adv` requires. -/
theorem flipCredit_avg : (∑ n ∈ Finset.Ico 0 2, flipCredit ε n) / (2 : Int).toNat ≤ ε := by
  rw [show Finset.Ico (0 : Int) 2 = {0, 1} by decide]
  simp [flipCredit]
  exact div_le_of_le_mul (mul_comm _ _).le

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS ℝ≥0∞ GF]
local bi IProp GF

/-- The value `0` refines `retry`, with no budget. -/
theorem zero_refines_retry : ⊢ REL[codensity tv] (pl(#0) : Exp rT) << retry : lrel_int := by
  -- `hsplit`: halve any positive budget; `hslack`: the budget itself is the seed `ε`; `k = 2`: each
  -- tails doubles the credit (`flipCredit`); the step map is the identity
  iapply refines_ind_amp (s := .id ℝ≥0∞) (k := 2)
    (fun b hb ↦ ⟨b / 2, b / 2, by simpa using hb.ne', by simpa using hb.ne', by rw [add_halves]⟩)
    (fun b hb ↦ ⟨b, hb, le_rfl⟩) absorbing_codensity_tv_one (by norm_num)
  simp only [coe_id, id_eq]
  iintro !> %ε %_ #IH Hε
  -- `ε ≥ 1` is absorbing; otherwise `ε` is finite and can be spent on the flip
  by_cases h1 : 1 ≤ ε
  · iapply refines_of_absorbing (absorbing_codensity_tv_one.mono h1) $$ Hε
  simp only [retry]
  rel_pures_r
  rel_apply_r (refines_randU_r_adv (s := .id ℝ≥0∞) 2 (by norm_num) ε (flipCredit ε)
    (flipCredit_avg ε) (IsAddRegular.of_ne_top (by simpa using (not_le.1 h1).ne_top)).1)
  simp only [coe_id, id_eq]
  iframe Hε
  iintro %n %hn Hn
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · rel_pures_r
    rel_values
  · simp only [flipCredit, one_ne_zero, ↓reduceIte]
    rel_pure_r 2
    rel_fold
    iapply IH $$ Hn

/-- On every event, `retry` is at least as likely as the value `0`. -/
theorem zero_le_retry (σ σ' : State rT) {S : Set (Exp rT)} (hS : MeasurableSet S) :
    limExecV ⟨pl(#0), σ⟩ S ≤ limExecV ⟨retry, σ'⟩ S := by
  simpa using limExecV_le_add_of_refines_tv (GF := MicrometerFunctor rT ℝ≥0∞)
    (fun _ _ ↦ lrel_int) _ _ σ σ' 0 (fun _ _ ↦ lrel_int_car_eq)
    (fun _ _ ↦ by iintro -; iapply zero_refines_retry) hS

open MeasureTheory in
/-- `retry` returns `0` with probability `1`. -/
theorem retry_eq_zero (σ : State rT) : limExecV ⟨retry, σ⟩ {pl(#0)} = 1 :=
  le_antisymm (IsSubProbabilityMeasure.measure_le_one _) <| by
    simpa [limExecV_of_isVal σ .lit] using zero_le_retry σ σ (measurableSet_singleton pl(#0))

end Retry
end ProbLang
