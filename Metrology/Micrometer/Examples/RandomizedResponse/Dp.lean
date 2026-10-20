module

public import Metrology.Micrometer.Examples.RandomizedResponse.Basic

@[expose] public section

/-! # Randomized response is `ln 3`-differentially private (clutch-dp `randomized_response.v`)

Instantiates `RandomizedResponse/Basic.lean` at `codensity dp` and budget `(ln 3, 0)`: one round
by `wp` and by refinement (`rr_dp`, `rr_DP`), and `k` rounds at `(k ln 3, 0)` (`rrCount_DP`). -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp codensity codensity_dp_of_fiber dp_iff)
open scoped ENNReal

namespace ProbLang.RandomizedResponse

/-! ## The one-round coupling -/

/-- One round couples at `(ln 3, 0)`: each report is at most three times likelier under one bit. -/
theorem rrCoupling_dp : RRCoupling (codensity dp) budget := fun b b' ↦
  codensity_dp_of_fiber .of_discrete .of_discrete fun c ↦
    expBudget_log_three ▸ rrOut_fiber_le_three b b' c

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-! ## One round, by `wp` -/

/-- One round against the spec, spending `(ln 3, 0)`. -/
theorem wp_rr {GF : BundledGFunctors} [MicrometerGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b b' : Bool) :
    ⊢@{IProp GF} ⤇ rr (rT := rT) b' -∗ ↯b budget -∗
      wp (codensity dp) ⊤ (rr b) (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝)) := by
  rw [spec_eq_fill_nil]
  iintro Hj Hb
  iapply wp_rr_of budget isAddLeftRegular_budget rrCoupling_dp
  iframe Hj Hb
  iintro %d Hj
  iapply spec_fill_nil_exists (.bool d) $$ Hj

/-- Randomized response is `(ln 3, 0)`-DP for any two private bits, through `wp_rr`. -/
theorem rr_dp (b b' : Bool) (σ σ' : State rT) :
    dp budget (limExecV ⟨rr b, σ⟩) (limExecV ⟨rr b', σ'⟩) :=
  wp_adequacy_div (GF := MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) _ _ σ σ' budget fun _ _ ↦ wp_rr b b'

/-- Every event is at most three times as likely under one private bit as under the other. -/
theorem rr_event_le (b b' : Bool) (σ σ' : State rT) (S : Set (Exp rT))
    (hS : MeasurableSet S) : limExecV ⟨rr b, σ⟩ S ≤ 3 * limExecV ⟨rr b', σ'⟩ S := by
  simpa [expBudget_log_three] using (dp_iff ENNReal.ofReal_ne_top).1 (rr_dp b b' σ σ') S hS

/-! ## One round, by refinement -/

/-- One round refines itself at equal reports, spending `(ln 3, 0)`. -/
theorem rr_refines {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b b' : Bool) :
    ⊢@{IProp GF} ↯b budget -∗ REL[codensity dp] (rr (rT := rT) b) << (rr b') : lrel_bool :=
  rr_refines_of budget isAddLeftRegular_budget rrCoupling_dp b b'

/-- Randomized response as a mechanism on private bits, started from state `σ`. -/
noncomputable abbrev rrMech (σ : State rT) : Mechanism Bool (Exp rT) :=
  progMech rr σ

/-- Randomized response is `(ln 3, 0)`-DP as a mechanism, through `rr_refines` (Def. 2.1). -/
theorem rr_DP (σ : State rT) : (rrMech σ).DP ⊤ (ENNReal.ofReal (Real.log 3)) 0 :=
  progMech_isPrivate (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) (L := codensity dp) rr σ budget
    (fun _ _ ↦ lrel_bool) (fun _ _ ↦ lrel_bool_car_eq) fun b b' _ _ _ ↦ rr_refines b b'

/-! ## `k` rounds -/

/-- `k` rounds are `(k ln 3, 0)`-DP (Def. 2.1). -/
theorem rrCount_DP (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).DP ⊤ (k * ENNReal.ofReal (Real.log 3)) 0 := by
  -- the loop theorem gives `k • (ln 3, 0)`; `simpa` turns it into `(k ln 3, 0)`
  simpa [nsmul_eq_mul] using
    rrCount_isPrivate (L := codensity dp) budget isAddLeftRegular_budget rrCoupling_dp k σ

end ProbLang.RandomizedResponse
