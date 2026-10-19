module

public import Metrology.Micrometer.Examples.RandomizedResponseLoop

@[expose] public section

/-! # Randomized response is tCDP

The zCDP coupling of one round maps into the tCDP lifting along `zcdpToTcdp`, so the loop
refinement of `RandomizedResponseLoop` runs at `tcdpLifting ω`: `k` rounds are `k ln 3`-tCDP
below any order `ω`. Mapping the closed coupling along `tcdpToDp` gives DP at every slack. -/

open Iris Iris.BI Iris.ProofMode GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] (ω : ℝ)

/-- The two draws couple along equal reports in the tCDP lifting at `ln 3`. -/
theorem rr_tcdp_coupling (b b' : Bool) :
    (tcdpLifting ω).Rel (ENNReal.ofReal (Real.log 3)) (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) := by
  simpa using (LiftingRelHom.zcdpToTcdp ω).map_rel (rr_zcdp_coupling b b')

/-- The loop refines itself at equal counts in the tCDP lifting, spending `ln 3` per round. -/
theorem rrCount_refines_tcdp {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS ℝ≥0∞ GF] (b b' : Bool) (k : ℕ) :
    ⊢@{IProp GF} ↯b (k • ENNReal.ofReal (Real.log 3)) -∗
      REL[tcdpLifting ω] (rrCount (rT := rT) b k) << (rrCount b' k) : lrel_int :=
  rrCount_refines_of _ (rr_refines_of _ (IsAddRegular.of_ne_top ENNReal.ofReal_ne_top).1
    (rr_tcdp_coupling ω)) b b' k

/-- `k` rounds couple equal outputs in the tCDP lifting at `k ln 3`. -/
theorem rrCount_tcdp_coupling (b b' : Bool) (k : ℕ) (σ σ' : State rT) :
    (tcdpLifting ω).Rel (k * ENNReal.ofReal (Real.log 3)) (· = ·)
      (limExecV ⟨rrCount b k, σ⟩) (limExecV ⟨rrCount b' k, σ'⟩) := by
  rw [← nsmul_eq_mul]
  exact (approximates_coupling (GF := MicrometerFunctor rT ℝ≥0∞) (fun _ _ ↦ lrel_int) _ _ _ σ σ'
    _ (fun _ _ ↦ lrel_int_car_eq) fun _ _ ↦ rrCount_refines_tcdp ω b b' k).mono le_rfl
    adequacyRel_eq_subset

/-- Randomized response in a loop of `k` rounds is `k ln 3`-tCDP below the order `ω`
(Def. 2.5). -/
theorem rrCount_tCDP (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).tCDP ⊤ ω (k * ENNReal.ofReal (Real.log 3)) :=
  fun b b' _ ↦ (tcdpLifting_sound (rrCount_tcdp_coupling ω b b' k σ σ) :)

/-- Randomized response in a loop of `k` rounds is DP at every slack `δ > 0`: map its tCDP
coupling along `tcdpToDp`, at the best order below `ω` ([t/D]). -/
theorem rrCount_DP_of_tCDP (k : ℕ) (σ : State rT) {δ : ℝ} (hδ : 0 < δ) :
    (rrCountMech k σ).DP ⊤
      (⨅ α ∈ Set.Ioo 1 ω, ENNReal.ofReal α * (k * ENNReal.ofReal (Real.log 3)) +
        ENNReal.ofReal (Real.log (1 / δ) / (α - 1)))
      (ENNReal.ofReal δ) := fun b b' _ ↦ by
  have h := codensity_sound ((LiftingRelHom.tcdpToDp hδ).map_rel
    (rrCount_tcdp_coupling ω b b' k σ σ))
  rw [LiftingRelHom.tcdpToDp_map] at h
  exact h

end RandomizedResponse
end ProbLang
