module

public import Metrology.Micrometer.Examples.RandomizedResponse.Zcdp

@[expose] public section

/-! # Randomized response is tCDP

The zCDP coupling of one round maps along `zcdpToTcdp`, so `k` rounds are `k ln 3`-tCDP below
any order `ω`; mapping along `tcdpToDp` gives DP at every slack. -/

open GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] (ω : ℝ)

/-- The two draws couple along equal reports in the tCDP lifting at `ln 3`. -/
theorem rr_tcdp_coupling (b b' : Bool) :
    (tcdpLifting ω).Rel (ENNReal.ofReal (Real.log 3)) (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) := by
  simpa using (LiftingRelHom.zcdpToTcdp ω).map_rel (rr_zcdp_coupling b b')

/-- `k` rounds are `k ln 3`-tCDP below the order `ω` (Def. 2.5). -/
theorem rrCount_tCDP (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).tCDP ⊤ ω (k * ENNReal.ofReal (Real.log 3)) := by
  simpa [nsmul_eq_mul] using rrCount_isPrivate (L := tcdpLifting ω) (ENNReal.ofReal (Real.log 3))
    (IsAddRegular.of_ne_top ENNReal.ofReal_ne_top).1 (rr_tcdp_coupling ω) k σ

/-- Randomized response in a loop of `k` rounds is DP at every slack `δ > 0`: map its tCDP
coupling along `tcdpToDp`, at the best order below `ω` ([t/D]). -/
theorem rrCount_DP_of_tCDP (k : ℕ) (σ : State rT) {δ : ℝ} (hδ : 0 < δ) :
    (rrCountMech k σ).DP ⊤
      (⨅ α ∈ Set.Ioo 1 ω, ENNReal.ofReal α * (k * ENNReal.ofReal (Real.log 3)) +
        ENNReal.ofReal (Real.log (1 / δ) / (α - 1)))
      (ENNReal.ofReal δ) := fun b b' _ ↦ by
  have hc := rrCount_rel (L := tcdpLifting ω) (ENNReal.ofReal (Real.log 3))
    (IsAddRegular.of_ne_top ENNReal.ofReal_ne_top).1 (rr_tcdp_coupling ω) b b' k σ σ
  rw [nsmul_eq_mul] at hc
  simpa [LiftingRelHom.tcdpToDp_map] using
    codensity_sound ((LiftingRelHom.tcdpToDp hδ).map_rel hc)

end RandomizedResponse
end ProbLang
