module

public import Metrology.Micrometer.Examples.RandomizedResponse.Zcdp

@[expose] public section

/-! # Randomized response is tCDP

Maps the zCDP coupling of one round along `zcdpToTcdp`: `k` rounds are `k ln 3`-tCDP below any
order `ω` (`rrCount_tCDP`), and along `tcdpToDp`, DP at every slack (`rrCount_DP_of_tCDP`). -/

open GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang.RandomizedResponse

open ENNReal (ofReal isAddLeftRegular_ofReal)
open Real (log)
open LiftingRelHom (zcdpToTcdp tcdpToDp tcdpToDp_map)

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] (ω : ℝ) (k : ℕ)
  (σ : State rT)

/-- One round is a tCDP coupling at `ln 3`, the image of its zCDP coupling. -/
theorem rrCoupling_tcdp : RRCoupling (tcdpLifting ω) (ofReal (log 3)) := fun b b' ↦ by
  simpa using (zcdpToTcdp ω).map_rel (rrCoupling_zcdp b b')

/-- `k` rounds are `k ln 3`-tCDP below the order `ω` (Def. 2.5). -/
theorem rrCount_tCDP : (rrCountMech k σ).tCDP ⊤ ω (k * ofReal (log 3)) := by
  simpa [nsmul_eq_mul] using rrCount_isPrivate (ofReal (log 3))
    (isAddLeftRegular_ofReal _) (rrCoupling_tcdp ω) k σ

/-- Randomized response in a loop of `k` rounds is DP at every slack `δ > 0`: map its tCDP
coupling along `tcdpToDp`, at the best order below `ω` ([t/D]). -/
theorem rrCount_DP_of_tCDP {δ : ℝ} (hδ : 0 < δ) :
    (rrCountMech k σ).DP ⊤
      (⨅ α ∈ Set.Ioo 1 ω, ofReal α * (k * ofReal (log 3)) +
        ofReal (log (1 / δ) / (α - 1)))
      (ofReal δ) := fun b b' _ ↦ by
  have hc := rrCount_rel (ofReal (log 3))
    (isAddLeftRegular_ofReal _) (rrCoupling_tcdp ω) b b' k σ σ
  rw [nsmul_eq_mul] at hc
  simpa [tcdpToDp_map] using
    codensity_sound ((tcdpToDp hδ).map_rel hc)

end ProbLang.RandomizedResponse
