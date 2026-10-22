module

public import Metrology.Couplings.Divergences.Dp

/-! # Avoiding an event in the DP coupling

Coupling a measure with itself along equality outside an event `T` costs `μ T` of DP slack
(`codensity_dp_avoid`). -/

@[expose] public section

open MeasureTheory GradedLifting
open scoped ENNReal

namespace GradedDivergence

variable {X : Type*} [MeasurableSpace X]

/-- A sub-probability measure couples with itself along equality outside `T` at slack `μ T`. -/
theorem codensity_dp_avoid (μ : Measure X) [IsSubProbabilityMeasure μ] {T : Set X}
    (hT : MeasurableSet T) : (codensity dp).Rel (0, μ T) (fun x y ↦ x = y ∧ x ∉ T) μ μ := by
  refine (codensity_dp_rel_iff ENNReal.zero_ne_top).2 fun f g _ hg hf1 _ hfg ↦ ?_
  -- Off `T`, `f ≤ g` by the relation; on `T`, `f ≤ 1` is paid for by the indicator term.
  calc ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x + T.indicator 1 x ∂μ := lintegral_mono fun x ↦ by
        by_cases hx : x ∈ T
        · simpa [hx] using (hf1 x).trans le_add_self
        · simpa [hx] using hfg x x ⟨rfl, hx⟩
    _ = expBudget 0 * ∫⁻ x, g x ∂μ + μ T := by
        rw [lintegral_add_left hg, lintegral_indicator_one hT, expBudget_zero, one_mul]

end GradedDivergence
