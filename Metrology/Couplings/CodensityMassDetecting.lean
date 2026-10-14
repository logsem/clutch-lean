module

public import Metrology.Couplings.CodensityTV
public import Metrology.Couplings.CodensityLifting
public import Metrology.Couplings.DP.Divergence

/-! Mass-detecting divergences: an exact codensity lifting bounds the probability of events. -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal Classical

namespace GradedDivergence

variable {ι : Type v} [Monoid ι] (Δ : GradedDivergence.{u} ι)

/-- Divergence at most `ε` between two point masses of mass at most one bounds the excess mass by
`ε`. -/
class IsMassDetecting : Prop where
  le_add_of_le {a b ε : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) :
    Δ 1 (a • dirac PUnit.unit.{u + 1}) (b • dirac PUnit.unit.{u + 1}) ≤ ε → a ≤ b + ε

variable {Δ} {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

/-- The kernel into a point that keeps the mass on `T`. -/
private noncomputable def indKernel {T : Set X} (hT : MeasurableSet T) : Kernel X PUnit.{u + 1} :=
  Kernel.piecewise hT (Kernel.const X (dirac PUnit.unit)) 0

private instance indKernel.isSubMarkov {T : Set X} (hT : MeasurableSet T) :
    IsSubMarkovKernel (indKernel hT) := by
  unfold indKernel
  infer_instance

private theorem indKernel_bind {T : Set X} (hT : MeasurableSet T) (μ : Measure X) :
    indKernel hT ∘ₘ μ = μ T • dirac PUnit.unit := by
  ext s hs
  rw [bind_apply hs (indKernel hT).measurable.aemeasurable]
  simp only [indKernel, Kernel.piecewise_apply, Measure.smul_apply, smul_eq_mul]
  rw [mul_comm, ← lintegral_indicator_const hT]
  refine lintegral_congr fun x ↦ ?_
  by_cases hx : x ∈ T <;> simp [hx]

/-- A codensity lifting at bound `ε` bounds the mass of an event by that of its image plus `ε`. -/
theorem Codensity.measure_le_add [Δ.IsReflexive] [Δ.IsZeroLeft] [Δ.IsMassDetecting]
    {R : Set (X × Y)} {ε : ℝ≥0∞} {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {T : Set X} {T' : Set Y} (hT : MeasurableSet T)
    (hT' : MeasurableSet T') (h : Δ.Codensity 1 ε R μ ν)
    (hR : ∀ x y, (x, y) ∈ R → x ∈ T → y ∈ T') : μ T ≤ ν T' + ε := by
  have := codensity_iff.1 h (I := PUnit) (β := 1) (γ := 0) (k := indKernel hT)
    (l := indKernel hT') fun x y hxy ↦ ?_
  · rw [indKernel_bind, indKernel_bind, one_mul, add_zero] at this
    exact IsMassDetecting.le_add_of_le (IsSubProbabilityMeasure.measure_le_one T)
      (IsSubProbabilityMeasure.measure_le_one T') this
  · by_cases hx : x ∈ T
    · have hy := hR x y hxy hx
      simp only [indKernel, Kernel.piecewise_apply, hx, hy, ite_true]
      exact IsReflexive.self_le_zero _
    · simp only [indKernel, Kernel.piecewise_apply, hx, ite_false, zero_apply]
      exact (IsZeroLeft.zero_left_le _ _).trans zero_le

/-- An exact codensity lifting bounds the mass of an event by that of its image. -/
theorem Codensity.measure_le [Δ.IsReflexive] [Δ.IsZeroLeft] [Δ.IsMassDetecting] {R : Set (X × Y)}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    {T : Set X} {T' : Set Y} (hT : MeasurableSet T) (hT' : MeasurableSet T')
    (h : Δ.Codensity 1 0 R μ ν) (hR : ∀ x y, (x, y) ∈ R → x ∈ T → y ∈ T') : μ T ≤ ν T' := by
  simpa using h.measure_le_add hT hT' hR

end GradedDivergence

namespace TVDiv

/-- The total variation detects masses. -/
instance isMassDetecting_tv : (tv.{u}).IsMassDetecting where
  le_add_of_le _ _ h := by simpa using tv_le_iff.1 h .univ .univ

end TVDiv

namespace DPDiv

/-- The DP divergence at budget zero detects masses. -/
instance isMassDetecting_dp : (dp.{u}).IsMassDetecting where
  le_add_of_le _ _ h := by simpa using dp_le_iff.1 h .univ .univ

end DPDiv
