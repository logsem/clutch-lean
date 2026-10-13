module

public import Metrology.Couplings.Measure

/-! Subprobability measures, the carrier of the sub-Giry monad (Approximate Span Liftings,
Def. 3.1). -/

@[expose] public section

open MeasureTheory Set ENNReal

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measure of total mass at most `1`. -/
class IsSubProbabilityMeasure (μ : Measure X) : Prop where
  measure_univ_le_one : μ univ ≤ 1

instance (priority := 100) IsSubProbabilityMeasure.toIsFiniteMeasure (μ : Measure X)
    [IsSubProbabilityMeasure μ] : IsFiniteMeasure μ where
  measure_univ_lt_top := measure_univ_le_one.trans_lt one_lt_top

instance (priority := 100) IsZeroOrProbabilityMeasure.toIsSubProbabilityMeasure
    (μ : Measure X) [IsZeroOrProbabilityMeasure μ] : IsSubProbabilityMeasure μ where
  measure_univ_le_one := prob_le_one

instance isSubProbabilityMeasure_map (μ : Measure X) [IsSubProbabilityMeasure μ] (f : X → Y) :
    IsSubProbabilityMeasure (μ.map f) where
  measure_univ_le_one := by
    by_cases hf : AEMeasurable f μ
    · rw [Measure.map_apply_of_aemeasurable hf .univ, preimage_univ]
      exact IsSubProbabilityMeasure.measure_univ_le_one
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [Measure.map_of_not_aemeasurable_of_ne_zero hf hμ]

instance isSubProbabilityMeasure_prod (μ : Measure X) (ν : Measure Y) [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : IsSubProbabilityMeasure (μ.prod ν) where
  measure_univ_le_one := by
    rw [← univ_prod_univ, Measure.prod_prod]
    exact mul_le_one' IsSubProbabilityMeasure.measure_univ_le_one
      IsSubProbabilityMeasure.measure_univ_le_one

/-- Not an instance: `Measure.bind` is junk for non-measurable kernels. -/
theorem isSubProbabilityMeasure_bind {μ : Measure X} {f : X → Measure Y}
    [IsSubProbabilityMeasure μ] (hfx : ∀ x, IsSubProbabilityMeasure (f x))
    (hf : AEMeasurable f μ := by fun_prop) : IsSubProbabilityMeasure (μ.bind f) :=
  ⟨calc μ.bind f univ = ∫⁻ x, f x univ ∂μ := Measure.bind_apply .univ hf
      _ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun x ↦ (hfx x).measure_univ_le_one
      _ ≤ 1 := by simpa using IsSubProbabilityMeasure.measure_univ_le_one (μ := μ)⟩

open Classical in
/-- `μ` if it is finite, and `0` otherwise. -/
noncomputable def Measure.finiteOrZero (μ : Measure X) : Measure X :=
  if IsFiniteMeasure μ then μ else 0

namespace Measure

instance isFiniteMeasure_finiteOrZero (μ : Measure X) : IsFiniteMeasure μ.finiteOrZero := by
  unfold finiteOrZero
  split <;> infer_instance

theorem finiteOrZero_eq (μ : Measure X) [h : IsFiniteMeasure μ] : μ.finiteOrZero = μ := by
  simp [finiteOrZero, h]

@[fun_prop]
theorem measurable_finiteOrZero : Measurable (finiteOrZero : Measure X → Measure X) :=
  Measurable.ite FiniteMeasure.measurableSet_isFiniteMeasure measurable_id measurable_const

end Measure

end MeasureTheory
