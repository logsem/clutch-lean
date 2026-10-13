module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod

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

instance (μ : Measure X) [IsSubProbabilityMeasure μ] (f : X → Y) :
    IsSubProbabilityMeasure (μ.map f) where
  measure_univ_le_one := by
    by_cases hf : AEMeasurable f μ
    · rw [Measure.map_apply_of_aemeasurable hf .univ, preimage_univ]
      exact IsSubProbabilityMeasure.measure_univ_le_one
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [Measure.map_of_not_aemeasurable_of_ne_zero hf hμ]

instance (μ : Measure X) (ν : Measure Y) [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : IsSubProbabilityMeasure (μ.prod ν) where
  measure_univ_le_one := by
    rw [← univ_prod_univ, Measure.prod_prod]
    exact mul_le_one' IsSubProbabilityMeasure.measure_univ_le_one
      IsSubProbabilityMeasure.measure_univ_le_one

/-- Not an instance: `Measure.bind` is junk for non-measurable kernels. -/
theorem isSubProbabilityMeasure_bind {μ : Measure X} {f : X → Measure Y}
    [IsSubProbabilityMeasure μ] (hf : AEMeasurable f μ)
    (hfx : ∀ x, IsSubProbabilityMeasure (f x)) : IsSubProbabilityMeasure (μ.bind f) :=
  ⟨calc μ.bind f univ = ∫⁻ x, f x univ ∂μ := Measure.bind_apply .univ hf
      _ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun x ↦ (hfx x).measure_univ_le_one
      _ ≤ 1 := by simpa using IsSubProbabilityMeasure.measure_univ_le_one (μ := μ)⟩

theorem _root_.Measurable.measure_prod {Z : Type*} [MeasurableSpace Z] {f : Z → Measure X}
    {g : Z → Measure Y} (hf : Measurable f) (hg : Measurable g) [∀ z, IsFiniteMeasure (f z)]
    [∀ z, IsFiniteMeasure (g z)] : Measurable fun z ↦ (f z).prod (g z) := by
  have hf' : Measurable fun z ↦ (⟨f z, inferInstance⟩ : FiniteMeasure X) := hf.subtype_mk
  have hg' : Measurable fun z ↦ (⟨g z, inferInstance⟩ : FiniteMeasure Y) := hg.subtype_mk
  exact FiniteMeasure.measurable_fun_prod.comp (hf'.prodMk hg')

end MeasureTheory
