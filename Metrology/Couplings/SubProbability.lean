module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Metrology.Couplings.Measure

/-! Subprobability measures, the carrier of the sub-Giry monad (Approximate Span Liftings,
Def. 3.1). -/

@[expose] public section

universe v

open MeasureTheory Measure Set ENNReal

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measure of total mass at most `1`. -/
class IsSubProbabilityMeasure (μ : Measure X) : Prop where
  measure_univ_le_one : μ univ ≤ 1

theorem IsSubProbabilityMeasure.measure_le_one {μ : Measure X} [IsSubProbabilityMeasure μ]
    (s : Set X) : μ s ≤ 1 :=
  (measure_mono (subset_univ s)).trans measure_univ_le_one

/-- Every set has real mass in `[0, 1]` under a subprobability measure. -/
theorem IsSubProbabilityMeasure.toReal_mem_Icc {μ : Measure X} [IsSubProbabilityMeasure μ]
    (s : Set X) : (μ s).toReal ∈ Icc (0 : ℝ) 1 :=
  ⟨toReal_nonneg, toReal_le_of_le_ofReal zero_le_one (ofReal_one ▸ measure_le_one s)⟩

/-- Adding a constant under the integral adds at most that constant. -/
theorem IsSubProbabilityMeasure.lintegral_add_const_le {μ : Measure X} [IsSubProbabilityMeasure μ]
    (f : X → ℝ≥0∞) (c : ℝ≥0∞) : ∫⁻ x, f x + c ∂μ ≤ ∫⁻ x, f x ∂μ + c := by
  rw [lintegral_add_right _ measurable_const, lintegral_const]
  gcongr
  exact mul_le_of_le_one_right' measure_univ_le_one

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
theorem isSubProbabilityMeasure_bind (μ : Measure X) (f : X → Measure Y)
    [IsSubProbabilityMeasure μ] [∀ x, IsSubProbabilityMeasure (f x)]
    (hf : AEMeasurable f μ := by fun_prop) : IsSubProbabilityMeasure (μ.bind f) :=
  ⟨calc μ.bind f univ = ∫⁻ x, f x univ ∂μ := Measure.bind_apply .univ hf
      _ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun x ↦ IsSubProbabilityMeasure.measure_univ_le_one
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

namespace ProbabilityTheory

open MeasureTheory

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- A kernel whose measures all have total mass at most `1`. -/
class IsSubMarkovKernel (κ : Kernel X Y) : Prop where
  isSubProbabilityMeasure (x : X) : IsSubProbabilityMeasure (κ x)

attribute [instance] IsSubMarkovKernel.isSubProbabilityMeasure

instance (priority := 100) IsZeroOrMarkovKernel.toIsSubMarkovKernel (κ : Kernel X Y)
    [IsZeroOrMarkovKernel κ] : IsSubMarkovKernel κ where
  isSubProbabilityMeasure _ := inferInstance

instance (priority := 100) IsSubMarkovKernel.toIsFiniteKernel (κ : Kernel X Y)
    [IsSubMarkovKernel κ] : IsFiniteKernel κ where
  exists_univ_le := ⟨1, ENNReal.one_lt_top, fun _ ↦ IsSubProbabilityMeasure.measure_univ_le_one⟩

instance isSubProbabilityMeasure_comp (μ : Measure X) [IsSubProbabilityMeasure μ]
    (κ : Kernel X Y) [IsSubMarkovKernel κ] : IsSubProbabilityMeasure (κ ∘ₘ μ) :=
  isSubProbabilityMeasure_bind μ κ κ.measurable.aemeasurable

instance isSubMarkovKernel_comp (η : Kernel Y Z) [IsSubMarkovKernel η] (κ : Kernel X Y)
    [IsSubMarkovKernel κ] : IsSubMarkovKernel (η ∘ₖ κ) where
  isSubProbabilityMeasure x := by rw [Kernel.comp_apply]; infer_instance

instance isSubMarkovKernel_map (κ : Kernel X Y) [IsSubMarkovKernel κ] (f : Y → Z) :
    IsSubMarkovKernel (κ.map f) where
  isSubProbabilityMeasure x := by
    by_cases hf : Measurable f
    · rw [Kernel.map_apply _ hf]
      infer_instance
    · rw [Kernel.map_of_not_measurable _ hf]
      exact ⟨by simp⟩

/-- Gluing two sub-Markov kernels along a measurable set gives a sub-Markov kernel. -/
instance isSubMarkovKernel_piecewise {s : Set X} [DecidablePred (· ∈ s)] (hs : MeasurableSet s)
    (κ η : Kernel X Y) [IsSubMarkovKernel κ] [IsSubMarkovKernel η] :
    IsSubMarkovKernel (Kernel.piecewise hs κ η) where
  isSubProbabilityMeasure x := by rw [Kernel.piecewise_apply]; split_ifs <;> infer_instance

instance isSubMarkovKernel_comap (κ : Kernel Y Z) [IsSubMarkovKernel κ] {g : X → Y}
    (hg : Measurable g) : IsSubMarkovKernel (κ.comap g hg) where
  isSubProbabilityMeasure x := by rw [Kernel.comap_apply]; infer_instance

/-- A measurable family of subprobability measures is a sub-Markov kernel. -/
instance isSubMarkovKernel_mk (f : X → Measure Y) (hf : Measurable f)
    [∀ x, IsSubProbabilityMeasure (f x)] : IsSubMarkovKernel ⟨f, hf⟩ where
  isSubProbabilityMeasure x := inferInstanceAs (IsSubProbabilityMeasure (f x))

instance isSubMarkovKernel_const (μ : Measure Y) [IsSubProbabilityMeasure μ] :
    IsSubMarkovKernel (Kernel.const X μ) where
  isSubProbabilityMeasure x := by rw [Kernel.const_apply]; infer_instance

instance isSubMarkovKernel_zero : IsSubMarkovKernel (0 : Kernel X Y) where
  isSubProbabilityMeasure x := by rw [zero_apply]; infer_instance

/-! ## Kernels into a point -/

variable {f : X → ℝ≥0∞}

/-- A measurable function as a kernel into a point: the point with that mass. -/
noncomputable def Kernel.mass (hf : Measurable f) : Kernel X PUnit.{v + 1} :=
  ⟨fun x ↦ f x • dirac PUnit.unit, hf.smul_measure _⟩

theorem Kernel.mass_apply (hf : Measurable f) (x : X) :
    Kernel.mass.{v} hf x = f x • dirac PUnit.unit :=
  rfl

theorem Kernel.isSubMarkovKernel_mass (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) :
    IsSubMarkovKernel (Kernel.mass.{v} hf) where
  isSubProbabilityMeasure x := ⟨by simpa [Kernel.mass_apply] using hf1 x⟩

/-- Composing with a mass kernel integrates its function. -/
theorem Kernel.mass_comp (hf : Measurable f) (μ : Measure X) :
    Kernel.mass.{v} hf ∘ₘ μ = (∫⁻ x, f x ∂μ) • dirac PUnit.unit := by
  ext s hs
  rw [bind_apply hs (Kernel.mass hf).measurable.aemeasurable]
  simp [Kernel.mass_apply, lintegral_mul_const _ hf]

end ProbabilityTheory

open ProbabilityTheory in
/-- A kernel cut off outside `s` composes with the restriction of the measure to `s`. -/
theorem MeasureTheory.Measure.piecewise_zero_comp {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {s : Set X} [DecidablePred (· ∈ s)] (hs : MeasurableSet s)
    (κ : Kernel X Y) (μ : Measure X) : Kernel.piecewise hs κ 0 ∘ₘ μ = κ ∘ₘ μ.restrict s := by
  ext t ht
  rw [bind_apply ht (Kernel.measurable _).aemeasurable, bind_apply ht κ.measurable.aemeasurable,
    ← lintegral_indicator hs]
  congr with x
  by_cases hx : x ∈ s <;> simp [Kernel.piecewise_apply, hx]
