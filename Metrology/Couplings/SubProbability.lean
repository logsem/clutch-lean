module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Metrology.Couplings.Measure

/-! # Sub-probability measures and sub-Markov kernels

`IsSubProbabilityMeasure` and `IsSubMarkovKernel` (mass at most `1`), closed under `map`, `prod`,
`bind`, `∘ₖ`, `⊗ₖ` (Approximate Span Liftings, Def. 3.1). -/

@[expose] public section

universe v

open MeasureTheory Measure Set ENNReal

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-! ## Sub-probability measures -/

/-- A measure of total mass at most `1`. -/
class IsSubProbabilityMeasure (μ : Measure X) : Prop where
  measure_univ_le_one : μ univ ≤ 1

open IsSubProbabilityMeasure

namespace IsSubProbabilityMeasure

variable {μ : Measure X} [IsSubProbabilityMeasure μ]

/-- Every set has mass at most `1` under a sub-probability measure. -/
theorem measure_le_one (s : Set X) : μ s ≤ 1 :=
  (measure_mono (subset_univ s)).trans measure_univ_le_one

/-- Every set has real mass in `[0, 1]` under a sub-probability measure. -/
theorem toReal_mem_Icc (s : Set X) : (μ s).toReal ∈ Icc (0 : ℝ) 1 :=
  ⟨toReal_nonneg, toReal_le_of_le_ofReal zero_le_one (ofReal_one ▸ measure_le_one s)⟩

/-- Adding a constant under the integral adds at most that constant. -/
theorem lintegral_add_const_le (f : X → ℝ≥0∞) (c : ℝ≥0∞) : ∫⁻ x, f x + c ∂μ ≤ ∫⁻ x, f x ∂μ + c := by
  rw [lintegral_add_right _ measurable_const, lintegral_const]
  gcongr
  exact mul_le_of_le_one_right' measure_univ_le_one

/-- Cutting a constant off the integrand costs at most that constant. -/
theorem lintegral_le_tsub_add (f : X → ℝ≥0∞) (c : ℝ≥0∞) : ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x - c ∂μ + c :=
  calc ∫⁻ x, f x ∂μ ≤ ∫⁻ x, (f x - c) + c ∂μ := lintegral_mono fun _ ↦ le_tsub_add
    _ ≤ ∫⁻ x, f x - c ∂μ + c := lintegral_add_const_le _ _

/-- A function below `1` integrates to at most `1`. -/
theorem lintegral_le_one {f : X → ℝ≥0∞} (hf : ∀ x, f x ≤ 1) : ∫⁻ x, f x ∂μ ≤ 1 :=
  (lintegral_mono hf).trans (by simpa using measure_univ_le_one)

end IsSubProbabilityMeasure

/-- Zero or probability measures are sub-probability measures. -/
instance (priority := 100) IsZeroOrProbabilityMeasure.toIsSubProbabilityMeasure
    (μ : Measure X) [IsZeroOrProbabilityMeasure μ] : IsSubProbabilityMeasure μ where
  measure_univ_le_one := prob_le_one

section Closure

variable (μ : Measure X) [IsSubProbabilityMeasure μ]

/-- Sub-probability measures are finite. -/
instance (priority := 100) IsSubProbabilityMeasure.toIsFiniteMeasure : IsFiniteMeasure μ where
  measure_univ_lt_top := measure_univ_le_one.trans_lt one_lt_top

/-- Pushing forward keeps a measure sub-probability. -/
instance isSubProbabilityMeasure_map (f : X → Y) : IsSubProbabilityMeasure (μ.map f) where
  measure_univ_le_one := by
    by_cases hf : AEMeasurable f μ
    · rw [map_apply_of_aemeasurable hf .univ, preimage_univ]
      exact measure_univ_le_one
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [map_of_not_aemeasurable_of_ne_zero hf hμ]

/-- The product of sub-probability measures is sub-probability. -/
instance isSubProbabilityMeasure_prod (ν : Measure Y) [IsSubProbabilityMeasure ν] :
    IsSubProbabilityMeasure (μ.prod ν) where
  measure_univ_le_one := by
    rw [← univ_prod_univ, prod_prod]
    exact mul_le_one' measure_univ_le_one measure_univ_le_one

-- Not an instance: `Measure.bind` is junk for non-measurable kernels.
/-- Binding a sub-probability measure with a.e.-measurable sub-probability continuations is
sub-probability. -/
theorem isSubProbabilityMeasure_bind (f : X → Measure Y) [∀ x, IsSubProbabilityMeasure (f x)]
    (hf : AEMeasurable f μ := by fun_prop) : IsSubProbabilityMeasure (μ.bind f) :=
  ⟨(bind_apply .univ hf).trans_le (lintegral_le_one fun _ ↦ measure_univ_le_one)⟩

/-- Reweighting by a density bounded by `1` keeps a measure sub-probability. -/
theorem isSubProbabilityMeasure_withDensity_of_le_one {f : X → ℝ≥0∞} (hf : ∀ x, f x ≤ 1) :
    IsSubProbabilityMeasure (μ.withDensity f) :=
  ⟨by simpa using lintegral_le_one hf⟩

end Closure

/-- A bind of mass `1` comes from almost surely total continuations. -/
theorem ae_measure_univ_eq_one_of_bind {μ : Measure X} [IsSubProbabilityMeasure μ]
    {κ : X → Measure Y} [∀ x, IsSubProbabilityMeasure (κ x)] (hκ : Measurable κ)
    (h : μ.bind κ univ = 1) : ∀ᵐ x ∂μ, κ x univ = 1 := by
  rw [bind_apply .univ hκ.aemeasurable] at h
  refine ae_eq_of_ae_le_of_lintegral_le (.of_forall fun _ ↦ measure_univ_le_one)
    (h ▸ one_ne_top) aemeasurable_const ?_
  simpa [h] using measure_univ_le_one

end MeasureTheory

namespace ProbabilityTheory

open IsSubProbabilityMeasure
open Kernel
open PUnit (unit)

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-! ## Sub-Markov kernels -/

/-- A kernel whose measures all have total mass at most `1`. -/
class IsSubMarkovKernel (κ : Kernel X Y) : Prop where
  isSubProbabilityMeasure (x : X) : IsSubProbabilityMeasure (κ x)

namespace IsSubMarkovKernel

attribute [instance] isSubProbabilityMeasure

/-- Sub-Markov kernels are finite. -/
instance (priority := 100) toIsFiniteKernel (κ : Kernel X Y) [IsSubMarkovKernel κ] :
    IsFiniteKernel κ where
  exists_univ_le := ⟨1, one_lt_top, fun _ ↦ measure_univ_le_one⟩

end IsSubMarkovKernel

/-- Zero or Markov kernels are sub-Markov. -/
instance (priority := 100) IsZeroOrMarkovKernel.toIsSubMarkovKernel (κ : Kernel X Y)
    [IsZeroOrMarkovKernel κ] : IsSubMarkovKernel κ where
  isSubProbabilityMeasure _ := inferInstance

section Closure

variable (κ : Kernel X Y) [IsSubMarkovKernel κ]

/-- A sub-Markov kernel applied to a sub-probability measure gives a sub-probability measure. -/
instance isSubProbabilityMeasure_comp (μ : Measure X) [IsSubProbabilityMeasure μ] :
    IsSubProbabilityMeasure (κ ∘ₘ μ) :=
  isSubProbabilityMeasure_bind μ κ κ.measurable.aemeasurable

/-- Composites of sub-Markov kernels are sub-Markov. -/
instance isSubMarkovKernel_comp (η : Kernel Y Z) [IsSubMarkovKernel η] :
    IsSubMarkovKernel (η ∘ₖ κ) where
  isSubProbabilityMeasure x := by rw [comp_apply]; infer_instance

/-- Pushing a sub-Markov kernel forward gives a sub-Markov kernel. -/
instance isSubMarkovKernel_map (f : Y → Z) : IsSubMarkovKernel (κ.map f) where
  isSubProbabilityMeasure x := by
    by_cases hf : Measurable f
    · rw [map_apply _ hf]
      infer_instance
    · rw [map_of_not_measurable _ hf]
      exact ⟨by simp⟩

/-- Products of sub-Markov kernels are sub-Markov. -/
instance isSubMarkovKernel_prod (η : Kernel X Z) [IsSubMarkovKernel η] :
    IsSubMarkovKernel (κ ×ₖ η) where
  isSubProbabilityMeasure x := by rw [prod_apply]; infer_instance

/-- Composition-products of sub-Markov kernels are sub-Markov. -/
instance isSubMarkovKernel_compProd (η : Kernel (X × Y) Z) [IsSubMarkovKernel η] :
    IsSubMarkovKernel (κ ⊗ₖ η) where
  isSubProbabilityMeasure x := ⟨by
    rw [compProd_apply .univ]
    exact lintegral_le_one fun _ ↦ measure_univ_le_one⟩

/-- Gluing two sub-Markov kernels along a measurable set gives a sub-Markov kernel. -/
instance isSubMarkovKernel_piecewise {s : Set X} [DecidablePred (· ∈ s)] (hs : MeasurableSet s)
    (η : Kernel X Y) [IsSubMarkovKernel η] : IsSubMarkovKernel (piecewise hs κ η) where
  isSubProbabilityMeasure x := by rw [piecewise_apply]; split_ifs <;> infer_instance

end Closure

/-- Left sections of a sub-Markov kernel are sub-Markov. -/
instance isSubMarkovKernel_sectL (k : Kernel (X × Y) Z) [IsSubMarkovKernel k] (y : Y) :
    IsSubMarkovKernel (k.sectL y) where
  isSubProbabilityMeasure x := by rw [sectL_apply]; infer_instance

/-- Right sections of a sub-Markov kernel are sub-Markov. -/
instance isSubMarkovKernel_sectR (k : Kernel (X × Y) Z) [IsSubMarkovKernel k] (x : X) :
    IsSubMarkovKernel (k.sectR x) where
  isSubProbabilityMeasure y := by rw [sectR_apply]; infer_instance

/-- Precomposing a sub-Markov kernel with a measurable map keeps it sub-Markov. -/
instance isSubMarkovKernel_comap (κ : Kernel Y Z) [IsSubMarkovKernel κ] {g : X → Y}
    (hg : Measurable g) : IsSubMarkovKernel (κ.comap g hg) where
  isSubProbabilityMeasure x := by rw [Kernel.comap_apply]; infer_instance

/-- A measurable family of sub-probability measures is a sub-Markov kernel. -/
instance isSubMarkovKernel_mk (f : X → Measure Y) (hf : Measurable f)
    [∀ x, IsSubProbabilityMeasure (f x)] : IsSubMarkovKernel ⟨f, hf⟩ where
  isSubProbabilityMeasure x := inferInstanceAs (IsSubProbabilityMeasure (f x))

/-- Constant kernels at a sub-probability measure are sub-Markov. -/
instance isSubMarkovKernel_const (μ : Measure Y) [IsSubProbabilityMeasure μ] :
    IsSubMarkovKernel (const X μ) where
  isSubProbabilityMeasure x := by rw [const_apply]; infer_instance

/-- The zero kernel is sub-Markov. -/
instance isSubMarkovKernel_zero : IsSubMarkovKernel (0 : Kernel X Y) where
  isSubProbabilityMeasure x := by rw [zero_apply]; infer_instance

/-- A kernel cut off outside `s` composes with the restriction of the measure to `s`. -/
theorem _root_.MeasureTheory.Measure.piecewise_zero_comp {s : Set X} [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (κ : Kernel X Y) (μ : Measure X) :
    piecewise hs κ 0 ∘ₘ μ = κ ∘ₘ μ.restrict s := by
  ext t ht
  rw [bind_apply ht (piecewise hs κ 0).measurable.aemeasurable,
    bind_apply ht κ.measurable.aemeasurable, ← lintegral_indicator hs]
  congr with x
  by_cases hx : x ∈ s <;> simp [piecewise_apply, hx]

/-! ## Kernels into a point -/

section Mass

variable {f : X → ℝ≥0∞} (hf : Measurable f)

include hf

namespace Kernel

/-- A measurable function as a kernel into a point: the point with that mass. -/
noncomputable def mass : Kernel X PUnit.{v + 1} :=
  ⟨fun x ↦ f x • dirac unit, hf.smul_measure _⟩

/-- The mass kernel at `x` is the point with mass `f x`. -/
theorem mass_apply (x : X) : mass.{v} hf x = f x • dirac unit :=
  rfl

/-- A mass kernel with values at most `1` is sub-Markov. -/
theorem isSubMarkovKernel_mass (hf1 : ∀ x, f x ≤ 1) : IsSubMarkovKernel (mass.{v} hf) where
  isSubProbabilityMeasure x := ⟨by simpa [mass_apply] using hf1 x⟩

/-- Composing with a mass kernel integrates its function. -/
theorem mass_comp (μ : Measure X) : mass.{v} hf ∘ₘ μ = (∫⁻ x, f x ∂μ) • dirac unit := by
  ext s hs
  rw [bind_apply hs (mass hf).measurable.aemeasurable]
  simp [mass_apply, lintegral_mul_const _ hf]

end Kernel

end Mass

end ProbabilityTheory
