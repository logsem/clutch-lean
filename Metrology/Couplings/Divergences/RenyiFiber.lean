module

public import Metrology.Couplings.BindLaws
public import Metrology.Couplings.Divergences.Conversions

/-! Rényi bounds between images of a finite-valued map give Rényi liftings of equal images and
escort heads, by conditioning on the fibers. -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting
open scoped ENNReal

namespace GradedDivergence

variable {X Y Z : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [Fintype Z] [DiscreteMeasurableSpace Z] {f : X → Z} {g : Y → Z} {μ : Measure X}
  {ν : Measure Y} {α : ℝ} {ρ : ℝ≥0∞}

/-- Conditioning `μ` on the fibers of `f`. -/
noncomputable def fiberCond (μ : Measure X) (f : X → Z) : Kernel Z X :=
  ⟨fun z ↦ μ[|f ⁻¹' {z}], .of_discrete⟩

omit [Fintype Z] in
theorem fiberCond_apply (z : Z) : fiberCond μ f z = μ[|f ⁻¹' {z}] :=
  rfl

/-- Conditioning a finite measure gives zero or a probability measure. -/
instance isSubMarkovKernel_fiberCond [IsFiniteMeasure μ] : IsSubMarkovKernel (fiberCond μ f) :=
  ⟨fun z ↦ by rw [fiberCond_apply]; infer_instance⟩

/-- The law of total probability: recombining the fibers of `μ` along `μ.map f` gives `μ`. -/
theorem fiberCond_comp_map (hf : Measurable f) [IsFiniteMeasure μ] :
    fiberCond μ f ∘ₘ μ.map f = μ := by
  ext A hA
  rw [bind_apply hA (Kernel.aemeasurable _), lintegral_fintype]
  conv_rhs => rw [← sum_meas_smul_cond_fiber hf μ]
  simp [fiberCond_apply, map_apply hf (measurableSet_singleton _), mul_comm]

omit [Fintype Z] [DiscreteMeasurableSpace Z] in
theorem comap_comp_eq_comp_map (κ : Kernel Z X) (hg : Measurable g) :
    κ.comap g hg ∘ₘ ν = κ ∘ₘ ν.map g := by
  ext A hA
  rw [bind_apply hA (Kernel.aemeasurable _), bind_apply hA (Kernel.aemeasurable _),
    lintegral_map (κ.measurable_coe hA) hg]
  rfl

/-- Reweighting by a function of the fiber commutes with recombining the fibers. -/
theorem fiberCond_comp_withDensity (hf : Measurable f) (ξ : Measure Z) (w : Z → ℝ≥0∞) :
    (fiberCond μ f ∘ₘ ξ).withDensity (fun x ↦ w (f x)) = fiberCond μ f ∘ₘ ξ.withDensity w := by
  ext A hA
  have hF : Measurable fun x ↦ A.indicator (fun x ↦ w (f x)) x :=
    (Measurable.of_discrete.comp hf).indicator hA
  rw [withDensity_apply _ hA, ← lintegral_indicator hA,
    Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable,
    bind_apply hA (Kernel.aemeasurable _),
    lintegral_withDensity_eq_lintegral_mul _ .of_discrete (Kernel.measurable_coe _ hA)]
  refine lintegral_congr fun z ↦ ?_
  rw [Pi.mul_apply, lintegral_indicator hA, fiberCond_apply,
    setLIntegral_congr_fun_ae hA ((ae_cond_mem (hf (measurableSet_singleton z))).mono
      fun x hx _ ↦ by rw [show f x = z from hx]), setLIntegral_const]

variable [Fact (1 < α)] [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]

/-- A Rényi bound between the images of `μ` and `ν` lifts equal images: condition `μ` on the
fibers to witness the lifting. -/
theorem codensity_renyi_rel_of_map (hf : Measurable f) (hg : Measurable g)
    (h : renyiDivergence α ρ (μ.map f) (ν.map g)) :
    (codensity (renyiDivergence α)).Rel ρ (fun x y ↦ f x = g y) μ ν := by
  refine codensity_renyi_of_kernel (measurable_relCost_fiber hf) (r := (fiberCond μ f).comap g hg)
    (fun y ↦ ?_) ?_
  · have hF : MeasurableSet (f ⁻¹' {g y}) := hf (measurableSet_singleton _)
    change ∫⁻ x, _ ∂μ[|f ⁻¹' {g y}] ≤ 1
    rw [ProbabilityTheory.cond, lintegral_smul_measure,
      setLIntegral_congr_fun hF fun x hx ↦ by
        rw [relCost_of (S := fun x y ↦ f x = g y) hx, expBudget_zero], setLIntegral_const,
      one_mul]
    exact ENNReal.inv_mul_le_one _
  · have := IsComposable.comp_self (fiberCond μ f) h
    rwa [fiberCond_comp_map hf, ← comap_comp_eq_comp_map _ hg] at this

/-- A Rényi bound between the image of `μ` and the image of `ν` reweighted by `e^{-ρ₂}` gives an
escort head on equal images inside supports `A` and `B`, continuing at `ρ₂` of the image. -/
theorem escortHead_of_map (hf : Measurable f) (hg : Measurable g) {A : Set X} {B : Set Y}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (ρ₂ : Z → ℝ≥0∞) {R : X → Y → ℝ≥0∞}
    (hR : ∀ x y, x ∈ A → y ∈ B → f x = g y → R x y = ρ₂ (f x))
    (h : renyiDivergence α ρ (μ.map f) ((ν.map g).withDensity fun z ↦ (expBudget (ρ₂ z))⁻¹)) :
    BindLaw.EscortHead α μ ν R ρ := by
  classical
  refine ⟨fun x y ↦ y ∈ B ∧ f x = g y, fun x ↦ ρ₂ (f x),
    Kernel.piecewise hB ((fiberCond μ f).comap g hg) 0, A, inferInstance, by fun_prop, hA, hμA,
    inferInstance, inferInstance, fun y ↦ ?_, fun x y hx ⟨hy, hxy⟩ ↦ hR x y hx hy hxy, ?_⟩
  · by_cases hy : y ∈ B
    · simpa [Kernel.piecewise_apply, hy, fiberCond_apply] using
        ae_cond_mem (μ := μ) (hf (measurableSet_singleton (g y)))
    · simp [Kernel.piecewise_apply, hy]
  · rw [Measure.piecewise_zero_comp, restrict_eq_self_of_ae_mem (mem_ae_iff.2 hνB),
      comap_comp_eq_comp_map _ hg,
      fiberCond_comp_withDensity hf (w := fun z ↦ (expBudget (ρ₂ z))⁻¹)]
    have := IsComposable.comp_self (fiberCond μ f) h
    rwa [fiberCond_comp_map hf] at this

end GradedDivergence
