module

public import Metrology.Couplings.Divergences.Conversions

/-! # Rényi and zCDP liftings of equal images

Lifts the relation `f x = g y`, witnessed (`codensity_renyi_of_kernel`) by conditioning `μ` on the
fibers of `f`. Used by the randomized-response examples. Main results:
`codensity_renyi_rel_of_map`, `zcdpLifting_rel_of_fiber`. -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting Set
open scoped ENNReal

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] {μ : Measure X}

/-! ## The cost of equal images -/

section Cost

variable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z] {f : X → Z} {g : Y → Z}

/-- The cost of equal images is measurable in the left point. -/
theorem measurable_relCost_fiber (hf : Measurable f) (y : Y) :
    Measurable fun x ↦ (relCost (fun x y ↦ f x = g y) x y : ℝ≥0∞) := by
  have : (fun x ↦ (relCost (fun x y ↦ f x = g y) x y : ℝ≥0∞)) =
      (f ⁻¹' {g y})ᶜ.indicator fun _ ↦ (⊤ : ℝ≥0∞) := by
    ext x
    by_cases hx : f x = g y <;> simp [hx]
  rw [this]
  exact measurable_const.indicator (hf (measurableSet_singleton _)).compl

/-- Conditioning on the fiber over `g y` stays on equal images, so it pays no cost. -/
theorem lintegral_expBudget_relCost_cond_le (hf : Measurable f) (y : Y) :
    ∫⁻ x, expBudget (relCost (fun x y ↦ f x = g y) x y) ∂μ[|f ⁻¹' {g y}] ≤ 1 := by
  have hF : MeasurableSet (f ⁻¹' {g y}) := hf (measurableSet_singleton _)
  rw [ProbabilityTheory.cond, lintegral_smul_measure,
    setLIntegral_congr_fun hF fun x hx ↦ by
      rw [relCost_of (S := fun x y ↦ f x = g y) hx, expBudget_zero], setLIntegral_const,
    one_mul]
  exact ENNReal.inv_mul_le_one _

end Cost

variable [MeasurableSpace Y] {ν : Measure Y}

/-! ## Conditioning on the fibers -/

section FiberCond

variable {Z : Type*} [MeasurableSpace Z] [DiscreteMeasurableSpace Z] {f : X → Z} {g : Y → Z}

/-- Conditioning `μ` on the fibers of `f`. -/
noncomputable def fiberCond (μ : Measure X) (f : X → Z) : Kernel Z X :=
  ⟨fun z ↦ μ[|f ⁻¹' {z}], .of_discrete⟩

theorem fiberCond_apply (z : Z) : fiberCond μ f z = μ[|f ⁻¹' {z}] :=
  rfl

/-- Conditioning a finite measure gives zero or a probability measure. -/
instance isSubMarkovKernel_fiberCond [IsFiniteMeasure μ] : IsSubMarkovKernel (fiberCond μ f) :=
  ⟨fun z ↦ by rw [fiberCond_apply]; infer_instance⟩

/-- The law of total probability: recombining the fibers of `μ` along `μ.map f` gives `μ`. -/
theorem fiberCond_comp_map [Fintype Z] (hf : Measurable f) [IsFiniteMeasure μ] :
    fiberCond μ f ∘ₘ μ.map f = μ := by
  ext A hA
  rw [bind_apply hA (Kernel.aemeasurable _), lintegral_fintype]
  conv_rhs => rw [← sum_meas_smul_cond_fiber hf μ]
  simp [fiberCond_apply, map_apply hf (measurableSet_singleton _), mul_comm]

omit [DiscreteMeasurableSpace Z] in
/-- Precomposing a kernel with `g` is pushing the measure forward along `g`. -/
theorem _root_.ProbabilityTheory.Kernel.comap_comp_eq_comp_map (κ : Kernel Z X)
    (hg : Measurable g) : κ.comap g hg ∘ₘ ν = κ ∘ₘ ν.map g := by
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

end FiberCond

/-! ## Rényi liftings of equal images -/

section Renyi

variable {Z : Type u} [MeasurableSpace Z] [Fintype Z] [DiscreteMeasurableSpace Z] {f : X → Z}
  {g : Y → Z} {α : ℝ} {ρ : ℝ≥0∞} [Fact (1 < α)]
  [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]

/-- A Rényi bound between the images of `μ` and `ν` lifts equal images: condition `μ` on the
fibers to witness the lifting. -/
theorem codensity_renyi_rel_of_map (hf : Measurable f) (hg : Measurable g)
    (h : renyiDivergence α ρ (μ.map f) (ν.map g)) :
    (codensity (renyiDivergence α)).Rel ρ (fun x y ↦ f x = g y) μ ν := by
  refine codensity_renyi_of_kernel (measurable_relCost_fiber hf) (r := (fiberCond μ f).comap g hg)
    (fun y ↦ ?_) ?_
  · exact lintegral_expBudget_relCost_cond_le hf y
  · have := IsComposable.comp_self (fiberCond μ f) h
    rwa [fiberCond_comp_map hf, ← Kernel.comap_comp_eq_comp_map _ hg] at this

end Renyi

/-! ## zCDP liftings from fiber bounds

Same witness as `codensity_renyi_rel_of_map`, but under countable `Y`/`Z` instead of finite
discrete `Z`. -/

section Zcdp

variable {Z : Type*} [MeasurableSpace Z] [Countable Y] [MeasurableSingletonClass Y] [Countable Z]
  [MeasurableSingletonClass Z] {f : X → Z} {g : Y → Z} {ε : ℝ≥0∞}

/-- Conditioning `μ` on the fiber of `f` over `g y`: the witness kernel for fiber bounds. -/
noncomputable def fiberKernel (μ : Measure X) (f : X → Z) (g : Y → Z) : Kernel Y X :=
  (fiberCond μ f).comap g .of_discrete

/-- Conditioning on the fibers keeps a pointwise DP bound on the fibers. -/
theorem dp_fiberKernel (hf : Measurable f) (hg : Measurable g) [IsFiniteMeasure μ]
    (h : ∀ z, μ (f ⁻¹' {z}) ≤ expBudget ε * ν (g ⁻¹' {z})) :
    dp (ε, 0) μ (fiberKernel μ f g ∘ₘ ν) := by
  refine dp_of_forall_le fun A hA ↦ ?_
  have hF (z : Z) : MeasurableSet (f ⁻¹' {z}) := hf (measurableSet_singleton z)
  set φ : Z → ℝ≥0∞ := fun z ↦ μ[|f ⁻¹' {z}] A
  -- Split `μ A` over the fibers, bound each fiber by the DP hypothesis, then recombine along `ν`.
  calc μ A = ∑' z, μ (f ⁻¹' {z} ∩ A) := by
        rw [← measure_iUnion (fun z z' hz ↦ ((disjoint_singleton.2 hz).preimage f).mono
          inter_subset_left inter_subset_left) fun z ↦ (hF z).inter hA, ← iUnion_inter,
          ← preimage_iUnion, iUnion_singleton_eq_range, ← Set.univ_inter A]
        simp
    _ ≤ ∑' z, expBudget ε * (φ z * ν (g ⁻¹' {z})) := by
        refine ENNReal.tsum_le_tsum fun z ↦ ?_
        simp only [φ, cond_apply (hF z)]
        rcases eq_or_ne (μ (f ⁻¹' {z})) 0 with h0 | h0
        · exact (measure_mono inter_subset_left).trans (by simp [h0])
        calc μ (f ⁻¹' {z} ∩ A)
            = (μ (f ⁻¹' {z}))⁻¹ * μ (f ⁻¹' {z} ∩ A) * μ (f ⁻¹' {z}) := by
              rw [mul_right_comm, ENNReal.inv_mul_cancel h0 (measure_ne_top _ _), one_mul]
          _ ≤ (μ (f ⁻¹' {z}))⁻¹ * μ (f ⁻¹' {z} ∩ A) * (expBudget ε * ν (g ⁻¹' {z})) := by
              gcongr
              exact h z
          _ = _ := by ring
    _ = expBudget ε * (fiberKernel μ f g ∘ₘ ν) A := by
        rw [ENNReal.tsum_mul_left, Measure.bind_apply hA (Kernel.aemeasurable _)]
        change _ = expBudget ε * ∫⁻ y, φ (g y) ∂ν
        rw [← lintegral_map (f := φ) .of_discrete hg, lintegral_countable']
        simp [map_apply hg (measurableSet_singleton _), φ]

/-- The fiber kernel stays on equal images, so it pays no cost. -/
theorem lintegral_fiberKernel_le (hf : Measurable f) (y : Y) :
    ∫⁻ x, expBudget (relCost (fun x y ↦ f x = g y) x y) ∂(fiberKernel μ f g y) ≤ 1 :=
  lintegral_expBudget_relCost_cond_le hf y

/-- Fibers with a pointwise DP bound give a zCDP lifting of equal images: condition `μ` on the
fibers to witness each Rényi lifting. -/
theorem zcdpLifting_rel_of_fiber (hf : Measurable f) (hg : Measurable g)
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : ∀ z, μ (f ⁻¹' {z}) ≤ expBudget ε * ν (g ⁻¹' {z})) :
    zcdpLifting.Rel (ε, 0) (fun x y ↦ f x = g y) μ ν := by
  refine concentratedLifting_rel_iff.2 fun α _ ↦ ?_
  rw [mul_zero, add_zero]
  have hr := lintegral_fiberKernel_le (μ := μ) (g := g) hf
  have := isSubMarkovKernel_of_lintegral_expBudget_le hr
  exact codensity_renyi_of_kernel (measurable_relCost_fiber hf) hr
    (renyi_of_dp α.2 (dp_fiberKernel hf hg h))

end Zcdp

end GradedDivergence
