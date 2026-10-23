module

public import Metrology.Couplings.Divergences.Conversions

/-! # Rényi and zCDP liftings of equal images

Lifts the relation `f x = g y` by conditioning `μ` on the fibers of `f`, giving the Rényi and zCDP
liftings of equal images. -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting Set
open scoped ENNReal

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] {μ : Measure X} {Z : Type u} [MeasurableSpace Z]
  {f : X → Z} {g : Y → Z}

/-! ## The cost of equal images -/

/-- The cost of equal images is measurable in the left point. -/
theorem measurable_relCost_fiber [MeasurableSingletonClass Z] (hf : Measurable f) (y : Y) :
    Measurable fun x ↦ (relCost (fun x y ↦ f x = g y) x y : ℝ≥0∞) := by
  have : (fun x ↦ (relCost (fun x y ↦ f x = g y) x y : ℝ≥0∞)) =
      (f ⁻¹' {g y})ᶜ.indicator fun _ ↦ (⊤ : ℝ≥0∞) := by
    ext x
    by_cases hx : f x = g y <;> simp [hx]
  rw [this]
  exact measurable_const.indicator (hf (measurableSet_singleton _)).compl

/-- Conditioning on the fiber over `g y` stays on equal images, so it pays no cost. -/
theorem lintegral_expBudget_relCost_cond_le [MeasurableSingletonClass Z] (hf : Measurable f)
    (y : Y) :
    ∫⁻ x, expBudget (relCost (fun x y ↦ f x = g y) x y) ∂μ[|f ⁻¹' {g y}] ≤ 1 := by
  have hF : MeasurableSet (f ⁻¹' {g y}) := hf (measurableSet_singleton _)
  rw [ProbabilityTheory.cond, lintegral_smul_measure,
    setLIntegral_congr_fun hF fun x hx ↦ by
      rw [relCost_of (S := fun x y ↦ f x = g y) hx, expBudget_zero], setLIntegral_const,
    one_mul]
  exact ENNReal.inv_mul_le_one _

variable [MeasurableSpace Y] {ν : Measure Y}

/-! ## Conditioning on the fibers -/

section FiberCond

variable [DiscreteMeasurableSpace Z]

/-- Conditioning `μ` on the fibers of `f`. -/
noncomputable def fiberCond (μ : Measure X) (f : X → Z) : Kernel Z X :=
  ⟨fun z ↦ μ[|f ⁻¹' {z}], .of_discrete⟩

/-- The fiber kernel at `z` is `μ` conditioned on the fiber over `z`. -/
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

/-- Reweighting by a function of the fiber commutes with recombining the fibers. -/
theorem fiberCond_comp_withDensity (hf : Measurable f) (ξ : Measure Z) (w : Z → ℝ≥0∞) :
    (fiberCond μ f ∘ₘ ξ).withDensity (fun x ↦ w (f x)) = fiberCond μ f ∘ₘ ξ.withDensity w := by
  ext A hA
  have hF : Measurable fun x ↦ A.indicator (fun x ↦ w (f x)) x :=
    (Measurable.of_discrete.comp hf).indicator hA
  rw [withDensity_apply _ hA, ← lintegral_indicator hA,
    lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable,
    bind_apply hA (Kernel.aemeasurable _),
    lintegral_withDensity_eq_lintegral_mul _ .of_discrete (Kernel.measurable_coe _ hA)]
  refine lintegral_congr fun z ↦ ?_
  rw [Pi.mul_apply, lintegral_indicator hA, fiberCond_apply,
    setLIntegral_congr_fun_ae hA ((ae_cond_mem (hf (measurableSet_singleton z))).mono
      fun x hx _ ↦ by rw [show f x = z from hx]), setLIntegral_const]

end FiberCond

/-! ## Liftings of equal images for composable divergences -/

section Fintype

variable [Fintype Z] [DiscreteMeasurableSpace Z] [IsSubProbabilityMeasure μ]
  [IsSubProbabilityMeasure ν]

/-- A bound between the images of `μ` and `ν` lifts equal images in the codensity lifting of a
composable divergence, when no image charged by `μ` is null for `ν`: bind the fibers. -/
theorem codensity_rel_of_map {B : Type*} [AddCommMonoid B] [PartialOrder B]
    [CanonicallyOrderedAdd B] [OrderTop B] {D : GradedDivergence.{u} B} [D.IsGraded]
    [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] {ρ : B} (hf : Measurable f) (hg : Measurable g)
    (hfib : ∀ z, ν (g ⁻¹' {z}) = 0 → μ (f ⁻¹' {z}) = 0) (h : D ρ (μ.map f) (ν.map g)) :
    (codensity D).Rel ρ (fun x y ↦ f x = g y) μ ν := by
  classical
  rw [codensity_rel_iff]
  intro I _ c _ k l _ _ hkl
  have e1 : k ∘ₘ μ = (k ∘ₖ fiberCond μ f) ∘ₘ μ.map f := by
    rw [← comp_assoc, fiberCond_comp_map hf]
  have e2 : l ∘ₘ ν = (l ∘ₖ fiberCond ν g) ∘ₘ ν.map g := by
    rw [← comp_assoc, fiberCond_comp_map hg]
  rw [e1, e2]
  refine IsComposable.comp h fun z ↦ ?_
  rw [Kernel.comp_apply, Kernel.comp_apply, fiberCond_apply, fiberCond_apply]
  by_cases hμz : μ (f ⁻¹' {z}) = 0
  · rw [cond_eq_zero_of_meas_eq_zero hμz, bind_zero_left]
    exact IsZeroLeft.zero_left _ _
  have hνz : ν (g ⁻¹' {z}) ≠ 0 := fun h0 ↦ hμz (hfib z h0)
  have hF : MeasurableSet (f ⁻¹' {z}) := hf (measurableSet_singleton z)
  have hG : MeasurableSet (g ⁻¹' {z}) := hg (measurableSet_singleton z)
  have : IsProbabilityMeasure μ[|f ⁻¹' {z}] := cond_isProbabilityMeasure hμz
  have : IsProbabilityMeasure ν[|g ⁻¹' {z}] := cond_isProbabilityMeasure hνz
  -- on the product of the two fibers the tests are related; elsewhere use `l` on both sides
  set π := (μ[|f ⁻¹' {z}]).prod (ν[|g ⁻¹' {z}])
  have hS : MeasurableSet ((f ⁻¹' {z}) ×ˢ (g ⁻¹' {z})) := hF.prod hG
  set L := l.comap Prod.snd measurable_snd
  set K := Kernel.piecewise hS (k.comap Prod.fst measurable_fst) L
  have hK (p : X × Y) : D c (K p) (L p) := by
    by_cases hp : p ∈ (f ⁻¹' {z}) ×ˢ (g ⁻¹' {z})
    · simp only [K, L, Kernel.piecewise_apply, hp, ↓reduceIte, Kernel.comap_apply]
      exact hkl _ _ ((mem_singleton_iff.1 hp.1).trans (mem_singleton_iff.1 hp.2).symm)
    · simp only [K, Kernel.piecewise_apply, hp, ↓reduceIte]
      exact IsGraded.mono zero_le (IsReflexive.refl _)
  have hπ : ∀ᵐ p ∂π, p ∈ (f ⁻¹' {z}) ×ˢ (g ⁻¹' {z}) := by
    rw [ae_prod_mem_iff_ae_ae_mem hS]
    filter_upwards [ae_cond_mem hF] with x hx
    filter_upwards [ae_cond_mem hG] with y hy
    exact ⟨hx, hy⟩
  have hKπ : K ∘ₘ π = k ∘ₘ μ[|f ⁻¹' {z}] := by
    rw [comp_congr (κ := K) (η := k.comap Prod.fst measurable_fst)
        (hπ.mono fun p hp ↦ by simp [K, Kernel.piecewise_apply, hp]),
      Kernel.comap_comp_eq_comp_map _ measurable_fst, map_fst_prod, measure_univ, one_smul]
  have hLπ : L ∘ₘ π = l ∘ₘ ν[|g ⁻¹' {z}] := by
    rw [Kernel.comap_comp_eq_comp_map _ measurable_snd, map_snd_prod, measure_univ,
      one_smul]
  rw [← hKπ, ← hLπ]
  exact zero_add c ▸ IsComposable.comp (IsReflexive.refl π) hK

/-! ## Rényi liftings of equal images -/

/-- A Rényi bound between the images of `μ` and `ν` lifts equal images: condition `μ` on the
fibers to witness the lifting. -/
theorem codensity_renyi_rel_of_map {α : ℝ} {ρ : ℝ≥0∞} [Fact (1 < α)] (hf : Measurable f)
    (hg : Measurable g)
    (h : renyiDivergence α ρ (μ.map f) (ν.map g)) :
    (codensity (renyiDivergence α)).Rel ρ (fun x y ↦ f x = g y) μ ν := by
  refine codensity_renyi_of_kernel (measurable_relCost_fiber hf) (r := (fiberCond μ f).comap g hg)
    (fun y ↦ ?_) ?_
  · exact lintegral_expBudget_relCost_cond_le hf y
  · have := IsComposable.comp_self (fiberCond μ f) h
    rwa [fiberCond_comp_map hf, ← Kernel.comap_comp_eq_comp_map _ hg] at this

end Fintype

/-! ## zCDP liftings from fiber bounds -/

section Zcdp

variable [Countable Y] [MeasurableSingletonClass Y] [Countable Z] [MeasurableSingletonClass Z]
  {ε : ℝ≥0∞}

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
          ← preimage_iUnion, iUnion_singleton_eq_range, ← univ_inter A]
        simp
    _ ≤ ∑' z, expBudget ε * (φ z * ν (g ⁻¹' {z})) := by
        refine ENNReal.tsum_le_tsum fun z ↦ ?_
        simp only [φ, cond_apply (hF z)]
        rcases eq_or_ne (μ (f ⁻¹' {z})) 0 with h0 | h0
        · exact (measure_mono inter_subset_left).trans (by simp [h0])
        calc μ (f ⁻¹' {z} ∩ A)
          _ = (μ (f ⁻¹' {z}))⁻¹ * μ (f ⁻¹' {z} ∩ A) * μ (f ⁻¹' {z}) := by
              rw [mul_right_comm, ENNReal.inv_mul_cancel h0 (measure_ne_top _ _), one_mul]
          _ ≤ (μ (f ⁻¹' {z}))⁻¹ * μ (f ⁻¹' {z} ∩ A) * (expBudget ε * ν (g ⁻¹' {z})) := by
              gcongr
              exact h z
          _ = _ := by ring
    _ = expBudget ε * (fiberKernel μ f g ∘ₘ ν) A := by
        rw [ENNReal.tsum_mul_left, bind_apply hA (Kernel.aemeasurable _)]
        change _ = expBudget ε * ∫⁻ y, φ (g y) ∂ν
        rw [← lintegral_map .of_discrete hg, lintegral_countable']
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
