module

public import Metrology.Couplings.Codensity
public import Metrology.Couplings.Divergences.Hellinger
public import Metrology.Couplings.Divergences.Kl
public import Metrology.Couplings.Divergences.Fill

/-! The Markov-tested codensity lifting `markovCodensity` and the equal-mass bind law `massEq`
(instances `kl`, `hellinger`) for generalized KL and `α`-Hellinger, which are not composable on
sub-probability measures (Rocq `GC_KL_full`, `GBL_KL_full`). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory Set GradedLifting InformationTheory
open scoped ENNReal

/-! ## Filling costs nothing at equal mass -/

section Fill

variable {X : Type*} [MeasurableSpace X]

/-- Adding the same finite mass at `none` to both sides does not raise an `f`-divergence with
`f 1 = 0`. -/
theorem fDiv_map_some_add_le {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) (hf1 : f 1 = 0) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : ℝ≥0∞} (hs : s ≠ ⊤) :
    fDiv f (μ.map some + s • dirac none) (ν.map some + s • dirac none) ≤ fDiv f μ ν := by
  have : IsFiniteMeasure (s • dirac (none : Option X)) := ⟨by simpa using hs.lt_top⟩
  rw [fDiv_eq_iSup_partition hf hf_cont]
  refine iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
  have hev (ρ : Measure X) [IsFiniteMeasure ρ] (i : Fin n) :
      ((ρ.map some + s • dirac (none : Option X) : Measure (Option X)) (k ⁻¹' {i})).toReal =
        (ρ ((k ∘ some) ⁻¹' {i})).toReal + ((s • dirac none) (k ⁻¹' {i})).toReal := by
    rw [Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      Measure.map_apply measurable_some (hk (measurableSet_singleton i))]
    rfl
  -- per partition cell: split off the none-mass, subadditivity of persp, and the none part
  -- costs s * f 1 = 0
  simp_rw [hev]
  refine (Finset.sum_le_sum fun i _ ↦ persp_add_le hf ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg).trans ?_
  simp only [persp_self ENNReal.toReal_nonneg, hf1, mul_zero, EReal.coe_zero, add_zero]
  exact sum_persp_le_fDiv hf hf_cont (hk.comp measurable_some)

/-- Filling the lost mass of two measures of equal mass does not raise an `f`-divergence with
`f 1 = 0`. -/
theorem fDiv_withBot_le {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) (hf1 : f 1 = 0) {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] (h : μ univ = ν univ) :
    fDiv f μ.withBot ν.withBot ≤ fDiv f μ ν := by
  rw [Measure.withBot, Measure.withBot, h]
  exact fDiv_map_some_add_le hf hf_cont hf1 (ENNReal.sub_ne_top ENNReal.one_ne_top)

end Fill

/-! ## The Markov-tested codensity lifting

`codensity klDivergence` is not complete, since KL is not composable (`not_isComposable_kl`).
Markov tests lose no mass, so equal-mass composition makes this variant complete. -/

namespace GradedDivergence

variable {B : Type v} {D : GradedDivergence.{u} B} {X Y : Type u} [MeasurableSpace X]
  [MeasurableSpace Y] {b : B} {R : X → Y → B} {μ : Measure X} {ν : Measure Y}

variable (D) in
/-- `codensity` with Markov tests whose premise is checked almost everywhere on the left
(Sato–Katsumata, §7; Rocq `GC_KL_full` tests with functions instead). -/
def markovCodensity [Add B] [LT B] [Top B] : GradedLifting.{u} B :=
  fun b {X Y} _ _ R μ ν ↦ ∀ ⦃I : Type u⦄ [MeasurableSpace I] ⦃c : B⦄, b + c < ⊤ →
    ∀ ⦃k : Kernel X I⦄ ⦃l : Kernel Y I⦄ [IsMarkovKernel k] [IsMarkovKernel l],
    (∀ᵐ x ∂μ, ∀ y, D (R x y + c) (k x) (l y)) → D (b + c) (k ∘ₘ μ) (l ∘ₘ ν)

theorem markovCodensity_mono [Add B] [Preorder B] [AddRightMono B] [Top B] [D.IsGraded]
    {b' : B} {R' : X → Y → B} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : D.markovCodensity b R μ ν) (hb : b ≤ b') (hR : R' ≤ R) : D.markovCodensity b' R' μ ν :=
  fun _ _ c hbc _ _ _ _ hkl ↦ IsGraded.mono (add_le_add_left hb c) <|
    h ((add_le_add_left hb c).trans_lt hbc) <| hkl.mono fun x hx y ↦
      IsGraded.mono (add_le_add_left (hR x y) c) (hx y)

theorem markovCodensity_frame [AddSemigroup B] [LT B] [Top B] {c : B}
    (h : D.markovCodensity b R μ ν) : D.markovCodensity (b + c) (fun x y ↦ R x y + c) μ ν := by
  intro I _ c' hbc k l _ _ hkl
  rw [add_assoc] at hbc ⊢
  exact h hbc (hkl.mono fun x hx y ↦ add_assoc (R x y) c c' ▸ hx y)

/-- Leftovers may be set to `⊤` off a set carrying the left measure: the premise is almost
everywhere. -/
theorem markovCodensity_restrict [Add B] [LT B] [Top B] {A : Set X} [DecidablePred (· ∈ A)]
    (hμ : μ Aᶜ = 0) (h : D.markovCodensity b R μ ν) :
    D.markovCodensity b (A.piecewise R fun _ _ ↦ ⊤) μ ν := by
  intro I _ c hbc k l _ _ hkl
  refine h hbc ?_
  filter_upwards [hkl, mem_ae_iff.2 (by rwa [compl_compl] : μ Aᶜᶜᶜ = 0)] with x hx hA y
  simpa [Set.piecewise_eq_of_mem _ _ _ (by simpa using hA)] using hx y

/-- A Dirac pair passes every test at its leftover: a property holding almost everywhere under a
point mass holds at the point, measurable or not. -/
theorem markovCodensity_dirac [Add B] [LT B] [Top B] (x : X) (y : Y) :
    D.markovCodensity (R x y) R (dirac x) (dirac y) := by
  intro I _ c _ k l _ _ hkl
  rw [dirac_bind k.measurable, dirac_bind l.measurable]
  by_contra h
  have h₁ := dirac_apply_of_mem (s := {x' | ¬∀ y, D (R x' y + c) (k x') (l y)}) fun hx ↦ h (hx y)
  exact zero_ne_one ((ae_iff.1 hkl).symm.trans h₁)

theorem markovCodensity_zero [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B] [Top B]
    [D.IsGraded] [D.IsReflexive] (b : B) (R : X → Y → B) :
    D.markovCodensity b R (0 : Measure X) (0 : Measure Y) := by
  intro I _ c _ k l _ _ _
  rw [bind_zero_left, bind_zero_left]
  exact IsGraded.mono zero_le (IsReflexive.refl _)

theorem markovCodensity_map [Add B] [LT B] [Top B] {X' Y' : Type u} [MeasurableSpace X']
    [MeasurableSpace Y'] {R : X' → Y' → B} {f : X → X'} {g : Y → Y'} (hf : Measurable f)
    (hg : Measurable g) (h : D.markovCodensity b (fun x y ↦ R (f x) (g y)) μ ν) :
    D.markovCodensity b R (μ.map f) (ν.map g) := by
  intro I _ c hbc k l _ _ hkl
  rw [bind_map_eq μ hf, bind_map_eq ν hg]
  exact h hbc (k := k.comap f hf) (l := l.comap g hg) <|
    (ae_of_ae_map hf.aemeasurable hkl).mono fun x hx y ↦ hx (g y)

/-- The Markov-tested lifting of a graded reflexive divergence is lawful. -/
instance isLawful_markovCodensity [AddCommMonoid B] [Preorder B] [CanonicallyOrderedAdd B]
    [Top B] [D.IsGraded] [D.IsReflexive] : (markovCodensity D).IsLawful where
  pure _ := markovCodensity_dirac _ _
  zero := markovCodensity_zero
  mono := markovCodensity_mono
  frame _ := markovCodensity_frame
  map := markovCodensity_map

/-- Leftovers may be set to `⊤` off a set carrying the left measure. -/
instance isSupportLocal_markovCodensity [Add B] [LT B] [Top B] :
    (markovCodensity D).IsSupportLocal :=
  ⟨fun _ ↦ markovCodensity_restrict⟩

/-- At budget `⊤` there is no test left. -/
instance isTopAbsorbing_markovCodensity [Add B] [Preorder B] [Top B] [CanonicallyOrderedAdd B] :
    (markovCodensity D).IsTopAbsorbing :=
  ⟨fun _ _ _ _ _ _ hc ↦ (le_self_add.not_gt hc).elim⟩

/-- Tests pass to the supremum of an increasing sequence: each measure lies below it, so the test
premise holds almost everywhere under each. -/
instance isLeftContinuous_markovCodensity [Add B] [LT B] [Top B] [D.IsLeftContinuous] :
    (markovCodensity D).IsLeftContinuous where
  iSup_left {X Y} _ _ b R μ _ hμ ν _ h := by
    intro I _ c hbc k l _ _ hkl
    rw [iSup_bind_of_monotone hμ k.measurable]
    exact IsLeftContinuous.iSup_left (fun _ _ hmn ↦ bind_mono_left (hμ hmn) k.measurable)
      fun n ↦ h n hbc (ae_mono (le_iSup μ n) hkl)

/-- Lifting equality gives the divergence: test with the identity kernel at slack `0`. -/
instance isSound_markovCodensity [AddZeroClass B] [Preorder B] [OrderTop B] [D.IsGraded]
    [D.IsReflexive] : (markovCodensity D).IsSound D where
  sound {X} _ b μ ν _ _ h := IsGraded.of_lt_top fun hb ↦ by
    have hkl (x y : X) : D (relCost (· = ·) x y + 0) (Kernel.id x) (Kernel.id y) := by
      obtain rfl | hxy := eq_or_ne x y
      · simpa [Kernel.id_apply] using IsReflexive.refl (dirac x)
      · simpa [Kernel.id_apply, hxy] using IsGraded.top (dirac x) (dirac y)
    simpa [id_comp] using h (c := 0) (by rwa [add_zero]) (ae_of_all _ fun x y ↦ hkl x y)

/-! ## Completeness from equal-mass composition -/

/-- Equal-mass composition makes the Markov-tested lifting complete: a test that fails on a null
set is repaired there by the right kernel, and Markov tests lose no mass. -/
theorem markovCodensity_complete {D : GradedDivergence.{u} ℝ≥0∞} [D.IsGraded] [D.IsReflexive]
    (hcomp : ∀ ⦃b c : ℝ≥0∞⦄ {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
      ⦃μ₁ μ₂ : Measure X⦄ [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
      ⦃κ η : Kernel X Y⦄ [IsSubMarkovKernel κ] [IsSubMarkovKernel η],
      (∀ x, κ x univ = η x univ) → D b μ₁ μ₂ → (∀ x, D c (κ x) (η x)) →
        D (b + c) (κ ∘ₘ μ₁) (η ∘ₘ μ₂))
    {X : Type u} [MeasurableSpace X] {b : ℝ≥0∞} {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (h : D b μ ν) : (markovCodensity D).Rel b (· = ·) μ ν := by
  classical
  intro I _ c _ k l _ _ hkl
  obtain ⟨N, hsub, hNm, hN⟩ := exists_measurable_superset_of_null
    (ae_iff.1 (hkl.mono fun x hx ↦ by simpa using hx x))
  let k' := Kernel.piecewise hNm l k
  have hk' : k' ∘ₘ μ = k ∘ₘ μ := Measure.comp_congr <| by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with x hx
    simp only [k', Kernel.piecewise_apply, hx, ↓reduceIte]
  rw [← hk']
  refine hcomp (fun _ ↦ by rw [measure_univ, measure_univ]) h fun x ↦ ?_
  rw [Kernel.piecewise_apply]
  split_ifs with hx
  · exact IsGraded.mono zero_le (IsReflexive.refl (l x))
  · exact not_not.1 fun h' ↦ hx (hsub h')

variable {X : Type u} [MeasurableSpace X] {μ ν : Measure X} {b : ℝ≥0∞}

/-- The Markov-tested KL lifting of equality is generalized KL within its budget. -/
theorem markovCodensity_kl_rel_eq_iff [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    (markovCodensity klDivergence).Rel b (· = ·) μ ν ↔ klDivergence b μ ν :=
  ⟨IsSound.sound, markovCodensity_complete fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦
    klDivergence_comp_of_mass_eq⟩

/-- The Markov-tested `α`-Hellinger lifting of equality is `α`-Hellinger within its budget. -/
theorem markovCodensity_hellinger_rel_eq_iff (α : ℝ) [hα : Fact (α ∈ Ioo (0 : ℝ) 1)]
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    (markovCodensity (hellingerDivergence α)).Rel b (· = ·) μ ν ↔ hellingerDivergence α b μ ν :=
  ⟨IsSound.sound, markovCodensity_complete (by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm hμ hκ
    exact hellingerDivergence_comp_of_mass_eq hα.out.1 hα.out.2 hm hμ hκ)⟩

/-- Reflexivity of the KL lifting is completeness at a measure and itself. -/
instance isReflexive_markovCodensity_kl : (markovCodensity klDivergence.{u}).IsReflexive :=
  ⟨fun μ _ ↦ markovCodensity_kl_rel_eq_iff.2 (IsReflexive.refl μ)⟩

/-- Reflexivity of the `α`-Hellinger lifting is completeness at a measure and itself. -/
instance isReflexive_markovCodensity_hellinger (α : ℝ) [Fact (α ∈ Ioo (0 : ℝ) 1)] :
    (markovCodensity (hellingerDivergence.{u} α)).IsReflexive :=
  ⟨fun μ _ ↦ (markovCodensity_hellinger_rel_eq_iff α).2 (IsReflexive.refl μ)⟩

/-- A KL lifting of equality bounds Mathlib's KL divergence (Rocq
`gcoupl_KL_full_implies_KL_classical`, here for sub-probability measures). -/
theorem klDiv_le_of_markovCodensity [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : (markovCodensity klDivergence).Rel b (· = ·) μ ν) : InformationTheory.klDiv μ ν ≤ b :=
  klDivergence_iff.1 (IsSound.sound h)

/-- No finite budget relates every pair: a point mass is at infinite KL from zero (Rocq
`no_GCFTop_KL_full`). -/
theorem not_absorbing_markovCodensity_kl (hb : b ≠ ⊤) :
    ¬ (markovCodensity klDivergence.{u}).Absorbing b := by
  intro h
  have := klDiv_le_of_markovCodensity (h (relCost (· = ·)) (dirac PUnit.unit.{u + 1}) 0)
  rw [InformationTheory.klDiv_of_not_ac fun hac ↦ by simpa using hac (s := univ)] at this
  exact hb (top_le_iff.1 this)

end GradedDivergence

/-! ## The equal-mass bind law

A Markov test after a sub-Markov kernel is no longer Markov, so it is filled on `none`, which
costs nothing at equal mass; data processing drops the fill again. -/

namespace GradedLifting.BindLaw

open GradedDivergence

variable {f : ℝ → ℝ} {γ : ℝ}

/-- The bind law for the Markov-tested lifting of a thresholded f-divergence `bofDivergence f γ`,
with continuation kernels that lose the same mass at every pair with finite leftover (Rocq
`GBL_KL_full`, whose `kl_sat_side` asks the right continuation to keep mass). -/
noncomputable def massEq (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (hf1 : f 1 = 0) (hf₀ : ∀ t, 0 ≤ t → 0 ≤ f t) :
    BindLaw (markovCodensity (bofDivergence.{u} f γ)) :=
  have : (bofDivergence.{u} f γ).IsGraded := isGraded_bofDivergence hf hf_cont
  { head μ ν R b := IsSubProbabilityMeasure μ ∧ IsSubProbabilityMeasure ν ∧
      markovCodensity (bofDivergence f γ) b R μ ν
    side _ _ R f g := ∀ x y, R x y < ⊤ → f x univ = g y univ
    sound := by
      rintro _ _ _ _ _ _ _ _ _ R _ μ ν f g _ _ ⟨hμ, hν, h⟩ hside hk I _ c hbc k l _ _ hkl
      have hae := Measure.ae_ae_of_ae_comp hkl
      -- test the head with the filled (Markov) kernels; equal mass makes filling free
      have hout := h hbc (k := (k ∘ₖ f).withBot) (l := (l ∘ₖ g).withBot) <|
        hae.mono fun x hx y ↦ by
          rcases lt_or_ge (R x y + c) ⊤ with hRc | hRc
          · have hR : R x y < ⊤ := le_self_add.trans_lt hRc
            have hm : (k ∘ₘ f x) univ = (l ∘ₘ g y) univ := by
              rw [Measure.comp_apply_univ, Measure.comp_apply_univ, hside x y hR]
            have h₁ := bofDivergence_iff.1 (hk x y hR hRc hx)
            rw [Kernel.withBot_apply, Kernel.withBot_apply, Kernel.comp_apply, Kernel.comp_apply]
            exact bofDivergence_iff.2 ((fDiv_withBot_le hf hf_cont hf1 hm).trans h₁)
          · rw [top_le_iff.1 hRc]
            exact IsGraded.top _ _
      -- the fill is dropped again by data processing
      rw [Measure.comp_assoc, Measure.comp_assoc, ← Kernel.dropBot_comp_withBot (k ∘ₖ f),
        ← Kernel.dropBot_comp_withBot (l ∘ₖ g), ← Measure.comp_assoc, ← Measure.comp_assoc]
      exact bofDivergence_comp_self hf hf_cont hf₀ _ hout
    mono_out := fun ⟨hμ, hν, h⟩ hb ↦ ⟨hμ, hν, markovCodensity_mono h hb le_rfl⟩
    head_supp := fun _ hμA ⟨hμ, hν, h⟩ ↦ ⟨hμ, hν, markovCodensity_restrict hμA h⟩
    side_supp := by
      intro _ _ _ _ _ _ _ _ R _ _ _ _ A _ h x y hxy
      by_cases hx : x ∈ A
      · exact h x y (by simpa [hx] using hxy)
      · simp [hx] at hxy }

/-- Equal-mass heads shift by framing. -/
instance headShift_massEq (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (hf1 : f 1 = 0) (hf₀ : ∀ t, 0 ≤ t → 0 ≤ f t) :
    (massEq (γ := γ) hf hf_cont hf1 hf₀).HeadShift :=
  ⟨fun _ ⟨hμ, hν, h⟩ ↦ ⟨hμ, hν, markovCodensity_frame h⟩⟩

/-- The generalized KL bind law: continuation kernels lose the same mass at related pairs (Rocq
`GBL_KL_full`). -/
noncomputable def kl : BindLaw (markovCodensity klDivergence.{u}) :=
  massEq convexOn_klFun continuous_klFun.continuousWithinAt klFun_one fun _ ↦ klFun_nonneg

/-- The `α`-Hellinger bind law, `massEq` at `hellFun α`. -/
noncomputable def hellinger (α : ℝ) [hα : Fact (α ∈ Ioo (0 : ℝ) 1)] :
    BindLaw (markovCodensity (hellingerDivergence.{u} α)) :=
  massEq (convexOn_hellFun hα.out.1 hα.out.2) (continuous_hellFun hα.out.1.le).continuousWithinAt
    (hellFun_one α) fun _ ↦ hellFun_nonneg hα.out.1 hα.out.2

end GradedLifting.BindLaw
