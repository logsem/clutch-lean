module

public import Metrology.Couplings.BindLaw

/-! The codensity lifting of a graded divergence (Sato–Katsumata, §7). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

namespace GradedDivergence

open GradedLifting

variable {B : Type v} {D : GradedDivergence.{u} B} {X Y X' Y' : Type u} [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y'] {b : B} {R : X → Y → B}
  {μ : Measure X} {ν : Measure Y}

/-! ## The codensity lifting -/

variable (D) in
/-- The codensity lifting: every test whose kernels are within the leftover plus a slack at each
pair stays within the budget plus that slack after binding (Sato–Katsumata, §7). Tests where the
budget plus slack is `⊤` are left out: they are vacuous under `IsGraded`, and dropping them makes
framing free and `le_codensity` independent of `IsGraded`. -/
def codensity [Add B] [LT B] [Top B] : GradedLifting.{u} B :=
  fun b {X Y} _ _ R μ ν ↦ ∀ ⦃I : Type u⦄ [MeasurableSpace I] ⦃c : B⦄, b + c < ⊤ →
    ∀ ⦃k : Kernel X I⦄ ⦃l : Kernel Y I⦄ [IsSubMarkovKernel k] [IsSubMarkovKernel l],
    (∀ x y, D (R x y + c) (k x) (l y)) → D (b + c) (k ∘ₘ μ) (l ∘ₘ ν)

theorem codensity_def [Add B] [LT B] [Top B] :
    D.codensity b R μ ν ↔ ∀ ⦃I : Type u⦄ [MeasurableSpace I] ⦃c : B⦄, b + c < ⊤ →
      ∀ ⦃k : Kernel X I⦄ ⦃l : Kernel Y I⦄ [IsSubMarkovKernel k] [IsSubMarkovKernel l],
      (∀ x y, D (R x y + c) (k x) (l y)) → D (b + c) (k ∘ₘ μ) (l ∘ₘ ν) :=
  Iff.rfl

/-- Relational unfolding: off the relation the test obligation is vacuous. -/
theorem codensity_rel_iff [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B] [Top B]
    [D.IsGraded] {S : X → Y → Prop} :
    (codensity D).Rel b S μ ν ↔ ∀ ⦃I : Type u⦄ [MeasurableSpace I] ⦃c : B⦄, b + c < ⊤ →
      ∀ ⦃k : Kernel X I⦄ ⦃l : Kernel Y I⦄ [IsSubMarkovKernel k] [IsSubMarkovKernel l],
      (∀ x y, S x y → D c (k x) (l y)) → D (b + c) (k ∘ₘ μ) (l ∘ₘ ν) := by
  refine ⟨fun h I _ c hbc k l _ _ hkl ↦ h hbc fun x y ↦ ?_,
    fun h I _ c hbc k l _ _ hkl ↦ h hbc fun x y hS ↦ by simpa [hS] using hkl x y⟩
  by_cases hS : S x y
  · simpa [hS] using hkl x y hS
  · exact IsGraded.of_top_le (by simp [hS]) _ _

/-! ## Structural laws -/

theorem codensity_dirac [Add B] [LT B] [Top B] (x : X) (y : Y) :
    D.codensity (R x y) R (dirac x) (dirac y) := by
  intro I _ c _ k l _ _ hkl
  rw [dirac_bind k.measurable, dirac_bind l.measurable]
  exact hkl x y

theorem codensity_zero [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B] [Top B]
    [D.IsGraded] [D.IsReflexive] (b : B) (R : X → Y → B) :
    D.codensity b R (0 : Measure X) (0 : Measure Y) := by
  intro I _ c _ k l _ _ _
  rw [bind_zero_left, bind_zero_left]
  exact IsGraded.mono zero_le (IsReflexive.refl _)

theorem codensity_mono [Add B] [Preorder B] [AddRightMono B] [Top B] [D.IsGraded]
    {b' : B} {R' : X → Y → B} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : D.codensity b R μ ν) (hb : b ≤ b') (hR : R' ≤ R) : D.codensity b' R' μ ν := by
  intro I _ c hbc k l _ _ hkl
  exact IsGraded.mono (add_le_add_left hb c) <| h ((add_le_add_left hb c).trans_lt hbc)
    fun x y ↦ IsGraded.mono (add_le_add_left (hR x y) c) (hkl x y)

theorem codensity_frame [AddSemigroup B] [LT B] [Top B] {c : B} (h : D.codensity b R μ ν) :
    D.codensity (b + c) (fun x y ↦ R x y + c) μ ν := by
  intro I _ c' hbc k l _ _ hkl
  rw [add_assoc] at hbc ⊢
  exact h hbc fun x y ↦ add_assoc (R x y) c c' ▸ hkl x y

theorem codensity_map [Add B] [LT B] [Top B] {R : X' → Y' → B} {f : X → X'} {g : Y → Y'}
    (hf : Measurable f) (hg : Measurable g) (h : D.codensity b (fun x y ↦ R (f x) (g y)) μ ν) :
    D.codensity b R (μ.map f) (ν.map g) := by
  intro I _ c hbc k l _ _ hkl
  rw [bind_map_eq μ hf, bind_map_eq ν hg]
  exact h hbc (k := k.comap f hf) (l := l.comap g hg) fun x y ↦ hkl (f x) (g y)

/-- Binding with kernels lifted wherever the leftover is finite; the other pairs pass every test
by `IsGraded.top`. -/
theorem codensity_bind [Add B] [Preorder B] [CanonicallyOrderedAdd B] [OrderTop B]
    [D.IsGraded] {R' : X' → Y' → B} {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f]
    [IsSubMarkovKernel g] (h : D.codensity b R μ ν)
    (hfg : ∀ x y, R x y < ⊤ → D.codensity (R x y) R' (f x) (g y)) :
    D.codensity b R' (f ∘ₘ μ) (g ∘ₘ ν) := by
  intro I _ c hbc k l _ _ hkl
  rw [comp_assoc, comp_assoc]
  refine h hbc fun x y ↦ ?_
  rw [Kernel.comp_apply, Kernel.comp_apply]
  exact IsGraded.of_lt_top fun hRc ↦ hfg x y (le_self_add.trans_lt hRc) hRc hkl

/-- The codensity lifting of a graded reflexive divergence is lawful. -/
instance isLawful_codensity [AddCommMonoid B] [Preorder B] [CanonicallyOrderedAdd B] [Top B]
    [D.IsGraded] [D.IsReflexive] : (codensity D).IsLawful where
  pure _ := codensity_dirac _ _
  zero := codensity_zero
  mono := codensity_mono
  frame _ := codensity_frame
  map := codensity_map

/-- The codensity lifting of a graded divergence binds (Rocq `cod_bind`). -/
instance hasBind_codensity [Add B] [Preorder B] [CanonicallyOrderedAdd B] [OrderTop B]
    [D.IsGraded] : (codensity D).HasBind where
  bind := codensity_bind

/-! ## Soundness and completeness -/

/-- The codensity lifting is sound exactly when point masses are within budget `0` of
themselves: the identity test at slack `0` reads the divergence off a lifting of equality. -/
theorem codensity_isSound_iff [AddZeroClass B] [Preorder B] [OrderTop B] [D.IsGraded] :
    (codensity D).IsSound D ↔
      ∀ {X : Type u} [MeasurableSpace X] (x : X), D 0 (dirac x) (dirac x) := by
  refine ⟨fun _ X _ x ↦ IsSound.sound (L := codensity D) ?_, fun hD ↦ ⟨fun {X} _ b μ ν _ _ h ↦ ?_⟩⟩
  · exact relCost_of (B := B) rfl ▸ codensity_dirac x x
  refine IsGraded.of_lt_top fun hb ↦ ?_
  simpa [id_comp] using h (k := Kernel.id) (l := Kernel.id) (c := 0) (by rwa [add_zero])
    fun x y ↦ by
      obtain rfl | hxy := eq_or_ne x y
      · simpa [Kernel.id_apply] using hD x
      · simpa [Kernel.id_apply, hxy] using IsGraded.top (dirac x) (dirac y)

/-- The codensity lifting of a graded reflexive divergence is sound for it. -/
instance isSound_codensity [AddZeroClass B] [Preorder B] [OrderTop B] [D.IsGraded]
    [D.IsReflexive] : (codensity D).IsSound D :=
  codensity_isSound_iff.2 fun _ ↦ IsReflexive.refl _

/-- The codensity lifting of a divergence is complete for it exactly when the divergence is
composable (Sato–Katsumata, Thm. 8.2). -/
theorem codensity_isComplete_iff [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B]
    [OrderTop B] [D.IsGraded] : (codensity D).IsComplete D ↔ D.IsComposable := by
  refine ⟨fun _ ↦ ⟨fun _ _ ↦ fun h hκη ↦ ?_⟩,
    fun _ ↦ ⟨fun {X} _ b μ ν _ _ h ↦ codensity_rel_iff.2 fun I _ c _ k l _ _ hkl ↦
      IsComposable.comp h fun x ↦ hkl x x rfl⟩⟩
  exact IsGraded.of_lt_top fun hbc ↦
    codensity_rel_iff.1 (IsComplete.complete h) hbc fun x y hxy ↦ hxy ▸ hκη x

/-- The codensity lifting of a composable divergence is complete for it. -/
instance isComplete_codensity [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B]
    [OrderTop B] [D.IsGraded] [D.IsComposable] : (codensity D).IsComplete D :=
  codensity_isComplete_iff.2 ‹_›

/-- The fundamental property: lifting equality is the divergence. -/
theorem codensity_rel_eq_iff [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B]
    [OrderTop B] [D.IsGraded] [D.IsReflexive] [D.IsComposable] {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    (codensity D).Rel b (· = ·) μ ν ↔ D b μ ν :=
  ⟨IsSound.sound, IsComplete.complete⟩

/-! ## Lifting classes from divergence classes -/

/-- The zero measure on the left passes every test (Rocq `GCFamDZeroL_cod`). -/
instance isZeroLeft_codensity [Add B] [LT B] [Top B] [D.IsZeroLeft] :
    (codensity D).IsZeroLeft where
  zero_left b R ν _ := by
    intro I _ c _ k l _ _ _
    rw [bind_zero_left]
    exact IsZeroLeft.zero_left _ _

/-- Tests pass to the supremum of an increasing sequence (Rocq `GCFamLim_cod`). -/
instance isLeftContinuous_codensity [Add B] [LT B] [Top B] [D.IsLeftContinuous] :
    (codensity D).IsLeftContinuous where
  iSup_left {X Y} _ _ b R μ _ hμ ν _ h := by
    intro I _ c hbc k l _ _ hkl
    rw [iSup_bind_of_monotone hμ k.measurable]
    exact IsLeftContinuous.iSup_left (fun _ _ hmn ↦ bind_mono_left (hμ hmn) k.measurable)
      fun n ↦ h n hbc hkl

/-- Off a set carrying the left measure, the test kernel is replaced by the zero kernel. -/
instance isSupportLocal_codensity [Add B] [LT B] [Top B] [D.IsZeroLeft] :
    (codensity D).IsSupportLocal where
  restrict {X Y} _ _ b R μ ν A _ hA hμ h := by
    intro I _ c hbc k l _ _ hkl
    rw [← restrict_eq_self_of_ae_mem (mem_ae_iff.2 hμ), ← piecewise_zero_comp hA]
    refine h hbc fun x y ↦ ?_
    by_cases hx : x ∈ A
    · simpa [Kernel.piecewise_apply, hx] using hkl x y
    · simpa [Kernel.piecewise_apply, hx] using IsZeroLeft.zero_left _ (l y)

/-- Reflexivity of the lifting composes each test with the divergence's reflexivity, so it needs
`IsComposable`, not `IsComplete` (Rocq `cod_diag`). -/
instance isReflexive_codensity [AddZeroClass B] [LT B] [Top B] [D.IsReflexive] [D.IsComposable] :
    (codensity D).IsReflexive where
  refl μ _ := by
    intro I _ c _ k l _ _ hkl
    exact IsComposable.comp (IsReflexive.refl μ) fun x ↦ by simpa using hkl x x

/-- A larger budget `b' + c` comes from a larger budget `b'` at the same slack. -/
instance isBudgetClosed_codensity [AddCommSemigroup B] [Preorder B] [CanonicallyOrderedAdd B]
    [OrderTop B] [D.IsGraded] [D.IsBudgetClosed] : (codensity D).IsBudgetClosed where
  of_forall_gt {X Y} _ _ b R μ ν _ _ h := by
    intro I _ c _ k l _ _ hkl
    refine IsBudgetClosed.of_forall_gt fun d hd ↦ ?_
    obtain ⟨b', hb, rfl⟩ := exists_lt_and_add_eq_of_add_lt hd
    exact IsGraded.of_lt_top fun hbc ↦ h b' hb hbc hkl

/-- The test kernels keep the mass on `T` and on `T'`, sent to a point. -/
instance isMassDetecting_codensity [AddZeroClass B] [Preorder B] [OrderTop B] [D.IsGraded]
    [D.IsReflexive] [D.IsZeroLeft] {s : ℝ≥0∞ →+o B} [D.IsMassDetecting s] :
    (codensity D).IsMassDetecting s where
  measure_le_add {X Y} _ _ δ S μ ν _ _ T T' hT hT' h hS := by
    classical
    let k := Kernel.piecewise hT (Kernel.const X (dirac PUnit.unit.{u + 1})) 0
    let l := Kernel.piecewise hT' (Kernel.const Y (dirac PUnit.unit.{u + 1})) 0
    have hkl : D (s δ) (k ∘ₘ μ) (l ∘ₘ ν) := IsGraded.of_lt_top fun hδ ↦
      add_zero (s δ) ▸ h (c := 0) (by rwa [add_zero]) fun x y ↦ by
        by_cases hxy : S x y
        · by_cases hx : x ∈ T
          · simpa [k, l, Kernel.piecewise_apply, hxy, hx, hS x y hxy hx] using
              IsReflexive.refl (dirac PUnit.unit)
          · simpa [k, Kernel.piecewise_apply, hxy, hx] using IsZeroLeft.zero_left 0 (l y)
        · simpa [hxy] using IsGraded.top (k x) (l y)
    rw [piecewise_zero_comp, piecewise_zero_comp, const_comp, const_comp, restrict_apply_univ,
      restrict_apply_univ] at hkl
    exact IsMassDetecting.le_add_of (IsSubProbabilityMeasure.measure_le_one T)
      (IsSubProbabilityMeasure.measure_le_one T') hkl

/-! ## Absorbing budgets -/

/-- At budget `⊤` there is no test left. -/
theorem codensity_top [Add B] [Preorder B] [Top B] [CanonicallyOrderedAdd B] (R : X → Y → B)
    (μ : Measure X) (ν : Measure Y) : D.codensity ⊤ R μ ν :=
  fun _ _ _ hc ↦ (le_self_add.not_gt hc).elim

theorem absorbing_codensity_top [Add B] [Preorder B] [Top B] [CanonicallyOrderedAdd B] :
    (codensity D).Absorbing ⊤ :=
  fun R μ ν _ _ ↦ codensity_top R μ ν

/-- The codensity lifting relates everything at `⊤`, where no test is left. -/
instance isTopAbsorbing_codensity [Add B] [Preorder B] [Top B] [CanonicallyOrderedAdd B] :
    (codensity D).IsTopAbsorbing :=
  ⟨codensity_top⟩

/-- A left measure of mass at most `δ` is related to everything at the slack `s δ`: every test
output has mass at most `δ`. -/
theorem codensity_of_measure_univ_le [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B]
    [Top B] [D.IsGraded] {s : ℝ≥0∞ →+o B} [D.HasSlack s] {δ : ℝ≥0∞} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (hμ : μ Set.univ ≤ δ) : D.codensity (s δ) R μ ν := by
  intro I _ c _ k l _ _ _
  refine IsGraded.mono le_self_add (HasSlack.of_forall_le fun S _ ↦ ?_)
  calc (k ∘ₘ μ) S
      ≤ μ Set.univ := by
        rw [bind_apply ‹_› k.measurable.aemeasurable]
        exact lintegral_le_meas (fun _ ↦ IsSubProbabilityMeasure.measure_le_one _) (by simp)
    _ ≤ (l ∘ₘ ν) S + δ := hμ.trans le_add_self

/-- The slack of the full mass relates every pair of sub-probability measures. -/
theorem absorbing_codensity_of_hasSlack [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B]
    [Top B] [D.IsGraded] {s : ℝ≥0∞ →+o B} [D.HasSlack s] : (codensity D).Absorbing (s 1) := by
  intro X Y _ _ R μ ν _ _
  exact codensity_of_measure_univ_le (IsSubProbabilityMeasure.measure_le_one _)

end GradedDivergence

namespace GradedLifting

open GradedDivergence

variable {B : Type v} {L : GradedLifting.{u} B} {D : GradedDivergence.{u} B} {X Y : Type u}
  [MeasurableSpace X] [MeasurableSpace Y]

/-- A lawful lifting with bind that is sound and complete for `D` lies below the codensity lifting
of `D`: frame by the test's slack, relate the tests by completeness, bind, then use soundness. -/
theorem le_codensity [AddCommMagma B] [Zero B] [Preorder B] [Top B] [CanonicallyOrderedAdd B]
    [L.IsLawful] [L.HasBind] [L.IsSound D] [L.IsComplete D] {b : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : L b R μ ν) : D.codensity b R μ ν := by
  intro I _ c hbc k l _ _ hkl
  exact IsSound.sound (L := L) <| HasBind.bind (IsLawful.frame (le_add_self.trans_lt hbc) h)
    fun x y _ ↦ IsComplete.complete (hkl x y)

end GradedLifting
