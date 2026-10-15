module

public import Metrology.Couplings.SubProbability

/-! Core of the redesigned coupling hierarchy: one-budget divergences, graded liftings, and the
codensity lifting as the largest lawful, sound and complete lifting (notes/hierarchy-redesign.md). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory

namespace Redesign

/-- A family of yes/no divergences: `D b μ ν` says `μ` is within budget `b` of `ν`. -/
def GradedDivergence (B : Type v) : Type (max v (u + 1)) :=
  B → ∀ {X : Type u} [MeasurableSpace X], Measure X → Measure X → Prop

namespace GradedDivergence

variable {B : Type v} (D : GradedDivergence.{u} B)

/-- Larger budgets are easier to meet, and the top budget always holds. -/
class IsGraded [Preorder B] [OrderTop B] : Prop where
  mono ⦃b b' : B⦄ (hb : b ≤ b') {X : Type u} [MeasurableSpace X] {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] : D b μ ν → D b' μ ν
  top {X : Type u} [MeasurableSpace X] (μ ν : Measure X) [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : D ⊤ μ ν

/-- Every sub-probability measure is within budget zero of itself. -/
class IsReflexive [Zero B] : Prop where
  refl {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsSubProbabilityMeasure μ] : D 0 μ μ

/-- Composing with kernels adds the kernels' pointwise budget to the budget. -/
class IsComposable [Add B] : Prop where
  comp ⦃b c : B⦄ {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] ⦃μ₁ μ₂ : Measure X⦄
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂] ⦃κ η : Kernel X Y⦄
    [IsSubMarkovKernel κ] [IsSubMarkovKernel η] :
    D b μ₁ μ₂ → (∀ x, D c (κ x) (η x)) → D (b + c) (κ ∘ₘ μ₁) (η ∘ₘ μ₂)

/-- The zero measure is within every budget of every sub-probability measure. -/
class IsZeroLeft : Prop where
  zero_left (b : B) {X : Type u} [MeasurableSpace X] (ν : Measure X)
    [IsSubProbabilityMeasure ν] : D b 0 ν

end GradedDivergence

/-- A family of liftings: `L b R μ ν` relates `μ` and `ν` within budget `b`, leaving `R x y` for
the continuation at each pair. -/
def GradedLifting (B : Type v) : Type (max v (u + 1)) :=
  B → ∀ {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y],
    (X → Y → B) → Measure X → Measure Y → Prop

section relCost

variable {B : Type v} [Zero B] [Top B] {X Y : Type*}

/-- The leftover of a relation: `0` on it, `⊤` off it. -/
noncomputable def relCost (S : X → Y → Prop) (x : X) (y : Y) : B :=
  {p : X × Y | ¬S p.1 p.2}.indicator (fun _ ↦ ⊤) (x, y)

@[simp]
theorem relCost_of {S : X → Y → Prop} {x : X} {y : Y} (h : S x y) : relCost (B := B) S x y = 0 :=
  Set.indicator_of_notMem (not_not.2 h) _

@[simp]
theorem relCost_of_not {S : X → Y → Prop} {x : X} {y : Y} (h : ¬S x y) :
    relCost (B := B) S x y = ⊤ :=
  Set.indicator_of_mem h _

end relCost

namespace GradedLifting

variable {B : Type v} (L : GradedLifting.{u} B)

/-- The lifting of a relation `S`: leftover `0` on `S` and `⊤` off it. -/
def rel [Zero B] [Top B] {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (b : B)
    (S : X → Y → Prop) (μ : Measure X) (ν : Measure Y) : Prop :=
  L b (relCost S) μ ν

/-- The structural laws of a lifting: Dirac pairs, zero measures, weakening and framing. -/
class IsLawful [Add B] [Preorder B] [Top B] : Prop where
  pure {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {R : X → Y → B} {x : X} {y : Y} :
    R x y < ⊤ → L (R x y) R (dirac x) (dirac y)
  zero {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (b : B) (R : X → Y → B) :
    L b R (0 : Measure X) (0 : Measure Y)
  mono {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b b' : B} {R R' : X → Y → B}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    L b R μ ν → b ≤ b' → R' ≤ R → L b' R' μ ν
  frame {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b c : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} : c < ⊤ → L b R μ ν → L (b + c) (fun x y ↦ R x y + c) μ ν

/-- Binding with sub-Markov kernels whose outputs are lifted wherever the leftover is finite. -/
class HasBind [LT B] [Top B] : Prop where
  bind {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
    [MeasurableSpace Y'] {b : B} {R : X → Y → B} {R' : X' → Y' → B} {μ : Measure X}
    {ν : Measure Y} {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f]
    [IsSubMarkovKernel g] :
    L b R μ ν → (∀ x y, R x y < ⊤ → L (R x y) R' (f x) (g y)) → L b R' (f ∘ₘ μ) (g ∘ₘ ν)

variable (D : GradedDivergence.{u} B)

/-- Lifting equality within a budget gives the divergence within that budget. -/
class IsSound [Zero B] [Top B] : Prop where
  sound {X : Type u} [MeasurableSpace X] {b : B} {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : L.rel b (· = ·) μ ν → D b μ ν

/-- The divergence within a budget gives a lifting of equality within that budget. -/
class IsComplete [Zero B] [Top B] : Prop where
  complete {X : Type u} [MeasurableSpace X] {b : B} {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] : D b μ ν → L.rel b (· = ·) μ ν

end GradedLifting

namespace GradedDivergence

variable {B : Type v} {D : GradedDivergence.{u} B}

/-- A larger budget is reached from `⊤`. -/
theorem IsGraded.of_top_le [Preorder B] [OrderTop B] [D.IsGraded] {b : B} (hb : ⊤ ≤ b)
    {X : Type u} [MeasurableSpace X] (μ ν : Measure X) [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : D b μ ν :=
  IsGraded.mono hb (IsGraded.top μ ν)

variable (D) in
/-- The codensity lifting: every test whose kernels are within the leftover plus a slack at each
pair stays within the budget plus that slack after binding (Sato–Katsumata, §7). -/
def codensity [Add B] : GradedLifting.{u} B :=
  fun b {X Y} _ _ R μ ν ↦ ∀ ⦃I : Type u⦄ [MeasurableSpace I] ⦃c : B⦄ ⦃k : Kernel X I⦄
    ⦃l : Kernel Y I⦄ [IsSubMarkovKernel k] [IsSubMarkovKernel l],
    (∀ x y, D (R x y + c) (k x) (l y)) → D (b + c) (k ∘ₘ μ) (l ∘ₘ ν)

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

/-- Unfolding the codensity lifting. -/
theorem codensity_def [Add B] {b : B} {R : X → Y → B} {μ : Measure X} {ν : Measure Y} :
    D.codensity b R μ ν ↔ ∀ ⦃I : Type u⦄ [MeasurableSpace I] ⦃c : B⦄ ⦃k : Kernel X I⦄
      ⦃l : Kernel Y I⦄ [IsSubMarkovKernel k] [IsSubMarkovKernel l],
      (∀ x y, D (R x y + c) (k x) (l y)) → D (b + c) (k ∘ₘ μ) (l ∘ₘ ν) :=
  Iff.rfl

/-- Dirac pairs lift with their own leftover as the budget. -/
theorem codensity_dirac [Add B] {R : X → Y → B} (x : X) (y : Y) :
    D.codensity (R x y) R (dirac x) (dirac y) := by
  intro I _ c k l _ _ hkl
  rw [dirac_bind k.measurable, dirac_bind l.measurable]
  exact hkl x y

/-- With zero-left divergences, the zero measures lift at every budget. -/
theorem codensity_zero_of_isZeroLeft [Add B] [D.IsZeroLeft] (b : B) (R : X → Y → B) :
    D.codensity b R 0 0 := by
  intro I _ c k l _ _ _
  rw [bind_zero_left, bind_zero_left]
  exact IsZeroLeft.zero_left _ _

/-- With reflexive graded divergences, the zero measures lift at every budget. -/
theorem codensity_zero [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
    [D.IsGraded] [D.IsReflexive] (b : B) (R : X → Y → B) : D.codensity b R 0 0 := by
  intro I _ c k l _ _ _
  rw [bind_zero_left, bind_zero_left]
  exact IsGraded.mono zero_le (IsReflexive.refl _)

/-- Larger budgets and smaller leftovers give larger liftings. -/
theorem codensity_mono [AddCommMonoid B] [PartialOrder B] [IsOrderedAddMonoid B] [OrderTop B]
    [D.IsGraded] {b b' : B} {R R' : X → Y → B} {μ : Measure X} {ν : Measure Y}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] (h : D.codensity b R μ ν)
    (hb : b ≤ b') (hR : R' ≤ R) : D.codensity b' R' μ ν := by
  intro I _ c k l _ _ hkl
  exact IsGraded.mono (add_le_add hb le_rfl)
    (h fun x y ↦ IsGraded.mono (add_le_add (hR x y) le_rfl) (hkl x y))

/-- Adding a slack to the budget and to every leftover. -/
theorem codensity_frame [AddSemigroup B] {b c : B} {R : X → Y → B} {μ : Measure X}
    {ν : Measure Y} (h : D.codensity b R μ ν) :
    D.codensity (b + c) (fun x y ↦ R x y + c) μ ν := by
  intro I _ c' k l _ _ hkl
  rw [add_assoc]
  exact h fun x y ↦ add_assoc (R x y) c c' ▸ hkl x y

instance isLawful_codensity [AddCommMonoid B] [PartialOrder B] [IsOrderedAddMonoid B]
    [CanonicallyOrderedAdd B] [OrderTop B] [D.IsGraded] [D.IsReflexive] :
    (codensity D).IsLawful where
  pure _ := codensity_dirac _ _
  zero := codensity_zero
  mono := codensity_mono
  frame _ := codensity_frame

/-- Binding with kernels lifted wherever the leftover is finite; infinite leftovers pass every
test by `IsGraded.top`. -/
theorem codensity_bind [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
    [D.IsGraded] {X' Y' : Type u} [MeasurableSpace X'] [MeasurableSpace Y'] {b : B}
    {R : X → Y → B} {R' : X' → Y' → B} {μ : Measure X} {ν : Measure Y} {f : Kernel X X'}
    {g : Kernel Y Y'} [IsSubMarkovKernel f] [IsSubMarkovKernel g] (h : D.codensity b R μ ν)
    (hfg : ∀ x y, R x y < ⊤ → D.codensity (R x y) R' (f x) (g y)) :
    D.codensity b R' (f ∘ₘ μ) (g ∘ₘ ν) := by
  intro I _ c k l _ _ hkl
  rw [comp_assoc, comp_assoc]
  refine h fun x y ↦ ?_
  rw [Kernel.comp_apply, Kernel.comp_apply]
  rcases lt_or_eq_of_le (le_top (a := R x y)) with hR | hR
  · exact hfg x y hR hkl
  · exact IsGraded.of_top_le (hR ▸ le_self_add) _ _

instance hasBind_codensity [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
    [OrderTop B] [D.IsGraded] : (codensity D).HasBind where
  bind := codensity_bind

instance isSound_codensity [AddZeroClass B] [Preorder B] [OrderTop B] [D.IsGraded]
    [D.IsReflexive] : (codensity D).IsSound D where
  sound {X} _ b μ ν _ _ h := by
    have := h (k := Kernel.id) (l := Kernel.id) (c := 0) fun x y ↦ by
      by_cases hxy : x = y
      · subst hxy
        simpa [Kernel.id_apply] using IsReflexive.refl (D := D) (dirac x)
      · simpa [Kernel.id_apply, hxy] using IsGraded.top (D := D) (dirac x) (dirac y)
    simpa [id_comp] using this

/-- The codensity lifting of a divergence is complete for it exactly when the divergence is
composable (Sato–Katsumata, Thm. 8.2). -/
theorem codensity_isComplete_iff [AddMonoid B] [Preorder B] [CanonicallyOrderedAdd B]
    [OrderTop B] [D.IsGraded] : (codensity D).IsComplete D ↔ D.IsComposable := by
  refine ⟨fun _ ↦ ⟨fun b c X Y _ _ μ₁ μ₂ _ _ κ η _ _ h hκη ↦
    GradedLifting.IsComplete.complete (L := codensity D) h fun x y ↦ ?_⟩,
    fun _ ↦ ⟨fun {X} _ b μ ν _ _ h I _ c k l _ _ hkl ↦
      IsComposable.comp h fun x ↦ by simpa using hkl x x⟩⟩
  by_cases hxy : x = y
  · subst hxy
    simpa using hκη x
  · simpa [hxy] using IsGraded.of_top_le (D := D) le_self_add (κ x) (η y)

instance isComplete_codensity [AddMonoid B] [Preorder B] [CanonicallyOrderedAdd B]
    [OrderTop B] [D.IsGraded] [D.IsComposable] : (codensity D).IsComplete D :=
  codensity_isComplete_iff.2 ‹_›

end GradedDivergence

namespace GradedLifting

open GradedDivergence

variable {B : Type v} {L : GradedLifting.{u} B} {D : GradedDivergence.{u} B}

/-- A lawful lifting with bind that is sound and complete for `D` lies below the codensity lifting
of `D`: frame by the test's slack, relate the tests by completeness, bind, then use soundness. -/
theorem le_codensity [AddMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
    [D.IsGraded] [L.IsLawful] [L.HasBind] [L.IsSound D] [L.IsComplete D] {X Y : Type u}
    [MeasurableSpace X] [MeasurableSpace Y] {b : B} {R : X → Y → B} {μ : Measure X}
    {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] (h : L b R μ ν) :
    D.codensity b R μ ν := by
  intro I _ c k l _ _ hkl
  rcases lt_or_eq_of_le (le_top (a := c)) with hc | rfl
  · exact IsSound.sound (L := L) <| HasBind.bind (IsLawful.frame hc h) fun x y _ ↦
      IsComplete.complete (hkl x y)
  · exact IsGraded.of_top_le le_add_self _ _

end GradedLifting

end Redesign
