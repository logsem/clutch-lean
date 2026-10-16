module

public import Metrology.Couplings.Budget
public import Metrology.Couplings.SubProbability

/-! Graded divergences with yes/no budgets (Approximate Span Liftings, §4). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

/-- A family of yes/no divergences: `D b μ ν` says `μ` is within budget `b` of `ν`. -/
def GradedDivergence (B : Type v) : Type (max v (u + 1)) :=
  B → ∀ {X : Type u} [MeasurableSpace X], Measure X → Measure X → Prop

namespace GradedDivergence

/-! ## Properties of a divergence -/

section Classes

variable {B : Type v} (D : GradedDivergence.{u} B)

/-- Larger budgets are easier to meet, and the top budget always holds. -/
class IsGraded [LE B] [Top B] : Prop where
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

/-- A budget met along an increasing sequence on the left is met by its supremum. -/
class IsLeftContinuous : Prop where
  iSup_left ⦃b : B⦄ {X : Type u} [MeasurableSpace X] {μ : ℕ → Measure X}
    [∀ n, IsSubProbabilityMeasure (μ n)] (hμ : Monotone μ) ⦃ν : Measure X⦄
    [IsSubProbabilityMeasure ν] : (∀ n, D b (μ n) ν) → D b (⨆ n, μ n) ν

/-- Growing the right measure keeps the budget. -/
class IsRightMonotone : Prop where
  right_mono ⦃b : B⦄ {X : Type u} [MeasurableSpace X] {μ ν ν' : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν'] (h : ν ≤ ν') : D b μ ν → D b μ ν'

/-- Shrinking the left measure keeps the budget. -/
class IsLeftAntitone : Prop where
  left_anti ⦃b : B⦄ {X : Type u} [MeasurableSpace X] {μ μ' ν : Measure X}
    [IsSubProbabilityMeasure μ'] [IsSubProbabilityMeasure ν] (h : μ ≤ μ') : D b μ' ν → D b μ ν

/-- Budgets are closed from above: meeting every larger budget meets the budget. -/
class IsBudgetClosed [LT B] : Prop where
  of_forall_gt {b : B} {X : Type u} [MeasurableSpace X] {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    (∀ b', b < b' → D b' μ ν) → D b μ ν

/-- An event gap `δ` is met at the budget `s δ`. -/
class HasSlack [AddZeroClass B] [Preorder B] (s : ℝ≥0∞ →+o B) : Prop where
  of_forall_le {δ : ℝ≥0∞} {X : Type u} [MeasurableSpace X] {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    (∀ S, MeasurableSet S → μ S ≤ ν S + δ) → D (s δ) μ ν

/-- Point masses within budget `s δ` differ in mass by at most `δ`. -/
class IsMassDetecting [AddZeroClass B] [Preorder B] (s : ℝ≥0∞ →+o B) : Prop where
  le_add_of {p q δ : ℝ≥0∞} (hp : p ≤ 1) (hq : q ≤ 1) :
    D (s δ) (p • dirac PUnit.unit.{u + 1}) (q • dirac PUnit.unit) → p ≤ q + δ

end Classes

/-! ## Derived laws -/

variable {B : Type v} {D : GradedDivergence.{u} B} {X Y : Type u} [MeasurableSpace X]
  [MeasurableSpace Y]

/-- A budget above `⊤` always holds. -/
theorem IsGraded.of_top_le [LE B] [Top B] [D.IsGraded] {b : B} (hb : ⊤ ≤ b)
    (μ ν : Measure X) [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] : D b μ ν :=
  IsGraded.mono hb (IsGraded.top μ ν)

/-- A budget holds once it holds whenever it is finite. -/
theorem IsGraded.of_lt_top [Preorder B] [OrderTop B] [D.IsGraded] {b : B} {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] (h : b < ⊤ → D b μ ν) : D b μ ν := by
  by_cases hb : ⊤ ≤ b
  · exact IsGraded.of_top_le hb μ ν
  · exact h (le_top.lt_of_not_ge hb)

/-- Substitutivity: a kernel bound carries over a bind against the same measure. -/
theorem IsComposable.subst [AddZeroClass B] [D.IsReflexive] [D.IsComposable] {c : B}
    (μ : Measure X) [IsSubProbabilityMeasure μ] {κ η : Kernel X Y} [IsSubMarkovKernel κ]
    [IsSubMarkovKernel η] (h : ∀ x, D c (κ x) (η x)) : D c (κ ∘ₘ μ) (η ∘ₘ μ) :=
  zero_add c ▸ IsComposable.comp (IsReflexive.refl μ) h

/-- Data processing along a sub-Markov kernel. -/
theorem IsComposable.comp_self [AddZeroClass B] [D.IsReflexive] [D.IsComposable] {b : B}
    {μ ν : Measure X} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] (κ : Kernel X Y)
    [IsSubMarkovKernel κ] (h : D b μ ν) : D b (κ ∘ₘ μ) (κ ∘ₘ ν) :=
  add_zero b ▸ IsComposable.comp h fun x ↦ IsReflexive.refl (κ x)

/-- Data processing along a measurable map. -/
theorem IsComposable.map [AddZeroClass B] [D.IsReflexive] [D.IsComposable] {b : B}
    {μ ν : Measure X} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {f : X → Y}
    (h : D b μ ν) (hf : Measurable f := by fun_prop) : D b (μ.map f) (ν.map f) := by
  rw [← deterministic_comp_eq_map hf, ← deterministic_comp_eq_map hf]
  exact IsComposable.comp_self _ h

/-- Products add budgets. -/
theorem IsComposable.prod [AddZeroClass B] [D.IsReflexive] [D.IsComposable] {b c : B}
    {μ₁ μ₂ : Measure X} {ν₁ ν₂ : Measure Y} [IsSubProbabilityMeasure μ₁]
    [IsSubProbabilityMeasure μ₂] [IsSubProbabilityMeasure ν₁] [IsSubProbabilityMeasure ν₂]
    (hμ : D b μ₁ μ₂) (hν : D c ν₁ ν₂) : D (b + c) (μ₁.prod ν₁) (μ₂.prod ν₂) := by
  have (ν : Measure Y) [IsSubProbabilityMeasure ν] :
      IsSubMarkovKernel (Kernel.id ×ₖ Kernel.const X ν) :=
    ⟨fun x ↦ by rw [Kernel.prod_apply]; infer_instance⟩
  rw [← compProd_const, ← compProd_const, compProd_eq_comp_prod, compProd_eq_comp_prod]
  refine IsComposable.comp hμ fun x ↦ ?_
  simpa [Kernel.prod_apply, Kernel.id_apply, dirac_prod] using IsComposable.map (f := Prod.mk x) hν

/-- Relabelling along a measurable embedding keeps every budget (`Injective` is not enough). -/
theorem IsComposable.map_iff_of_measurableEmbedding [AddZeroClass B] [D.IsReflexive]
    [D.IsComposable] {b : B} {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {f : X → Y} (hf : MeasurableEmbedding f) :
    D b (μ.map f) (ν.map f) ↔ D b μ ν := by
  refine ⟨fun h ↦ ?_, (IsComposable.map · hf.measurable)⟩
  cases isEmpty_or_nonempty X
  · convert IsComposable.comp_self (0 : Kernel Y X) h <;> exact Subsingleton.elim _ _
  obtain ⟨g, hg, hgf⟩ := hf.exists_measurable_extend measurable_id fun _ ↦ inferInstance
  simpa [map_map hg hf.measurable, hgf] using IsComposable.map h hg
