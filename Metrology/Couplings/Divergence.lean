module

public import Metrology.Couplings.Budget
public import Metrology.Couplings.SubProbability

/-! # Graded divergences

`GradedDivergence`: yes/no predicates `D b μ ν` indexed by a budget, with property classes and laws
(ASL §4). -/

@[expose] public section

universe u v w

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

/-- A family of yes/no divergences: `D b μ ν` says `μ` is within budget `b` of `ν`. -/
def GradedDivergence (B : Type v) : Type (max v (u + 1)) :=
  B → ∀ {X : Type u} [MeasurableSpace X], Measure X → Measure X → Prop

namespace GradedDivergence

section Classes

variable {B : Type v} (D : GradedDivergence.{u} B)

/-! ## The core properties: graded, reflexive, composable -/

/-- Larger budgets are easier to meet, and the top budget always holds. -/
class IsGraded [LE B] [Top B] : Prop where
  /-- Larger budgets are easier to meet. -/
  mono ⦃b b' : B⦄ (hb : b ≤ b') {X : Type u} [MeasurableSpace X] {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] : D b μ ν → D b' μ ν
  /-- The top budget always holds. -/
  top {X : Type u} [MeasurableSpace X] (μ ν : Measure X) [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : D ⊤ μ ν

/-- Every sub-probability measure is within budget zero of itself. -/
class IsReflexive [Zero B] : Prop where
  /-- Every sub-probability measure is within budget zero of itself. -/
  refl {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsSubProbabilityMeasure μ] : D 0 μ μ

/-- Chain rule: binding with kernels that are pointwise within `c` adds `c` to the budget. -/
class IsComposable [Add B] : Prop where
  /-- The chain rule. -/
  comp ⦃b c : B⦄ {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] ⦃μ₁ μ₂ : Measure X⦄
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂] ⦃κ η : Kernel X Y⦄
    [IsSubMarkovKernel κ] [IsSubMarkovKernel η] :
    D b μ₁ μ₂ → (∀ x, D c (κ x) (η x)) → D (b + c) (κ ∘ₘ μ₁) (η ∘ₘ μ₂)

/-! ## Further properties -/

/-- The zero measure is within every budget of every sub-probability measure. -/
class IsZeroLeft : Prop where
  /-- The zero measure is within every budget of every sub-probability measure. -/
  zero_left (b : B) {X : Type u} [MeasurableSpace X] (ν : Measure X)
    [IsSubProbabilityMeasure ν] : D b 0 ν

/-- A budget met along an increasing sequence on the left is met by its supremum. -/
class IsLeftContinuous : Prop where
  /-- A budget met along an increasing sequence on the left is met by its supremum. -/
  iSup_left ⦃b : B⦄ {X : Type u} [MeasurableSpace X] {μ : ℕ → Measure X}
    [∀ n, IsSubProbabilityMeasure (μ n)] (hμ : Monotone μ) ⦃ν : Measure X⦄
    [IsSubProbabilityMeasure ν] : (∀ n, D b (μ n) ν) → D b (⨆ n, μ n) ν

/-- Growing the right measure keeps the budget. -/
class IsRightMonotone : Prop where
  /-- Growing the right measure keeps the budget. -/
  right_mono ⦃b : B⦄ {X : Type u} [MeasurableSpace X] {μ ν ν' : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν'] (h : ν ≤ ν') : D b μ ν → D b μ ν'

/-- Shrinking the left measure keeps the budget. -/
class IsLeftAntitone : Prop where
  /-- Shrinking the left measure keeps the budget. -/
  left_anti ⦃b : B⦄ {X : Type u} [MeasurableSpace X] {μ μ' ν : Measure X}
    [IsSubProbabilityMeasure μ'] [IsSubProbabilityMeasure ν] (h : μ ≤ μ') : D b μ' ν → D b μ ν

/-- Budgets are closed from above: meeting every larger budget meets the budget. -/
class IsBudgetClosed [LT B] : Prop where
  /-- Meeting every larger budget meets the budget. -/
  of_forall_gt {b : B} {X : Type u} [MeasurableSpace X] {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    (∀ b', b < b' → D b' μ ν) → D b μ ν

/-- An additive event gap `δ` is met at budget `s δ`, where `s` places `δ` inside the budget
(`δ ↦ (0, δ)` for dp). -/
class HasSlack [AddZeroClass B] [Preorder B] (s : ℝ≥0∞ →+o B) : Prop where
  /-- A mass gap of at most `δ` on every measurable set meets budget `s δ`. -/
  of_forall_le {δ : ℝ≥0∞} {X : Type u} [MeasurableSpace X] {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    (∀ S, MeasurableSet S → μ S ≤ ν S + δ) → D (s δ) μ ν

/-- Scaled point masses within budget `s δ` have left mass at most the right mass plus `δ`. -/
class IsMassDetecting [AddZeroClass B] [Preorder B] (s : ℝ≥0∞ →+o B) : Prop where
  /-- Point masses within budget `s δ` have left mass at most the right mass plus `δ`. -/
  le_add_of {p q δ : ℝ≥0∞} (hp : p ≤ 1) (hq : q ≤ 1) :
    D (s δ) (p • dirac PUnit.unit.{u + 1}) (q • dirac PUnit.unit) → p ≤ q + δ

end Classes

/-! ## Derived laws: data processing, post-processing, products, relabelling -/

section Laws

variable {B : Type v} {D : GradedDivergence.{u} B} {X Y : Type u} [MeasurableSpace X]
  [MeasurableSpace Y]

/-- A budget above `⊤` always holds. -/
theorem IsGraded.of_top_le [LE B] [Top B] [D.IsGraded] {b : B} (hb : ⊤ ≤ b)
    (μ ν : Measure X) [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] : D b μ ν :=
  IsGraded.mono hb (IsGraded.top μ ν)

/-- To prove `D b μ ν` it suffices to assume `b < ⊤`. -/
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

/-- Data processing along a sub-Markov kernel: the chain rule with `κ = η` and `c = 0`. -/
theorem IsComposable.comp_self [AddZeroClass B] [D.IsReflexive] [D.IsComposable] {b : B}
    {μ ν : Measure X} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] (κ : Kernel X Y)
    [IsSubMarkovKernel κ] (h : D b μ ν) : D b (κ ∘ₘ μ) (κ ∘ₘ ν) :=
  add_zero b ▸ IsComposable.comp h fun x ↦ IsReflexive.refl (κ x)

/-- Post-processing: data processing along a measurable map. -/
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
  -- write μ₁.prod ν₁ as μ₁ followed by the kernel x ↦ (ν₁.map (x, ·)), then bind
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
  · -- empty `X`: every measure on it is zero
    convert IsComposable.comp_self (0 : Kernel Y X) h <;> exact Subsingleton.elim _ _
  -- otherwise map back along a measurable left inverse `g` of `f`
  obtain ⟨g, hg, hgf⟩ := hf.exists_measurable_extend measurable_id fun _ ↦ inferInstance
  simpa [map_map hg hf.measurable, hgf] using IsComposable.map h hg

end Laws

/-! ## Regrading along a budget map (`comap`) -/

section Comap

variable {B : Type v} {B' : Type w} {φ : B' → B} {D : GradedDivergence.{u} B}

variable (D φ) in
/-- Regrading: the divergence read through a budget map `φ : B' → B` (Rocq `GCF_regrade`). -/
def comap : GradedDivergence.{u} B' :=
  fun b ↦ D (φ b)

/-- Unfolding of the regraded divergence. -/
theorem comap_def {b : B'} {X : Type u} [MeasurableSpace X] {μ ν : Measure X} :
    D.comap φ b μ ν ↔ D (φ b) μ ν :=
  Iff.rfl

/-- Regrading twice is regrading along the composite map. -/
theorem comap_comap {B'' : Type*} {ψ : B'' → B'} : (D.comap φ).comap ψ = D.comap (φ ∘ ψ) :=
  rfl

/-- Regrading keeps grading along a monotone map whose image of `⊤` always holds. -/
theorem isGraded_comap [Preorder B] [Top B] [Preorder B'] [Top B'] [D.IsGraded]
    (hφ : Monotone φ) (htop : ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
      [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν], D (φ ⊤) μ ν) :
    (D.comap φ).IsGraded where
  mono _ _ hb := IsGraded.mono (hφ hb)
  top := htop

/-- Regrading keeps grading along a monotone map that keeps `⊤`. -/
theorem isGraded_comap_of_map_top [Preorder B] [Top B] [Preorder B'] [Top B'] [D.IsGraded]
    (hφ : Monotone φ) (htop : φ ⊤ = ⊤) : (D.comap φ).IsGraded :=
  isGraded_comap hφ fun μ ν _ _ ↦ htop ▸ IsGraded.top μ ν

/-- Regrading keeps reflexivity when `φ 0` is at least `0`. -/
theorem isReflexive_comap [Zero B] [LE B] [Top B] [Zero B'] [D.IsGraded] [D.IsReflexive]
    (h0 : 0 ≤ φ 0) : (D.comap φ).IsReflexive where
  refl μ _ := IsGraded.mono h0 (IsReflexive.refl μ)

/-- Regrading keeps composability along a superadditive map. -/
theorem isComposable_comap [Add B] [LE B] [Top B] [Add B'] [D.IsGraded] [D.IsComposable]
    (hadd : ∀ b c, φ b + φ c ≤ φ (b + c)) : (D.comap φ).IsComposable where
  comp b c := fun h hκ ↦ IsGraded.mono (hadd b c) (IsComposable.comp h hκ)

/-- Regrading keeps the zero-measure law. -/
instance isZeroLeft_comap [D.IsZeroLeft] : (D.comap φ).IsZeroLeft where
  zero_left b := IsZeroLeft.zero_left (φ b)

/-- Regrading keeps left continuity. -/
instance isLeftContinuous_comap [D.IsLeftContinuous] : (D.comap φ).IsLeftContinuous where
  iSup_left b := IsLeftContinuous.iSup_left (b := φ b)

/-- Regrading keeps right monotonicity. -/
instance isRightMonotone_comap [D.IsRightMonotone] : (D.comap φ).IsRightMonotone where
  right_mono b := IsRightMonotone.right_mono (b := φ b)

/-- Regrading keeps left antitonicity. -/
instance isLeftAntitone_comap [D.IsLeftAntitone] : (D.comap φ).IsLeftAntitone where
  left_anti b := IsLeftAntitone.left_anti (b := φ b)

end Comap

/-! ## Families of divergences (`pi`) -/

section Pi

variable {ι : Type w} {B : ι → Type v} {D : ∀ i, GradedDivergence.{u} (B i)}

variable (D) in
/-- A family of divergences met at once, each within its own coordinate of the budget
(Rocq `RDPcoupl_curve`). -/
def pi : GradedDivergence.{u} (∀ i, B i) :=
  fun b _ _ μ ν ↦ ∀ i, D i (b i) μ ν

/-- Unfolding of a family of divergences. -/
theorem pi_def {b : ∀ i, B i} {X : Type u} [MeasurableSpace X] {μ ν : Measure X} :
    pi D b μ ν ↔ ∀ i, D i (b i) μ ν :=
  Iff.rfl

/-- A family is graded when every coordinate is. -/
instance isGraded_pi [∀ i, LE (B i)] [∀ i, Top (B i)] [∀ i, (D i).IsGraded] :
    (pi D).IsGraded where
  mono _ _ hb := fun h i ↦ IsGraded.mono (hb i) (h i)
  top μ ν _ _ _ := IsGraded.top μ ν

/-- A family is reflexive when every coordinate is. -/
instance isReflexive_pi [∀ i, Zero (B i)] [∀ i, (D i).IsReflexive] : (pi D).IsReflexive where
  refl μ _ _ := IsReflexive.refl μ

/-- A family is composable when every coordinate is. -/
instance isComposable_pi [∀ i, Add (B i)] [∀ i, (D i).IsComposable] :
    (pi D).IsComposable where
  comp _ _ := fun h hκ i ↦ IsComposable.comp (h i) fun x ↦ hκ x i

/-- A family has the zero-measure law when every coordinate does. -/
instance isZeroLeft_pi [∀ i, (D i).IsZeroLeft] : (pi D).IsZeroLeft where
  zero_left b _ _ ν _ i := IsZeroLeft.zero_left (b i) ν

/-- A family is left continuous when every coordinate is. -/
instance isLeftContinuous_pi [∀ i, (D i).IsLeftContinuous] : (pi D).IsLeftContinuous where
  iSup_left _ := fun hμ _ _ h i ↦ IsLeftContinuous.iSup_left hμ fun n ↦ h n i

/-- A family is right monotone when every coordinate is. -/
instance isRightMonotone_pi [∀ i, (D i).IsRightMonotone] : (pi D).IsRightMonotone where
  right_mono _ := fun hν h i ↦ IsRightMonotone.right_mono hν (h i)

/-- A family is left antitone when every coordinate is. -/
instance isLeftAntitone_pi [∀ i, (D i).IsLeftAntitone] : (pi D).IsLeftAntitone where
  left_anti _ := fun hμ h i ↦ IsLeftAntitone.left_anti hμ (h i)

/-- Budgets are closed one coordinate at a time. -/
instance isBudgetClosed_pi [∀ i, Preorder (B i)] [∀ i, (D i).IsBudgetClosed] :
    (pi D).IsBudgetClosed where
  of_forall_gt {b} := fun h i ↦ by
    classical
    -- raise only coordinate `i` to `t`
    exact IsBudgetClosed.of_forall_gt fun t ht ↦ by
      simpa using h (Function.update b i t) (lt_update_self_iff.2 ht) i

end Pi
