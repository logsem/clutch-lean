module

public import Metrology.Couplings.Divergence

/-! # Graded liftings

`GradedLifting B` relates two measures within a budget, leaving a per-pair leftover (Approximate
Span Liftings, §5): relational liftings `Rel`, the law classes, and their derived laws. -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal
open Set (indicator_of_notMem indicator_of_mem)
open Kernel (id_apply)
open PUnit (unit)

-- Budget first: with the spaces first Lean fills them in early and `(codensity D).IsLawful`
-- fails to elaborate.
/-- A family of liftings: `L b R μ ν` relates `μ` and `ν` within budget `b`, leaving `R x y` for
the continuation at each pair (Approximate Span Liftings, §5). -/
def GradedLifting (B : Type v) : Type (max v (u + 1)) :=
  B → ∀ {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y],
    (X → Y → B) → Measure X → Measure Y → Prop

namespace GradedLifting

/-! ## Relations as leftovers -/

section relCost

variable {B : Type v} {X Y : Type*} {S S' : X → Y → Prop} {x : X} {y : Y}

section Leftover

variable [Zero B] [Top B]

/-- The leftover of a relation: `0` on it, `⊤` off it. -/
noncomputable def relCost (S : X → Y → Prop) (x : X) (y : Y) : B :=
  {p : X × Y | ¬S p.1 p.2}.indicator (fun _ ↦ ⊤) (x, y)

/-- The leftover of a related pair is `0`. -/
@[simp]
theorem relCost_of (h : S x y) : relCost (B := B) S x y = 0 :=
  indicator_of_notMem (not_not.2 h) _

/-- The leftover of an unrelated pair is `⊤`. -/
@[simp]
theorem relCost_of_not (h : ¬S x y) : relCost (B := B) S x y = ⊤ :=
  indicator_of_mem h _

variable (L : GradedLifting.{u} B) in
/-- The lifting of a relation `S`: leftover `0` on `S` and `⊤` off it. -/
def Rel {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (b : B) (S : X → Y → Prop)
    (μ : Measure X) (ν : Measure Y) : Prop :=
  L b (relCost S) μ ν

end Leftover

/-- A relation's leftover is finite exactly where the relation holds. -/
theorem relCost_lt_top_iff [AddZeroClass B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
    [Nontrivial B] : relCost (B := B) S x y < ⊤ ↔ S x y := by
  refine ⟨fun h ↦ by_contra fun hS ↦ (relCost_of_not (B := B) hS ▸ h).false, fun h ↦ ?_⟩
  rw [relCost_of h]
  refine zero_le.lt_of_ne fun h0 ↦ ?_
  obtain ⟨b, hb⟩ := exists_ne (0 : B)
  exact hb ((h0 ▸ le_top).antisymm zero_le)

/-- A leftover plus a slack `c` is finite exactly on the relation and when `c` is finite. -/
theorem relCost_add_lt_top_iff [AddZeroClass B] [Preorder B] [Top B] [CanonicallyOrderedAdd B]
    {c : B} : relCost S x y + c < ⊤ ↔ S x y ∧ c < ⊤ := by
  by_cases hS : S x y
  · simp [hS]
  · simpa [hS] using le_self_add.not_gt

/-- Enlarging a relation shrinks its leftover. -/
theorem relCost_anti [Zero B] [Preorder B] [OrderTop B] (h : ∀ x y, S x y → S' x y) :
    relCost (B := B) S' ≤ relCost S := fun x y ↦ by
  by_cases hS : S x y
  · rw [relCost_of hS, relCost_of (h x y hS)]
  · exact (relCost_of_not (B := B) hS).symm ▸ le_top

/-- A bound on `a` by `b` plus the leftover of a relation holds iff it holds on related points. -/
theorem _root_.GradedDivergence.le_add_relCost_iff {a b : ℝ≥0∞} :
    a ≤ b + relCost S x y ↔ (S x y → a ≤ b) := by
  by_cases hS : S x y <;> simp [hS]

end relCost

section Classes

/-! ## Laws of a lifting -/

variable {B : Type v} (L : GradedLifting.{u} B)

/- The `< ⊤` guards on `pure` and `frame` are needed by span liftings (`isLawful_spanLifting_iff`)
and by regradings (`isLawful_comap`); the codensity lifting satisfies both laws without them.
`mono` needs sub-probability measures because divergences are graded only on those. -/
/-- The structural laws of a lifting: Dirac pairs, zero measures, weakening, framing and
pushforward. -/
class IsLawful [Add B] [Preorder B] [Top B] : Prop where
  /-- Dirac measures at a pair of finite leftover lift at that leftover. -/
  pure {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {R : X → Y → B} {x : X} {y : Y} :
    R x y < ⊤ → L (R x y) R (dirac x) (dirac y)
  /-- The zero measures lift at any budget and leftover. -/
  zero {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (b : B) (R : X → Y → B) :
    L b R (0 : Measure X) (0 : Measure Y)
  /-- Lifting weakens in the budget and in the leftover. -/
  mono {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b b' : B} {R R' : X → Y → B}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    L b R μ ν → b ≤ b' → R' ≤ R → L b' R' μ ν
  /-- Framing by a finite `c` adds `c` to the budget and to every leftover. -/
  frame {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b c : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} : c < ⊤ → L b R μ ν → L (b + c) (fun x y ↦ R x y + c) μ ν
  /-- Lifting is preserved by pushing both measures forward along measurable maps. -/
  map {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
    [MeasurableSpace Y'] {b : B} {R : X' → Y' → B} {μ : Measure X} {ν : Measure Y} {f : X → X'}
    {g : Y → Y'} (hf : Measurable f) (hg : Measurable g) :
    L b (fun x y ↦ R (f x) (g y)) μ ν → L b R (μ.map f) (ν.map g)

/- Separate from `IsLawful`: `markovCodensity` (KL, Hellinger) is lawful but binds only under a
side condition, through `BindLaw.massEq`. -/
/-- Binding with sub-Markov kernels whose outputs are lifted wherever the leftover is finite. -/
class HasBind [LT B] [Top B] : Prop where
  /-- Lifted measures bind to lifted measures along kernels lifted at finite leftovers. -/
  bind {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
    [MeasurableSpace Y'] {b : B} {R : X → Y → B} {R' : X' → Y' → B} {μ : Measure X}
    {ν : Measure Y} {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f]
    [IsSubMarkovKernel g] :
    L b R μ ν → (∀ x y, R x y < ⊤ → L (R x y) R' (f x) (g y)) → L b R' (f ∘ₘ μ) (g ∘ₘ ν)

/-! ## Soundness and completeness -/

/-- Lifting equality within a budget gives the divergence within that budget. -/
class IsSound [Zero B] [Top B] (D : GradedDivergence.{u} B) : Prop where
  /-- Equality lifted within `b` gives `D b μ ν`. -/
  sound {X : Type u} [MeasurableSpace X] {b : B} {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : L.Rel b (· = ·) μ ν → D b μ ν

/-- The divergence within a budget gives a lifting of equality within that budget. -/
class IsComplete [Zero B] [Top B] (D : GradedDivergence.{u} B) : Prop where
  /-- `D b μ ν` gives equality lifted within `b`. -/
  complete {X : Type u} [MeasurableSpace X] {b : B} {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] : D b μ ν → L.Rel b (· = ·) μ ν

/-! ## Further properties used by the logic -/

/-- The zero measure on the left lifts against every sub-probability measure; lifting analogue of
`GradedDivergence.IsZeroLeft`. -/
class IsZeroLeft : Prop where
  /-- The zero measure lifts against any sub-probability measure at any budget and leftover. -/
  zero_left {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (b : B) (R : X → Y → B)
    (ν : Measure Y) [IsSubProbabilityMeasure ν] : L b R (0 : Measure X) ν

/-- A lifting along an increasing sequence on the left passes to its supremum; lifting analogue of
`GradedDivergence.IsLeftContinuous`. -/
class IsLeftContinuous : Prop where
  /-- Lifting along an increasing sequence on the left passes to the supremum. -/
  iSup_left {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B} {R : X → Y → B}
    {μ : ℕ → Measure X} [∀ n, IsSubProbabilityMeasure (μ n)] (hμ : Monotone μ) {ν : Measure Y}
    [IsSubProbabilityMeasure ν] : (∀ n, L b R (μ n) ν) → L b R (⨆ n, μ n) ν

/-- Leftovers may be set to `⊤` off a measurable set carrying the left measure (Rocq
`gbl_head_supp`). -/
class IsSupportLocal [Top B] : Prop where
  /-- Setting the leftover to `⊤` off a measurable set of full left measure preserves lifting. -/
  restrict {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} {A : Set X} [DecidablePred (· ∈ A)] (hA : MeasurableSet A)
    (hμ : μ Aᶜ = 0) : L b R μ ν → L b (A.piecewise R fun _ _ ↦ ⊤) μ ν

/-- Every sub-probability measure lifts against itself along equality at budget `0`; lifting
analogue of `GradedDivergence.IsReflexive`. -/
class IsReflexive [Zero B] [Top B] : Prop where
  /-- A sub-probability measure lifts against itself along equality at budget `0`. -/
  refl {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsSubProbabilityMeasure μ] :
    L.Rel 0 (· = ·) μ μ

/-- Leftovers keyed on the right sample are paid in expectation, where `s` embeds an additive
slack into the budget. -/
class IsExpectationAdditive [AddZeroClass B] [Preorder B] (s : ℝ≥0∞ →+o B) : Prop where
  /-- Adding `s (c y)` to the leftover at `y` adds `s (∫⁻ y, c y ∂ν)` to the budget. -/
  add_right {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    {c : Y → ℝ≥0∞} (hc : Measurable c) :
    L b R μ ν → L (b + s (∫⁻ y, c y ∂ν)) (fun x y ↦ R x y + s (c y)) μ ν

/-- Events carried along a relation lifted at slack `s δ` satisfy `μ T ≤ ν T' + δ`, where `s`
embeds an additive slack into the budget; lifting analogue of `GradedDivergence.IsMassDetecting`. -/
class IsMassDetecting [AddZeroClass B] [Preorder B] [Top B] (s : ℝ≥0∞ →+o B) : Prop where
  /-- A lifting of `S` at slack `s δ` bounds `μ T` by `ν T' + δ` when `S` carries `T` into `T'`. -/
  measure_le_add {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {δ : ℝ≥0∞}
    {S : X → Y → Prop} {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {T : Set X} {T' : Set Y} (hT : MeasurableSet T)
    (hT' : MeasurableSet T') :
    L.Rel (s δ) S μ ν → (∀ x y, S x y → x ∈ T → y ∈ T') → μ T ≤ ν T' + δ

/-- Budgets are closed from above: a lifting at every larger budget gives the lifting; lifting
analogue of `GradedDivergence.IsBudgetClosed`. -/
class IsBudgetClosed [LT B] : Prop where
  /-- A lifting at every larger budget gives the lifting. -/
  of_forall_gt {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    (∀ b', b < b' → L b' R μ ν) → L b R μ ν

/-! ## Absorbing budgets -/

/-- A budget at which every pair of sub-probability measures is related (Rocq `GCFTop`). -/
def Absorbing (b : B) : Prop :=
  ∀ {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (R : X → Y → B) (μ : Measure X)
    (ν : Measure Y) [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν], L b R μ ν

/-- The top budget relates every pair of measures. -/
class IsTopAbsorbing [Top B] : Prop where
  /-- Every pair of measures is lifted at the top budget. -/
  top {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (R : X → Y → B) (μ : Measure X)
    (ν : Measure Y) : L ⊤ R μ ν

end Classes

/-! ## Derived laws for relational liftings -/

variable {B : Type v} {L : GradedLifting.{u} B} {X Y X' Y' : Type u} [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y'] {b b' c : B}
  {S : X → Y → Prop} {μ : Measure X} {ν : Measure Y}

/-- Restricting a relational lifting to a set carrying the left measure. -/
theorem Rel.restrict [Zero B] [Top B] [L.IsSupportLocal] {A : Set X} (h : L.Rel b S μ ν)
    (hA : MeasurableSet A) (hμ : μ Aᶜ = 0) : L.Rel b (fun x y ↦ S x y ∧ x ∈ A) μ ν := by
  classical
  unfold Rel
  convert IsSupportLocal.restrict hA hμ h using 2
  ext x y
  by_cases hx : x ∈ A <;> by_cases hS : S x y <;> simp [hx, hS]

section Lawful

variable [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]

namespace Rel

section Sub

variable [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] (h : L.Rel b S μ ν)

include h

/-- Weakening a relational lifting: a larger budget and a larger relation. -/
theorem mono {S' : X → Y → Prop} (hb : b ≤ b') (hS : ∀ x y, S x y → S' x y) : L.Rel b' S' μ ν :=
  IsLawful.mono h hb (relCost_anti hS)

/-- Pushing a relational lifting forward along measurable maps on both sides. -/
theorem map {S' : X' → Y' → Prop} {f : X → X'} {g : Y → Y'} (hS : ∀ x y, S x y → S' (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    L.Rel b S' (μ.map f) (ν.map g) :=
  IsLawful.map hf hg (IsLawful.mono h le_rfl (relCost_anti hS))

/-- Pushing a relational lifting forward along a measurable map on the left. -/
theorem map_left {S' : X' → Y → Prop} {f : X → X'} (hS : ∀ x y, S x y → S' (f x) y)
    (hf : Measurable f := by fun_prop) : L.Rel b S' (μ.map f) ν := by
  simpa only [map_id] using h.map (g := id) hS hf

/-- Pushing a relational lifting forward along a measurable map on the right. -/
theorem map_right {S' : X → Y' → Prop} {g : Y → Y'} (hS : ∀ x y, S x y → S' x (g y))
    (hg : Measurable g := by fun_prop) : L.Rel b S' μ (ν.map g) := by
  simpa only [map_id] using h.map (f := id) hS measurable_id hg

end Sub

end Rel

section Refl

variable [L.IsReflexive]

/-- Probability measures lift the full relation at budget `0`, through their product. -/
theorem rel_true (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    L.Rel 0 (fun _ _ ↦ True) μ ν := by
  simpa [map_fst_prod, map_snd_prod] using (IsReflexive.refl (μ.prod ν)).map
    (S' := fun _ _ ↦ True) (fun _ _ _ ↦ trivial) measurable_fst measurable_snd

/-- A measure lifts against its pushforward along the graph of the map. -/
theorem rel_graph (μ : Measure X) [IsSubProbabilityMeasure μ] {f : X → Y}
    (hf : Measurable f := by fun_prop) : L.Rel 0 (fun x y ↦ f x = y) μ (μ.map f) :=
  (IsReflexive.refl μ).map_right (fun _ _ h ↦ congrArg f h) hf

/-- A probability measure lifts against the point mass at `y₀`, relating everything to `y₀`. -/
theorem rel_const_right (μ : Measure X) [IsProbabilityMeasure μ] (y₀ : Y) :
    L.Rel 0 (fun _ y ↦ y = y₀) μ (dirac y₀) := by
  simpa [Measure.map_const] using (IsReflexive.refl μ).map_right
    (S' := fun _ y ↦ y = y₀) fun _ _ _ ↦ rfl

/-- A Dirac measure lifts against a probability measure carried by `A`, relating its point to
`A`. -/
theorem rel_dirac_left [L.IsSupportLocal] (ν : Measure Y) [IsProbabilityMeasure ν] {A : Set Y}
    (hA : MeasurableSet A) (hν : ν Aᶜ = 0) (x₀ : X) :
    L.Rel 0 (fun x y ↦ x = x₀ ∧ y ∈ A) (dirac x₀) ν := by
  simpa [Measure.map_const] using ((IsReflexive.refl ν).restrict hA hν).map_left
    (S' := fun x y ↦ x = x₀ ∧ y ∈ A) fun _ _ h ↦ ⟨rfl, h.1 ▸ h.2⟩

/-- A probability measure carried by `A` lifts against a Dirac measure, relating `A` to its
point. -/
theorem rel_dirac_right [L.IsSupportLocal] (μ : Measure X) [IsProbabilityMeasure μ] {A : Set X}
    (hA : MeasurableSet A) (hμ : μ Aᶜ = 0) (y₀ : Y) :
    L.Rel 0 (fun x y ↦ x ∈ A ∧ y = y₀) μ (dirac y₀) :=
  ((rel_const_right μ y₀).restrict hA hμ).mono le_rfl fun _ _ h ↦ ⟨h.2, h.1⟩

end Refl

end Lawful

/-- Framing a relational lifting by `c` lifts any leftover bounded by `c` on the relation. -/
theorem Rel.frame_le [AddZeroClass B] [Preorder B] [OrderTop B] [CanonicallyOrderedAdd B]
    [L.IsLawful] [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {R : X → Y → B}
    (h : L.Rel b S μ ν) (hR : ∀ x y, S x y → R x y ≤ c) (hc : c < ⊤) : L (b + c) R μ ν :=
  IsLawful.mono (IsLawful.frame hc h) le_rfl fun x y ↦ by
    by_cases hS : S x y
    · simpa [hS] using hR x y hS
    · simpa [hS] using le_top.trans le_self_add

/-- Related points lift as point masses, at any budget. -/
theorem rel_dirac [AddZeroClass B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
    [Nontrivial B] [L.IsLawful] {x : X} {y : Y} (h : S x y) (b : B) :
    L.Rel b S (dirac x) (dirac y) :=
  IsLawful.mono (relCost_of (B := B) h ▸ IsLawful.pure (relCost_lt_top_iff.2 h)) zero_le le_rfl

/-! ## Derived laws for binding -/

namespace HasBind

/-- Binding with measurable families of sub-probability measures. -/
theorem bind_fun [LT B] [Top B] [L.HasBind] {R : X → Y → B} {R' : X' → Y' → B}
    (h : L b R μ ν) {f : X → Measure X'} {g : Y → Measure Y'}
    [∀ x, IsSubProbabilityMeasure (f x)] [∀ y, IsSubProbabilityMeasure (g y)]
    (hk : ∀ x y, R x y < ⊤ → L (R x y) R' (f x) (g y)) (hf : Measurable f := by fun_prop)
    (hg : Measurable g := by fun_prop) : L b R' (μ.bind f) (ν.bind g) :=
  bind (f := ⟨f, hf⟩) (g := ⟨g, hg⟩) h hk

/-- Binding a relational lifting with sub-Markov kernels lifted at a finite budget `c` on the
relation. -/
theorem bind_rel [AddZeroClass B] [Preorder B] [Top B] [CanonicallyOrderedAdd B]
    [L.IsLawful] [L.HasBind] {R' : X' → Y' → B} (hc : c < ⊤) (h : L.Rel b S μ ν)
    {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f] [IsSubMarkovKernel g]
    (hk : ∀ x y, S x y → L c R' (f x) (g y)) : L (b + c) R' (f ∘ₘ μ) (g ∘ₘ ν) := by
  refine bind (IsLawful.frame hc h) fun x y hxy ↦ ?_
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hxy
  simpa [hS] using hk x y hS

/-- Binding a relational lifting with measurable families of sub-probability measures lifted at
a finite budget `c` on the relation. -/
theorem bind_rel_fun [AddZeroClass B] [Preorder B] [Top B] [CanonicallyOrderedAdd B]
    [L.IsLawful] [L.HasBind] {R' : X' → Y' → B} (hc : c < ⊤) (h : L.Rel b S μ ν)
    {f : X → Measure X'} {g : Y → Measure Y'} [∀ x, IsSubProbabilityMeasure (f x)]
    [∀ y, IsSubProbabilityMeasure (g y)] (hk : ∀ x y, S x y → L c R' (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    L (b + c) R' (μ.bind f) (ν.bind g) :=
  bind_rel (f := ⟨f, hf⟩) (g := ⟨g, hg⟩) hc h hk

end HasBind

open HasBind (bind_fun bind_rel)

/-- Relational liftings of two independent pairs lift the product relation between the product
measures, at the sum of the budgets. -/
theorem Rel.prod [AddZeroClass B] [Preorder B] [OrderTop B] [CanonicallyOrderedAdd B]
    [L.IsLawful] [L.HasBind] [SFinite μ] [SFinite ν] {T : X' → Y' → Prop} {μ' : Measure X'}
    {ν' : Measure Y'} [IsSubProbabilityMeasure μ'] [IsSubProbabilityMeasure ν']
    (h : L.Rel b S μ ν) (hc : c < ⊤) (h' : L.Rel c T μ' ν') :
    L.Rel (b + c) (fun p q ↦ S p.1 q.1 ∧ T p.2 q.2) (μ.prod μ') (ν.prod ν') := by
  -- write μ.prod μ' as μ followed by the kernel x ↦ (μ'.map (x, ·)), then bind
  rw [← compProd_const, ← compProd_const, compProd_eq_comp_prod, compProd_eq_comp_prod]
  refine bind_rel hc h fun x y hS ↦ ?_
  simpa [Rel, Kernel.prod_apply, id_apply, dirac_prod] using h'.map fun _ _ hT ↦ ⟨hS, hT⟩

/-! ## Slack paid in expectation; event masses -/

/-- Binding with continuations whose budget `s (E y)` depends on the right sample pays only the
expectation of `E`. -/
theorem IsExpectationAdditive.bind_adv [AddZeroClass B] [Preorder B] [Top B]
    [CanonicallyOrderedAdd B] {s : ℝ≥0∞ →+o B} [L.HasBind] [L.IsExpectationAdditive s]
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {R' : X' → Y' → B}
    (h : L.Rel b S μ ν) {f : X → Measure X'} {g : Y → Measure Y'}
    [∀ x, IsSubProbabilityMeasure (f x)] [∀ y, IsSubProbabilityMeasure (g y)] {E : Y → ℝ≥0∞}
    (hk : ∀ x y, S x y → L (s (E y)) R' (f x) (g y)) (hf : Measurable f := by fun_prop)
    (hg : Measurable g := by fun_prop) (hE : Measurable E := by fun_prop) :
    L (b + s (∫⁻ y, E y ∂ν)) R' (μ.bind f) (ν.bind g) := by
  refine bind_fun (add_right hE h) (fun x y hxy ↦ ?_) hf hg
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hxy
  simpa [hS] using hk x y hS

/-- An exact relational lifting bounds the mass of an event by that of its image. -/
theorem IsMassDetecting.measure_le [AddZeroClass B] [Preorder B] [Top B] {s : ℝ≥0∞ →+o B}
    [L.IsMassDetecting s] [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {T : Set X}
    {T' : Set Y} (hT : MeasurableSet T) (hT' : MeasurableSet T') (h : L.Rel 0 S μ ν)
    (hS : ∀ x y, S x y → x ∈ T → y ∈ T') : μ T ≤ ν T' := by
  simpa using measure_le_add (s := s) (δ := 0) hT hT' (by rwa [map_zero]) hS

/-! ## Absorbing budgets and the top budget -/

/-- A budget above an absorbing one is absorbing. -/
theorem Absorbing.mono [Add B] [Preorder B] [Top B] [L.IsLawful] (h : L.Absorbing b)
    (hb : b ≤ b') : L.Absorbing b' := fun R μ ν _ _ ↦ IsLawful.mono (h R μ ν) hb le_rfl

/-- A budget is not absorbing once it fails to relate two point masses along the empty
relation. -/
theorem not_absorbing_of_refutes [Zero B] [Top B]
    (h : ¬L.Rel b (fun _ _ ↦ False) (dirac unit.{u + 1}) (dirac unit.{u + 1})) :
    ¬L.Absorbing b := fun hb ↦ h (hb _ _ _)

/-- The top budget is absorbing. -/
theorem IsTopAbsorbing.absorbing_top [Top B] [L.IsTopAbsorbing] : L.Absorbing ⊤ :=
  fun R μ ν _ _ ↦ top R μ ν

section Top

variable [PartialOrder B] [OrderTop B] [L.IsTopAbsorbing]

/-- A lifting holds once it holds at finite budgets, since everything is related at `⊤`. -/
theorem IsTopAbsorbing.of_lt_top {R : X → Y → B} (h : b < ⊤ → L b R μ ν) : L b R μ ν := by
  obtain rfl | hb := eq_or_ne b ⊤
  · exact top R μ ν
  · exact h (lt_top_iff_ne_top.2 hb)

open IsTopAbsorbing (of_lt_top)

/-- Framing by any `c`, finite or not. -/
theorem IsTopAbsorbing.frame [AddCommMagma B] [CanonicallyOrderedAdd B] [L.IsLawful]
    {R : X → Y → B} (h : L b R μ ν) : L (b + c) (fun x y ↦ R x y + c) μ ν :=
  of_lt_top fun hbc ↦ IsLawful.frame (le_add_self.trans_lt hbc) h

/-- `Rel.frame_le` for any `c`, finite or not. -/
theorem Rel.frame_le_of_isTopAbsorbing [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {R : X → Y → B} (h : L.Rel b S μ ν)
    (hR : ∀ x y, S x y → R x y ≤ c) : L (b + c) R μ ν :=
  of_lt_top fun hbc ↦ h.frame_le hR (le_add_self.trans_lt hbc)

/-- `Rel.prod` for any `c`, finite or not. -/
theorem Rel.prod_of_isTopAbsorbing [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.HasBind] [SFinite μ] [SFinite ν] {T : X' → Y' → Prop} {μ' : Measure X'}
    {ν' : Measure Y'} [IsSubProbabilityMeasure μ'] [IsSubProbabilityMeasure ν']
    (h : L.Rel b S μ ν) (h' : L.Rel c T μ' ν') :
    L.Rel (b + c) (fun p q ↦ S p.1 q.1 ∧ T p.2 q.2) (μ.prod μ') (ν.prod ν') :=
  of_lt_top fun hbc ↦ h.prod (le_add_self.trans_lt hbc) h'

end Top

end GradedLifting
