module

public import Metrology.Couplings.Divergence

/-! # Graded liftings

`GradedLifting B` relates two measures within a budget along a per-pair leftover (Approximate Span
Liftings, §5); this file gives its law classes and derived laws such as `Rel.prod`. -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

/-- A family of liftings: `L b R μ ν` relates `μ` and `ν` within budget `b`, leaving `R x y` for
the continuation at each pair. Budget first: with the spaces first Lean fills them in early and
`(codensity D).IsLawful` fails to elaborate. -/
def GradedLifting (B : Type v) : Type (max v (u + 1)) :=
  B → ∀ {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y],
    (X → Y → B) → Measure X → Measure Y → Prop

namespace GradedLifting

/-! ## Relations as leftovers

A relation `S` is the leftover `relCost S` (`0` on `S`, `⊤` off it); `Rel` lifts it. -/

section relCost

variable {B : Type v} {X Y : Type*} {S S' : X → Y → Prop} {x : X} {y : Y}

/-- The leftover of a relation: `0` on it, `⊤` off it. -/
noncomputable def relCost [Zero B] [Top B] (S : X → Y → Prop) (x : X) (y : Y) : B :=
  {p : X × Y | ¬S p.1 p.2}.indicator (fun _ ↦ ⊤) (x, y)

@[simp]
theorem relCost_of [Zero B] [Top B] (h : S x y) : relCost (B := B) S x y = 0 :=
  Set.indicator_of_notMem (not_not.2 h) _

@[simp]
theorem relCost_of_not [Zero B] [Top B] (h : ¬S x y) : relCost (B := B) S x y = ⊤ :=
  Set.indicator_of_mem h _

theorem relCost_lt_top_iff [AddZeroClass B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
    [Nontrivial B] : relCost (B := B) S x y < ⊤ ↔ S x y := by
  refine ⟨fun h ↦ by_contra fun hS ↦ (relCost_of_not (B := B) hS ▸ h).false, fun h ↦ ?_⟩
  rw [relCost_of h]
  refine zero_le.lt_of_ne fun h0 ↦ ?_
  obtain ⟨b, hb⟩ := exists_ne (0 : B)
  exact hb ((h0 ▸ le_top).antisymm zero_le)

theorem relCost_add_lt_top_iff [AddZeroClass B] [Preorder B] [Top B] [CanonicallyOrderedAdd B]
    {c : B} : relCost S x y + c < ⊤ ↔ S x y ∧ c < ⊤ := by
  by_cases hS : S x y
  · simp [hS]
  · simpa [hS] using le_self_add.not_gt

theorem relCost_anti [Zero B] [Preorder B] [OrderTop B] (h : ∀ x y, S x y → S' x y) :
    relCost (B := B) S' ≤ relCost S := fun x y ↦ by
  by_cases hS : S x y
  · rw [relCost_of hS, relCost_of (h x y hS)]
  · exact (relCost_of_not (B := B) hS).symm ▸ le_top

end relCost

section Classes

variable {B : Type v} (L : GradedLifting.{u} B)

/-- The lifting of a relation `S`: leftover `0` on `S` and `⊤` off it. -/
def Rel [Zero B] [Top B] {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (b : B)
    (S : X → Y → Prop) (μ : Measure X) (ν : Measure Y) : Prop :=
  L b (relCost S) μ ν

/-! ## Laws of a lifting -/

/-- The structural laws of a lifting: Dirac pairs, zero measures, weakening, framing and
pushforward. The `< ⊤` guards on `pure` and `frame` are needed by span liftings
(`isLawful_spanLifting_iff`) and by regradings (`isLawful_comap`); the codensity lifting satisfies
both laws without them. -/
class IsLawful [Add B] [Preorder B] [Top B] : Prop where
  pure {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {R : X → Y → B} {x : X} {y : Y} :
    R x y < ⊤ → L (R x y) R (dirac x) (dirac y)
  zero {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (b : B) (R : X → Y → B) :
    L b R (0 : Measure X) (0 : Measure Y)
  /-- Sub-probability is needed because divergences are graded only on sub-probability
  measures. -/
  mono {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b b' : B} {R R' : X → Y → B}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    L b R μ ν → b ≤ b' → R' ≤ R → L b' R' μ ν
  frame {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b c : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} : c < ⊤ → L b R μ ν → L (b + c) (fun x y ↦ R x y + c) μ ν
  map {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
    [MeasurableSpace Y'] {b : B} {R : X' → Y' → B} {μ : Measure X} {ν : Measure Y} {f : X → X'}
    {g : Y → Y'} (hf : Measurable f) (hg : Measurable g) :
    L b (fun x y ↦ R (f x) (g y)) μ ν → L b R (μ.map f) (ν.map g)

/-- Binding with sub-Markov kernels whose outputs are lifted wherever the leftover is finite.
Separate from `IsLawful`: `markovCodensity` (KL, Hellinger) is lawful but binds only under a side
condition, through `BindLaw.massEq`. -/
class HasBind [LT B] [Top B] : Prop where
  bind {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
    [MeasurableSpace Y'] {b : B} {R : X → Y → B} {R' : X' → Y' → B} {μ : Measure X}
    {ν : Measure Y} {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f]
    [IsSubMarkovKernel g] :
    L b R μ ν → (∀ x y, R x y < ⊤ → L (R x y) R' (f x) (g y)) → L b R' (f ∘ₘ μ) (g ∘ₘ ν)

/-! ## Soundness and completeness -/

/-- Lifting equality within a budget gives the divergence within that budget. -/
class IsSound [Zero B] [Top B] (D : GradedDivergence.{u} B) : Prop where
  sound {X : Type u} [MeasurableSpace X] {b : B} {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : L.Rel b (· = ·) μ ν → D b μ ν

/-- The divergence within a budget gives a lifting of equality within that budget. -/
class IsComplete [Zero B] [Top B] (D : GradedDivergence.{u} B) : Prop where
  complete {X : Type u} [MeasurableSpace X] {b : B} {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] : D b μ ν → L.Rel b (· = ·) μ ν

/-! ## Further properties used by the logic -/

/-- The zero measure on the left lifts against every sub-probability measure; lifting analogue of
`GradedDivergence.IsZeroLeft`. -/
class IsZeroLeft : Prop where
  zero_left {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (b : B) (R : X → Y → B)
    (ν : Measure Y) [IsSubProbabilityMeasure ν] : L b R (0 : Measure X) ν

/-- A lifting along an increasing sequence on the left passes to its supremum; lifting analogue of
`GradedDivergence.IsLeftContinuous`. -/
class IsLeftContinuous : Prop where
  iSup_left {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B} {R : X → Y → B}
    {μ : ℕ → Measure X} [∀ n, IsSubProbabilityMeasure (μ n)] (hμ : Monotone μ) {ν : Measure Y}
    [IsSubProbabilityMeasure ν] : (∀ n, L b R (μ n) ν) → L b R (⨆ n, μ n) ν

/-- Leftovers may be set to `⊤` off a measurable set carrying the left measure: the continuation
owes nothing at left states `μ` never reaches (Rocq `gbl_head_supp`). -/
class IsSupportLocal [Top B] : Prop where
  restrict {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} {A : Set X} [DecidablePred (· ∈ A)] (hA : MeasurableSet A)
    (hμ : μ Aᶜ = 0) : L b R μ ν → L b (A.piecewise R fun _ _ ↦ ⊤) μ ν

/-- Every sub-probability measure lifts against itself along equality at budget `0`; lifting
analogue of `GradedDivergence.IsReflexive`. -/
class IsReflexive [Zero B] [Top B] : Prop where
  refl {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsSubProbabilityMeasure μ] :
    L.Rel 0 (· = ·) μ μ

/-- A leftover keyed on the right sample is paid in expectation. The map `s` embeds an additive
slack `δ` into the budget (`δ ↦ (0, δ)` for dp); only tv has this, and it gives `bind_adv`. -/
class IsExpectationAdditive [AddZeroClass B] [Preorder B] (s : ℝ≥0∞ →+o B) : Prop where
  add_right {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    {c : Y → ℝ≥0∞} (hc : Measurable c) :
    L b R μ ν → L (b + s (∫⁻ y, c y ∂ν)) (fun x y ↦ R x y + s (c y)) μ ν

/-- Events related at slack `s δ` differ in mass by at most `δ`, where `s` embeds an additive slack
`δ` into the budget (`δ ↦ (0, δ)` for dp); lifting analogue of
`GradedDivergence.IsMassDetecting`. -/
class IsMassDetecting [AddZeroClass B] [Preorder B] [Top B] (s : ℝ≥0∞ →+o B) : Prop where
  measure_le_add {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {δ : ℝ≥0∞}
    {S : X → Y → Prop} {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {T : Set X} {T' : Set Y} (hT : MeasurableSet T)
    (hT' : MeasurableSet T') :
    L.Rel (s δ) S μ ν → (∀ x y, S x y → x ∈ T → y ∈ T') → μ T ≤ ν T' + δ

/-- Budgets are closed from above: a lifting at every larger budget gives the lifting; lifting
analogue of `GradedDivergence.IsBudgetClosed`. -/
class IsBudgetClosed [LT B] : Prop where
  of_forall_gt {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    (∀ b', b < b' → L b' R μ ν) → L b R μ ν

/-- A budget at which every pair of sub-probability measures is related (Rocq `GCFTop`). -/
def Absorbing (b : B) : Prop :=
  ∀ {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (R : X → Y → B) (μ : Measure X)
    (ν : Measure Y) [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν], L b R μ ν

/-- The top budget relates every pair of measures (Rocq `GCFTop` at the order top). -/
class IsTopAbsorbing [Top B] : Prop where
  top {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (R : X → Y → B) (μ : Measure X)
    (ν : Measure Y) : L ⊤ R μ ν

end Classes

/-! ## Derived laws for relational liftings -/

variable {B : Type v} {L : GradedLifting.{u} B} {X Y X' Y' : Type u} [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y'] {b b' c : B}
  {S : X → Y → Prop} {μ : Measure X} {ν : Measure Y}

/-- Weakening a relational lifting: a larger budget and a larger relation. -/
theorem Rel.mono [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {S' : X → Y → Prop}
    (h : L.Rel b S μ ν) (hb : b ≤ b') (hS : ∀ x y, S x y → S' x y) : L.Rel b' S' μ ν :=
  IsLawful.mono h hb (relCost_anti hS)

/-- Framing a relational lifting by `c` meets every leftover bounded by `c` on the relation. -/
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

/-- Pushing a relational lifting forward along measurable maps on both sides. -/
theorem Rel.map [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {S' : X' → Y' → Prop} {f : X → X'}
    {g : Y → Y'} (h : L.Rel b S μ ν) (hS : ∀ x y, S x y → S' (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    L.Rel b S' (μ.map f) (ν.map g) :=
  IsLawful.map hf hg (IsLawful.mono h le_rfl (relCost_anti hS))

theorem Rel.map_left [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {S' : X' → Y → Prop} {f : X → X'}
    (h : L.Rel b S μ ν) (hS : ∀ x y, S x y → S' (f x) y) (hf : Measurable f := by fun_prop) :
    L.Rel b S' (μ.map f) ν := by
  simpa only [map_id] using h.map (g := id) hS hf

theorem Rel.map_right [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {S' : X → Y' → Prop} {g : Y → Y'}
    (h : L.Rel b S μ ν) (hS : ∀ x y, S x y → S' x (g y)) (hg : Measurable g := by fun_prop) :
    L.Rel b S' μ (ν.map g) := by
  simpa only [map_id] using h.map (f := id) hS measurable_id hg

/-- Pairing related points with a relational lifting lifts the product relation (strength). -/
theorem Rel.strength [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {S₀ : X' → Y' → Prop} {x : X'}
    {y : Y'} (h : L.Rel b S μ ν) (hxy : S₀ x y) :
    L.Rel b (fun p q ↦ S₀ p.1 q.1 ∧ S p.2 q.2) (μ.map (Prod.mk x)) (ν.map (Prod.mk y)) :=
  h.map fun _ _ hS ↦ ⟨hxy, hS⟩

/-- Probability measures lift the full relation at budget `0`, through their product. -/
theorem rel_true [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful] [L.IsReflexive]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    L.Rel 0 (fun _ _ ↦ True) μ ν := by
  simpa [map_fst_prod, map_snd_prod] using (IsReflexive.refl (L := L) (μ.prod ν)).map
    (S' := fun _ _ ↦ True) (fun _ _ _ ↦ trivial) measurable_fst measurable_snd

/-- A measure lifts against its pushforward along the graph of the map. -/
theorem rel_graph [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful] [L.IsReflexive]
    (μ : Measure X) [IsSubProbabilityMeasure μ] {f : X → Y} (hf : Measurable f := by fun_prop) :
    L.Rel 0 (fun x y ↦ f x = y) μ (μ.map f) :=
  (IsReflexive.refl μ).map_right (fun _ _ h ↦ congrArg f h) hf

/-- Restricting a relational lifting to a set carrying the left measure. -/
theorem Rel.restrict [Zero B] [Top B] [L.IsSupportLocal] {A : Set X} (h : L.Rel b S μ ν)
    (hA : MeasurableSet A) (hμ : μ Aᶜ = 0) : L.Rel b (fun x y ↦ S x y ∧ x ∈ A) μ ν := by
  classical
  unfold Rel
  convert IsSupportLocal.restrict hA hμ h using 2
  ext x y
  by_cases hx : x ∈ A <;> by_cases hS : S x y <;> simp [hx, hS]

/-- A probability measure lifts against the point mass at `y₀`, relating everything to `y₀`
(from reflexivity by `map_right`). -/
theorem rel_const_right [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful] [L.IsReflexive]
    (μ : Measure X) [IsProbabilityMeasure μ] (y₀ : Y) :
    L.Rel 0 (fun _ y ↦ y = y₀) μ (dirac y₀) := by
  simpa [Measure.map_const] using (IsReflexive.refl (L := L) μ).map_right
    (S' := fun _ y ↦ y = y₀) (g := fun _ ↦ y₀) fun _ _ _ ↦ rfl

/-- The point mass at `x₀` lifts against a probability measure, relating `x₀` to everything
(from reflexivity by `map_left`). -/
theorem rel_const_left [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful] [L.IsReflexive]
    (ν : Measure Y) [IsProbabilityMeasure ν] (x₀ : X) :
    L.Rel 0 (fun x _ ↦ x = x₀) (dirac x₀) ν := by
  simpa [Measure.map_const] using (IsReflexive.refl (L := L) ν).map_left
    (S' := fun x _ ↦ x = x₀) (f := fun _ ↦ x₀) fun _ _ _ ↦ rfl

/-- A Dirac measure lifts against a probability measure carried by `A`, relating its point to
`A`. -/
theorem rel_dirac_left [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful] [L.IsReflexive]
    [L.IsSupportLocal] (ν : Measure Y) [IsProbabilityMeasure ν] {A : Set Y}
    (hA : MeasurableSet A) (hν : ν Aᶜ = 0) (x₀ : X) :
    L.Rel 0 (fun x y ↦ x = x₀ ∧ y ∈ A) (dirac x₀) ν := by
  simpa [Measure.map_const] using ((IsReflexive.refl (L := L) ν).restrict hA hν).map_left
    (S' := fun x y ↦ x = x₀ ∧ y ∈ A) (f := fun _ ↦ x₀) fun _ _ h ↦ ⟨rfl, h.1 ▸ h.2⟩

/-- A probability measure carried by `A` lifts against a Dirac measure, relating `A` to its
point. -/
theorem rel_dirac_right [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful] [L.IsReflexive]
    [L.IsSupportLocal] (μ : Measure X) [IsProbabilityMeasure μ] {A : Set X}
    (hA : MeasurableSet A) (hμ : μ Aᶜ = 0) (y₀ : Y) :
    L.Rel 0 (fun x y ↦ x ∈ A ∧ y = y₀) μ (dirac y₀) :=
  ((rel_const_right μ y₀).restrict hA hμ).mono le_rfl fun _ _ h ↦ ⟨h.2, h.1⟩

/-! ## Derived laws for binding -/

/-- Binding with measurable families of sub-probability measures. -/
theorem HasBind.bind_fun [LT B] [Top B] [L.HasBind] {R : X → Y → B} {R' : X' → Y' → B}
    (h : L b R μ ν) {f : X → Measure X'} {g : Y → Measure Y'}
    [∀ x, IsSubProbabilityMeasure (f x)] [∀ y, IsSubProbabilityMeasure (g y)]
    (hk : ∀ x y, R x y < ⊤ → L (R x y) R' (f x) (g y)) (hf : Measurable f := by fun_prop)
    (hg : Measurable g := by fun_prop) : L b R' (μ.bind f) (ν.bind g) :=
  HasBind.bind (f := ⟨f, hf⟩) (g := ⟨g, hg⟩) h hk

/-- Binding with continuations needed only almost everywhere on the left: restrict the
leftover to a measurable set of full measure where they exist. -/
theorem HasBind.bind_of_ae [Preorder B] [Top B] [L.IsSupportLocal] [L.HasBind] {R : X → Y → B}
    {R' : X' → Y' → B} {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f]
    [IsSubMarkovKernel g] (h : L b R μ ν)
    (hk : ∀ᵐ x ∂μ, ∀ y, R x y < ⊤ → L (R x y) R' (f x) (g y)) : L b R' (f ∘ₘ μ) (g ∘ₘ ν) := by
  classical
  obtain ⟨T, hkT, hT, hμT⟩ := exists_measurable_superset_of_null (ae_iff.1 hk)
  have hTk : ∀ x ∈ Tᶜ, ∀ y, R x y < ⊤ → L (R x y) R' (f x) (g y) :=
    fun x hx ↦ not_not.1 fun hn ↦ hx (hkT hn)
  refine HasBind.bind (IsSupportLocal.restrict hT.compl (by rwa [compl_compl]) h)
    fun x y hxy ↦ ?_
  by_cases hx : x ∈ Tᶜ
  · simpa [hx] using hTk x hx y (by simpa [hx] using hxy)
  · simp [hx] at hxy

/-- Binding a relational lifting with sub-Markov kernels lifted at a finite budget `c` on the
relation. -/
theorem HasBind.bind_rel [AddZeroClass B] [Preorder B] [Top B] [CanonicallyOrderedAdd B]
    [L.IsLawful] [L.HasBind] {R' : X' → Y' → B} (hc : c < ⊤) (h : L.Rel b S μ ν)
    {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f] [IsSubMarkovKernel g]
    (hk : ∀ x y, S x y → L c R' (f x) (g y)) : L (b + c) R' (f ∘ₘ μ) (g ∘ₘ ν) := by
  refine HasBind.bind (IsLawful.frame hc h) fun x y hxy ↦ ?_
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hxy
  simpa [hS] using hk x y hS

/-- Binding a relational lifting with measurable families of sub-probability measures lifted at
a finite budget `c` on the relation. -/
theorem HasBind.bind_rel_fun [AddZeroClass B] [Preorder B] [Top B] [CanonicallyOrderedAdd B]
    [L.IsLawful] [L.HasBind] {R' : X' → Y' → B} (hc : c < ⊤) (h : L.Rel b S μ ν)
    {f : X → Measure X'} {g : Y → Measure Y'} [∀ x, IsSubProbabilityMeasure (f x)]
    [∀ y, IsSubProbabilityMeasure (g y)] (hk : ∀ x y, S x y → L c R' (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    L (b + c) R' (μ.bind f) (ν.bind g) :=
  HasBind.bind_rel (f := ⟨f, hf⟩) (g := ⟨g, hg⟩) hc h hk

/-- Relational liftings of two independent pairs lift the product relation between the product
measures, at the sum of the budgets. -/
theorem Rel.prod [AddZeroClass B] [Preorder B] [OrderTop B] [CanonicallyOrderedAdd B]
    [L.IsLawful] [L.HasBind] [SFinite μ] [SFinite ν] {T : X' → Y' → Prop} {μ' : Measure X'}
    {ν' : Measure Y'} [IsSubProbabilityMeasure μ'] [IsSubProbabilityMeasure ν']
    (h : L.Rel b S μ ν) (hc : c < ⊤) (h' : L.Rel c T μ' ν') :
    L.Rel (b + c) (fun p q ↦ S p.1 q.1 ∧ T p.2 q.2) (μ.prod μ') (ν.prod ν') := by
  -- write μ.prod μ' as μ followed by the kernel x ↦ (μ'.map (x, ·)), then bind
  rw [← compProd_const, ← compProd_const, compProd_eq_comp_prod, compProd_eq_comp_prod]
  refine HasBind.bind_rel hc h fun x y hS ↦ ?_
  simpa [Rel, Kernel.prod_apply, Kernel.id_apply, dirac_prod] using
    h'.map (f := Prod.mk x) (g := Prod.mk y) fun _ _ hT ↦ ⟨hS, hT⟩

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
  refine HasBind.bind_fun (IsExpectationAdditive.add_right hE h) (fun x y hxy ↦ ?_) hf hg
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hxy
  simpa [hS] using hk x y hS

/-- An exact relational lifting bounds the mass of an event by that of its image. -/
theorem IsMassDetecting.measure_le [AddZeroClass B] [Preorder B] [Top B] {s : ℝ≥0∞ →+o B}
    [L.IsMassDetecting s] [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {T : Set X}
    {T' : Set Y} (hT : MeasurableSet T) (hT' : MeasurableSet T') (h : L.Rel 0 S μ ν)
    (hS : ∀ x y, S x y → x ∈ T → y ∈ T') : μ T ≤ ν T' := by
  simpa using IsMassDetecting.measure_le_add (s := s) (δ := 0) hT hT' (by rwa [map_zero]) hS

/-! ## Absorbing budgets and the top budget -/

/-- A budget above an absorbing one is absorbing. -/
theorem Absorbing.mono [Add B] [Preorder B] [Top B] [L.IsLawful] (h : L.Absorbing b)
    (hb : b ≤ b') : L.Absorbing b' := fun R μ ν _ _ ↦ IsLawful.mono (h R μ ν) hb le_rfl

/-- A budget is not absorbing once it fails to relate two point masses along the empty
relation. -/
theorem not_absorbing_of_refutes [Zero B] [Top B]
    (h : ¬L.Rel b (fun _ _ ↦ False) (dirac PUnit.unit.{u + 1}) (dirac PUnit.unit.{u + 1})) :
    ¬L.Absorbing b := fun hb ↦ h (hb _ _ _)

theorem IsTopAbsorbing.absorbing_top [Top B] [L.IsTopAbsorbing] : L.Absorbing ⊤ :=
  fun R μ ν _ _ ↦ IsTopAbsorbing.top R μ ν

/-- A lifting holds once it holds at finite budgets, since everything is related at `⊤`. -/
theorem IsTopAbsorbing.of_lt_top [PartialOrder B] [OrderTop B] [L.IsTopAbsorbing]
    {R : X → Y → B} (h : b < ⊤ → L b R μ ν) : L b R μ ν := by
  obtain rfl | hb := eq_or_ne b ⊤
  · exact IsTopAbsorbing.top R μ ν
  · exact h (lt_top_iff_ne_top.2 hb)

/-- Framing by any `c`, finite or not. -/
theorem IsTopAbsorbing.frame [AddCommMagma B] [PartialOrder B] [OrderTop B]
    [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsTopAbsorbing] {R : X → Y → B}
    (h : L b R μ ν) : L (b + c) (fun x y ↦ R x y + c) μ ν :=
  IsTopAbsorbing.of_lt_top fun hbc ↦ IsLawful.frame (le_add_self.trans_lt hbc) h

/-- `Rel.frame_le` for any `c`, finite or not. -/
theorem Rel.frame_le_of_isTopAbsorbing [AddCommMonoid B] [PartialOrder B] [OrderTop B]
    [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsTopAbsorbing] [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {R : X → Y → B} (h : L.Rel b S μ ν)
    (hR : ∀ x y, S x y → R x y ≤ c) : L (b + c) R μ ν :=
  IsTopAbsorbing.of_lt_top fun hbc ↦ h.frame_le hR (le_add_self.trans_lt hbc)

/-- `Rel.prod` for any `c`, finite or not. -/
theorem Rel.prod_of_isTopAbsorbing [AddCommMonoid B] [PartialOrder B] [OrderTop B]
    [CanonicallyOrderedAdd B] [L.IsLawful] [L.HasBind] [L.IsTopAbsorbing] [SFinite μ] [SFinite ν]
    {T : X' → Y' → Prop} {μ' : Measure X'} {ν' : Measure Y'} [IsSubProbabilityMeasure μ']
    [IsSubProbabilityMeasure ν'] (h : L.Rel b S μ ν) (h' : L.Rel c T μ' ν') :
    L.Rel (b + c) (fun p q ↦ S p.1 q.1 ∧ T p.2 q.2) (μ.prod μ') (ν.prod ν') :=
  IsTopAbsorbing.of_lt_top fun hbc ↦ h.prod (le_add_self.trans_lt hbc) h'

end GradedLifting
