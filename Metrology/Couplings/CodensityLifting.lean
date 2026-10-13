module

public import Metrology.Couplings.ApproximateSpanLifting

/-! Codensity liftings of graded divergences (Sato–Katsumata, *Divergences on Monads for Relational
Program Logics*, §7). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

namespace GradedDivergence

variable {ι : Type v} [Monoid ι] (Δ : GradedDivergence.{u} ι)
variable {X Y X' Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
  [MeasurableSpace Y']

/-- The basic codensity lifting of `R` with observation space `Ω`, base relation `S₀` and target
relation `S`: measures whose binds with every `S₀`-respecting pair of kernels land in `S`
(Katsumata–Sato, *Codensity Liftings of Monads*). -/
def BasicCodensity (Ω : Type*) [MeasurableSpace Ω] (S₀ S : Measure Ω → Measure Ω → Prop)
    (R : Set (X × Y)) (μ : Measure X) (ν : Measure Y) : Prop :=
  ∀ ⦃k : Kernel X Ω⦄ ⦃l : Kernel Y Ω⦄ [IsSubMarkovKernel k] [IsSubMarkovKernel l],
    (∀ ⦃x y⦄, (x, y) ∈ R → S₀ (k x) (l y)) → S (k ∘ₘ μ) (l ∘ₘ ν)

/-- The codensity lifting `T[Δ](α, δ) R`: for every test space, grade and bound, the basic
codensity lifting from `Δ`-closeness to `Δ`-closeness with the grades multiplied and the bounds
added (Thm. 8). -/
def Codensity (α : ι) (δ : ℝ≥0∞) (R : Set (X × Y)) (μ : Measure X) (ν : Measure Y) : Prop :=
  ∀ ⦃I : Type u⦄ [MeasurableSpace I] ⦃β : ι⦄ ⦃γ : ℝ≥0∞⦄,
    BasicCodensity I (fun p q ↦ Δ β p q ≤ γ) (fun p q ↦ Δ (α * β) p q ≤ δ + γ) R μ ν

variable {Δ}

/-! ### The lifting laws (Def. 15, Thm. 8.1) -/

/-- Larger grades and bounds give larger liftings. -/
theorem Codensity.mono [Preorder ι] [MulRightMono ι] [Δ.IsGraded] {α α' : ι} {δ δ' : ℝ≥0∞}
    {R : Set (X × Y)} {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (h : Δ.Codensity α δ R μ ν) (hα : α ≤ α') (hδ : δ ≤ δ') :
    Δ.Codensity α' δ' R μ ν := by
  intro I _ β γ k l _ _ hkl
  calc Δ (α' * β) (k ∘ₘ μ) (l ∘ₘ ν)
      ≤ Δ (α * β) (k ∘ₘ μ) (l ∘ₘ ν) := IsGraded.anti (mul_le_mul_left hα β) _ _
    _ ≤ δ + γ := h hkl
    _ ≤ δ' + γ := add_le_add hδ le_rfl

/-- Related points lift to their Dirac measures at the unit grade. -/
theorem codensity_dirac {R : Set (X × Y)} {x : X} {y : Y} (h : (x, y) ∈ R) :
    Δ.Codensity 1 0 R (dirac x) (dirac y) := by
  intro I _ β γ k l _ _ hkl
  rw [dirac_bind k.measurable, dirac_bind l.measurable, one_mul, zero_add]
  exact hkl h

/-- Binding with kernels that map related inputs into the lifting of `S` (Kleisli extension). -/
theorem Codensity.bind {α α' : ι} {δ δ' : ℝ≥0∞} {R : Set (X × Y)} {S : Set (X' × Y')}
    {μ : Measure X} {ν : Measure Y} (h : Δ.Codensity α δ R μ ν) {f : Kernel X X'}
    {g : Kernel Y Y'} [IsSubMarkovKernel f] [IsSubMarkovKernel g]
    (hfg : ∀ ⦃x y⦄, (x, y) ∈ R → Δ.Codensity α' δ' S (f x) (g y)) :
    Δ.Codensity (α * α') (δ + δ') S (f ∘ₘ μ) (g ∘ₘ ν) := by
  intro I _ β γ k l _ _ hkl
  rw [comp_assoc, comp_assoc, mul_assoc, add_assoc]
  refine h fun x y hxy ↦ ?_
  rw [Kernel.comp_apply, Kernel.comp_apply]
  exact hfg hxy hkl

/-- The product of two relations. -/
def relProd (R : Set (X × Y)) (S : Set (X' × Y')) : Set ((X × X') × (Y × Y')) :=
  {p | (p.1.1, p.2.1) ∈ R ∧ (p.1.2, p.2.2) ∈ S}

/-- Pairing related points with lifted measures stays in the lifting of the product relation
(strength). -/
theorem Codensity.strength {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)} {S : Set (X' × Y')}
    {μ : Measure X'} {ν : Measure Y'} (h : Δ.Codensity α δ S μ ν) {x : X} {y : Y}
    (hxy : (x, y) ∈ R) :
    Δ.Codensity α δ (relProd R S) (μ.map (Prod.mk x)) (ν.map (Prod.mk y)) := by
  have := h.bind (f := .deterministic (Prod.mk x) (by fun_prop))
    (g := .deterministic (Prod.mk y) (by fun_prop)) fun x' y' h' ↦ by
      rw [Kernel.deterministic_apply, Kernel.deterministic_apply]
      exact codensity_dirac (R := relProd R S) ⟨hxy, h'⟩
  rwa [mul_one, add_zero, deterministic_comp_eq_map, deterministic_comp_eq_map] at this

/-! ### The fundamental property (Thm. 8.2) -/

/-- The diagonal relation. -/
def diagRel (X : Type*) : Set (X × X) := {p | p.1 = p.2}

/-- Reflexivity: the codensity lifting of equality is at most the divergence. -/
theorem Codensity.le_of_diag [Δ.IsReflexive] {X : Type u} [MeasurableSpace X] {α : ι}
    {δ : ℝ≥0∞} {μ ν : Measure X} (h : Δ.Codensity α δ (diagRel X) μ ν) : Δ α μ ν ≤ δ := by
  have := h (k := Kernel.id) (l := Kernel.id)
    fun x y (hxy : x = y) ↦ by subst hxy; exact IsReflexive.self_le_zero _
  rwa [id_comp, id_comp, mul_one, add_zero] at this

/-- Composability: the divergence is at most the codensity lifting of equality. -/
theorem codensity_diag_of_le [Δ.IsComposable] {X : Type u} [MeasurableSpace X] {α : ι}
    {δ : ℝ≥0∞} {μ ν : Measure X} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : Δ α μ ν ≤ δ) : Δ.Codensity α δ (diagRel X) μ ν := fun _ _ β γ k l _ _ hkl ↦
    calc Δ (α * β) (k ∘ₘ μ) (l ∘ₘ ν)
        ≤ Δ α μ ν + ⨆ x, Δ β (k x) (l x) := IsComposable.bind_le α β μ ν k l
      _ ≤ δ + γ := add_le_add h (iSup_le fun x ↦ hkl (show x = x from rfl))

/-- With reflexivity and composability, the codensity lifting of equality is exactly the
divergence bound (the fundamental property, Thm. 8.2). -/
theorem codensity_diag_iff [Δ.IsReflexive] [Δ.IsComposable] {X : Type u} [MeasurableSpace X]
    {α : ι} {δ : ℝ≥0∞} {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : Δ.Codensity α δ (diagRel X) μ ν ↔ Δ α μ ν ≤ δ :=
  ⟨Codensity.le_of_diag, codensity_diag_of_le⟩

/-- Conversely, if the lifting of equality contains every divergence bound, then `Δ` is
composable (Thm. 8.2). -/
theorem isComposable_of_codensity_diag
    (h : ∀ (α : ι) {X : Type u} [MeasurableSpace X] (μ ν : Measure X) [IsSubProbabilityMeasure μ]
      [IsSubProbabilityMeasure ν], Δ.Codensity α (Δ α μ ν) (diagRel X) μ ν) :
    Δ.IsComposable where
  bind_le α β _ _ _ _ μ₁ μ₂ _ _ κ η _ _ :=
    h α μ₁ μ₂ fun x _ (hxy : x = _) ↦ hxy ▸ le_iSup (fun x ↦ Δ β (κ x) (η x)) x

/-- Conversely, if the lifting of equality is within the divergence bounds, then Dirac measures
are at divergence zero from themselves (Thm. 8.2). -/
theorem dirac_self_le_zero_of_codensity_diag
    (h : ∀ {X : Type u} [MeasurableSpace X] {μ ν : Measure X},
      Δ.Codensity 1 0 (diagRel X) μ ν → Δ 1 μ ν ≤ 0) {X : Type u} [MeasurableSpace X] (x : X) :
    Δ 1 (dirac x) (dirac x) ≤ 0 :=
  h (codensity_dirac rfl)

theorem relProd_diagRel {X Y : Type*} :
    relProd (diagRel X) (diagRel Y) = diagRel (X × Y) := by
  ext ⟨⟨x, y⟩, x', y'⟩
  simp [relProd, diagRel]

/-- Pairing both sides with the same point does not increase the divergence (Prop. 13, from the
fundamental property and strength). -/
theorem map_prodMk_le [Δ.IsReflexive] [Δ.IsComposable] {X Y : Type u} [MeasurableSpace X]
    [MeasurableSpace Y] (α : ι) (x : X) (μ ν : Measure Y) [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : Δ α (μ.map (Prod.mk x)) (ν.map (Prod.mk x)) ≤ Δ α μ ν := by
  have h := (codensity_diag_of_le (Δ := Δ) (le_refl (Δ α μ ν))).strength
    (R := diagRel X) (show x = x from rfl)
  rw [relProd_diagRel] at h
  exact h.le_of_diag

/-! ### Fixing the test space (Def. 11, Prop. 14) -/

/-- `Δ` is generated over `Ω`: it is the supremum of its pushforwards along kernels into `Ω`
(Def. 11). -/
def IsGenerated (Ω : Type u) [MeasurableSpace Ω] : Prop :=
  ∀ (α : ι) {I : Type u} [MeasurableSpace I] (μ ν : Measure I) [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν], Δ α μ ν = ⨆ (k : Kernel I Ω) (_ : IsSubMarkovKernel k),
      Δ α (k ∘ₘ μ) (k ∘ₘ ν)

/-- For a divergence generated over `Ω`, tests into `Ω` suffice (Prop. 14). -/
theorem codensity_iff_of_isGenerated {Ω : Type u} [MeasurableSpace Ω] (hΩ : Δ.IsGenerated Ω)
    {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)} {μ : Measure X} {ν : Measure Y}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    Δ.Codensity α δ R μ ν ↔ ∀ ⦃β : ι⦄ ⦃γ : ℝ≥0∞⦄,
      BasicCodensity Ω (fun p q ↦ Δ β p q ≤ γ) (fun p q ↦ Δ (α * β) p q ≤ δ + γ) R μ ν := by
  refine ⟨fun h β γ ↦ @h Ω _ β γ, fun h I _ β γ k l _ _ hkl ↦ ?_⟩
  beta_reduce at hkl ⊢
  rw [hΩ]
  refine iSup₂_le fun j _ ↦ ?_
  rw [comp_assoc, comp_assoc]
  refine h (fun x y hxy ↦ ?_)
  rw [Kernel.comp_apply, Kernel.comp_apply]
  exact le_trans (by rw [hΩ β (k x) (l y)]; exact le_iSup₂_of_le j ‹_› le_rfl) (hkl hxy)

end GradedDivergence

/-! ### Span liftings sit inside codensity liftings -/

namespace Span

open GradedDivergence

variable {ι : Type v} [Monoid ι] {Δ : GradedDivergence.{u} ι} [Δ.IsComposable]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {Φ : Type u} [MeasurableSpace Φ]

/-- Measures related by a span lifting pass every test of the span's relation: forgetting the
witnesses lands in the codensity lifting. -/
theorem Rel.codensity {s : Span X Y Φ} {α : ι} {δ : ℝ≥0∞} {μ : Measure X} {ν : Measure Y}
    (h : (s♯[Δ, α, δ]).Rel μ ν) : Δ.Codensity α δ {p | s.Rel p.1 p.2} μ ν := by
  obtain ⟨w, rfl, rfl⟩ := h
  intro I _ β γ k l _ _ hkl
  calc Δ (α * β) (k ∘ₘ w.fst.map s.left) (l ∘ₘ w.snd.map s.right)
      = Δ (α * β) (k.comap s.left s.leftMeasurable ∘ₘ w.fst)
          (l.comap s.right s.rightMeasurable ∘ₘ w.snd) :=
        congrArg₂ (fun a b ↦ Δ (α * β) a b) (bind_map_eq _) (bind_map_eq _)
    _ ≤ Δ α w.fst w.snd + ⨆ φ, Δ β (k (s.left φ)) (l (s.right φ)) :=
        IsComposable.bind_le α β _ _ _ _
    _ ≤ δ + γ := add_le_add w.le (iSup_le fun φ ↦ hkl ⟨φ, rfl, rfl⟩)

end Span
