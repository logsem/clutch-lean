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

/-- Larger relations give larger liftings. -/
theorem Codensity.mono_rel {α : ι} {δ : ℝ≥0∞} {R R' : Set (X × Y)} {μ : Measure X}
    {ν : Measure Y} (h : Δ.Codensity α δ R μ ν) (hR : R ⊆ R') : Δ.Codensity α δ R' μ ν :=
  fun _ _ _ _ _ _ _ _ hkl ↦ h fun _ _ hxy ↦ hkl (hR hxy)

/-- Larger bounds give larger liftings. -/
theorem Codensity.mono_bound {α : ι} {δ δ' : ℝ≥0∞} {R : Set (X × Y)} {μ : Measure X}
    {ν : Measure Y} (h : Δ.Codensity α δ R μ ν) (hδ : δ ≤ δ') : Δ.Codensity α δ' R μ ν :=
  fun _ _ _ _ _ _ _ _ hkl ↦ (h hkl).trans (add_le_add_left hδ _)

/-- Weakening the bound and the relation, in the form `gcongr` uses. -/
@[gcongr]
theorem Codensity.imp {α : ι} {δ δ' : ℝ≥0∞} {R R' : Set (X × Y)} {μ : Measure X} {ν : Measure Y}
    (hδ : δ ≤ δ') (hR : R ⊆ R') : Δ.Codensity α δ R μ ν → Δ.Codensity α δ' R' μ ν :=
  fun h ↦ (h.mono_rel hR).mono_bound hδ

/-- Weakening the grade, the bound and the relation, in the form `gcongr` uses. -/
@[gcongr]
theorem Codensity.imp_grade [Preorder ι] [MulRightMono ι] [Δ.IsGraded] {α α' : ι}
    {δ δ' : ℝ≥0∞} {R R' : Set (X × Y)} {μ : Measure X} {ν : Measure Y}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] (hα : α ≤ α') (hδ : δ ≤ δ')
    (hR : R ⊆ R') : Δ.Codensity α δ R μ ν → Δ.Codensity α' δ' R' μ ν :=
  fun h ↦ (h.mono_rel hR).mono hα hδ

/-- A bound that holds above `δ` holds at `δ`. -/
theorem Codensity.of_forall_lt {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)} {μ : Measure X}
    {ν : Measure Y} (h : ∀ δ' > δ, Δ.Codensity α δ' R μ ν) : Δ.Codensity α δ R μ ν := by
  intro I _ β γ k l _ _ hkl
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hδ : δ < δ + ε := ENNReal.lt_add_right (ne_top_of_le_ne_top hlt.ne le_self_add)
    (by simpa using hε.ne')
  calc Δ (α * β) (k ∘ₘ μ) (l ∘ₘ ν) ≤ δ + ε + γ := h _ hδ hkl
    _ = δ + γ + ε := add_right_comm _ _ _

/-- Pushing forward along maps that send `R` into `S` (functoriality). -/
theorem Codensity.map {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)} {S : Set (X' × Y')} {μ : Measure X}
    {ν : Measure Y} (h : Δ.Codensity α δ R μ ν) {f : X → X'} {g : Y → Y'}
    (hfg : ∀ ⦃x y⦄, (x, y) ∈ R → (f x, g y) ∈ S) (hf : Measurable f := by fun_prop)
    (hg : Measurable g := by fun_prop) : Δ.Codensity α δ S (μ.map f) (ν.map g) := by
  intro I _ β γ k l _ _ hkl
  rw [bind_map_eq μ hf, bind_map_eq ν hg]
  exact h (k := k.comap f hf) (l := l.comap g hg) fun x y hxy ↦ hkl (hfg hxy)

/-- Pushing forward the left measure along a map that sends `R` into `S`. -/
theorem Codensity.map_left {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)} {S : Set (X' × Y)}
    {μ : Measure X} {ν : Measure Y} (h : Δ.Codensity α δ R μ ν) {f : X → X'}
    (hf' : ∀ ⦃x y⦄, (x, y) ∈ R → (f x, y) ∈ S) (hf : Measurable f := by fun_prop) :
    Δ.Codensity α δ S (μ.map f) ν := by
  simpa [map_id] using h.map (g := id) hf' hf measurable_id

/-- Pushing forward the right measure along a map that sends `R` into `S`. -/
theorem Codensity.map_right {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)} {S : Set (X × Y')}
    {μ : Measure X} {ν : Measure Y} (h : Δ.Codensity α δ R μ ν) {g : Y → Y'}
    (hg' : ∀ ⦃x y⦄, (x, y) ∈ R → (x, g y) ∈ S) (hg : Measurable g := by fun_prop) :
    Δ.Codensity α δ S μ (ν.map g) := by
  simpa [map_id] using h.map (f := id) hg' measurable_id hg

/-- Binding with measurable families of subprobability measures (`Codensity.bind` for plain
functions). -/
theorem Codensity.bind_fun {α α' : ι} {δ δ' : ℝ≥0∞} {R : Set (X × Y)} {S : Set (X' × Y')}
    {μ : Measure X} {ν : Measure Y} (h : Δ.Codensity α δ R μ ν) {f : X → Measure X'}
    {g : Y → Measure Y'} [∀ x, IsSubProbabilityMeasure (f x)]
    [∀ y, IsSubProbabilityMeasure (g y)]
    (hfg : ∀ ⦃x y⦄, (x, y) ∈ R → Δ.Codensity α' δ' S (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    Δ.Codensity (α * α') (δ + δ') S (μ.bind f) (ν.bind g) :=
  h.bind (f := ⟨f, hf⟩) (g := ⟨g, hg⟩) hfg

/-- The product of two relations. -/
def relProd (R : Set (X × Y)) (S : Set (X' × Y')) : Set ((X × X') × (Y × Y')) :=
  {p | (p.1.1, p.2.1) ∈ R ∧ (p.1.2, p.2.2) ∈ S}

/-- Pairing related points with lifted measures stays in the lifting of the product relation
(strength). -/
theorem Codensity.strength {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)} {S : Set (X' × Y')}
    {μ : Measure X'} {ν : Measure Y'} (h : Δ.Codensity α δ S μ ν) {x : X} {y : Y}
    (hxy : (x, y) ∈ R) :
    Δ.Codensity α δ (relProd R S) (μ.map (Prod.mk x)) (ν.map (Prod.mk y)) :=
  h.map fun _ _ h' ↦ ⟨hxy, h'⟩

/-! ### Limits, null sets and mass bounds -/

/-- The zero measure lifts anything. -/
theorem codensity_zero_left [Δ.IsZeroLeft] {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)}
    {ν : Measure Y} : Δ.Codensity α δ R 0 ν := by
  intro I _ β γ k l _ _ _
  rw [bind_zero_left]
  exact (IsZeroLeft.zero_left_le _ _).trans zero_le

/-- The limit of an increasing sequence of liftings is a lifting. -/
theorem Codensity.iSup_left [Δ.IsLeftContinuous] {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)}
    {μ : ℕ → Measure X} [∀ n, IsSubProbabilityMeasure (μ n)] (hμ : Monotone μ) {ν : Measure Y}
    [IsSubProbabilityMeasure ν] (h : ∀ n, Δ.Codensity α δ R (μ n) ν) :
    Δ.Codensity α δ R (⨆ n, μ n) ν := by
  intro I _ β γ k l _ _ hkl
  rw [iSup_bind_of_monotone hμ k.measurable]
  exact (IsLeftContinuous.iSup_left_le _ (fun _ _ hmn ↦ bind_mono_left (hμ hmn) k.measurable)
    _).trans (iSup_le fun n ↦ h n hkl)

/-- A measure lifts anything with a bound at least its mass. -/
theorem codensity_of_measure_univ_le [Δ.IsMassBounded] {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (hδ : μ .univ ≤ δ) : Δ.Codensity α δ R μ ν := by
  intro I _ β γ k l _ _ _
  calc Δ (α * β) (k ∘ₘ μ) (l ∘ₘ ν)
      ≤ (k ∘ₘ μ) .univ := IsMassBounded.le_measure_univ _ _ _
    _ ≤ μ .univ := by
        rw [bind_apply .univ k.measurable.aemeasurable]
        exact lintegral_le_meas (fun _ ↦ IsSubProbabilityMeasure.measure_univ_le_one) (by simp)
    _ ≤ δ + γ := hδ.trans le_self_add

/-- A bound of at least one makes any subprobability measure lift anything. -/
theorem codensity_of_one_le [Δ.IsMassBounded] {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (hδ : 1 ≤ δ) : Δ.Codensity α δ R μ ν :=
  codensity_of_measure_univ_le (IsSubProbabilityMeasure.measure_univ_le_one.trans hδ)

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
      _ ≤ δ + γ := add_le_add h (iSup_le fun _ ↦ hkl rfl)

/-- With reflexivity and composability, the codensity lifting of equality is exactly the
divergence bound (the fundamental property, Thm. 8.2). -/
theorem codensity_diag_iff [Δ.IsReflexive] [Δ.IsComposable] {X : Type u} [MeasurableSpace X]
    {α : ι} {δ : ℝ≥0∞} {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : Δ.Codensity α δ (diagRel X) μ ν ↔ Δ α μ ν ≤ δ :=
  ⟨Codensity.le_of_diag, codensity_diag_of_le⟩

/-- A measure lifts the graph of a map against its pushforward (exact coupling). -/
theorem codensity_graph [Δ.IsReflexive] [Δ.IsComposable] {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsSubProbabilityMeasure μ] {f : X → Y} (hf : Measurable f := by fun_prop) :
    Δ.Codensity 1 0 {p | f p.1 = p.2} μ (μ.map f) := by
  have h := (codensity_diag_of_le (IsReflexive.self_le_zero (Δ := Δ) μ)).map (f := id) (g := f)
    (S := {p | f p.1 = p.2}) fun x y (hxy : x = y) ↦ congrArg f hxy
  rwa [map_id] at h

/-- Probability measures lift the full relation (trivial coupling). -/
theorem codensity_univ [Δ.IsReflexive] [Δ.IsComposable] {X Y : Type u} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : Δ.Codensity 1 0 .univ μ ν := by
  have h := (codensity_diag_of_le (IsReflexive.self_le_zero (Δ := Δ) (μ.prod ν))).map
    (f := Prod.fst) (g := Prod.snd) (S := .univ) fun _ _ _ ↦ trivial
  rwa [map_fst_prod, map_snd_prod, measure_univ, measure_univ, one_smul, one_smul] at h

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
  refine h fun x y hxy ↦ le_trans ?_ (hkl hxy)
  rw [Kernel.comp_apply, Kernel.comp_apply, hΩ β (k x) (l y)]
  exact le_iSup₂_of_le j ‹_› le_rfl

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
