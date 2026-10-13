module

public import Metrology.Couplings.ApproximateSpanLifting

/-! Codensity liftings of graded divergences (Sato–Katsumata, *Divergences on Monads for Relational
Program Logics*, §7). -/

@[expose] public section

universe u v

open MeasureTheory Measure

namespace GradedDivergence

variable {ι : Type v} [Monoid ι] (Δ : GradedDivergence.{u} ι)
variable {X Y X' Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
  [MeasurableSpace Y']

/-- A test for the relation `R` at grade `β` and bound `γ`: two measurable subprobability kernels
into a common space whose outputs are `Δ`-close on related inputs. -/
structure IsTest (R : Set (X × Y)) (β : ι) (γ : EReal) {I : Type u} [MeasurableSpace I]
    (k : X → Measure I) (l : Y → Measure I) : Prop where
  measurable_left : Measurable k
  measurable_right : Measurable l
  subProb_left x : IsSubProbabilityMeasure (k x)
  subProb_right y : IsSubProbabilityMeasure (l y)
  le ⦃x y⦄ : (x, y) ∈ R → Δ β (k x) (l y) ≤ γ

/-- The codensity lifting `T[Δ](α, δ) R`: subprobability measures that pass every test of `R`,
with the grades multiplied and the bounds added (Thm. 8). -/
structure Codensity (α : ι) (δ : EReal) (R : Set (X × Y)) (μ : Measure X) (ν : Measure Y) :
    Prop where
  fst : IsSubProbabilityMeasure μ
  snd : IsSubProbabilityMeasure ν
  le ⦃I : Type u⦄ [MeasurableSpace I] ⦃β : ι⦄ ⦃γ : EReal⦄ ⦃k : X → Measure I⦄
    ⦃l : Y → Measure I⦄ : IsTest Δ R β γ k l → Δ (α * β) (μ.bind k) (ν.bind l) ≤ δ + γ

variable {Δ}

/-! ### The lifting laws (Def. 15, Thm. 8.1) -/

/-- Larger grades and bounds give larger liftings. -/
theorem Codensity.mono [Preorder ι] [MulRightMono ι] [Δ.IsGraded] {α α' : ι} {δ δ' : EReal}
    {R : Set (X × Y)} {μ : Measure X} {ν : Measure Y} (h : Δ.Codensity α δ R μ ν)
    (hα : α ≤ α') (hδ : δ ≤ δ') : Δ.Codensity α' δ' R μ ν where
  fst := h.fst
  snd := h.snd
  le I _ β γ k l hkl := by
    have := hkl.subProb_left
    have := hkl.subProb_right
    have := h.fst
    have := h.snd
    have : IsSubProbabilityMeasure (μ.bind k) :=
      isSubProbabilityMeasure_bind (fun _ ↦ inferInstance) hkl.measurable_left.aemeasurable
    have : IsSubProbabilityMeasure (ν.bind l) :=
      isSubProbabilityMeasure_bind (fun _ ↦ inferInstance) hkl.measurable_right.aemeasurable
    exact (IsGraded.anti (mul_le_mul_left hα β) _ _).trans
      ((h.le hkl).trans (add_le_add hδ le_rfl))

/-- Related points lift to their Dirac measures at the unit grade. -/
theorem codensity_dirac {R : Set (X × Y)} {x : X} {y : Y} (h : (x, y) ∈ R) :
    Δ.Codensity 1 0 R (dirac x) (dirac y) where
  fst := inferInstance
  snd := inferInstance
  le I _ β γ k l hkl := by
    rw [dirac_bind hkl.measurable_left, dirac_bind hkl.measurable_right, one_mul, zero_add]
    exact hkl.le h

/-- Binding with kernels that map related inputs into the lifting of `S` (Kleisli extension). -/
theorem Codensity.bind {α α' : ι} {δ δ' : EReal} {R : Set (X × Y)} {S : Set (X' × Y')}
    {μ : Measure X} {ν : Measure Y} (h : Δ.Codensity α δ R μ ν) {f : X → Measure X'}
    {g : Y → Measure Y'} (hf : Measurable f) (hg : Measurable g)
    [∀ x, IsSubProbabilityMeasure (f x)] [∀ y, IsSubProbabilityMeasure (g y)]
    (hfg : ∀ ⦃x y⦄, (x, y) ∈ R → Δ.Codensity α' δ' S (f x) (g y)) :
    Δ.Codensity (α * α') (δ + δ') S (μ.bind f) (ν.bind g) where
  fst := have := h.fst; isSubProbabilityMeasure_bind (fun _ ↦ inferInstance) hf.aemeasurable
  snd := have := h.snd; isSubProbabilityMeasure_bind (fun _ ↦ inferInstance) hg.aemeasurable
  le I _ β γ k l hkl := by
    have := hkl.subProb_left
    have := hkl.subProb_right
    have hk := hkl.measurable_left
    have hl := hkl.measurable_right
    rw [bind_bind hf.aemeasurable (by fun_prop), bind_bind hg.aemeasurable (by fun_prop),
      mul_assoc, add_assoc]
    refine h.le ⟨by fun_prop, by fun_prop, fun x ↦ isSubProbabilityMeasure_bind
      (fun _ ↦ inferInstance) hk.aemeasurable, fun y ↦ isSubProbabilityMeasure_bind
      (fun _ ↦ inferInstance) hl.aemeasurable, fun x y hxy ↦ (hfg hxy).le hkl⟩

/-- The product of two relations. -/
def relProd (R : Set (X × Y)) (S : Set (X' × Y')) : Set ((X × X') × (Y × Y')) :=
  {p | (p.1.1, p.2.1) ∈ R ∧ (p.1.2, p.2.2) ∈ S}

/-- Pairing related points with lifted measures stays in the lifting of the product relation
(strength). -/
theorem Codensity.strength {α : ι} {δ : EReal} {R : Set (X × Y)} {S : Set (X' × Y')}
    {μ : Measure X'} {ν : Measure Y'} (h : Δ.Codensity α δ S μ ν) {x : X} {y : Y}
    (hxy : (x, y) ∈ R) :
    Δ.Codensity α δ (relProd R S) (μ.map (Prod.mk x)) (ν.map (Prod.mk y)) := by
  have := h.bind (f := fun x' ↦ dirac (x, x')) (g := fun y' ↦ dirac (y, y')) (by fun_prop)
    (by fun_prop) fun x' y' h' ↦ codensity_dirac (Δ := Δ) (R := relProd R S) ⟨hxy, h'⟩
  rwa [mul_one, add_zero, bind_dirac_eq_map _ (by fun_prop),
    bind_dirac_eq_map _ (by fun_prop)] at this

/-! ### The fundamental property (Thm. 8.2) -/

/-- The diagonal relation. -/
def diagRel (X : Type*) : Set (X × X) := {p | p.1 = p.2}

/-- Reflexivity: the codensity lifting of equality is at most the divergence. -/
theorem Codensity.le_of_diag [Δ.IsReflexive] {X : Type u} [MeasurableSpace X] {α : ι}
    {δ : EReal} {μ ν : Measure X} (h : Δ.Codensity α δ (diagRel X) μ ν) : Δ α μ ν ≤ δ := by
  have := h.le (k := dirac) (l := dirac) ⟨measurable_dirac, measurable_dirac,
    fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun x y (hxy : x = y) ↦ by subst hxy; exact IsReflexive.self_le_zero _⟩
  rwa [Measure.bind_dirac, Measure.bind_dirac, mul_one, add_zero] at this

/-- Composability: the divergence is at most the codensity lifting of equality. -/
theorem codensity_diag_of_le [Δ.IsComposable] {X : Type u} [MeasurableSpace X] {α : ι}
    {δ : EReal} {μ ν : Measure X} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : Δ α μ ν ≤ δ) : Δ.Codensity α δ (diagRel X) μ ν where
  fst := inferInstance
  snd := inferInstance
  le I _ β γ k l hkl := by
    have := hkl.subProb_left
    have := hkl.subProb_right
    calc Δ (α * β) (μ.bind k) (ν.bind l)
        ≤ Δ α μ ν + ⨆ x, Δ β (k x) (l x) :=
          IsComposable.bind_le α β μ ν hkl.measurable_left hkl.measurable_right
      _ ≤ δ + γ := add_le_add h (iSup_le fun x ↦ hkl.le (show x = x from rfl))

/-- With reflexivity and composability, the codensity lifting of equality is exactly the
divergence bound (the fundamental property, Thm. 8.2). -/
theorem codensity_diag_iff [Δ.IsReflexive] [Δ.IsComposable] {X : Type u} [MeasurableSpace X]
    {α : ι} {δ : EReal} {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : Δ.Codensity α δ (diagRel X) μ ν ↔ Δ α μ ν ≤ δ :=
  ⟨Codensity.le_of_diag, codensity_diag_of_le⟩

/-! ### Fixing the test space (Def. 11, Prop. 14) -/

/-- `Δ` is generated over `Ω`: it is the supremum of its pushforwards along kernels into `Ω`
(Def. 11). -/
def IsGenerated (Ω : Type u) [MeasurableSpace Ω] : Prop :=
  ∀ (α : ι) {I : Type u} [MeasurableSpace I] (μ ν : Measure I), IsSubProbabilityMeasure μ →
    IsSubProbabilityMeasure ν → Δ α μ ν = ⨆ (k : I → Measure Ω) (_ : Measurable k)
      (_ : ∀ i, IsSubProbabilityMeasure (k i)), Δ α (μ.bind k) (ν.bind k)

/-- For a divergence generated over `Ω`, tests into `Ω` suffice (Prop. 14). -/
theorem codensity_iff_of_isGenerated {Ω : Type u} [MeasurableSpace Ω] (hΩ : Δ.IsGenerated Ω)
    {α : ι} {δ : EReal} {R : Set (X × Y)} {μ : Measure X} {ν : Measure Y}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    Δ.Codensity α δ R μ ν ↔ ∀ ⦃β : ι⦄ ⦃γ : EReal⦄ ⦃k : X → Measure Ω⦄ ⦃l : Y → Measure Ω⦄,
      IsTest Δ R β γ k l → Δ (α * β) (μ.bind k) (ν.bind l) ≤ δ + γ := by
  refine ⟨fun h _ _ _ _ hkl ↦ h.le hkl, fun h ↦ ⟨inferInstance, inferInstance, ?_⟩⟩
  intro I _ β γ k l hkl
  have := hkl.subProb_left
  have := hkl.subProb_right
  have hk := hkl.measurable_left
  have hl := hkl.measurable_right
  rw [hΩ _ _ _ (isSubProbabilityMeasure_bind (fun _ ↦ inferInstance) hk.aemeasurable)
    (isSubProbabilityMeasure_bind (fun _ ↦ inferInstance) hl.aemeasurable)]
  refine iSup_le fun j ↦ iSup_le fun hj ↦ iSup_le fun hj1 ↦ ?_
  rw [bind_bind hk.aemeasurable hj.aemeasurable, bind_bind hl.aemeasurable hj.aemeasurable]
  refine h ⟨by fun_prop, by fun_prop, fun x ↦ isSubProbabilityMeasure_bind hj1 hj.aemeasurable,
    fun y ↦ isSubProbabilityMeasure_bind hj1 hj.aemeasurable, fun x y hxy ↦ ?_⟩
  refine le_trans ?_ (hkl.le hxy)
  rw [hΩ β (k x) (l y) inferInstance inferInstance]
  exact le_iSup_of_le j <| le_iSup_of_le hj <| le_iSup_of_le hj1 le_rfl

end GradedDivergence

/-! ### Span liftings sit inside codensity liftings -/

namespace Span

open GradedDivergence

variable {ι : Type v} [Monoid ι] {Δ : GradedDivergence.{u} ι} [Δ.IsComposable]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {Φ : Type u} [MeasurableSpace Φ]

/-- Measures related by a span lifting pass every test of the span's relation: forgetting the
witnesses lands in the codensity lifting. -/
theorem Rel.codensity {s : Span X Y Φ} {α : ι} {δ : EReal} {μ : Measure X} {ν : Measure Y}
    (h : (s♯[Δ, α, δ]).Rel μ ν) : Δ.Codensity α δ {p | s.Rel p.1 p.2} μ ν := by
  obtain ⟨w, rfl, rfl⟩ := h
  refine ⟨(inferInstance : IsSubProbabilityMeasure (w.fst.map s.left)),
    (inferInstance : IsSubProbabilityMeasure (w.snd.map s.right)), fun I _ β γ k l hkl ↦ ?_⟩
  have := hkl.subProb_left
  have := hkl.subProb_right
  have hk := hkl.measurable_left
  have hl := hkl.measurable_right
  calc Δ (α * β) ((w.fst.map s.left).bind k) ((w.snd.map s.right).bind l)
      = Δ (α * β) (w.fst.bind fun φ ↦ k (s.left φ)) (w.snd.bind fun φ ↦ l (s.right φ)) :=
        congrArg₂ (fun a b ↦ Δ (α * β) a b) (bind_map_eq _) (bind_map_eq _)
    _ ≤ Δ α w.fst w.snd + ⨆ φ, Δ β (k (s.left φ)) (l (s.right φ)) :=
        IsComposable.bind_le α β _ _ (by fun_prop) (by fun_prop)
    _ ≤ δ + γ := add_le_add w.le (iSup_le fun φ ↦ hkl.le ⟨φ, rfl, rfl⟩)

end Span
