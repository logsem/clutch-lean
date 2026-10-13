module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! The category `Span(Meas)` (Approximate Span Liftings, Def. 3.2). -/

@[expose] public section

/-- A span `α ← Φ → β` of measurable maps. -/
structure Span (α β Φ : Type _) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Φ] where
  left : Φ → α
  right : Φ → β
  leftMeasurable : Measurable left
  rightMeasurable : Measurable right

namespace Span

variable {α α' α'' β β' β'' Φ Φ' Φ'' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Φ]
variable [MeasurableSpace α'] [MeasurableSpace β'] [MeasurableSpace Φ']
variable [MeasurableSpace α''] [MeasurableSpace β''] [MeasurableSpace Φ'']
variable {γ δ Ψ : Type _} [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSpace Ψ]

/-- A morphism of spans `(h, k, l)`: `h ∘ ρ₁ = ρ₁' ∘ l` and `k ∘ ρ₂ = ρ₂' ∘ l`. -/
@[ext]
structure Hom (s₁ : Span α β Φ) (s₂ : Span α' β' Φ') where
  leftMap : α → α'
  rightMap : β → β'
  witnessMap : Φ → Φ'
  leftMeasurable : Measurable leftMap
  rightMeasurable : Measurable rightMap
  witnessMeasurable : Measurable witnessMap
  comm_left φ : leftMap (s₁.left φ) = s₂.left (witnessMap φ)
  comm_right φ : rightMap (s₁.right φ) = s₂.right (witnessMap φ)

@[inherit_doc] scoped infixr:25 " →ₛ " => Hom

/-- Two points are related by a span when some witness projects onto them. -/
def Rel (s : Span α β Φ) (a : α) (b : β) : Prop :=
  ∃ φ, s.left φ = a ∧ s.right φ = b

/-- The diagonal span `α ← α → α`, isomorphic to the equality relation. -/
def diag (α : Type _) [MeasurableSpace α] : Span α α α where
  left := id
  right := id
  leftMeasurable := measurable_id
  rightMeasurable := measurable_id

/-- A relation `R ⊆ α × β`, viewed as the span `α ← R → β` of projections. -/
def ofRel (R : Set (α × β)) : Span α β R where
  left p := p.1.1
  right p := p.1.2
  leftMeasurable := measurable_fst.comp measurable_subtype_coe
  rightMeasurable := measurable_snd.comp measurable_subtype_coe

/-- The full relation `⊤ = α × β`. -/
abbrev top (α β : Type _) [MeasurableSpace α] [MeasurableSpace β] :
    Span α β (Set.univ : Set (α × β)) :=
  ofRel Set.univ

@[simp] theorem rel_diag {a b : α} : (diag α).Rel a b ↔ a = b :=
  ⟨fun ⟨_, ha, hb⟩ ↦ ha ▸ hb, fun h ↦ ⟨a, rfl, h⟩⟩

@[simp] theorem rel_ofRel {R : Set (α × β)} {a : α} {b : β} : (ofRel R).Rel a b ↔ (a, b) ∈ R :=
  ⟨fun ⟨p, ha, hb⟩ ↦ ha ▸ hb ▸ p.2, fun h ↦ ⟨⟨_, h⟩, rfl, rfl⟩⟩

/-- Binary products in `Span(Meas)` are computed componentwise. -/
def prod (s₁ : Span α β Φ) (s₂ : Span α' β' Φ') : Span (α × α') (β × β') (Φ × Φ') where
  left := Prod.map s₁.left s₂.left
  right := Prod.map s₁.right s₂.right
  leftMeasurable := s₁.leftMeasurable.prodMap s₂.leftMeasurable
  rightMeasurable := s₁.rightMeasurable.prodMap s₂.rightMeasurable

@[inherit_doc] scoped infixr:35 " ×̇ " => prod

/-- Binary coproducts in `Span(Meas)` are computed componentwise. -/
def sum (s₁ : Span α β Φ) (s₂ : Span α' β' Φ') : Span (α ⊕ α') (β ⊕ β') (Φ ⊕ Φ') where
  left := Sum.map s₁.left s₂.left
  right := Sum.map s₁.right s₂.right
  leftMeasurable := s₁.leftMeasurable.sumMap s₂.leftMeasurable
  rightMeasurable := s₁.rightMeasurable.sumMap s₂.rightMeasurable

@[inherit_doc] scoped infixr:30 " +̇ " => sum

@[simp] theorem rel_prod {s₁ : Span α β Φ} {s₂ : Span α' β' Φ'} {a : α × α'} {b : β × β'} :
    (s₁ ×̇ s₂).Rel a b ↔ s₁.Rel a.1 b.1 ∧ s₂.Rel a.2 b.2 := by
  constructor
  · rintro ⟨⟨φ, φ'⟩, rfl, rfl⟩
    exact ⟨⟨φ, rfl, rfl⟩, ⟨φ', rfl, rfl⟩⟩
  · rintro ⟨⟨φ, ha, hb⟩, ⟨φ', ha', hb'⟩⟩
    exact ⟨(φ, φ'), Prod.ext ha ha', Prod.ext hb hb'⟩

@[simp] theorem rel_sum_inl_inl {s₁ : Span α β Φ} {s₂ : Span α' β' Φ'} {a : α} {b : β} :
    (s₁ +̇ s₂).Rel (.inl a) (.inl b) ↔ s₁.Rel a b := by
  constructor
  · rintro ⟨φ | φ, ha, hb⟩
    · exact ⟨φ, Sum.inl_injective ha, Sum.inl_injective hb⟩
    · cases ha
  · rintro ⟨φ, rfl, rfl⟩
    exact ⟨.inl φ, rfl, rfl⟩

@[simp] theorem rel_sum_inr_inr {s₁ : Span α β Φ} {s₂ : Span α' β' Φ'} {a : α'} {b : β'} :
    (s₁ +̇ s₂).Rel (.inr a) (.inr b) ↔ s₂.Rel a b := by
  constructor
  · rintro ⟨φ | φ, ha, hb⟩
    · cases ha
    · exact ⟨φ, Sum.inr_injective ha, Sum.inr_injective hb⟩
  · rintro ⟨φ, rfl, rfl⟩
    exact ⟨.inr φ, rfl, rfl⟩

@[simp] theorem rel_sum_inl_inr {s₁ : Span α β Φ} {s₂ : Span α' β' Φ'} {a : α} {b : β'} :
    ¬(s₁ +̇ s₂).Rel (.inl a) (.inr b) := by
  rintro ⟨φ | φ, ⟨⟩, ⟨⟩⟩

@[simp] theorem rel_sum_inr_inl {s₁ : Span α β Φ} {s₂ : Span α' β' Φ'} {a : α'} {b : β} :
    ¬(s₁ +̇ s₂).Rel (.inr a) (.inl b) := by
  rintro ⟨φ | φ, ⟨⟩, ⟨⟩⟩

namespace Hom

variable {s : Span α β Φ} {t : Span α' β' Φ'} {u : Span α'' β'' Φ''}

/-- The identity morphism. -/
@[simps]
def id (s : Span α β Φ) : s →ₛ s where
  leftMap := _root_.id
  rightMap := _root_.id
  witnessMap := _root_.id
  leftMeasurable := measurable_id
  rightMeasurable := measurable_id
  witnessMeasurable := measurable_id
  comm_left _ := rfl
  comm_right _ := rfl

/-- Composition of morphisms, in the same order as function composition. -/
@[simps]
def comp (n : t →ₛ u) (m : s →ₛ t) : s →ₛ u where
  leftMap := n.leftMap ∘ m.leftMap
  rightMap := n.rightMap ∘ m.rightMap
  witnessMap := n.witnessMap ∘ m.witnessMap
  leftMeasurable := n.leftMeasurable.comp m.leftMeasurable
  rightMeasurable := n.rightMeasurable.comp m.rightMeasurable
  witnessMeasurable := n.witnessMeasurable.comp m.witnessMeasurable
  comm_left φ := by simp [m.comm_left, n.comm_left]
  comm_right φ := by simp [m.comm_right, n.comm_right]

/-- Span morphisms preserve the related pairs. -/
theorem rel (m : s →ₛ t) {a : α} {b : β} (h : s.Rel a b) : t.Rel (m.leftMap a) (m.rightMap b) := by
  obtain ⟨φ, rfl, rfl⟩ := h
  exact ⟨m.witnessMap φ, (m.comm_left φ).symm, (m.comm_right φ).symm⟩

/-- A relation-preserving pair of measurable maps `(f, g) : R → S` gives the span morphism
`(f, g, f × g|_R)`. -/
def ofRel {R : Set (α × β)} {S : Set (α' × β')} {f : α → α'} {g : β → β'}
    (hf : Measurable f) (hg : Measurable g) (h : ∀ p ∈ R, (f p.1, g p.2) ∈ S) :
    Span.ofRel R →ₛ Span.ofRel S where
  leftMap := f
  rightMap := g
  witnessMap p := ⟨(f p.1.1, g p.1.2), h p.1 p.2⟩
  leftMeasurable := hf
  rightMeasurable := hg
  witnessMeasurable :=
    ((hf.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
      (hg.comp (measurable_snd.comp measurable_subtype_coe))).subtype_mk
  comm_left _ := rfl
  comm_right _ := rfl

/-- An inclusion of relations `R ⊆ S`; this is how the paper reads implications `Φ ⇒ Ψ`. -/
def ofSubset {R S : Set (α × β)} (h : R ⊆ S) : Span.ofRel R →ₛ Span.ofRel S :=
  ofRel measurable_id measurable_id fun _ hp ↦ h hp

/-- `diag α` includes into the equality relation. -/
def diagToEq : diag α →ₛ Span.ofRel {p : α × α | p.1 = p.2} where
  leftMap := _root_.id
  rightMap := _root_.id
  witnessMap a := ⟨(a, a), rfl⟩
  leftMeasurable := measurable_id
  rightMeasurable := measurable_id
  witnessMeasurable := (measurable_id.prodMk measurable_id).subtype_mk
  comm_left _ := rfl
  comm_right _ := rfl

/-- The equality relation includes into `diag α`. -/
def eqToDiag : Span.ofRel {p : α × α | p.1 = p.2} →ₛ diag α where
  leftMap := _root_.id
  rightMap := _root_.id
  witnessMap p := p.1.1
  leftMeasurable := measurable_id
  rightMeasurable := measurable_id
  witnessMeasurable := measurable_fst.comp measurable_subtype_coe
  comm_left _ := rfl
  comm_right p := p.2.symm

/-- The product of two morphisms. -/
def prod {s' : Span γ δ Ψ} {t' : Span α'' β'' Φ''} (m : s →ₛ t) (m' : s' →ₛ t') :
    s ×̇ s' →ₛ t ×̇ t' where
  leftMap := Prod.map m.leftMap m'.leftMap
  rightMap := Prod.map m.rightMap m'.rightMap
  witnessMap := Prod.map m.witnessMap m'.witnessMap
  leftMeasurable := m.leftMeasurable.prodMap m'.leftMeasurable
  rightMeasurable := m.rightMeasurable.prodMap m'.rightMeasurable
  witnessMeasurable := m.witnessMeasurable.prodMap m'.witnessMeasurable
  comm_left φ := Prod.ext (m.comm_left φ.1) (m'.comm_left φ.2)
  comm_right φ := Prod.ext (m.comm_right φ.1) (m'.comm_right φ.2)

/-- The first projection out of a product. -/
def fst (s : Span α β Φ) (t : Span α' β' Φ') : s ×̇ t →ₛ s where
  leftMap := Prod.fst
  rightMap := Prod.fst
  witnessMap := Prod.fst
  leftMeasurable := measurable_fst
  rightMeasurable := measurable_fst
  witnessMeasurable := measurable_fst
  comm_left _ := rfl
  comm_right _ := rfl

/-- The second projection out of a product. -/
def snd (s : Span α β Φ) (t : Span α' β' Φ') : s ×̇ t →ₛ t where
  leftMap := Prod.snd
  rightMap := Prod.snd
  witnessMap := Prod.snd
  leftMeasurable := measurable_snd
  rightMeasurable := measurable_snd
  witnessMeasurable := measurable_snd
  comm_left _ := rfl
  comm_right _ := rfl

/-- Pairing into a product. -/
def prodMk (m : u →ₛ s) (m' : u →ₛ t) : u →ₛ s ×̇ t where
  leftMap a := (m.leftMap a, m'.leftMap a)
  rightMap b := (m.rightMap b, m'.rightMap b)
  witnessMap φ := (m.witnessMap φ, m'.witnessMap φ)
  leftMeasurable := m.leftMeasurable.prodMk m'.leftMeasurable
  rightMeasurable := m.rightMeasurable.prodMk m'.rightMeasurable
  witnessMeasurable := m.witnessMeasurable.prodMk m'.witnessMeasurable
  comm_left φ := Prod.ext (m.comm_left φ) (m'.comm_left φ)
  comm_right φ := Prod.ext (m.comm_right φ) (m'.comm_right φ)

/-- The left injection into a coproduct. -/
def inl (s : Span α β Φ) (t : Span α' β' Φ') : s →ₛ s +̇ t where
  leftMap := Sum.inl
  rightMap := Sum.inl
  witnessMap := Sum.inl
  leftMeasurable := measurable_inl
  rightMeasurable := measurable_inl
  witnessMeasurable := measurable_inl
  comm_left _ := rfl
  comm_right _ := rfl

/-- The right injection into a coproduct. -/
def inr (s : Span α β Φ) (t : Span α' β' Φ') : t →ₛ s +̇ t where
  leftMap := Sum.inr
  rightMap := Sum.inr
  witnessMap := Sum.inr
  leftMeasurable := measurable_inr
  rightMeasurable := measurable_inr
  witnessMeasurable := measurable_inr
  comm_left _ := rfl
  comm_right _ := rfl

/-- Copairing out of a coproduct of spans. -/
def sumElim {s' : Span α'' β'' Φ''} (m : s →ₛ t) (m' : s' →ₛ t) : s +̇ s' →ₛ t where
  leftMap := Sum.elim m.leftMap m'.leftMap
  rightMap := Sum.elim m.rightMap m'.rightMap
  witnessMap := Sum.elim m.witnessMap m'.witnessMap
  leftMeasurable := m.leftMeasurable.sumElim m'.leftMeasurable
  rightMeasurable := m.rightMeasurable.sumElim m'.rightMeasurable
  witnessMeasurable := m.witnessMeasurable.sumElim m'.witnessMeasurable
  comm_left
    | .inl φ => m.comm_left φ
    | .inr φ => m'.comm_left φ
  comm_right
    | .inl φ => m.comm_right φ
    | .inr φ => m'.comm_right φ

end Hom

end Span
