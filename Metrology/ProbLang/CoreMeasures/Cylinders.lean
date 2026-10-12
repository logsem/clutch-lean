module

public import Metrology.ProbLang.Measure

@[expose] public section

noncomputable section ProbLangMeasures
open Classical MeasureTheory ProbabilityTheory Measure

/-! # Shared cylinder lemmas

Generic lemmas behind `cylinder_defs` (`CylinderGen.lean`), over the cylinder type `Cyl`, the
underlying type `T` and the shape type `Shp`. The sections follow the order of the generated code.
-/

/-- The generated `flatten`, `shape`, `Cylinder.shape`, `Shape.cylinder` and `cover.*` equations. -/
register_simp_attr cylinder_simp

namespace Cylinders

variable {Cyl T Shp : Type _}
  {flatten : Cyl → Set T} {shape : T → Shp} {cShape : Cyl → Shp}

/-! ### Measurable cylinders (for `flatten_measurable`) -/

theorem flatten_measurable {HML : Cyl → Prop} [m : MeasurableSpace T]
    (hgen : m = .generateFrom (flatten '' {c : Cyl | HML c}))
    {c : Cyl} (hc : HML c) : MeasurableSet (flatten c) := by
  subst hgen
  exact MeasurableSpace.measurableSet_generateFrom ⟨c, hc, rfl⟩

/-! ### Shapes (for `Cylinder.flatten_disjoint_of_shape_ne` and `Shape.cylinder_preimage_shape`) -/

theorem flatten_disjoint_of_shape_ne
    (shape_of_mem : ∀ {c : Cyl} {p : T}, p ∈ flatten c → shape p = cShape c)
    {c₁ c₂ : Cyl} (h : cShape c₁ ≠ cShape c₂) :
    flatten c₁ ∩ flatten c₂ = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨hp₁, hp₂⟩ =>
    h ((shape_of_mem hp₁).symm.trans (shape_of_mem hp₂))

/-- `mem_self` is proved per type by induction on `p` alone, which keeps the proof linear in the
number of constructors (no casing on `s`). -/
theorem cylinder_preimage_shape {sCyl : Shp → Cyl}
    (shape_of_mem : ∀ {c : Cyl} {p : T}, p ∈ flatten c → shape p = cShape c)
    (cShape_sCyl : ∀ s : Shp, cShape (sCyl s) = s)
    (mem_self : ∀ p : T, p ∈ flatten (sCyl (shape p)))
    (s : Shp) : flatten (sCyl s) = shape ⁻¹' {s} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hp; rw [shape_of_mem hp, cShape_sCyl]
  · rintro rfl; exact mem_self p

/-! ### The generating family (for `Cylinder.flatten_inter_some`, `Cylinder.flatten_isPiSystem`
and `Cylinder.flatten_isCountablySpanning`) -/

theorem flatten_inter_some {inter? : Cyl → Cyl → Option Cyl}
    (flatten_inter : ∀ c₁ c₂ : Cyl,
      flatten c₁ ∩ flatten c₂ = (inter? c₁ c₂).elim ∅ flatten)
    {c₁ c₂ c : Cyl} (h : inter? c₁ c₂ = some c) :
    flatten c = flatten c₁ ∩ flatten c₂ := by
  rw [flatten_inter, h]; rfl

theorem flatten_isPiSystem {inter? : Cyl → Cyl → Option Cyl} {HML : Cyl → Prop}
    (flatten_inter : ∀ c₁ c₂ : Cyl,
      flatten c₁ ∩ flatten c₂ = (inter? c₁ c₂).elim ∅ flatten)
    (hML_inter : ∀ {c₁ c₂ c : Cyl}, HML c₁ → HML c₂ → inter? c₁ c₂ = some c → HML c) :
    IsPiSystem ({S : Set T | ∃ c : Cyl, HML c ∧ flatten c = S}) := by
  rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hne
  obtain ⟨c, hc⟩ : ∃ c, inter? c₁ c₂ = some c := Option.ne_none_iff_exists'.mp fun h =>
    hne.ne_empty (by rw [flatten_inter, h]; rfl)
  exact ⟨c, hML_inter hc₁ hc₂ hc, flatten_inter_some flatten_inter hc⟩

/-- `fallback` is any cylinder with measurable leaves (e.g. a nullary one). -/
theorem flatten_isCountablySpanning [Countable Shp] {HML : Cyl → Prop} {sCyl : Shp → Cyl}
    (hML_cyl : ∀ s : Shp, HML (sCyl s))
    (preimage_shape : ∀ s : Shp, flatten (sCyl s) = shape ⁻¹' {s})
    (fallback : Cyl) (hML_fallback : HML fallback) :
    IsCountablySpanning ({S : Set T | ∃ c : Cyl, HML c ∧ flatten c = S}) := by
  obtain ⟨enc⟩ := nonempty_encodable Shp
  refine ⟨fun n =>
    match enc.decode n with
    | some s => flatten (sCyl s)
    | none => flatten fallback, ?_, ?_⟩
  · intro n
    cases h : enc.decode n with
    | none => exact ⟨fallback, hML_fallback, by simp [h]⟩
    | some s => exact ⟨sCyl s, hML_cyl s, by simp [h]⟩
  · ext p
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨enc.encode (shape p), ?_⟩
    rw [enc.encodek]
    simp [preimage_shape]

/-! ### Base fields (for `c.measurableEmbedding`)

The generating family of a countable type with measurable singletons. A rectangle with a singleton
at each base field is the image of one cylinder; with `∅`, it is empty. -/

def points (X : Type _) : Set (Set X) := insert ∅ (Set.range ({·}))

theorem points_isPiSystem {X : Type _} : IsPiSystem (points X) := by
  rintro _ (rfl | ⟨x, rfl⟩) _ (rfl | ⟨y, rfl⟩) ⟨z, hz⟩
  all_goals try simp at hz
  obtain ⟨rfl, rfl⟩ : z = x ∧ z = y := by simpa using hz
  exact .inr ⟨z, by simp⟩

theorem points_isCountablySpanning {X : Type _} [Countable X] : IsCountablySpanning (points X) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨fun _ => ∅, fun _ => .inl rfl, Set.eq_univ_of_forall fun x => isEmptyElim x⟩
  · obtain ⟨f, hf⟩ := exists_surjective_nat X
    exact ⟨fun n => {f n}, fun n => .inr ⟨f n, rfl⟩,
      Set.eq_univ_of_forall fun x => by obtain ⟨n, rfl⟩ := hf x; exact Set.mem_iUnion.2 ⟨n, rfl⟩⟩

theorem points_generateFrom {X : Type _} [Countable X] [MeasurableSpace X]
    [MeasurableSingletonClass X] : MeasurableSpace.generateFrom (points X) = ‹MeasurableSpace X› := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) fun s _ => ?_
  · rintro _ (rfl | ⟨x, rfl⟩)
    exacts [.empty, .singleton x]
  · rw [← Set.biUnion_of_singleton s]
    exact .biUnion s.to_countable fun x _ => MeasurableSpace.measurableSet_generateFrom (.inr ⟨x, rfl⟩)

/-! ### Constructors (for `c.ι.measurable` and `c.π.measurable`) -/

theorem measurableSet_of_forall_notMem {X : Type _} [MeasurableSpace X] {s : Set X}
    (h : ∀ x, x ∉ s) : MeasurableSet s := by
  rw [Set.eq_empty_of_forall_notMem h]; exact .empty

/-- The projection `π` of a constructor with uncurried form `g` is its partial inverse. -/
theorem proj_measurable {A : Type _} [MeasurableSpace A] [MeasurableSpace T]
    {π : T → Option A} {g : A → T}
    (hemb : MeasurableEmbedding g)
    (h_none : π ⁻¹' ({none} : Set (Option A)) = (Set.range g)ᶜ)
    (h_some : ∀ S : Set A, π ⁻¹' (some '' S) = g '' S) :
    Measurable π :=
  Measurable.option_of_cov hemb.measurableSet_range h_none
    (fun S hS => by rw [h_some S]; exact hemb.measurableSet_image' hS)

/-! ### Singletons (for `instMeasurableSingletonClass`) -/

theorem measurableSet_singleton {HML : Cyl → Prop} [m : MeasurableSpace T]
    (hgen : m = .generateFrom (flatten '' {c : Cyl | HML c}))
    {sCylP : T → Cyl}
    (sCylP_flatten : ∀ p : T, flatten (sCylP p) = {p})
    (sCylP_hML : ∀ p : T, HML (sCylP p))
    (p : T) : MeasurableSet ({p} : Set T) := by
  rw [← sCylP_flatten p]
  subst hgen
  exact MeasurableSpace.measurableSet_generateFrom ⟨sCylP p, sCylP_hML p, rfl⟩

/-! ### Structural recursion (for `measurable_struct_rec*`)

`StructRec.measurable_of_cells` reduces measurability of a structurally recursive function to its
cells `{p | shape p = s ∧ f p ∈ U}`. On the cell of a constructor `ι : A → T`, `f ∘ ι` is some
`G : A → α`; the cell is measurable when `G` is measurable on the cell's preimage. -/

theorem restrict_of_cell {T α : Type _} [MeasurableSpace T] [MeasurableSpace α] {f : T → α}
    {C : Set T} (h : ∀ {U : Set α}, MeasurableSet U → MeasurableSet {p | p ∈ C ∧ f p ∈ U}) :
    Measurable (C.domRestrict f) := fun U hU => by
  convert measurable_subtype_coe (h hU) using 1
  ext ⟨p, hp⟩
  simp

theorem restrict_comp {X T α : Type _} [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace α]
    {f : T → α} {C' : Set T} (hf : Measurable (C'.domRestrict f)) {g : X → T} (hg : Measurable g)
    {C : Set X} (hmap : ∀ x ∈ C, g x ∈ C') : Measurable (C.domRestrict (f ∘ g)) :=
  hf.comp (hg.subtype_map hmap)

theorem cell {T A α Sh : Type _} [MeasurableSpace T] [MeasurableSpace A] [MeasurableSpace α]
    {shape : T → Sh} {s : Sh} {ι : A → T} (hι : MeasurableEmbedding ι)
    (hC : MeasurableSet (shape ⁻¹' {s})) (hcov : ∀ p, shape p = s → p ∈ Set.range ι)
    {f : T → α} {G : A → α} (hfG : ∀ a, shape (ι a) = s → f (ι a) = G a)
    (hG : Measurable ((ι ⁻¹' (shape ⁻¹' {s})).domRestrict G)) {U : Set α} (hU : MeasurableSet U) :
    MeasurableSet {p | shape p = s ∧ f p ∈ U} := by
  convert hι.measurableSet_image' ((hι.measurable hC).subtype_image (hG hU)) using 1
  ext p
  constructor
  · rintro ⟨hp, hfp⟩
    obtain ⟨a, rfl⟩ := hcov p hp
    exact ⟨a, ⟨⟨a, hp⟩, show G a ∈ U from hfG a hp ▸ hfp, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨⟨a, ha⟩, hGa, rfl⟩, rfl⟩
    exact ⟨ha, show f (ι a) ∈ U from (hfG a ha).symm ▸ hGa⟩

theorem cell_param {T A α β Sh : Type _} [MeasurableSpace T] [MeasurableSpace A]
    [MeasurableSpace α] [MeasurableSpace β]
    {shape : T → Sh} {s : Sh} {ι : A → T} (hι : MeasurableEmbedding ι)
    (hC : MeasurableSet (shape ⁻¹' {s})) (hcov : ∀ p, shape p = s → p ∈ Set.range ι)
    {g : β → T → α} {G : β × A → α} (hfG : ∀ b a, shape (ι a) = s → g b (ι a) = G (b, a))
    (hG : Measurable ({q : β × A | shape (ι q.2) = s}.domRestrict G)) {U : Set α}
    (hU : MeasurableSet U) :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  have hι' : MeasurableEmbedding (Prod.map id ι : β × A → β × T) :=
    MeasurableEmbedding.id.prodMap hι
  have hD : MeasurableSet {q : β × A | shape (ι q.2) = s} :=
    (hι.measurable.comp measurable_snd) hC
  convert hι'.measurableSet_image' (hD.subtype_image (hG hU)) using 1
  ext ⟨b, p⟩
  constructor
  · rintro ⟨hp, hgp⟩
    obtain ⟨a, rfl⟩ := hcov p hp
    exact ⟨(b, a), ⟨⟨(b, a), hp⟩, show G (b, a) ∈ U from hfG b a hp ▸ hgp, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨⟨⟨b, a⟩, ha⟩, hGa, rfl⟩, h⟩
    simp only [Prod.map, id, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ha, show g b (ι a) ∈ U from (hfG b a ha).symm ▸ hGa⟩

end Cylinders

end ProbLangMeasures
