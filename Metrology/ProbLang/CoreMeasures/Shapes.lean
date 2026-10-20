module

public import Metrology.ProbLang.Measure

@[expose] public section

/-!
# Types as sums over shapes

A value of an inductive type `T` is a *shape* (constructors and countable fields) with *leaves*
(other fields), so `T ≃ Σ s, V s`. For a recursive type the shape is the whole constructor tree
(`T.Shape` has a recursive field wherever `T` does) and the leaves are the data fields of every
node. Deriving `MeasurableSpace` uses this file to show constructors are measurable embeddings,
maps out of `T` are measurable shape by shape, and singletons measurable.
-/

open MeasureTheory Set

namespace Metrology.Shapes

universe u w

variable {α β A B : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace A]
  [MeasurableSpace B]
variable {I J : Type*} {X : I → Type*} {Y : J → Type*} [∀ i, MeasurableSpace (X i)]
  [∀ j, MeasurableSpace (Y j)]

/-! ## Maps into and out of sigma types -/

theorem measurable_mk (i : I) : Measurable (Sigma.mk i : X i → Σ i, X i) :=
  (MeasurableEmbedding.sigmaMk i).measurable

/-- A map out of `A × Σ j, Y j` is measurable if it is on every fiber. -/
theorem measurable_prod_sigma [Countable J] {f : A × (Σ j, Y j) → α}
    (h : ∀ j, Measurable fun p : A × Y j => f (p.1, ⟨j, p.2⟩)) : Measurable f := by
  intro U hU
  have : f ⁻¹' U =
      ⋃ j, Prod.map id (Sigma.mk j) '' ((fun p : A × Y j => f (p.1, ⟨j, p.2⟩)) ⁻¹' U) := by
    ext ⟨a, j, y⟩
    simp only [mem_preimage, mem_iUnion, mem_image, Prod.map, id, Prod.mk.injEq]
    refine ⟨fun h => ⟨j, (a, y), h, rfl, rfl⟩, ?_⟩
    rintro ⟨j', ⟨a', y'⟩, h, rfl, h'⟩
    cases h'
    exact h
  rw [this]
  exact .iUnion fun j =>
    (MeasurableEmbedding.id.prodMap (MeasurableEmbedding.sigmaMk j)).measurableSet_image' (h j hU)

/-- A map out of `(Σ i, X i) × B` is measurable if it is on every fiber. -/
theorem measurable_sigma_prod [Countable I] {f : (Σ i, X i) × B → α}
    (h : ∀ i, Measurable fun p : X i × B => f (⟨i, p.1⟩, p.2)) : Measurable f :=
  (measurable_prod_sigma (f := f ∘ Prod.swap) fun i => (h i).comp measurable_swap).comp
    measurable_swap

/-- `p ↦ ⟨f p.1, p.2⟩`, for an injective `f` on a countable type, is a measurable embedding. -/
theorem measurableEmbedding_sigmaMap {K : Type*} [Countable K] {f : K → J} (hf : f.Injective) :
    MeasurableEmbedding fun p : Σ k, Y (f k) => (⟨f p.1, p.2⟩ : Σ j, Y j) := by
  refine ⟨fun p q h => ?_, measurable_sigma_iff.2 fun k => measurable_mk (f k), fun S hS => ?_⟩
  · obtain ⟨k, y⟩ := p
    obtain ⟨k', y'⟩ := q
    obtain ⟨hk, hy⟩ := Sigma.mk.inj h
    obtain rfl := hf hk
    cases eq_of_heq hy
    rfl
  · have : (fun p : Σ k, Y (f k) => (⟨f p.1, p.2⟩ : Σ j, Y j)) '' S =
        ⋃ k, Sigma.mk (f k) '' (@Sigma.mk K (fun k => Y (f k)) k ⁻¹' S) := by
      ext ⟨j, y⟩
      simp only [mem_image, mem_iUnion, mem_preimage]
      constructor
      · rintro ⟨⟨k, y'⟩, h, he⟩
        exact ⟨k, y', h, he⟩
      · rintro ⟨k, y', h, he⟩
        exact ⟨⟨k, y'⟩, h, he⟩
    rw [this]
    exact .iUnion fun k => (MeasurableEmbedding.sigmaMk (f k)).measurableSet_image'
      ((measurable_mk k) hS)

/-! ## Splitting tuples of fields into a shape and leaves

A field is either *indexed* (its value is part of the shape: `A ≃ᵐ Σ i, X i`) or a *leaf*. A tuple
of fields is indexed by the tuple of its indices, with the tuple of its leaves on each fiber. -/

/-- A countable field: all of it is in the shape. -/
def point (A : Type u) [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A] :
    A ≃ᵐ Σ _ : A, PUnit.{w + 1} where
  toFun a := ⟨a, PUnit.unit⟩
  invFun p := p.1
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := measurable_sigma_iff.2 fun _ => measurable_const

/-- Any other field is a leaf, lifted to the universe of the leaves. -/
def leaf (A : Type u) [MeasurableSpace A] : A ≃ᵐ ULift.{w} A := MeasurableEquiv.ulift.symm

/-- No fields: a constructor without fields has no leaves. -/
def unit : Unit ≃ᵐ PUnit.{w + 1} where
  toFun _ := PUnit.unit
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_const
  measurable_invFun := measurable_const

/-- Regroups two indexed fields: the pair of indices, then the pair of leaves. -/
def sigmaProd [Countable I] [Countable J] :
    (Σ i, X i) × (Σ j, Y j) ≃ᵐ Σ p : I × J, X p.1 × Y p.2 where
  toFun p := ⟨(p.1.1, p.2.1), (p.1.2, p.2.2)⟩
  invFun q := (⟨q.1.1, q.2.1⟩, ⟨q.1.2, q.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_sigma_prod fun i => measurable_prod_sigma fun j =>
    measurable_mk ((i, j) : I × J)
  measurable_invFun := measurable_sigma_iff.2 fun p =>
    ((measurable_mk p.1).comp measurable_fst).prodMk ((measurable_mk p.2).comp measurable_snd)

/-- Regroups a leaf and an indexed field: the index, then the pair of leaves. -/
def prodSigma [Countable J] : A × (Σ j, Y j) ≃ᵐ Σ j, A × Y j where
  toFun p := ⟨p.2.1, (p.1, p.2.2)⟩
  invFun q := (q.2.1, ⟨q.1, q.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_prod_sigma fun j => measurable_mk j
  measurable_invFun := measurable_sigma_iff.2 fun j =>
    measurable_fst.prodMk ((measurable_mk j).comp measurable_snd)

/-- Regroups an indexed field and a leaf: the index, then the pair of leaves. -/
def sigmaProdLeaf [Countable I] : (Σ i, X i) × B ≃ᵐ Σ i, X i × B where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun q := (⟨q.1, q.2.1⟩, q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_sigma_prod fun i => measurable_mk i
  measurable_invFun := measurable_sigma_iff.2 fun i =>
    ((measurable_mk i).comp measurable_fst).prodMk measurable_snd

/-- Combines the splittings of two indexed fields, by `sigmaProd`. -/
def pair [Countable I] [Countable J] (e : A ≃ᵐ Σ i, X i) (e' : B ≃ᵐ Σ j, Y j) :
    A × B ≃ᵐ Σ p : I × J, X p.1 × Y p.2 :=
  (e.prodCongr e').trans sigmaProd

/-- Combines the splittings of a leaf and an indexed field, by `prodSigma`. -/
def leafPair [Countable J] {A' : Type*} [MeasurableSpace A'] (e : A ≃ᵐ A') (e' : B ≃ᵐ Σ j, Y j) :
    A × B ≃ᵐ Σ j, A' × Y j :=
  (e.prodCongr e').trans prodSigma

/-- Combines the splittings of an indexed field and a leaf, by `sigmaProdLeaf`. -/
def pairLeaf [Countable I] {B' : Type*} [MeasurableSpace B'] (e : A ≃ᵐ Σ i, X i) (e' : B ≃ᵐ B') :
    A × B ≃ᵐ Σ i, X i × B' :=
  (e.prodCongr e').trans sigmaProdLeaf

/-! ## The type as a sum over its shapes -/

section Sum

variable {S : Type*} {V : S → Type*} [∀ s, MeasurableSpace (V s)] {T : Type*}

/-- `T` with the σ-algebra pulled back along an equivalence `e` with `Σ s, V s`. -/
def measurableEquiv [m : MeasurableSpace T] (e : T ≃ Σ s, V s)
    (h : m = MeasurableSpace.comap e inferInstance) : T ≃ᵐ Σ s, V s where
  toEquiv := e
  measurable_toFun := h ▸ comap_measurable e
  measurable_invFun := by
    subst h
    rintro _ ⟨U, hU, rfl⟩
    rwa [show e.symm ⁻¹' (e ⁻¹' U) = U by ext; simp]

variable [MeasurableSpace T] (e : T ≃ᵐ Σ s, V s)

/-- A constructor `ι` is a measurable embedding if its fields split (`g`) into an index `k : K`
and leaves, with `e (ι a)` the leaves at shape `f k`. For the generator, `f` is the uncurried shape
constructor `T.Shape.c`, which is injective. -/
theorem measurableEmbedding {K : Type*} [Countable K] {f : K → S} (hf : f.Injective)
    (g : A ≃ᵐ Σ k, V (f k)) {ι : A → T} (h : ∀ a, e (ι a) = ⟨f (g a).1, (g a).2⟩) :
    MeasurableEmbedding ι := by
  have : ι = e.symm ∘ (fun p : Σ k, V (f k) => (⟨f p.1, p.2⟩ : Σ s, V s)) ∘ g := by
    funext a; simp [← h a]
  rw [this]
  exact e.symm.measurableEmbedding.comp
    ((measurableEmbedding_sigmaMap hf).comp g.measurableEmbedding)

/-- A constructor `ι` without indexed fields is a measurable embedding into its single shape. -/
theorem measurableEmbedding_leaves (s : S) (g : A ≃ᵐ V s) {ι : A → T}
    (h : ∀ a, e (ι a) = ⟨s, g a⟩) : MeasurableEmbedding ι := by
  have : ι = e.symm ∘ Sigma.mk s ∘ g := by funext a; simp [← h a]
  rw [this]
  exact e.symm.measurableEmbedding.comp ((MeasurableEmbedding.sigmaMk s).comp g.measurableEmbedding)

/-- A map out of `T` is measurable if it is on the values of every shape. -/
theorem measurable_of_fibers (f : T → α) (h : ∀ s, Measurable fun v => f (e.symm ⟨s, v⟩)) :
    Measurable f := by
  have : f = (fun p => f (e.symm p)) ∘ e := by funext; simp
  rw [this]
  exact (measurable_sigma_iff.2 h).comp e.measurable

/-- A map out of `β × T` is measurable if it is on the values of every shape. -/
theorem measurable_uncurry_of_fibers [Countable S] (g : β → T → α)
    (h : ∀ s, Measurable fun p : β × V s => g p.1 (e.symm ⟨s, p.2⟩)) :
    Measurable (Function.uncurry g) := by
  have : Function.uncurry g = (fun q : β × Σ s, V s => g q.1 (e.symm q.2)) ∘ Prod.map id e := by
    funext ⟨b, x⟩; simp
  rw [this]
  exact (measurable_prod_sigma h).comp (measurable_id.prodMap e.measurable)

/-- The values of shape `s`, as a function of their leaves. -/
theorem measurable_symm_mk (s : S) : Measurable fun v : V s => e.symm ⟨s, v⟩ :=
  e.symm.measurable.comp (measurable_mk s)

omit e in
/-- `T` has measurable singletons if the leaves of every shape do. -/
theorem measurableSingletonClass (e : T ≃ᵐ Σ s, V s) [∀ s, MeasurableSingletonClass (V s)] :
    MeasurableSingletonClass T where
  measurableSet_singleton x := by
    have : ({x} : Set T) = e ⁻¹' (Sigma.mk (e x).1 '' {(e x).2}) := by ext; simp
    rw [this]
    exact e.measurable ((MeasurableEmbedding.sigmaMk _).measurableSet_image'
      (measurableSet_singleton _))

end Sum

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- A constructor `ι` is injective: `π` inverts it. -/
theorem injective_of_proj (ι : A → B) (π : B → Option A) (h : ∀ a, π (ι a) = some a) :
    ι.Injective :=
  fun a b hab => Option.some.inj ((h a).symm.trans ((congrArg π hab).trans (h b)))

/-- Rewrites the function a measurability proof is about. -/
theorem measurable_of_eq (f g : α → β) (h : ∀ a, f a = g a) (hg : Measurable g) : Measurable f :=
  funext h ▸ hg

/-- `ULift` preserves measurable singletons. -/
instance {A : Type u} [MeasurableSpace A] [MeasurableSingletonClass A] :
    MeasurableSingletonClass (ULift.{w} A) where
  measurableSet_singleton x := by
    change MeasurableSet (ULift.up ⁻¹' {x})
    convert measurableSet_singleton x.down using 1
    ext; simp [ULift.ext_iff]

end Metrology.Shapes
