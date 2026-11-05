module

public import Metrology.ProbLang.Measure

@[expose] public section

/-!
# Types as sums over shapes

Writes an inductive type as a sum over its shapes, with leaves on each.
-/

open MeasureTheory Set
open MeasurableEmbedding (sigmaMk)
open Sigma (mk)
open Prod (map swap)
open Function (uncurry)
open ULift (up ext_iff)

namespace Metrology.Shapes

universe u w

/-- A constructor `ι` is injective if some `π` recovers `a` from `ι a`. -/
theorem injective_of_proj {A B : Type*} (ι : A → B) (π : B → Option A)
    (h : ∀ a, π (ι a) = some a) : ι.Injective :=
  fun a b hab => Option.some.inj ((h a).symm.trans ((congrArg π hab).trans (h b)))

variable {α β A B : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace A]
  [MeasurableSpace B]
variable {I J : Type*} {X : I → Type*} {Y : J → Type*} [∀ i, MeasurableSpace (X i)]
  [∀ j, MeasurableSpace (Y j)]

/-! ## Measurability of maps into and out of sigma types -/

/-- The inclusion of a fiber into a sigma type is measurable. -/
theorem measurable_mk (i : I) : Measurable (mk i : X i → Σ i, X i) :=
  (sigmaMk i).measurable

/-- `p ↦ ⟨f p.1, p.2⟩`, for an injective `f` on a countable type, is a measurable embedding. -/
theorem measurableEmbedding_sigmaMap {K : Type*} [Countable K] {f : K → J} (hf : f.Injective) :
    MeasurableEmbedding fun p : Σ k, Y (f k) => (⟨f p.1, p.2⟩ : Σ j, Y j) := by
  refine ⟨fun p q h => ?_, measurable_sigma_iff.2 fun k => measurable_mk (f k), fun S hS => ?_⟩
  · obtain ⟨k, y⟩ := p
    obtain ⟨k', y'⟩ := q
    obtain ⟨hk, hy⟩ := mk.inj h
    obtain rfl := hf hk
    cases eq_of_heq hy
    rfl
  · have : (fun p : Σ k, Y (f k) => (⟨f p.1, p.2⟩ : Σ j, Y j)) '' S =
        ⋃ k, mk (f k) '' (@mk K (fun k => Y (f k)) k ⁻¹' S) := by
      ext ⟨j, y⟩
      simp only [mem_image, mem_iUnion, mem_preimage]
      constructor
      · rintro ⟨⟨k, y'⟩, h, he⟩
        exact ⟨k, y', h, he⟩
      · rintro ⟨k, y', h, he⟩
        exact ⟨⟨k, y'⟩, h, he⟩
    rw [this]
    exact .iUnion fun k => (sigmaMk (f k)).measurableSet_image' ((measurable_mk k) hS)

/-! ## Splitting tuples of fields into a shape and leaves

A field is either *indexed* (its value is part of the shape: `A ≃ᵐ Σ i, X i`) or a *leaf*. A tuple
of fields is indexed by the tuple of its indices, with the tuple of its leaves on each fiber. -/

/-- A countable field: all of it is in the shape. -/
def point (A : Type u) [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A] :
    A ≃ᵐ Σ _ : A, PUnit.{w + 1} where
  toFun a := ⟨a, ⟨⟩⟩
  invFun p := p.1
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := measurable_sigma_iff.2 fun _ => measurable_const

/-- Any other field is a leaf, lifted to the universe of the leaves. -/
def leaf (A : Type u) [MeasurableSpace A] : A ≃ᵐ ULift.{w} A := MeasurableEquiv.ulift.symm

/-- No fields: a constructor without fields has no leaves. -/
def unit : Unit ≃ᵐ PUnit.{w + 1} where
  toFun _ := ⟨⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_const
  measurable_invFun := measurable_const

section Regroup

variable [Countable I] [Countable J]

/-! ### Maps out of a product with a sigma type -/

/-- A map out of `A × Σ j, Y j` is measurable if it is on every fiber. -/
theorem measurable_prod_sigma {f : A × (Σ j, Y j) → α}
    (h : ∀ j, Measurable fun p : A × Y j => f (p.1, ⟨j, p.2⟩)) : Measurable f := by
  intro U hU
  have : f ⁻¹' U = ⋃ j, map id (mk j) '' ((fun p : A × Y j => f (p.1, ⟨j, p.2⟩)) ⁻¹' U) := by
    ext ⟨a, j, y⟩
    simp only [mem_preimage, mem_iUnion, mem_image, map, id, Prod.mk.injEq]
    refine ⟨fun h => ⟨j, (a, y), h, rfl, rfl⟩, ?_⟩
    rintro ⟨j', ⟨a', y'⟩, h, rfl, h'⟩
    cases h'
    exact h
  rw [this]
  exact .iUnion fun j =>
    (MeasurableEmbedding.id.prodMap (sigmaMk j)).measurableSet_image' (h j hU)

/-- A map out of `(Σ i, X i) × B` is measurable if it is on every fiber. -/
theorem measurable_sigma_prod {f : (Σ i, X i) × B → α}
    (h : ∀ i, Measurable fun p : X i × B => f (⟨i, p.1⟩, p.2)) : Measurable f :=
  (measurable_prod_sigma (f := f ∘ swap) fun i => (h i).comp measurable_swap).comp measurable_swap

/-! ### Regrouping tuples of fields -/

/-- Regroups two indexed fields: the pair of indices, then the pair of leaves. -/
def sigmaProd : (Σ i, X i) × (Σ j, Y j) ≃ᵐ Σ p : I × J, X p.1 × Y p.2 where
  toFun p := ⟨(p.1.1, p.2.1), (p.1.2, p.2.2)⟩
  invFun q := (⟨q.1.1, q.2.1⟩, ⟨q.1.2, q.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_sigma_prod fun i => measurable_prod_sigma fun j =>
    measurable_mk ((i, j) : I × J)
  measurable_invFun := measurable_sigma_iff.2 fun p =>
    ((measurable_mk p.1).comp measurable_fst).prodMk ((measurable_mk p.2).comp measurable_snd)

/-- Regroups a leaf and an indexed field: the index, then the pair of leaves. -/
def prodSigma : A × (Σ j, Y j) ≃ᵐ Σ j, A × Y j where
  toFun p := ⟨p.2.1, (p.1, p.2.2)⟩
  invFun q := (q.2.1, ⟨q.1, q.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_prod_sigma fun j => measurable_mk j
  measurable_invFun := measurable_sigma_iff.2 fun j =>
    measurable_fst.prodMk ((measurable_mk j).comp measurable_snd)

/-- Regroups an indexed field and a leaf: the index, then the pair of leaves. -/
def sigmaProdLeaf : (Σ i, X i) × B ≃ᵐ Σ i, X i × B where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun q := (⟨q.1, q.2.1⟩, q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_sigma_prod fun i => measurable_mk i
  measurable_invFun := measurable_sigma_iff.2 fun i =>
    ((measurable_mk i).comp measurable_fst).prodMk measurable_snd

/-- Combines the splittings of two indexed fields, by `sigmaProd`. -/
def pair (e : A ≃ᵐ Σ i, X i) (e' : B ≃ᵐ Σ j, Y j) :
    A × B ≃ᵐ Σ p : I × J, X p.1 × Y p.2 :=
  (e.prodCongr e').trans sigmaProd

/-- Combines the splittings of a leaf and an indexed field, by `prodSigma`. -/
def leafPair {A' : Type*} [MeasurableSpace A'] (e : A ≃ᵐ A') (e' : B ≃ᵐ Σ j, Y j) :
    A × B ≃ᵐ Σ j, A' × Y j :=
  (e.prodCongr e').trans prodSigma

/-- Combines the splittings of an indexed field and a leaf, by `sigmaProdLeaf`. -/
def pairLeaf {B' : Type*} [MeasurableSpace B'] (e : A ≃ᵐ Σ i, X i) (e' : B ≃ᵐ B') :
    A × B ≃ᵐ Σ i, X i × B' :=
  (e.prodCongr e').trans sigmaProdLeaf

end Regroup

/-! ## The type as a sum over its shapes

For a recursive type the shape is the whole constructor tree (`T.Shape` has a recursive field
wherever `T` does) and the leaves are the data fields of every node. -/

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

variable [MeasurableSpace T]

/-! ### Measurable equality -/

/-- Products have measurable equality when both factors do. -/
instance instMeasurableEqProd [MeasurableEq A] [MeasurableEq B] : MeasurableEq (A × B) where
  measurableSet_diagonal := by
    have hdiag : diagonal (A × B) =
        {p : (A × B) × (A × B) | p.1.1 = p.2.1} ∩
          {p : (A × B) × (A × B) | p.1.2 = p.2.2} := by
      ext p
      simp [mem_diagonal_iff, Prod.ext_iff]
    rw [hdiag]
    exact (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd)).inter
        (measurableSet_eq_fun (measurable_snd.comp measurable_fst)
          (measurable_snd.comp measurable_snd))

/-- Lifting a type preserves measurable equality. -/
instance instMeasurableEqULift [MeasurableEq A] : MeasurableEq (ULift.{w} A) where
  measurableSet_diagonal := by
    have hdiag : diagonal (ULift.{w} A) =
        (fun p : ULift.{w} A × ULift.{w} A => (p.1.down, p.2.down)) ⁻¹' diagonal A := by
      ext p
      rw [mem_diagonal_iff, mem_preimage, mem_diagonal_iff]
      exact ULift.down_inj.symm
    rw [hdiag]
    exact measurableSet_diagonal.preimage (measurable_down.comp measurable_fst |>.prodMk
      (measurable_down.comp measurable_snd))

/-- A countable dependent sum has measurable equality when every fiber does. -/
instance instMeasurableEqSigma [Countable I] [∀ i, MeasurableEq (X i)] :
    MeasurableEq (Σ i, X i) where
  measurableSet_diagonal := by
    have hdiag : diagonal (Σ i, X i) = ⋃ i, (fun p : X i × X i =>
        ((⟨i, p.1⟩, ⟨i, p.2⟩) : (Σ i, X i) × (Σ i, X i))) '' diagonal (X i) := by
      ext ⟨⟨i, x⟩, ⟨j, y⟩⟩
      simp only [mem_diagonal_iff, mem_iUnion, mem_image]
      constructor
      · intro h
        exact ⟨i, (x, x), rfl, Prod.ext rfl h⟩
      · rintro ⟨k, ⟨x', y'⟩, hxy, h⟩
        exact (congrArg Prod.fst h).symm.trans
          ((congrArg (Sigma.mk k) hxy).trans (congrArg Prod.snd h))
    rw [hdiag]
    refine MeasurableSet.iUnion fun i => ?_
    exact ((sigmaMk i).prodMap (sigmaMk i)).measurableSet_image' measurableSet_diagonal

/-! ### Singletons -/

/-- `T` has measurable singletons if the leaves of every shape do. -/
theorem measurableSingletonClass (e : T ≃ᵐ Σ s, V s) [∀ s, MeasurableSingletonClass (V s)] :
    MeasurableSingletonClass T where
  measurableSet_singleton x := by
    have : ({x} : Set T) = e ⁻¹' (mk (e x).1 '' {(e x).2}) := by ext; simp
    rw [this]
    exact e.measurable ((sigmaMk _).measurableSet_image' (measurableSet_singleton _))

/-- A type measurably equivalent to countably many fibers with measurable equality has it too. -/
theorem measurableEq [Countable S] (e : T ≃ᵐ Σ s, V s) [∀ s, MeasurableEq (V s)] :
    MeasurableEq T where
  measurableSet_diagonal := by
    have hdiag : diagonal T = (fun p : T × T => (e p.1, e p.2)) ⁻¹' diagonal (Σ s, V s) := by
      ext p
      simp [mem_diagonal_iff]
    rw [hdiag]
    exact measurableSet_diagonal.preimage (e.measurable.comp measurable_fst |>.prodMk
      (e.measurable.comp measurable_snd))

variable (e : T ≃ᵐ Σ s, V s)

/-! ### Constructors are measurable embeddings -/

/-- A constructor `ι` is a measurable embedding if its fields split (`g`) into an index `k : K`
and leaves, with `e (ι a)` the leaves at shape `f k`. -/
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
  have : ι = e.symm ∘ mk s ∘ g := by funext a; simp [← h a]
  rw [this]
  exact e.symm.measurableEmbedding.comp ((sigmaMk s).comp g.measurableEmbedding)

/-! ### Maps out of `T`, shape by shape -/

/-- A map out of `T` is measurable if it is on the values of every shape. -/
theorem measurable_of_fibers (f : T → α) (h : ∀ s, Measurable fun v => f (e.symm ⟨s, v⟩)) :
    Measurable f := by
  have : f = (fun p => f (e.symm p)) ∘ e := by funext; simp
  rw [this]
  exact (measurable_sigma_iff.2 h).comp e.measurable

/-- A map out of `β × T` is measurable if it is on the values of every shape. -/
theorem measurable_uncurry_of_fibers [Countable S] (g : β → T → α)
    (h : ∀ s, Measurable fun p : β × V s => g p.1 (e.symm ⟨s, p.2⟩)) :
    Measurable (uncurry g) := by
  have : uncurry g = (fun q : β × Σ s, V s => g q.1 (e.symm q.2)) ∘ map id e := by
    funext ⟨b, x⟩; simp
  rw [this]
  exact (measurable_prod_sigma h).comp (measurable_id.prodMap e.measurable)

/-- The values of shape `s`, as a function of their leaves. -/
theorem measurable_symm_mk (s : S) : Measurable fun v : V s => e.symm ⟨s, v⟩ :=
  e.symm.measurable.comp (measurable_mk s)

end Sum

/-! ## Small helpers -/

/-- A function pointwise equal to a measurable function is measurable. -/
theorem measurable_of_eq (f g : α → β) (h : ∀ a, f a = g a) (hg : Measurable g) : Measurable f :=
  funext h ▸ hg

/-- `ULift` preserves measurable singletons. -/
instance {A : Type u} [MeasurableSpace A] [MeasurableSingletonClass A] :
    MeasurableSingletonClass (ULift.{w} A) where
  measurableSet_singleton x := by
    change MeasurableSet (up ⁻¹' {x})
    convert measurableSet_singleton x.down using 1
    ext; simp [ext_iff]

end Metrology.Shapes
