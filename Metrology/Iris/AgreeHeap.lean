module

public import Mathlib.Basic.ENNReal.Basic
public import Iris
public import Iris.Algebra.HeapView
public import Iris.Instances.IProp.Instance
public import Iris.Std.HeapInstances
public import Metrology.ProbLang.Syntax.Syntax
import Metrology.Iris.LocalBI

/-! # `Agree`-valued heap views

Heaps of `Agree` values and the `HeapView` rules shared by the spec and program sides. -/

@[expose] public section

open Std Iris Iris.Std COFE ProbLang

/-! ## Heaps of `Agree` values -/

/-- Wraps every heap value in `Agree`. -/
def LocHeap.asAgree [OFE V] (h : LocHeap V) : LocHeap (Agree V) :=
  PartialMap.map LocHeap toAgree h

/-- Reading the wrapped heap is reading the heap, then wrapping. -/
theorem LocHeap.asAgree_get? [OFE V] (h : LocHeap V) (l : Loc) :
    PartialMap.get? (LocHeap.asAgree h) l = (PartialMap.get? h l).map toAgree := by
  simp only [LocHeap.asAgree, PartialMap.map, LawfulPartialMap.get?_bindAlter]
  cases PartialMap.get? h l <;> rfl

/-- Wrapping commutes with insertion. -/
theorem LocHeap.asAgree_insert [OFE V] (h : LocHeap V) (l : Loc) (v : V) :
    LocHeap.asAgree (PartialMap.insert h l v) =
      PartialMap.insert (LocHeap.asAgree h) l (toAgree v) := by
  refine LawfulPartialMap.equiv_iff_eq.mp fun k => ?_
  by_cases hk : l = k
  · subst hk
    rw [LocHeap.asAgree_get?, LawfulPartialMap.get?_insert_eq rfl,
        LawfulPartialMap.get?_insert_eq rfl]
    rfl
  · rw [LocHeap.asAgree_get?, LawfulPartialMap.get?_insert_ne hk,
        LawfulPartialMap.get?_insert_ne hk, LocHeap.asAgree_get?]

/-- The fresh location is unmapped in the wrapped heap. -/
theorem LocHeap.asAgree_get?_fresh [OFE V] (h : LocHeap V) :
    PartialMap.get? (LocHeap.asAgree h) h.fresh = none := by
  rw [LocHeap.asAgree_get?]
  show (h[h.fresh]?).map toAgree = none
  rw [ExtTreeMap.fresh_get?]; rfl

/-- A fragment included in the wrapped heap's value pins down the plain heap's value. -/
theorem LocHeap.get?_of_asAgree_get? [OFE V] {h : LocHeap V} {l : Loc} {v : V} {a : Agree V}
    (hget : PartialMap.get? (LocHeap.asAgree h) l = some a) (hinc : toAgree v ≼ a) :
    PartialMap.get? h l = some v := by
  rw [LocHeap.asAgree_get?] at hget
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hget
  rw [hw, Agree.toAgree_included.mp hinc]

/-! ## Heap-view facts shared by the spec and program sides

Facts about one `HeapView Loc (Agree V) LocHeap` cell, stated for any ghost slot `E` and name `γ`;
`SpecProgram` and `AppProgram` instantiate them for their heaps and tapes. -/

namespace AgreeHeap

variable {V : Type _} [OFE V] {GF : BundledGFunctors}
  {E : ElemG GF (constOF (HeapView Loc (Agree V) LocHeap))} {γ : GName} {l : Loc}

local bi IProp GF

/-- Allocating the authority for a plain heap `σ`. -/
theorem alloc_auth (σ : LocHeap V) :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      iOwn (E := E) γ (HeapView.Auth (.own 1) (LocHeap.asAgree σ)) :=
  iOwn_alloc _ HeapView.auth_one_valid

/-- Owning a cell against the authority shows the heap holds its value there. -/
theorem lookup [OFE.Discrete V] {σ : LocHeap V} {v : V} :
    ⊢ iOwn (E := E) γ (HeapView.Auth (.own 1) (LocHeap.asAgree σ)) -∗
      iOwn (E := E) γ (HeapView.Frag l (.own 1) (toAgree v)) -∗ ⌜σ[l]? = some v⌝ := by
  iintro Hh Hf
  icombine Hh Hf gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  obtain ⟨_, _, _, hget, _, hinc⟩ := HeapView.auth_op_frag_valid_total_discrete_iff hv
  exact LocHeap.get?_of_asAgree_get? hget hinc

/-- Overwriting a cell updates the authority and the cell together. -/
theorem update {σ : LocHeap V} {v w : V} :
    iOwn (E := E) γ (HeapView.Auth (.own 1) (LocHeap.asAgree σ)) ∗
        iOwn (E := E) γ (HeapView.Frag l (.own 1) (toAgree v)) ⊢
      |==> (iOwn (E := E) γ (HeapView.Auth (.own 1) (LocHeap.asAgree (PartialMap.insert σ l w))) ∗
        iOwn (E := E) γ (HeapView.Frag l (.own 1) (toAgree w))) := by
  iintro H
  imod iOwn_update_op (HeapView.update_replace (Agree.toAgree_valid (a := w))) $$ H with Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op $$ Hu
  simp only [LocHeap.asAgree_insert]
  iframe

/-- Allocating a value yields a cell at the fresh location. -/
theorem alloc {σ : LocHeap V} (v : V) :
    iOwn (E := E) γ (HeapView.Auth (.own 1) (LocHeap.asAgree σ)) ⊢
      |==> (iOwn (E := E) γ
          (HeapView.Auth (.own 1) (LocHeap.asAgree (PartialMap.insert σ σ.fresh v))) ∗
        iOwn (E := E) γ (HeapView.Frag σ.fresh (.own 1) (toAgree v))) := by
  iintro Hh
  imod iOwn_update (HeapView.update_one_alloc (LocHeap.asAgree_get?_fresh σ)
    DFrac.valid_own_one (Agree.toAgree_valid (a := v))) $$ Hh with Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op $$ Hu
  simp only [LocHeap.asAgree_insert]
  iframe

/-- Two full cells at one location are contradictory. -/
theorem frag_valid_2 [OFE.Discrete V] {v₁ v₂ : V} :
    ⊢ iOwn (E := E) γ (HeapView.Frag l (.own 1) (toAgree v₁)) -∗
      iOwn (E := E) γ (HeapView.Frag l (.own 1) (toAgree v₂)) -∗ False := by
  iintro H1 H2
  icombine H1 H2 gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  exfalso
  exact absurd (DFrac.valid_own_op (HeapView.frag_op_valid_iff.mp hv).1) (lt_irrefl _)

/-- An empty integer tape is an empty tape fragment. -/
theorem natTape_to_empty {F : Loc → Tape → IProp GF} {z : Int} :
    iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
      ⌜fs.map (fun x ↦ x.val) = ([] : List Int)⌝ ∗ F l ⟨z, fs⟩) ⊢ F l ⟨z, []⟩ := by
  iintro ⟨%fs, %hmap, Hl⟩
  obtain rfl := List.map_eq_nil_iff.mp hmap
  iexact Hl

/-- An empty tape fragment is an empty integer tape. -/
theorem empty_to_natTape {F : Loc → Tape → IProp GF} {z : Int} :
    F l ⟨z, []⟩ ⊢ iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
      ⌜fs.map (fun x ↦ x.val) = ([] : List Int)⌝ ∗ F l ⟨z, fs⟩) := by
  iintro Hl
  iexists []
  isplitr
  · ipureintro
    rfl
  iexact Hl

/-- An integer tape with head `n` exposes its first entry, and can be rebuilt from the tail. -/
theorem read_natTape_head {F : Loc → Tape → IProp GF} {z : Int} {n : Int}
    {ns : List Int} :
    iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
        ⌜fs.map (fun x ↦ x.val) = n :: ns⌝ ∗ F l ⟨z, fs⟩) ⊢
      iprop(∃ (x : { z' : Int // 0 ≤ z' ∧ z' < z }) (xs : List { z' : Int // 0 ≤ z' ∧ z' < z }),
        F l ⟨z, x :: xs⟩ ∗ ⌜x.val = n⌝ ∗
        (F l ⟨z, xs⟩ -∗ ∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
          ⌜fs.map (fun x ↦ x.val) = ns⌝ ∗ F l ⟨z, fs⟩)) := by
  iintro ⟨%fs, %hmap, Hl⟩
  obtain ⟨x, xs, rfl, hx, hxs⟩ := List.map_eq_cons_iff.mp hmap
  iexists x, xs
  isplitl [Hl]
  · iexact Hl
  isplitr
  · ipureintro
    exact hx
  iintro Hl
  iexists xs
  isplitr
  · ipureintro
    exact hxs
  iexact Hl

end AgreeHeap
