module

public import Metrology.ProbLang.Syntax.Syntax

/-! # Finite heap-fragment updates -/

@[expose] public section

open Std.ExtTreeMap Prod List

namespace ProbLang

variable {V : Type} {rT : Type}

/-- Insert a finite fragment into a heap in list order. -/
def LocHeap.writeFragment (heap : LocHeap V) (entries : List (Loc × V)) : LocHeap V :=
  entries.foldl (fun heap entry => heap.insert entry.1 entry.2) heap

/-- Writing a finite fragment preserves every location outside its key list. -/
theorem LocHeap.writeFragment_lookup_of_not_mem (heap : LocHeap V)
    (entries : List (Loc × V)) (l : Loc) (h : l ∉ entries.map fst) :
    (heap.writeFragment entries)[l]? = heap[l]? := by
  induction entries generalizing heap with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨key, value⟩ := entry
    have hkey : key ≠ l := by
      intro heq
      apply h
      simp [heq]
    have htail : l ∉ entries.map fst := by
      intro hmem
      apply h
      simp [hmem]
    rw [writeFragment, foldl_cons]
    change (LocHeap.writeFragment (heap.insert key value) entries)[l]? = heap[l]?
    rw [ih _ htail]
    simp [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hkey]

/-- A duplicate-free output fragment determines the new value at every listed location. -/
theorem LocHeap.writeFragment_lookup_of_mem (heap : LocHeap V)
    (entries : List (Loc × V)) (hnodup : (entries.map fst).Nodup)
    (l : Loc) (v : V) (hmem : (l, v) ∈ entries) :
    (heap.writeFragment entries)[l]? = some v := by
  induction entries generalizing heap with
  | nil => simp at hmem
  | cons entry entries ih =>
    obtain ⟨key, value⟩ := entry
    have htail := (nodup_cons.mp hnodup).2
    rcases mem_cons.mp hmem with heq | hmem
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      have hnotmem := (nodup_cons.mp hnodup).1
      change (LocHeap.writeFragment (heap.insert l v) entries)[l]? = some v
      rw [writeFragment_lookup_of_not_mem _ entries l hnotmem]
      simp
    · change (LocHeap.writeFragment (heap.insert key value) entries)[l]? = some v
      exact ih _ htail hmem

section StateFragment
variable (σ : State rT) (entries : List (Loc × Val rT))

/-- Replace the finite fragment of a state without changing its tapes. -/
def State.writeFragment : State rT :=
  σ.update_heap (fun heap => LocHeap.writeFragment heap entries)

/-- The first fragment cell is inserted before the remaining cells. -/
theorem State.writeFragment_cons (l : Loc) (v : Val rT) :
    σ.writeFragment ((l, v) :: entries) =
      (σ.update_heap (fun heap => heap.insert l v)).writeFragment entries := rfl

/-- Writing a finite state fragment preserves every heap location outside its keys. -/
theorem State.writeFragment_lookup_of_not_mem (l : Loc) (h : l ∉ entries.map fst) :
    (σ.writeFragment entries).heap[l]? = σ.heap[l]? :=
  LocHeap.writeFragment_lookup_of_not_mem σ.heap entries l h

/-- A duplicate-free output fragment determines the new values in the state heap. -/
theorem State.writeFragment_lookup_of_mem (hnodup : (entries.map fst).Nodup)
    (l : Loc) (v : Val rT) (hmem : (l, v) ∈ entries) :
    (σ.writeFragment entries).heap[l]? = some v :=
  LocHeap.writeFragment_lookup_of_mem σ.heap entries hnodup l v hmem

/-- Writing a heap fragment preserves the tape map. -/
theorem State.writeFragment_tapes :
    (σ.writeFragment entries).tapes = σ.tapes := rfl

end StateFragment

end ProbLang
