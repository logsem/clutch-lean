module

public import Metrology.ProbLang.Asm.Boundary

/-! # Finite integer fragments at the assembly boundary -/

@[expose] public section

namespace ProbLang.Asm

variable (F : Finset Loc) (values : Loc → Int)

open Iris.Std Iris.Std.LawfulPartialMap Std.ExtTreeMap

/-- Archive one integer value for each location in a finite footprint. -/
def integerSnapshot : HeapSnapshot :=
  (footprintLocations F).map (fun l => (l, values l))

/-- Restore the integer fragment selected by a finite footprint. -/
def integerHeap : LocHeap BoundaryValue :=
  (integerSnapshot F values).restore

/-- The archived keys are exactly the footprint enumeration. -/
@[simp] theorem integerSnapshot_keys :
    (integerSnapshot F values).map Prod.fst = footprintLocations F := by
  simp [integerSnapshot, List.map_map, Function.comp_def]

/-- The archived integer fragment has no duplicate locations. -/
theorem integerSnapshot_nodup :
    NoDupKeys (integerSnapshot F values) := by
  simpa only [NoDupKeys, integerSnapshot_keys] using footprintLocations_nodup F

/-- The restored fragment contains exactly the selected integer cells. -/
@[simp] theorem integerHeap_get (l : Loc) :
    (integerHeap F values)[l]? = if l ∈ F then some (.int (values l)) else none := by
  have hkeys : ((integerSnapshot F values).map (fun (l, z) => (l, BoundaryValue.int z))).map
      Prod.fst = footprintLocations F := by
    simp [integerSnapshot, List.map_map, Function.comp_def]
  have hnodup : NoDupKeys ((integerSnapshot F values).map
      (fun (l, z) => (l, BoundaryValue.int z))) := by
    rw [NoDupKeys, hkeys]
    exact footprintLocations_nodup F
  unfold integerHeap HeapSnapshot.restore
  by_cases hl : l ∈ F
  · rw [ite_eq_left hl]
    refine get?_ofList_some (M := LocHeap) ?_ hnodup
    simp [integerSnapshot, hl]
  · rw [ite_eq_right hl]
    refine get?_ofList_none (M := LocHeap) ?_ hnodup
    rintro ⟨v, hmem⟩
    refine hl ((mem_footprintLocations F l).mp ?_)
    rw [← hkeys]
    exact List.mem_map.mpr ⟨(l, v), hmem, rfl⟩

/-- Restricting a constructed fragment to its footprint leaves it unchanged. -/
@[simp] theorem restrict_integerHeap :
    restrict F (integerHeap F values) = integerHeap F values := by
  apply ext_getElem?
  intro l
  simp only [restrict_get, integerHeap_get]
  split <;> rfl

/-- Embedding the constructed fragment exposes exactly its integer ProbLang values. -/
@[simp] theorem valueHeap_integerHeap_get {rT : Type} (l : Loc) :
    (valueHeap (rT := rT) (integerHeap F values))[l]? =
      if l ∈ F then some (Val.int (values l)) else none := by
  simp only [valueHeap, getElem?_map, integerHeap_get]
  split <;> rfl

private theorem snapshot_list_of_ints (entries : List (Loc × BoundaryValue))
    (h : ∀ entry ∈ entries, ∃ z, entry.2 = .int z) :
    ∃ saved, entries.mapM (fun (l, v) => match v with
      | .int z => some (l, z)
      | _ => none) = some saved := by
  induction entries with
  | nil => exact ⟨[], rfl⟩
  | cons entry entries ih =>
    obtain ⟨l, v⟩ := entry
    obtain ⟨z, rfl⟩ := h (l, v) List.mem_cons_self
    obtain ⟨saved, hsaved⟩ := ih (fun entry hmem => h entry (List.mem_cons_of_mem _ hmem))
    exact ⟨(l, z) :: saved, by simp [List.mapM_cons, hsaved]⟩

/-- Every constructed integer fragment can be archived successfully. -/
theorem snapshot_integerHeap :
    ∃ saved, snapshot (integerHeap F values) = some saved := by
  apply snapshot_list_of_ints
  intro entry hmem
  obtain ⟨l, v⟩ := entry
  have hlookup : (integerHeap F values)[l]? = some v := (toList_get (M := LocHeap)).mp hmem
  rw [integerHeap_get] at hlookup
  split at hlookup
  · exact ⟨values l, Option.some.inj hlookup.symm⟩
  · cases hlookup

/-- Restoring a successful archive of the constructed fragment recovers that fragment. -/
theorem restore_snapshot_integerHeap
    {saved : HeapSnapshot} (h : snapshot (integerHeap F values) = some saved) :
    saved.restore = integerHeap F values := restore_snapshot h

end ProbLang.Asm
