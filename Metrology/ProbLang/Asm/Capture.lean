module

public import Metrology.ProbLang.Asm.Boundary

/-! # Capturing finite foreign-call footprints -/

@[expose] public section

namespace ProbLang.Asm

variable {rT : Type} (F : Finset Loc)

private theorem mapM_congrOn {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forall_mem_cons] at h
    simp only [List.mapM_cons, h.1, ih h.2]

/-- Read the current integer contents of a finite footprint. -/
def capture (heap : LocHeap (Val rT)) : Option HeapSnapshot :=
  (footprintLocations F).mapM fun l => do
    let v ← heap[l]?
    let z ← intValue v
    pure (l, z)

/-- Capturing a footprint depends only on its selected heap locations. -/
theorem capture_congr (heap heap' : LocHeap (Val rT))
    (h : ∀ l ∈ F, heap[l]? = heap'[l]?) : capture F heap = capture F heap' := by
  unfold capture
  apply mapM_congrOn
  intro l hl
  rw [h l ((mem_footprintLocations F l).mp hl)]

/-- Known integer cells produce the corresponding finite snapshot. -/
theorem capture_eq_snapshot (values : Loc → Int) (heap : LocHeap (Val rT))
    (h : ∀ l ∈ F, heap[l]? = some (.int (values l))) :
    capture F heap = some ((footprintLocations F).map (fun l => (l, values l))) := by
  unfold capture
  calc
    _ = (footprintLocations F).mapM (fun l => some (l, values l)) := by
      apply mapM_congrOn
      intro l hl
      rw [h l ((mem_footprintLocations F l).mp hl)]
      rfl
    _ = _ := List.mapM_pure

/-- Reading a footprint ignores all surrounding heap cells. -/
theorem capture_local (heap : LocHeap (Val rT)) :
    capture F heap = capture F (restrict F heap) := by
  apply capture_congr
  intro l hl
  simp only [restrict_get, ite_eq_left hl]

end ProbLang.Asm
