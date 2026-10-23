module

public import Metrology.ProbLang.Asm.Boundary

/-! # Capturing finite foreign-call footprints -/

@[expose] public section

namespace ProbLang.Asm

variable {rT α β : Type}

private theorem mapM_congrOn (xs : List α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  revert h
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    have hx := h x List.mem_cons_self
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.mapM_cons, hx, hxs]

/-- Read the current integer contents of a finite footprint. -/
def capture (F : Finset Loc) (heap : LocHeap (Val rT)) : Option HeapSnapshot :=
  (footprintLocations F).mapM fun l => do
    let v ← heap[l]?
    let z ← intValue v
    pure (l, z)

/-- Capturing a footprint depends only on its selected heap locations. -/
theorem capture_congr (F : Finset Loc) (heap heap' : LocHeap (Val rT))
    (h : ∀ l ∈ F, heap[l]? = heap'[l]?) : capture F heap = capture F heap' := by
  unfold capture
  apply mapM_congrOn
  intro l hl
  rw [h l ((mem_footprintLocations F l).mp hl)]

/-- Known integer cells produce the corresponding finite snapshot. -/
theorem capture_eq_snapshot (F : Finset Loc) (values : Loc → Int) (heap : LocHeap (Val rT))
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
theorem capture_local (F : Finset Loc) (heap : LocHeap (Val rT)) :
    capture F heap = capture F (restrict F heap) := by
  apply capture_congr
  intro l hl
  simp only [restrict_get, ite_eq_left hl]

end ProbLang.Asm
