module

public import Metrology.ProbLang.Syntax.Syntax

/-! # Consecutive allocation in finite heaps -/

@[expose] public section

open Std Std.ExtTreeMap

namespace ProbLang
namespace LocHeap

variable {V : Type _}

/-- Repeated allocation at successive fresh locations. -/
def allocN (h : LocHeap V) (v : V) : Nat → LocHeap V
  | 0 => h
  | n + 1 => allocN (h.insert h.fresh v) v n

variable (h : LocHeap V) (v : V)

@[simp] theorem fresh_insert :
    (h.insert h.fresh v).fresh = h.fresh + 1 := by
  unfold fresh
  rw [maxKey?_insert]
  cases hm : h.maxKey? with
  | none => simp
  | some m => simp [compare, compareOfLessAndEq]

@[simp] theorem fresh_allocN (n : Nat) :
    (allocN h v n).fresh = h.fresh + n := by
  induction n generalizing h with
  | zero => simp [allocN]
  | succ n ih =>
    simp [allocN, ih, fresh_insert]
    omega

theorem allocN_get? (n : Nat) (l : Loc) :
    (allocN h v n)[l]? = if h.fresh ≤ l ∧ l < h.fresh + n then some v else h[l]? := by
  induction n generalizing h with
  | zero => simp [allocN]
  | succ n ih =>
    simp only [allocN, ih, fresh_insert, getElem?_insert,
      _root_.compare_eq_iff_eq, Int.natCast_succ]
    by_cases hl : h.fresh = l
    · subst l
      simp
    · have hcond : (h.fresh + 1 ≤ l ∧ l < h.fresh + 1 + (n : Int)) ↔
          (h.fresh ≤ l ∧ l < h.fresh + ((n : Int) + 1)) := by
        constructor
        · rintro ⟨hle, hlt⟩
          constructor
          · omega
          · simpa [add_assoc, add_comm, add_left_comm] using hlt
        · rintro ⟨hle, hlt⟩
          constructor
          · omega
          · simpa [add_assoc, add_comm, add_left_comm] using hlt
      simp only [hl, ite_false, hcond]

/-- Every location at or beyond the fresh location is unallocated. -/
theorem get?_eq_none_of_fresh_le (l : Loc) (hl : h.fresh ≤ l) :
    h[l]? = none := by
  unfold fresh at hl
  cases hm : h.maxKey? with
  | none => simp [maxKey?_eq_none_iff.mp hm]
  | some m =>
    simp only [hm] at hl
    have hn := (maxKey?_eq_some_iff_getElem? h m).mp hm |>.2 l (by omega)
    simpa using hn

end LocHeap
end ProbLang
