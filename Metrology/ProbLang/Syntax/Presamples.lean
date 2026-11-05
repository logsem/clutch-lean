module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Basic

/-! # Infinite tape contents

Optional values indexed by natural numbers, with shifting and presampling operations. -/

@[expose] public section

open Function

namespace ProbLang

namespace Presamples

variable {V : Type _}

/-- The stream of a list: its entries, then `none`. -/
def ofList (bs : List V) : ℕ → Option V := fun k => bs[k]?

/-- The stream after a read: position `k` holds what position `k + 1` held. -/
def shift (f : ℕ → Option V) : ℕ → Option V := fun k => f (k + 1)

/-- Fills position `k` with `x` if it holds `none`. -/
def fillAt (f : ℕ → Option V) (k : ℕ) (x : V) : ℕ → Option V :=
  update f k (some ((f k).getD x))

/-- Fills every `none` position `k` with `ω k`. -/
def fillAll (f : ℕ → Option V) (ω : ℕ → V) : ℕ → Option V := fun k => some ((f k).getD (ω k))

open Classical in
/-- The first position holding `none`, if any. -/
noncomputable def firstNone (f : ℕ → Option V) : Option ℕ :=
  if h : ∃ k, f k = none then some (Nat.find h) else none

/-- Fills the first `none` position with `x`; no change if there is none. -/
noncomputable def fillNext (f : ℕ → Option V) (x : V) : ℕ → Option V :=
  match firstNone f with
  | some k => fillAt f k x
  | none => f

@[simp] theorem ofList_apply (bs : List V) (k : ℕ) : ofList bs k = bs[k]? := rfl

@[simp] theorem shift_apply (f : ℕ → Option V) (k : ℕ) : shift f k = f (k + 1) := rfl

@[simp] theorem fillAll_apply (f : ℕ → Option V) (ω : ℕ → V) (k : ℕ) :
    fillAll f ω k = some ((f k).getD (ω k)) :=
  rfl

/-- The empty list gives the all-`none` stream. -/
@[simp] theorem ofList_nil : ofList ([] : List V) = fun _ => none := rfl

/-- Shifting a list's stream drops its head. -/
@[simp] theorem shift_ofList_cons (b : V) (bs : List V) : shift (ofList (b :: bs)) = ofList bs :=
  rfl

/-- Shifting the all-`none` stream leaves it unchanged. -/
@[simp] theorem shift_none : shift (fun _ : ℕ => (none : Option V)) = fun _ => none := rfl

/-- A list's stream determines the list. -/
theorem ofList_injective : Injective (ofList : List V → ℕ → Option V) :=
  fun _ _ h => List.ext_getElem? (congrFun h)

/-- Filling an empty position. -/
theorem fillAt_of_none {f : ℕ → Option V} {k : ℕ} (h : f k = none) (x : V) :
    fillAt f k x = update f k (some x) := by
  simp [fillAt, h]

/-- Filling a full position changes nothing. -/
theorem fillAt_of_some {f : ℕ → Option V} {k : ℕ} {y : V} (h : f k = some y) (x : V) :
    fillAt f k x = f := by
  simp [fillAt, h]

/-- Filling position `k + 1` commutes with the shift. -/
theorem shift_fillAt_succ (f : ℕ → Option V) (k : ℕ) (x : V) :
    shift (fillAt f (k + 1) x) = fillAt (shift f) k x := by
  funext j
  simp only [shift, fillAt, update_apply, Nat.add_right_cancel_iff]

/-- Filling position `0` is forgotten by the shift. -/
theorem shift_fillAt_zero (f : ℕ → Option V) (x : V) : shift (fillAt f 0 x) = shift f := by
  funext j
  simp [shift, fillAt]

/-- Filling every position commutes with the shift. -/
theorem shift_fillAll (f : ℕ → Option V) (ω : ℕ → V) :
    shift (fillAll f ω) = fillAll (shift f) (fun k => ω (k + 1)) :=
  rfl

/-- The first `none` of a list's stream is past the list. -/
theorem firstNone_ofList (bs : List V) : firstNone (ofList bs) = some bs.length := by
  have h : ∃ k, ofList bs k = none := ⟨bs.length, by simp⟩
  rw [firstNone, dite_eq_left h, Option.some_inj, Nat.find_eq_iff]
  exact ⟨by simp, fun n hn => by simp [hn]⟩

/-- Filling the next position of a list's stream appends to the list. -/
theorem fillNext_ofList (bs : List V) (x : V) : fillNext (ofList bs) x = ofList (bs ++ [x]) := by
  rw [fillNext, firstNone_ofList]
  dsimp only
  rw [fillAt_of_none (by simp)]
  funext k
  rcases _root_.lt_trichotomy k bs.length with hk | rfl | hk
  · simp [show k ≠ bs.length by omega, List.getElem?_append_left hk]
  · simp
  · simp [show k ≠ bs.length by omega, List.getElem?_eq_none (by omega : bs.length ≤ k),
      List.getElem?_eq_none (by simp; omega : (bs ++ [x]).length ≤ k)]

/-- Filling the first position after a finite prefix appends the new value. -/
@[simp]
theorem fillAt_ofList_length (bs : List V) (x : V) :
    fillAt (ofList bs) bs.length x = ofList (bs ++ [x]) := by
  rw [← fillNext_ofList]
  simp [fillNext, firstNone_ofList]

end Presamples

end ProbLang
