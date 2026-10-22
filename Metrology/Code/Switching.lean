module

public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.LocallyClosed
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Switching lemma programs

Lazy random functions and permutations and the weak PRF/PRP games, after clutch's
`prp_prf_weak.v`. -/

namespace ProbLang

variable {rT : Type _}

namespace Switching

/-! ## Pure list values

A list value is `inl ()` (nil) or `inr (x, rest)` (cons). -/

/-- The value encoding a list of integers. -/
def intListVal : List Int → Val rT
  | [] => .inl .unit
  | n :: l => .inr (.pair (.int n) (intListVal l))

/-- The value encoding an association list; the leftmost binding wins. -/
def assocVal : List (Int × Int) → Val rT
  | [] => .inl .unit
  | (k, y) :: m => .inr (.pair (.pair (.int k) (.int y)) (assocVal m))

/-! ## List programs -/

/-- The length of a list value. -/
@[pl_fold] def listLength : Exp rT := pl%
  rec len l :=
    case! l
    | inl(_u) => #0
    | inr(p) => #1 + len (snd(p))

/-- Remove the `i`-th element: `SOME (elem, rest)`, or `NONE` when out of range. -/
@[pl_fold] def listRemoveNth : Exp rT := pl%
  rec rem l i :=
    case! l
    | inl(_u) => inl(#())
    | inr(p) =>
      if i = #0 then inr((fst(p), snd(p)))
      else
        case! (rem (snd(p)) (i - #1))
        | inl(_u) => inl(#())
        | inr(q) => inr((fst(q), inr((fst(p), snd(q)))))

/-! ## Association-list maps in a single cell -/

/-- `SOME v` if the list value binds `k` to `v`, else `NONE`. -/
@[pl_fold] def findList : Exp rT := pl%
  rec find l k :=
    case! l
    | inl(_u) => inl(#())
    | inr(p) => if fst(fst(p)) = k then inr(snd(fst(p))) else find (snd(p)) k

/-- Allocate an empty map. -/
def initMap : Exp rT := pl% fun _u, alloc(inl(#()))

/-- `SOME v` if `k ↦ v` is in the map, else `NONE`. -/
@[pl_fold] def getMap : Exp rT := pl% fun m k, &findList (!m) k

/-- Bind `k` to `v` in the map. -/
@[pl_fold] def setMap : Exp rT := pl% fun m k v, m ← inr(((k, v), !m))

section Programs

variable (N : Int) (ℓ ℓm ℓfv : Loc)

/-! ## The idealised random function -/

/-- After allocating its map at `ℓ`, `randomFunction N` steps to this closure. -/
def rfQuery : Exp rT := pl%
  fun x,
    case! (&getMap #loc ℓ x)
    | inl(_u) => (let y := rand(#N, #()); &setMap #loc ℓ x y; y)
    | inr(y) => y

/-- A lazily sampled random function into `{0, …, N-1}`. -/
def randomFunction : Exp rT := pl%
  let m := &initMap #();
  fun x,
    case! (&getMap m x)
    | inl(_u) => (let y := rand(#N, #()); &setMap m x y; y)
    | inr(y) => y

/-! ## The idealised random permutation -/

/-- After allocating its map at `ℓm` and its list of unsampled values at `ℓfv`,
`randomPermutation N` steps to this closure. -/
def prpQuery : Exp rT := pl%
  fun x,
    case! (&getMap #loc ℓm x)
    | inl(_u) =>
      (let ln := &listLength (!#loc ℓfv);
       let n := rand(ln, #());
       case! (&listRemoveNth (!#loc ℓfv) n)
       | inl(_u) => #0 -- unreachable: `n` is in range
       | inr(p) => (&setMap #loc ℓm x (fst(p)); #loc ℓfv ← snd(p); fst(p)))
    | inr(y) => y

/-- A lazily sampled random permutation of `{0, …, N-1}`. -/
def randomPermutation : Exp rT := pl%
  -- `.1`: the expression of the list value
  let fv := alloc({(intListVal ((List.range N.toNat).map Int.ofNat)).1});
  let m := &initMap #();
  fun x,
    case! (&getMap m x)
    | inl(_u) =>
      (let ln := &listLength (!fv);
       let n := rand(ln, #());
       case! (&listRemoveNth (!fv) n)
       | inl(_u) => #0 -- unreachable: `n` is in range
       | inr(p) => (&setMap m x (fst(p)); fv ← snd(p); fst(p)))
    | inr(y) => y

/-! ## The weak PRF/PRP games -/

/-- Query `f` at `i` uniform inputs, recording the (input, output) pairs in `res`. -/
@[pl_fold] def wLoop : Exp rT := pl%
  rec loop f res i :=
    if i = #0 then #()
    else
      (let x := rand(#N, #());
       let y := f x;
       res ← inr(((x, y), !res));
       loop f res (i - #1))

/-- The weak PRF game against the random function. -/
def wPRF (Q : Int) : Exp rT := pl%
  let f := {randomFunction N};
  let res := alloc(inl(#()));
  {wLoop N} f res #Q;
  !res

/-- The weak PRF game against the random permutation. -/
def wPRP (Q : Int) : Exp rT := pl%
  let f := {randomPermutation N};
  let res := alloc(inl(#()));
  {wLoop N} f res #Q;
  !res

/-! ## `openRec`/`closeRec` erasure (`pl_step_simp`)

The constants are closed, so `openRec`/`closeRec` fix them. As `pl_step_simp` lemmas they let the
step tactics erase the wrappers β-substitution leaves around constants under binders, instead of
every later `whnf` re-evaluating the constant's body. -/

theorem findList_fv : (findList : Exp rT).fv = ∅ := rfl
theorem listLength_fv : (listLength : Exp rT).fv = ∅ := rfl
theorem listRemoveNth_fv : (listRemoveNth : Exp rT).fv = ∅ := rfl
theorem initMap_fv : (initMap : Exp rT).fv = ∅ := rfl
theorem getMap_fv : (getMap : Exp rT).fv = ∅ := rfl
theorem setMap_fv : (setMap : Exp rT).fv = ∅ := rfl
theorem rfQuery_fv : (rfQuery N ℓ : Exp rT).fv = ∅ := rfl
theorem prpQuery_fv : (prpQuery ℓm ℓfv : Exp rT).fv = ∅ := rfl
theorem randomFunction_fv : (randomFunction N : Exp rT).fv = ∅ := rfl
theorem wLoop_fv : (wLoop N : Exp rT).fv = ∅ := rfl

section Erasure

open Exp

variable (k : Nat) (t : Exp rT) (x : Var)

@[pl_step_simp] theorem openRec_findList : openRec k t findList = findList :=
  (open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_findList : closeRec k x (findList : Exp rT) = findList :=
  closeRec_fresh x _ k (by simp [findList_fv])

@[pl_step_simp] theorem openRec_listLength : openRec k t listLength = listLength :=
  (open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_listLength : closeRec k x (listLength : Exp rT) = listLength :=
  closeRec_fresh x _ k (by simp [listLength_fv])

@[pl_step_simp] theorem openRec_listRemoveNth : openRec k t listRemoveNth = listRemoveNth :=
  (open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_listRemoveNth :
    closeRec k x (listRemoveNth : Exp rT) = listRemoveNth :=
  closeRec_fresh x _ k (by simp [listRemoveNth_fv])

@[pl_step_simp] theorem openRec_initMap : openRec k t initMap = initMap :=
  (open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_initMap : closeRec k x (initMap : Exp rT) = initMap :=
  closeRec_fresh x _ k (by simp [initMap_fv])

@[pl_step_simp] theorem openRec_getMap : openRec k t getMap = getMap :=
  (open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_getMap : closeRec k x (getMap : Exp rT) = getMap :=
  closeRec_fresh x _ k (by simp [getMap_fv])

@[pl_step_simp] theorem openRec_setMap : openRec k t setMap = setMap :=
  (open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_setMap : closeRec k x (setMap : Exp rT) = setMap :=
  closeRec_fresh x _ k (by simp [setMap_fv])

@[pl_step_simp] theorem openRec_rfQuery : openRec k t (rfQuery N ℓ) = rfQuery N ℓ :=
  (open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_rfQuery : closeRec k x (rfQuery N ℓ : Exp rT) = rfQuery N ℓ :=
  closeRec_fresh x _ k (by simp [rfQuery_fv])

@[pl_step_simp] theorem openRec_prpQuery : openRec k t (prpQuery ℓm ℓfv) = prpQuery ℓm ℓfv :=
  (open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_prpQuery :
    closeRec k x (prpQuery ℓm ℓfv : Exp rT) = prpQuery ℓm ℓfv :=
  closeRec_fresh x _ k (by simp [prpQuery_fv])

@[pl_step_simp] theorem openRec_randomFunction :
    openRec k t (randomFunction N) = randomFunction N :=
  (open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_randomFunction :
    closeRec k x (randomFunction N : Exp rT) = randomFunction N :=
  closeRec_fresh x _ k (by simp [randomFunction_fv])

@[pl_step_simp] theorem openRec_wLoop : openRec k t (wLoop N) = wLoop N :=
  (open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_wLoop : closeRec k x (wLoop N : Exp rT) = wLoop N :=
  closeRec_fresh x _ k (by simp [wLoop_fv])

end Erasure
end Programs

end Switching
end ProbLang
