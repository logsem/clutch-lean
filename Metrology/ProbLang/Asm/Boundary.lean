module

public import Metrology.ProbLang.Asm.Semantics
public import Mathlib.Data.Finset.Sort

/-! # Foreign-call boundary checks and heap fragments -/

@[expose] public section

namespace ProbLang.Asm

open Std.ExtTreeMap

variable {rT V : Type}

/-- The cells of a footprint in ascending logical-location order. -/
def footprintLocations (F : Finset Loc) : List Loc := F.sort (· ≤ ·)

/-- Sorted footprint enumeration contains exactly the footprint cells. -/
@[simp] theorem mem_footprintLocations (F : Finset Loc) (l : Loc) :
    l ∈ footprintLocations F ↔ l ∈ F := by simp [footprintLocations]

/-- Sorted footprint enumeration contains each logical location once. -/
@[simp] theorem footprintLocations_nodup (F : Finset Loc) : (footprintLocations F).Nodup := by
  simp [footprintLocations]

/-- The integer payload of a ProbLang value, if it is an integer literal. -/
def intValue (v : Val rT) : Option Int :=
  match v.fst with
  | .lit (.int z) => some z
  | _ => none

/-- Embed a boundary scalar into ProbLang values. -/
def BoundaryValue.toVal : BoundaryValue → Val rT
  | .int z => .int z
  | .loc l => .loc l
  | .unit => .unit

/-- Extract a representable scalar from a ProbLang value. -/
def BoundaryValue.ofVal (v : Val rT) : Option BoundaryValue :=
  match v.fst with
  | .lit (.int z) => some (.int z)
  | .lit (.loc l) => some (.loc l)
  | .lit .unit => some .unit
  | _ => none

/-- Embedding a boundary scalar preserves its representation. -/
@[simp] theorem BoundaryValue.ofVal_toVal (v : BoundaryValue) :
    ofVal (v.toVal : Val rT) = some v := by
  cases v <;> rfl

/-- Convert a scalar heap to ProbLang values. -/
def valueHeap (heap : LocHeap BoundaryValue) : LocHeap (Val rT) :=
  heap.map (fun _ v => v.toVal)

/-- Restore an integer heap snapshot as boundary values. -/
def HeapSnapshot.restore (heap : HeapSnapshot) : LocHeap BoundaryValue :=
  Iris.Std.PartialMap.ofList (heap.map fun (l, z) => (l, BoundaryValue.int z))

/-- Archive an integer-valued boundary heap, rejecting other cell contents. -/
def snapshot (heap : LocHeap BoundaryValue) : Option HeapSnapshot :=
  heap.toList.mapM fun (l, v) =>
    match v with
    | .int z => some (l, z)
    | _ => none

/-- A snapshot succeeds exactly when the heap lists the same integer cells. -/
theorem snapshot_eq_some_iff {heap : LocHeap BoundaryValue} {saved : HeapSnapshot} :
    snapshot heap = some saved ↔
      saved.map (fun (l, z) => (l, BoundaryValue.int z)) = heap.toList := by
  unfold snapshot
  generalize heap.toList = xs
  induction xs generalizing saved with
  | nil => cases saved <;> simp
  | cons x xs ih =>
    rcases x with ⟨l, v⟩
    cases v <;> cases saved <;>
      simp [List.mapM_cons, Option.bind_eq_some_iff, ih, Prod.ext_iff, and_comm]
    exact fun _ => and_congr eq_comm eq_comm

/-- Restoring a successful snapshot recovers the original boundary heap. -/
theorem restore_snapshot {heap : LocHeap BoundaryValue} {saved : HeapSnapshot}
    (h : snapshot heap = some saved) : saved.restore = heap := by
  unfold HeapSnapshot.restore
  rw [snapshot_eq_some_iff.mp h]
  exact Iris.Std.LawfulFiniteMap.ofList_toList

/-- The location payload of a ProbLang value, if it is a location literal. -/
def locValue (v : Val rT) : Option Loc :=
  match v.fst with
  | .lit (.loc l) => some l
  | _ => none

/-- Resolve an array length using the original argument tuple. -/
def Len.resolve (args : List (Val rT)) : Len → Option Nat
  | .const n => some n
  | .arg i => do
    let v ← args[i]?
    let z ← intValue v
    if z < 0 then none else some z.toNat

/-- The logical cells and representation of a pointer argument. -/
structure Region where
  /-- The first logical location. -/
  base : Loc
  /-- The number of logical cells. -/
  length : Nat
  /-- The bit width of each cell. -/
  width : Nat
  /-- Whether cell integers use a signed representation. -/
  signed : Bool
  deriving DecidableEq, BEq, Repr

/-- The logical cells in a region. -/
def Region.cells (r : Region) : Finset Loc :=
  (Finset.range r.length).image (fun (i : Nat) => r.base + (i : Int))

/-- The region denoted by a pointer argument, if its shape is valid. -/
def ArgKind.region (args : List (Val rT)) (v : Val rT) : ArgKind → Option Region
  | .loc => do return ⟨← locValue v, 1, 64, true⟩
  | .array width len => do return ⟨← locValue v, ← len.resolve args, width, false⟩
  | _ => none

/-- The pointer regions of a call. -/
def regions (sig : CallSig) (args : List (Val rT)) : List Region :=
  (sig.args.zip args).filterMap fun (kind, v) => kind.region args v

/-- The signature-derived footprint of a call. -/
def footprint (sig : CallSig) (args : List (Val rT)) : Finset Loc :=
  (regions sig args).foldl (fun F r => F ∪ r.cells) ∅

/-- Integer encodability at a given signedness and width. -/
def inRange (signed : Bool) (width : Nat) (z : Int) : Bool :=
  if width = 0 ∨ 64 < width then false else
  if signed then decide (-(2 ^ (width - 1) : Int) ≤ z ∧ z < 2 ^ (width - 1))
  else decide (0 ≤ z ∧ z < 2 ^ width)

/-- An integer value representable by the requested machine width. -/
def intFits (signed : Bool) (width : Nat) (v : Val rT) : Bool :=
  (intValue v).any (inRange signed width)

/-- Every cell in a region is allocated and representable. -/
def Region.check (heap : LocHeap (Val rT)) (r : Region) : Bool :=
  [8, 16, 32, 64].contains r.width && (List.range r.length).all fun i =>
    (heap[r.base + (i : Int)]?).any (intFits r.signed r.width)

/-- Check one argument against its signature and the current heap. -/
def ArgKind.check (args : List (Val rT)) (heap : LocHeap (Val rT)) (v : Val rT) :
    ArgKind → Bool
  | .int width => intFits true width v
  | .uint width => intFits false width v
  | .loc => (ArgKind.loc.region args v).any (Region.check heap)
  | .array width len => (ArgKind.array width len |>.region args v).any (Region.check heap)
  | .unit => match v.fst with | .lit .unit => true | _ => false

/-- Two pointer arguments either coincide with identical representations or are disjoint. -/
def Region.compatible (a b : Region) : Bool :=
  a == b || decide (Disjoint a.cells b.cells)

/-- The result kinds supported by the register-return convention. -/
def ArgKind.validResult : ArgKind → Bool
  | .array _ _ => false
  | .int w | .uint w => decide (0 < w ∧ w ≤ 64)
  | _ => true

/-- Import names are unambiguous and each callback fits the register-return convention. -/
def Sig.valid (sig : Sig) : Bool :=
  decide ((sig.imports.map Prod.fst).Nodup) &&
    sig.imports.all (fun (_, s) => decide (s.args.length ≤ 8) && s.result.validResult)

/-- Check a result, including pointers into the footprint or one past a pointer region. -/
def checkResult (sig : CallSig) (args : List (Val rT)) (kind : ArgKind) (v : Val rT) : Bool :=
  match kind with
  | .loc => (locValue v).any fun l =>
    decide (l ∈ footprint sig args) ||
      (regions sig args).any (fun r => l == r.base + (r.length : Int))
  | .array _ _ => false
  | _ => kind.check [] ∅ v

/-- Check arity, register representations, pointed-to cells and aliasing. -/
def check (sig : CallSig) (args : List (Val rT)) (heap : LocHeap (Val rT)) : Bool :=
  decide (args.length = sig.args.length ∧ args.length ≤ 8) && sig.result.validResult &&
    (sig.args.zip args).all (fun (kind, v) => kind.check args heap v) &&
    (regions sig args).all (fun a => (regions sig args).all (a.compatible ·))

/-- Restrict a heap to the cells owned by a foreign call. -/
def restrict (F : Finset Loc) (heap : LocHeap V) : LocHeap V :=
  heap.filter (fun l _ => decide (l ∈ F))

/-- Restriction preserves exactly the selected cells. -/
@[simp] theorem restrict_get (F : Finset Loc) (heap : LocHeap V) (l : Loc) :
    (restrict F heap)[l]? = if l ∈ F then heap[l]? else none := by
  simp only [restrict, getElem?_filter']
  split <;> cases heap[l]? <;> simp_all

/-- A heap with no cells outside the footprint is its own restriction. -/
theorem restrict_eq_self_of {F : Finset Loc} {heap : LocHeap V}
    (h : ∀ l, l ∉ F → heap[l]? = none) : restrict F heap = heap := by
  apply ext_getElem?
  intro l
  rw [restrict_get]
  split
  · rfl
  · exact (h l ‹_›).symm

/-- Restricting twice to the same footprint has no additional effect. -/
@[simp] theorem restrict_idem (F : Finset Loc) (heap : LocHeap V) :
    restrict F (restrict F heap) = restrict F heap :=
  restrict_eq_self_of fun l hl => by simp [hl]

/-- Replace the footprint with a new fragment and retain the surrounding heap. -/
def overwrite (F : Finset Loc) (heap fragment : LocHeap V) : LocHeap V :=
  restrict F fragment ∪ heap.filter (fun l _ => decide (l ∉ F))

/-- The updated heap agrees with the new fragment on the footprint. -/
@[simp] theorem overwrite_get (F : Finset Loc) (heap fragment : LocHeap V) (l : Loc) :
    (overwrite F heap fragment)[l]? = if l ∈ F then fragment[l]? else heap[l]? := by
  rw [overwrite, getElem?_union, restrict_get, getElem?_filter']
  by_cases hl : l ∈ F <;> cases heap[l]? <;> simp_all

/-- The updated heap exposes precisely the new fragment when restricted. -/
@[simp] theorem restrict_overwrite (F : Finset Loc) (heap fragment : LocHeap V) :
    restrict F (overwrite F heap fragment) = restrict F fragment := by
  apply ext_getElem?
  intro l
  simp only [restrict_get, overwrite_get]
  split <;> rfl

/-- A callback returns an encodable value and exactly the original footprint. -/
def responseOK (code : Code) (args : List (Val rT)) (F : Finset Loc)
    (name : String) (r : Val rT) (heap : LocHeap (Val rT)) : Prop :=
  code.sig.valid = true ∧ F = footprint code.sig.toCallSig args ∧
    heap = restrict F heap ∧ check code.sig.toCallSig args heap = true ∧
    ∃ sig, (name, sig) ∈ code.sig.imports ∧ sig.result.validResult = true ∧
      checkResult code.sig.toCallSig args sig.result r = true

/-- Evaluate a machine call over ProbLang values, as `start` does over boundary scalars. -/
noncomputable def evalCall (M : AsmSemantics Code (Val rT)) (code : Code)
    (args : List (Val rT)) (heap : LocHeap (Val rT)) : Option (Interaction (Val rT)) :=
  let F := footprint code.sig.toCallSig args
  M.eval code args F (restrict F heap)

/-- Foreign-call evaluation depends only on the signature-derived footprint. -/
theorem evalCall_local (M : AsmSemantics Code (Val rT)) (code : Code)
    (args : List (Val rT)) (heap : LocHeap (Val rT)) :
    evalCall M code args heap =
      evalCall M code args (restrict (footprint code.sig.toCallSig args) heap) := by
  simp only [evalCall, restrict_idem]

end ProbLang.Asm
