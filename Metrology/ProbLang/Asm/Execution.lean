module

public import Metrology.ProbLang.Asm.Boundary

/-! # First-order assembly calls and callback replay -/

@[expose] public section

namespace ProbLang.Asm

/-- The machine interpretation and ProbLang implementations of its imports. -/
structure FfiEnv (rT : Type) where
  /-- The machine semantics on representable boundary scalars. -/
  machine : AsmSemantics Code BoundaryValue
  /-- The ProbLang function implementing each named import. -/
  impls : String → Val rT

/-- An observable action of the foreign-call dispatcher. -/
inductive Action where
  | invalid
  | stuck
  | ret (value : BoundaryValue) (heap : LocHeap BoundaryValue)
  | call (name : String) (args : List BoundaryValue) (heap : LocHeap BoundaryValue)
      (archive : Replay)
  deriving Countable

/-- Encode boundary arguments as a right-nested ProbLang tuple ending in unit. -/
def argumentTuple {rT : Type} : List BoundaryValue → Exp rT
  | [] => .lit .unit
  | value :: rest => .pair value.toVal.fst (argumentTuple rest)

/-- The value represented by a boundary argument tuple. -/
def argumentValues {rT : Type} : List BoundaryValue → Val rT
  | [] => .unit
  | value :: rest => .pair value.toVal (argumentValues rest)

/-- Argument tuple expressions are the expressions of their tuple values. -/
theorem argumentTuple_eq {rT : Type} (args : List BoundaryValue) :
    argumentTuple args = (argumentValues (rT := rT) args).fst := by
  induction args with
  | nil => rfl
  | cons value rest ih => exact congrArg (Exp.pair value.toVal.fst) ih

/-- Decode a tuple with exactly the requested number of scalar arguments. -/
def readTuple {rT : Type} : Nat → Exp rT → Option (List BoundaryValue)
  | 0, .lit .unit => some []
  | n + 1, .pair (.lit (.int z)) rest => (readTuple n rest).map (.int z :: ·)
  | n + 1, .pair (.lit (.loc l)) rest => (readTuple n rest).map (.loc l :: ·)
  | n + 1, .pair (.lit .unit) rest => (readTuple n rest).map (.unit :: ·)
  | _, _ => none

/-- Tuple encoding preserves boundary arguments and their arity. -/
@[simp] theorem readTuple_argumentTuple {rT : Type} (args : List BoundaryValue) :
    readTuple args.length (argumentTuple (rT := rT) args) = some args := by
  induction args with
  | nil => rfl
  | cons value rest ih => cases value <;> simp [argumentTuple, readTuple, BoundaryValue.toVal, ih]

/-- Boundary arguments embedded in an empty real type for signature checks. -/
def boundaryArgs (args : List BoundaryValue) : List (Val Empty) := args.map BoundaryValue.toVal

/-- The logical cells owned by an assembly invocation. -/
def callFootprint (code : Code) (args : List BoundaryValue) : Finset Loc :=
  footprint code.sig.toCallSig (boundaryArgs args)

/-- A fragment with exactly the signature footprint and valid integer cell contents. -/
def validFragment (code : Code) (args : List BoundaryValue) (heap : LocHeap BoundaryValue) : Prop :=
  code.sig.valid = true ∧ heap = restrict (callFootprint code args) heap ∧
    check code.sig.toCallSig (boundaryArgs args) (valueHeap (rT := Empty) heap) = true

/-- An import response satisfying the scalar signature and fixed heap footprint. -/
def boundaryResponseOK (code : Code) (args : List BoundaryValue) (F : Finset Loc)
    (name : String) (r : BoundaryValue) (heap : LocHeap BoundaryValue) : Prop :=
  responseOK code (boundaryArgs args) F name r.toVal (valueHeap (rT := Empty) heap)

/-- The dispatcher action at a tree's root, with an archive for a future callback. -/
noncomputable def rootAction (archive : Replay) : Interaction BoundaryValue → Action
  | .ret value heap =>
    open Classical in
    if validFragment archive.code archive.args heap ∧
        checkResult archive.code.sig.toCallSig (boundaryArgs archive.args)
          archive.code.sig.result value.toVal = true
    then .ret value heap else .invalid
  | .call name args heap _ =>
    open Classical in
    if validFragment archive.code archive.args heap ∧
        ∃ sig, (name, sig) ∈ archive.code.sig.imports ∧
          check sig (boundaryArgs args) (valueHeap (rT := Empty) heap) = true
    then .call name args heap archive else .invalid

/-- Start a checked call from its restricted, integer-valued entry fragment. -/
noncomputable def start (M : AsmSemantics Code BoundaryValue) (code : Code)
    (args : List BoundaryValue) (heap : LocHeap BoundaryValue) : Action :=
  let F := callFootprint code args
  let entry := restrict F heap
  if code.sig.valid &&
      check code.sig.toCallSig (boundaryArgs args) (valueHeap (rT := Empty) entry) then
    match snapshot entry with
    | none => .invalid
    | some h₀ =>
      match M.eval code args F entry with
      | none => .stuck
      | some tree => rootAction ⟨code, args, h₀, []⟩ tree
  else .invalid

/-- Replay a paused call and resume it with the callback's current heap fragment. -/
noncomputable def resume (M : AsmSemantics Code BoundaryValue) (archive : Replay)
    (response : BoundaryValue) (heap : LocHeap BoundaryValue) : Action :=
  open Classical in
  let F := callFootprint archive.code archive.args
  let current := restrict F heap
  match M.eval archive.code archive.args F archive.entry.restore with
  | none => .stuck
  | some tree =>
    match tree.replay (archive.responses.map fun (r, h) => (r, h.restore)) with
    | none | some (.ret _ _) => .invalid
    | some (.call name _ _ next) =>
      if M.ResponseOK archive.code archive.args F name response current then
        match snapshot current with
        | none => .invalid
        | some h =>
          rootAction { archive with responses := archive.responses ++ [(response, h)] }
            (next response current)
      else .invalid

/-- A return-valued evaluator result determines the dispatcher's return action. -/
theorem start_ret_of_eval {M : AsmSemantics Code BoundaryValue}
    {code : Code} {args : List BoundaryValue} {heap output : LocHeap BoundaryValue}
    {value : BoundaryValue} {saved : HeapSnapshot}
    (hcheck : (code.sig.valid && check code.sig.toCallSig (boundaryArgs args)
      (valueHeap (rT := Empty) (restrict (callFootprint code args) heap))) = true)
    (hsaved : snapshot (restrict (callFootprint code args) heap) = some saved)
    (heval : M.eval code args (callFootprint code args)
      (restrict (callFootprint code args) heap) = some (.ret value output))
    (houtput : validFragment code args output ∧
      checkResult code.sig.toCallSig (boundaryArgs args) code.sig.result value.toVal = true) :
    start M code args heap = .ret value output := by
  classical
  simp only [start, hcheck, ite_true, hsaved,
    heval, rootAction, ite_eq_left houtput]

/-- A proved return-only machine specification determines the dispatcher's return action. -/
theorem start_ret {M : AsmSemantics Code BoundaryValue} (law : LawfulAsmSemantics M)
    {code : Code} {args : List BoundaryValue} {heap output : LocHeap BoundaryValue}
    {value : BoundaryValue} {saved : HeapSnapshot}
    (hcheck : (code.sig.valid && check code.sig.toCallSig (boundaryArgs args)
      (valueHeap (rT := Empty) (restrict (callFootprint code args) heap))) = true)
    (hsaved : snapshot (restrict (callFootprint code args) heap) = some saved)
    (hspec : M.Evaluates code args (callFootprint code args)
      (restrict (callFootprint code args) heap) (.ret value output))
    (houtput : validFragment code args output ∧
      checkResult code.sig.toCallSig (boundaryArgs args) code.sig.result value.toVal = true) :
    start M code args heap = .ret value output := by
  apply start_ret_of_eval hcheck hsaved _ houtput
  exact M.eval_eq_some law hspec

/-- Starting a foreign call ignores all cells outside its signature footprint. -/
theorem start_local (M : AsmSemantics Code BoundaryValue) (code : Code)
    (args : List BoundaryValue) (heap : LocHeap BoundaryValue) :
    start M code args heap = start M code args (restrict (callFootprint code args) heap) := by
  simp only [start, restrict_idem]

/-- Resuming a foreign call reads the callback's current footprint. -/
theorem resume_local (M : AsmSemantics Code BoundaryValue) (archive : Replay)
    (response : BoundaryValue) (heap : LocHeap BoundaryValue) :
    resume M archive response heap =
      resume M archive response (restrict (callFootprint archive.code archive.args) heap) := by
  simp only [resume, restrict_idem]
  rw [restrict_idem]

end ProbLang.Asm
