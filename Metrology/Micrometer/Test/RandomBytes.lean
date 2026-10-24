module

public meta import Lean
import Metrology.Micrometer.Examples.RandomBytes
import Metrology.ProbLang.Interp.BigStepIO
meta import Metrology.Micrometer.Examples.RandomBytes
meta import Metrology.ProbLang.Interp.BigStepIO

/-! # Randombytes interpreter and axiom regression checks -/

open Lean Elab Command in
/-- Fail unless each named theorem depends only on the standard axioms. -/
elab "#assert_standard_axioms " ids:ident* : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axioms ← liftCoreM <| collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwErrorAt id "'{name}' depends on the axiom '{ax}'"

namespace ProbLang.RandomBytes.Test

open Exp (ofVal)

/-- Read an integer-valued cell from the test heap. -/
private def cellInt? (σ : State Float) (l : Loc) : Option Int := do
  let v ← σ.heap[l]?
  match v.fst with
  | .lit (.int z) => some z
  | _ => none

/-- The value of the sentinel cells around the output block. -/
private def sentinel : Int := -777

/-- The array lengths, repetitions per length and nonpositive lengths that the smoke test runs. -/
private def lengths : List Nat := [0, 1, 4, 32]
private def repetitions : Nat := 10
private def nonpositive : List Int := [0, -1, -100]

/-- Check every output byte and both surrounding sentinel cells. -/
private def checkFilled (e : Exp Float) (σ : State Float) (n : Nat) : Bool :=
  match e with
  | .pair (.lit (.loc l)) (.lit .unit) =>
    σ.heap.size == n + 2 && cellInt? σ l == some sentinel &&
      cellInt? σ (l + n + 1) == some sentinel &&
      (List.range n).all (fun i =>
        match cellInt? σ (l + i + 1) with
        | some b => decide (0 ≤ b ∧ b < 256)
        | none => false)
  | _ => false

/-- Allocate a byte block between two sentinel cells and invoke the tuple callback. -/
private def fillProgram (n : Nat) : Exp Float := pl%
  let ptr := allocN(#int (n + 2), #(-777));
  let answer := {ofVal randombytesValue} ((ptr +ₗ #1), (#int n, #()));
  (ptr, answer)

/-- Run both interpreters on byte arrays and check nonpositive lengths on an empty heap. -/
private def smoke : IO Unit := do
  for n in lengths do
    for _ in [:repetitions] do
      let r ← Interp.run (.eval [] (fillProgram n) default)
      unless checkFilled r.val.rb r.state n do
        throw (IO.userError s!"environment evaluator failed at n={n}")
      let s ← Interp.runSubst ⟨fillProgram n, default⟩
      unless checkFilled s.expr s.state n do
        throw (IO.userError s!"substitution evaluator failed at n={n}")
  for n in nonpositive do
    let r ← Interp.run (.eval []
      (pl% {ofVal randombytesValue} (#loc 123456, (#int n, #()))) default)
    unless r.state.heap.size == 0 do throw (IO.userError "nonpositive length changed heap")
    match r.val with
    | .lit .unit => pure ()
    | _ => throw (IO.userError "nonpositive length did not return unit")
  IO.println s!"randombytes: both interpreters passed {lengths.length * repetitions * 2} \
    array/frame cases and {nonpositive.length} empty-heap cases"

/-- info: randombytes: both interpreters passed 80 array/frame cases and 3 empty-heap cases -/
#guard_msgs in
#eval smoke

#assert_standard_axioms randombytes_steps fill_nonpos_steps byte_draw byte_draw_singleton wp_fill
  wp_randombytes

end ProbLang.RandomBytes.Test
