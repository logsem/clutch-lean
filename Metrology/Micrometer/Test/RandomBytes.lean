module

import Metrology.Micrometer.Examples.RandomBytes
import Metrology.ProbLang.Interp.BigStepIO
meta import Metrology.Micrometer.Examples.RandomBytes
meta import Metrology.ProbLang.Interp.BigStepIO

/-! # Randombytes interpreter and axiom regression checks -/

namespace ProbLang.RandomBytes.Test

open Exp (ofVal)

/-- Read an integer-valued cell from the test heap. -/
private def cellInt? (σ : State Float) (l : Loc) : Option Int := do
  let v ← σ.heap[l]?
  match v.fst with
  | .lit (.int z) => some z
  | _ => none

/-- Check every output byte and both surrounding sentinel cells. -/
private def checkFilled (e : Exp Float) (σ : State Float) (n : Nat) : Bool :=
  match e with
  | .pair (.lit (.loc l)) (.lit .unit) =>
    σ.heap.size == n + 2 && cellInt? σ l == some (-777) && cellInt? σ (l + n + 1) == some (-777) &&
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
  for n in [0, 1, 4, 32] do
    for _ in [:10] do
      let r ← Interp.run (.eval [] (fillProgram n) default)
      unless checkFilled r.val.rb r.state n do
        throw (IO.userError s!"environment evaluator failed at n={n}")
      let s ← Interp.runSubst ⟨fillProgram n, default⟩
      unless checkFilled s.expr s.state n do
        throw (IO.userError s!"substitution evaluator failed at n={n}")
  for n in [0, -1, -100] do
    let r ← Interp.run (.eval []
      (pl% {ofVal randombytesValue} (#loc 123456, (#int n, #()))) default)
    unless r.state.heap.size == 0 do throw (IO.userError "nonpositive length changed heap")
    match r.val with
    | .lit .unit => pure ()
    | _ => throw (IO.userError "nonpositive length did not return unit")
  IO.println "randombytes: both interpreters passed 80 array/frame cases and 3 empty-heap cases"

/-- info: randombytes: both interpreters passed 80 array/frame cases and 3 empty-heap cases -/
#guard_msgs in
#eval smoke

/--
info: 'ProbLang.RandomBytes.randombytes_steps' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms randombytes_steps

/--
info: 'ProbLang.RandomBytes.fill_nonpos_steps' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fill_nonpos_steps

/--
info: 'ProbLang.RandomBytes.byte_draw' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms byte_draw

/--
info: 'ProbLang.RandomBytes.byte_draw_singleton' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms byte_draw_singleton

/--
info: 'ProbLang.RandomBytes.wp_fill' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wp_fill

/--
info: 'ProbLang.RandomBytes.wp_randombytes' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wp_randombytes

end ProbLang.RandomBytes.Test
