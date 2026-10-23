import MetrologyAsm.Diagnostics.Spike
import MetrologyAsm.Diagnostics.InstructionBody
import Lean

/-! # Sail execution smoke checks

Compiler observations use aliases with kernel-checked equality to the original Sail wrapper.
-/

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000
set_option maxErrors 1

open Lean

run_elab do
  let env ← getEnv
  let roots := [``MetrologyAsm.swapObservation, ``MetrologyAsm.addiObservation,
    ``MetrologyAsm.userInitial]
  let rec visit (fuel : Nat) (name : Name) (seen : NameSet) (out : Array Name) :
      NameSet × Array Name := Id.run do
    if fuel == 0 then return (seen, out)
    if seen.contains name then return (seen, out)
    let mut seen := seen.insert name
    let mut out := out
    if let some (.defnInfo info) := env.find? name then
      for dep in info.value.getUsedConstants do
        let (seen', out') := visit (fuel - 1) dep seen out
        seen := seen'
        out := out'
      if isNoncomputable env name &&
          ((`MetrologyAsm).isPrefixOf name || (`RiscvZkvm.Sail).isPrefixOf name) then
        out := out.push name
    return (seen, out)
  let mut seen : NameSet := {}
  let mut names := #[]
  for name in roots do
    let (seen', names') := visit 10000 name seen names
    seen := seen'
    names := names'
  logInfo m!"Compiling {names.size} definitionally equal execution aliases"
  let mut renamed : NameMap Name := {}
  for name in names do
    renamed := renamed.insert name ((`SailEval).append name)
  let rewrite := fun (e : Expr) => e.replace fun e =>
    match e with
    | .const name levels => (renamed.find? name).map fun n => .const n levels
    | _ => none
  for name in names do
    if let some (.defnInfo info) := env.find? name then
      addAndCompile <| .defnDecl { info with
        name := (renamed.find? name).getD name
        type := rewrite info.type
        value := rewrite info.value }

/-- info: true -/
#guard_msgs in
#eval SailEval.MetrologyAsm.userInitial.isSome
/-- info: some (some 7) -/
#guard_msgs in
#eval SailEval.MetrologyAsm.addiObservation
/-- info: some (99, 42, some 2147491840) -/
#guard_msgs in
#eval SailEval.MetrologyAsm.swapObservation

/-- The executable step alias is definitionally equal to the official Sail wrapper. -/
theorem evalStep_eq : SailEval.MetrologyAsm.rvStep = MetrologyAsm.rvStep := by rfl

/-- The executable swap observation is definitionally equal to the original observation. -/
theorem evalSwap_eq : SailEval.MetrologyAsm.swapObservation = MetrologyAsm.swapObservation := by rfl

#print axioms evalStep_eq
#print axioms evalSwap_eq
