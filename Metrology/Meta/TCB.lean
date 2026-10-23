module

public meta import Lean

/-! # Statement dependency auditing -/

public meta section

open Lean Elab Command

namespace Metrology.TCB

/-- The constants reachable through declaration types and non-theorem bodies. -/
partial def dependencies (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then dependencies env rest seen else
    let seen := seen.insert name
    match env.find? name with
    | none => dependencies env rest seen
    | some info =>
      let body := if info.isTheorem then #[] else
        (info.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
      let constructors := match info with
        | .inductInfo v => v.ctors
        | _ => []
      dependencies env
        (info.type.getUsedConstants.toList ++ body.toList ++ constructors ++ rest) seen

/-- Print project statement dependencies and the theorem's kernel axiom dependencies. -/
elab "#tcb " decl:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  let env ← getEnv
  let some info := env.find? name | throwError "unknown declaration {name}"
  let deps := dependencies env info.type.getUsedConstants.toList
  let names := deps.toArray.qsort Name.lt
  let mut project : Array Name := #[]
  let axioms ← collectAxioms name
  let mut unavailable : Array Name := #[]
  for n in names do
    let moduleName := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    if (`Metrology).isPrefixOf moduleName || (`MetrologyAsm).isPrefixOf moduleName then
      if let some ci := env.find? n then
        let isProof ← liftTermElabM <| Meta.isProp ci.type
        if !isProof then
          project := project.push n
          if ci.isAxiom && !axioms.contains n then unavailable := unavailable.push n
  logInfo m!"TCB of {name}: {deps.size} reachable constants, \
    {project.size} project definitions and type constructors.\nTheorem axioms: {axioms}"
  let mut modules : NameMap (Array Name) := {}
  for n in project do
    let moduleName := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    modules := modules.insert moduleName ((modules.find? moduleName).getD #[] |>.push n)
  let groups := modules.toArray.map fun (moduleName, declarations) => Json.mkObj [
    ("module", toJson moduleName.toString),
    ("declarations", toJson (declarations.map Name.toString))]
  let receipt := Json.mkObj [("theorem", toJson name.toString),
    ("axioms", toJson (axioms.map Name.toString)),
    ("unavailable_bodies", toJson (unavailable.map Name.toString)), ("groups", Json.arr groups)]
  logInfo m!"TCBJSON {receipt.compress}"
  for (moduleName, declarations) in modules.toArray do
    let mut lines : Std.HashSet Nat := {}
    let mut missing : Nat := 0
    for n in declarations do
      if let some ranges ← findDeclarationRanges? n then
        for line in [ranges.range.pos.line:ranges.range.endPos.line + 1] do
          lines := lines.insert line
      else missing := missing + 1
    logInfo m!"{moduleName}: {declarations.size} declarations, \
      {lines.size} distinct source lines, {missing} missing ranges.\n{declarations}"

end Metrology.TCB
