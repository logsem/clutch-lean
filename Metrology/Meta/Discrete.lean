module

public meta import Lean

@[expose] public section

open Lean Elab Command Term Meta

/-!
# The `@[discrete]` attribute

A `@[discrete]` declaration may only be referenced by other `@[discrete]` declarations;
other references trigger the `linter.discrete` warning at the use site.
Discrete declarations assume steps with atomic support (no `urand`), e.g. `wp_lift_step_later`;
the linter flags continuous developments that rely on them.
-/

namespace Metrology.Discrete

meta initialize discreteExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun es => es.foldl (fun s arr => arr.foldl (·.insert ·) s) {}
    addEntryFn    := fun s n => s.insert n
    toArrayFn     := fun es => es.toArray
  }

/-- Whether `declName` is marked `@[discrete]`. -/
meta def isDiscrete (env : Environment) (declName : Name) : Bool :=
  (discreteExt.getState env).contains declName

syntax (name := discrete) "discrete" : attr

meta initialize registerBuiltinAttribute {
  name  := `discrete
  descr := "Mark a definition as belonging to the discrete fragment. It may only be referenced \
    by other discrete definitions; non-discrete clients get a `linter.discrete` warning."
  add   := fun decl _stx _kind => do
    modifyEnv fun env => discreteExt.addEntry env decl
}

meta register_option linter.discrete : Bool := {
  defValue := true
  descr    := "if true, warn when a `@[discrete]` declaration is referenced from a \
    non-discrete declaration"
}

/-- The fully-qualified names defined by this command: its binder `.const` occurrences.
Parsing the surface `declId` instead would give unqualified names that miss `discreteExt`. -/
meta def definedNames (trees : Array Elab.InfoTree) : IO NameSet := do
  let acc : IO.Ref NameSet ← IO.mkRef {}
  for tree in trees do
    tree.visitM' (postNode := fun _ info _ => do
      let .ofTermInfo ti := info | return
      unless ti.isBinder do return
      let .const declName _ := ti.expr | return
      acc.modify (·.insert declName))
  acc.get

/-- Warns where a `@[discrete]` declaration is used by a non-discrete one. -/
meta def discreteUse : Linter where
  run := fun _cmdStx => do
    unless Linter.getLinterValue linter.discrete (← Linter.getLinterOptions) do return
    let env ← getEnv
    let trees := (← get).infoState.trees.toArray
    if (← definedNames trees).any (isDiscrete env ·) then
      return
    let warned : IO.Ref NameSet ← IO.mkRef {}
    for tree in trees do
      tree.visitM' (postNode := fun _ info _ => do
        let .ofTermInfo ti := info | return
        if ti.isBinder then return
        let .const declName _ := ti.expr | return
        unless isDiscrete env declName do return
        let some _ := info.range? | return
        let .original .. := info.stx.getHeadInfo | return
        if (← warned.get).contains declName then return
        warned.modify (·.insert declName)
        logWarningAt info.stx
          (.tagged linter.discrete.name
            m!"`{.ofConstName declName true}` is discrete and may only be referenced by \
              discrete declarations."))

meta initialize addLinter discreteUse

end Metrology.Discrete

end
