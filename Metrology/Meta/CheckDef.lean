module

public import Lean

@[expose] public section

open Lean Elab Command Term Meta

/-! # `#checkdef`

Prints the type, value and reducibility hint of a definition. -/

syntax (name := checkdef) "#checkdef " ident : command

/-- Elaborates `#checkdef`. -/
@[command_elab checkdef]
meta def checkDefCore : CommandElab
  | `(#checkdef $decl) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
    let .defnInfo info ← getConstInfo name | throwError "bad constant"
    let .regular u := info.hints | throwError "not a regular definition"
    let .safe := info.safety | throwError "not safe"
    logInfo s!"Declaration {decl} is a definition\n\
               name: {info.name}\n\
               levelParams: {info.levelParams}\n\
               type: {info.type}\n\
               value: {info.value}\n\
               reducibility hint height: {u}\n\
               safe"
  | _ => throwUnsupportedSyntax

end
