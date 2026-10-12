module

public import Lean

@[expose] public section

open Lean Elab Command Term Meta

syntax (name := checkdef) "#checkdef " ident : command

@[command_elab checkdef]
meta def checkDefCore : CommandElab
  | `(#checkdef $decl) => do
    let some (.defnInfo info) := (← getEnv).constants.find? decl.getId | throwError "bad constant"
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
