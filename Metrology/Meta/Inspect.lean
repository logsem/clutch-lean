module

public import Lean

@[expose] public section

open Lean Elab Command Term Meta

/-! # `#inspect`

Prints the raw `Expr` tree of a term. -/

/-- The raw `Expr` tree of a term, with binder annotations (metadata is elided). -/
meta def inspectFormat : Lean.Expr → Format
  | .bvar i => .text s!"(bvar {i})"
  | .fvar i => .text s!"(fvar {i.name})"
  | .mvar i => .text s!"(mvar {i.name})"
  | .sort i => .text s!"(sort {i})"
  | .const n us => .text s!"(const{us} {n})"
  | .app fn arg => .group <|
      "(app " ++ .nest 2 (.align false ++ inspectFormat fn ++ " " ++ .align false ++
        inspectFormat arg) ++ ")"
  | .lam x ty b info => .group <|
      "(lam " ++ binder x (inspectFormat ty) info ++ " => " ++
        .nest 2 (.align false ++ .nest 2 (inspectFormat b)) ++ ")"
  | .forallE x ty b info => .group <|
      "(all " ++ binder x (inspectFormat ty) info ++ " => " ++
        .nest 2 (.align false ++ .nest 2 (inspectFormat b)) ++ ")"
  | .letE x ty v b dep => .group <|
      "(" ++ letDepFormat dep ++ s!" ({x} : " ++ inspectFormat ty ++ ") := " ++ .line ++
        inspectFormat v ++ " in " ++ .line ++ inspectFormat b ++ ")"
  | .lit v => .text s!"(lit {formatLit v})"
  | .mdata _ e => .text s!"(mdata [...] {inspectFormat e})"
  | .proj tn ix e => .text s!"(proj[{tn}.{ix}] {inspectFormat e})"
where
  inBinderParen (f : Format) : BinderInfo → Format
  | .default => "(" ++ f ++ ")"
  | .implicit => "{" ++ f ++ "}"
  | .strictImplicit => "{{" ++ f ++ "}}"
  | .instImplicit => "[" ++ f ++ "]"
  binder (x : Name) (ty : Format) (b : BinderInfo) : Format := inBinderParen (s!"{x} : " ++ ty) b
  letDepFormat : Bool → Format
  | true  => "dlet"
  | false => "let"
  formatLit : Literal → Format
  | .natVal n => s!"{n}"
  | .strVal s => repr s

syntax (name := inspect) "#inspect " term : command

/-- Elaborates `#inspect`. -/
@[command_elab inspect]
meta def inspectCore : CommandElab
  | `(#inspect $term) =>
    withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_inspect do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
      let e ← Term.levelMVarToParam (← instantiateMVars e)
      logInfo s!"{inspectFormat e}"
  | _ => throwUnsupportedSyntax
