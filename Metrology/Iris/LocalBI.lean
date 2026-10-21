module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public import Iris.BI.BI

/-! # `local bi PROP`: a default separation-logic proposition type for a section -/

open Lean Elab Command Term

namespace Iris

public section

/-- The proposition type of the current section, as written in `local bi`. -/
public meta initialize biExt : SimpleScopedEnvExtension Syntax (Option Syntax) ←
  registerSimpleScopedEnvExtension {
    addEntry _ s := some s
    initial := none
  }

/-- The proposition type set by `local bi`, or a hole when none is set. -/
@[expose] elab "bi%" : term => do
  match biExt.getState (← getEnv) with
  | none => elabTerm (← `(_)) none
  | some T => elabType T

/-- `local bi T` makes `T` the proposition type of the entailment notations in this section. -/
syntax (name := biCmd) Lean.Parser.Term.attrKind &"bi " term : command

@[command_elab biCmd]
public meta def elabBiCmd : CommandElab := fun stx => do
  let `(command| $k:attrKind bi $T:term) := stx | throwUnsupportedSyntax
  unless (← liftMacroM <| toAttributeKind k) == .local do
    throwError "`bi` must be `local`: it sets the proposition type of the current section"
  runTermElabM fun _ => do
    let Te ← elabType T
    unless (← Meta.trySynthInstance (← Meta.mkAppM ``BI #[Te])) matches .some _ do
      throwError "`bi` requires a `BI` instance for{indentExpr Te}"
  biExt.add T .local

/-! ## Entailment notations that take their proposition type from `bi%` -/

open BI.BIBase

macro_rules | `(⊢ $P) => ``(EmpValid (PROP := bi%) iprop($P))
macro_rules | `($P ⊢ $Q) => ``(Entails (PROP := bi%) iprop($P) iprop($Q))
macro_rules | `($P ⊣⊢ $Q) => ``(BiEntails (PROP := bi%) iprop($P) iprop($Q))

end

end Iris
