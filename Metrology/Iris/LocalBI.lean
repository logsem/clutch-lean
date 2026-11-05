module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public import Iris.BI.BI
public meta import Iris.BI.LocalBI
public import Metrology.Meta.Settings

/-!
# The `bi` clause of the `problang` panel

`bi T` sets the section's proposition type, as Iris's `local bi T` does.
-/

open Lean Elab Command Term Metrology.Settings

namespace Iris

public section

/-- Makes `T` the section's proposition type, checking that it has a `BI` instance. -/
meta def setBi (T : Term) : CommandElabM Unit := do
  runTermElabM fun _ => do
    let Te ← elabType T
    unless (← Meta.trySynthInstance (← Meta.mkAppM ``BI #[Te])) matches .some _ do
      throwError "`bi` requires a `BI` instance for{indentExpr Te}"
  biExt.add T .local

/-- `bi T` in the `problang` panel: `T` is the proposition type. -/
syntax (name := biOpt) &"bi " term : problang_opt

/-- Elaborates the `bi` clause. -/
@[command_elab Metrology.Settings.problangClauseCmd]
meta def elabBiOpt : CommandElab := fun stx => do
  let c := stx[1]
  unless c.isOfKind ``biOpt do throwUnsupportedSyntax
  setBi ⟨c[1]⟩

end

end Iris
