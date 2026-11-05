module

public meta import Lean.Elab.Command
public import Metrology.TotalEris.ErisGS
public import Metrology.ProbLang.Syntax.Settings
public import Metrology.Iris.LocalBI

/-! # The Eris clause of the `problang` panel

`eris GF` declares the Eris ghost state of a section and makes its propositions the default. -/

open Lean Elab Command Metrology.Settings Iris

namespace ProbLang.TotalEris

public section

/-- `eris GF` declares the Eris ghost state `GF` (with any later-credit flag `hlc`) over the reals
and makes `IProp GF` the proposition type. -/
syntax (name := erisOpt) &"eris " ident : problang_opt

/-- Elaborates the `eris` clause. -/
@[command_elab Metrology.Settings.problangClauseCmd]
meta def elabErisOpt : CommandElab := fun stx => do
  let c := stx[1]
  unless c.isOfKind ``erisOpt do throwUnsupportedSyntax
  let rT : Term := ⟨← getSetting `reals "reals"⟩
  let GF : Ident := ⟨c[1]⟩
  let hlc := mkIdentFrom c `hlc
  elabCommand (← `(variable [ProbLangDist $rT]))
  if (← getSetting? `ffi).isNone then elabCommand (← `(variable [ProbLangFFI $rT]))
  elabCommand (← `(variable [ProbLangObs $rT] {$hlc : HasLC} {$GF : BundledGFunctors}
    [ErisGS $rT $hlc $GF]))
  elabCommand (← `(problang_clause bi IProp $GF))
  setSetting `eris GF

end

end ProbLang.TotalEris
