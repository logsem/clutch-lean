module

public meta import Lean.Elab.Command
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.Meta.Settings

/-! # The `reals` and `ffi` clauses of the `problang` panel
`reals` sets the section's type of reals, which `rt%` reads and bare syntax families take; `ffi`
sets the section's foreign code. -/

open Lean Elab Command Term Metrology.Settings

namespace ProbLang

public section

/-- The section's type of reals, from the panel's `reals` clause, or a hole. -/
elab "rt%" : term => do
  match ← getSetting? `reals with
  | some T => elabType T
  | none => elabTerm (← `(_)) none

/-- `reals rT` declares a generic type of reals `rT : Type` (or `reals rT : U` with `rT : U`) with
its σ-algebra and laws. -/
syntax &"reals " ident (" : " term)? : problang_opt

/-- `reals := T` uses the type of reals `T`. -/
syntax &"reals " " := " term : problang_opt

/-- Elaborates the `reals` clause. -/
elab_rules : command
  | `(problang_clause reals $rT:ident $[: $U]?) => do
    let U ← U.getDM `(Type)
    elabCommand (← `(variable {$rT : $U} [MeasurableSpace $rT] [LawfulProbLangℝ $rT]))
    setSetting `reals rT
  | `(problang_clause reals := $T) => do
    runTermElabM fun _ => discard <| elabType T
    setSetting `reals T

/-- `ffi X` makes the foreign code `X` an instance for the rest of the section; it goes before
`micrometer` and `eris`, which then declare no foreign code of their own. -/
syntax &"ffi " ident : problang_opt

/-- Elaborates the `ffi` clause. -/
elab_rules : command
  | `(problang_clause ffi $X:ident) => do
    if (← getSetting? `micrometer).isSome || (← getSetting? `eris).isSome then
      throwError "`problang`: put `ffi` before `micrometer` and `eris`"
    elabCommand (← `(attribute [local instance] $X))
    setSetting `ffi X

end

end ProbLang
