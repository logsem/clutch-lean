module

public import Metrology.TotalEris.TotalWeakestpre

/-!
# Hoare-triple syntax for `tglWp`

A total triple `[{ P }] e @ E [{ x, RET v; Q }]` abbreviates
`⊢ ∀ Φ, P -∗ (∀ x, Q -∗ Φ v) -∗ tglWp E e Φ`.
-/

@[expose] public section

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris.ErisWpGS
open Lean Macro

namespace ProbLang
namespace TotalEris

/-- The precondition of a total triple. -/
declare_syntax_cat twpPre
syntax " [" noWs "{ " (term:min)? " }" noWs "] " : twpPre

/-- The program of a total triple, with an optional mask. -/
declare_syntax_cat twpProg
syntax term:max (" @ " term:max)? : twpProg

/-- The postcondition of a total triple: binders, the returned value, and what holds of it. -/
declare_syntax_cat twpPost
syntax " [" noWs "{ " ((ppSpace (binderIdent <|> bracketedBinder))+ ", ")?
  "RET " term:min "; " term:min " }" noWs "] " : twpPost

/-- The total triple notation `[{ P }] e [{ RET v; Q }]`. -/
syntax (name := twpTriple) twpPre twpProg twpPost : term
/-- The total triple notation with the program logic instance pinned by `⊢@{PROP}`. -/
syntax (name := twpTriplePinned) "⊢@{" term "} " twpPre twpProg twpPost : term

/-- Reads the precondition of a total triple, defaulting to `emp`. -/
meta def parseTwpPre : TSyntax `twpPre → MacroM Term
  | `(twpPre| [{ $[$P]? }]) => P.getDM `(iprop(emp))
  | _ => throwUnsupported

/-- Reads the program and the mask of a total triple, defaulting the mask to `⊤`. -/
meta def parseTwpProg : TSyntax `twpProg → MacroM (Term × Term)
  | `(twpProg| $e:term $[ @ $E:term]?) => return (e, ← E.getDM `(⊤))
  | _ => throwUnsupported

/-- Reads the postcondition of a total triple as a continuation entailment. -/
meta def parseTwpPost : TSyntax `twpPost → MacroM Term
  | `(twpPost| [{ $[$[$xs]* ,]? RET $pat ; $Q }]) => do
    match xs with
    | some xs =>
      let xs : TSyntaxArray [`ident, `Lean.Parser.Term.hole,
          `Lean.Parser.Term.bracketedBinder] ← xs.mapM fun
        | `(binderIdent| _) => `(hole| _)
        | `(binderIdent| $i:ident) => `(ident| $i)
        | `(bracketedBinder| $x) => `(bracketedBinder| $x)
      `(iprop(∀ $xs*, $Q -∗ Φ $pat))
    | none => `(iprop($Q -∗ Φ $pat))
  | _ => throwUnsupported

/-- Expands a total triple into its `tglWp` entailment. -/
@[macro twpTriple] meta def expandTwpTriple : Macro
  | `($pre:twpPre $prog:twpProg $post:twpPost) => do
    let P ← parseTwpPre pre
    let (e, E) ← parseTwpProg prog
    let k ← parseTwpPost post
    `(⊢ ∀ Φ, $P -∗ $k -∗ tglWp $E $e Φ)
  | _ => throwUnsupported

/-- Expands a total triple with a pinned program logic instance. -/
@[macro twpTriplePinned] meta def expandTwpTriplePinned : Macro
  | stx => do
    let #[_, PROP, _, pre, prog, post] := stx.getArgs | throwUnsupported
    let P ← parseTwpPre ⟨pre⟩
    let (e, E) ← parseTwpProg ⟨prog⟩
    let k ← parseTwpPost ⟨post⟩
    `(⊢@{$(⟨PROP⟩)} ∀ Φ, $P -∗ $k -∗ tglWp $E $e Φ)

end TotalEris
end ProbLang
