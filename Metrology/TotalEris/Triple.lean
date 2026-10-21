module

public import Metrology.TotalEris.TotalWeakestpre

@[expose] public section

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris.ErisWpGS
open Lean

namespace ProbLang
namespace TotalEris

/-!
# Hoare-triple syntax for `tglWp`

A total-correctness triple

```
[{ P }] e @ E [{ x, RET v; Q }]
```

means: from `P`, the program `e` terminates at a value of the form `v`, and `Q` holds
of the result. It abbreviates the continuation-passing entailment

```
⊢ ∀ Φ, P -∗ (∀ x, Q -∗ Φ v) -∗ tglWp E e Φ
```

so a triple is proved by `iintro %Φ HP HΦ` and used by `iapply`, which leaves the
precondition and the continuation as goals.

The mask `@ E` defaults to `⊤`, and the binder group before `RET` is optional. The
brackets are `[{ … }]` rather than `{{ … }}` because these are total triples: `e` is
claimed to terminate, not merely to be safe.

Nothing in a triple names the ambient `GF`, so a statement whose surroundings leave it
open must pin it once, by ascribing the precondition:

```
[{ (↯ ε : IProp GF) }] pl(&Gauss #()) @ E [{ y, RET .real y; ⌜|y| < t⌝ }]
```

This is the same pin `⊢@{IProp GF}` performs for a bare-`tglWp` statement, and is
needed for the same reason: `ECGS`/`ErisWpGS` do not take `GF` as an `outParam`, so
instance search will not run while it is a metavariable.

The shape is shared with the HeapLang triples of `Iris.BI.WeakestPre`. Both parses are
attempted and only one elaborates, so the two coexist.
-/

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

syntax (name := twpTriple) twpPre twpProg twpPost : term
syntax (name := twpTriplePinned) "⊢@{" term "} " twpPre twpProg twpPost : term

meta def parseTwpPre : TSyntax `twpPre → MacroM Term
  | `(twpPre| [{ $[$P]? }]) => P.getDM `(iprop(emp))
  | _ => Macro.throwUnsupported

meta def parseTwpProg : TSyntax `twpProg → MacroM (Term × Term)
  | `(twpProg| $e:term $[ @ $E:term]?) => return (e, ← E.getDM `(⊤))
  | _ => Macro.throwUnsupported

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
  | _ => Macro.throwUnsupported

@[macro twpTriple] meta def expandTwpTriple : Macro
  | `($pre:twpPre $prog:twpProg $post:twpPost) => do
    let P ← parseTwpPre pre
    let (e, E) ← parseTwpProg prog
    let k ← parseTwpPost post
    `(⊢ ∀ Φ, $P -∗ $k -∗ tglWp $E $e Φ)
  | _ => Macro.throwUnsupported

@[macro twpTriplePinned] meta def expandTwpTriplePinned : Macro
  | stx => do
    let #[_, PROP, _, pre, prog, post] := stx.getArgs | Macro.throwUnsupported
    let P ← parseTwpPre ⟨pre⟩
    let (e, E) ← parseTwpProg ⟨prog⟩
    let k ← parseTwpPost ⟨post⟩
    `(⊢@{$(⟨PROP⟩)} ∀ Φ, $P -∗ $k -∗ tglWp $E $e Φ)

end TotalEris
end ProbLang
