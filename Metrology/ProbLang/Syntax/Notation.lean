module

public meta import Lean.PrettyPrinter.Delaborator
public meta import Lean.PrettyPrinter.Parenthesizer
public meta import Lean.Elab.Term
public import Metrology.ProbLang.Syntax.Syntax
public meta import Metrology.ProbLang.Syntax.Syntax

@[expose] public section

/-! # Surface syntax for ProbLang

Parses `pl% …` / `pl(…)` into `Exp` (binders closed to de Bruijn form by `Exp.close`), and prints
`Exp` back as `pl(…)` with source binder names. -/

namespace ProbLang

open Lean Lean.Elab Lean.Elab.Term Lean.PrettyPrinter Lean.Meta Lean.Parser

/-- Controls rendering of ProbLang type annotations. `0` hide all, `1` show
    annotations on let/fun/rec binders only, `2` show every annotation. -/
meta register_option pp.problang.annot : Nat := {
  defValue := 0
  descr := "ProbLang: display type annotations (0=none | 1=binders | 2=all)"
}

/-! ## Grammar -/

declare_syntax_cat pl_exp
declare_syntax_cat pl_ty
declare_syntax_cat pl_arg
declare_syntax_cat pl_pat

syntax:max "pl(" pl_exp ")" : term
syntax:max "pl_ty(" pl_ty ")" : term
syntax:max "pl_pat(" pl_pat ")" : term

/-! ### `pl% e`: entry without a closing paren, as in HeapLang's `hl% e` -/
syntax:min "pl% " pl_exp:min : term
syntax:min "pl_ty% " pl_ty:min : term
syntax:min "pl_pat% " pl_pat:min : term
macro_rules
  | `(pl% $e)     => `(pl($e))
  | `(pl_ty% $τ)  => `(pl_ty($τ))
  | `(pl_pat% $p) => `(pl_pat($p))

/-! ## `plBinderHint! name τ? e`: `e` wrapped in mdata carrying the binder's display name

The elaborator wraps each binder in this so the printer can recover the source name that
`Exp.close` erased. The `τ?` slot is parsed but unused, reserved for type-annotation rendering. -/

syntax (name := plBinderHint) "plBinderHint!" str term:max term:max : term

/-- The `mdata` key under which `plBinderHint!` stores a binder's source name. -/
meta def plBinderNameKey : Name := `ProbLang.plBinderName

/-- Elaborates `e` and wraps it in `mdata` carrying the binder name. -/
@[term_elab plBinderHint]
meta def elabPlBinderHint : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  let `(plBinderHint! $nameStr:str $_τ $eTerm) := stx
    | throwError "plBinderHint!: unexpected syntax"
  let e ← Lean.Elab.Term.elabTerm eTerm expectedType?
  let kv := ({} : KVMap).insert plBinderNameKey (DataValue.ofString nameStr.getString)
  return Expr.mdata kv e

syntax binderIdent : pl_arg
syntax "(" ident " : " pl_ty ")" : pl_arg

-- Types
syntax:max "int"                                                : pl_ty
syntax:max "bool"                                               : pl_ty
syntax:max "unit"                                               : pl_ty
syntax:max "real"                                               : pl_ty
syntax:max "(" pl_ty ")"                                        : pl_ty
syntax:35 pl_ty:36 " × " pl_ty:35                               : pl_ty
syntax:30 pl_ty:31 " + " pl_ty:30                               : pl_ty
syntax:25 pl_ty:26 " → " pl_ty:25                              : pl_ty
syntax:max "ref(" pl_ty ")"                                     : pl_ty
syntax:max "tape"                                               : pl_ty

-- Patterns
syntax:max "_"                                                  : pl_pat
syntax:max ident                                                : pl_pat
syntax:max "#" term:max                                         : pl_pat
syntax:max "(" pl_pat ")"                                       : pl_pat
syntax:max "(" pl_pat ", " pl_pat ")"                           : pl_pat
syntax:max "inl(" pl_pat ")"                                    : pl_pat
syntax:max "inr(" pl_pat ")"                                    : pl_pat
syntax:max "(" pl_pat " : " pl_ty ")"                           : pl_pat

-- Expressions
-- Lean-term escapes: `{t}` for any term, `&t` for an atom (`&(g x)` for compound terms).
syntax:max "{" term "}"                                         : pl_exp
syntax:max "&" term:max                                         : pl_exp
syntax:max "#" term:max                                         : pl_exp
syntax:max ident                                                : pl_exp
syntax:max "(" pl_exp ")"                                       : pl_exp
syntax:max "(" pl_exp " : " pl_ty ")"                           : pl_exp
syntax:65 pl_exp:65 " + " pl_exp:66                             : pl_exp
syntax:65 pl_exp:65 " - " pl_exp:66                             : pl_exp
syntax:70 pl_exp:70 " * " pl_exp:71                             : pl_exp
syntax:70 pl_exp:70 " / " pl_exp:71                             : pl_exp
syntax:70 pl_exp:70 " % " pl_exp:71                             : pl_exp
syntax:50 pl_exp:50 " < " pl_exp:50                             : pl_exp
syntax:50 pl_exp:50 " <= " pl_exp:50                            : pl_exp
syntax:60 pl_exp:60 " && " pl_exp:61                            : pl_exp
syntax:55 pl_exp:55 " || " pl_exp:56                            : pl_exp
syntax:58 pl_exp:58 " ^^ " pl_exp:59                            : pl_exp
syntax:50 pl_exp:50 " = " pl_exp:50                             : pl_exp
syntax:10 "if " pl_exp " then " pl_exp " else " pl_exp          : pl_exp
syntax:75 "~" pl_exp:75                                         : pl_exp
syntax:100 "toReal(" pl_exp ")"                                 : pl_exp
syntax:100 "frac(" pl_exp ")"                                   : pl_exp
syntax:75 "-" pl_exp:75                                         : pl_exp
syntax:100 pl_exp:100 colGt ppSpace pl_exp:101                  : pl_exp
syntax:10 "let " pl_arg " := " pl_exp:10 "; " pl_exp:1          : pl_exp
syntax:5 pl_exp:6 "; " pl_exp:5                                 : pl_exp
syntax:10 "fun" pl_arg+ ", " pl_exp:10                          : pl_exp
syntax:10 "rec " pl_arg ppSpace pl_arg+ " := " pl_exp:10        : pl_exp
syntax:max "(" pl_exp ", " pl_exp,+ ")"                         : pl_exp
syntax:100 "fst(" pl_exp ")"                                    : pl_exp
syntax:100 "snd(" pl_exp ")"                                    : pl_exp
syntax:100 "inl(" pl_exp ")"                                    : pl_exp
syntax:100 "inr(" pl_exp ")"                                    : pl_exp
syntax:10 "case " pl_exp " | " pl_pat " => " pl_exp:10
          (" | " pl_pat " => " pl_exp:10)*                      : pl_exp
-- Raw `Exp.case`, no `scrut`: steps on any `inl`/`inr` head even when the payload is
-- abstract (where `Pat.tryMatch` is stuck). Use it for library code verified on symbolic data.
syntax:10 "case! " pl_exp " | " pl_pat " => " pl_exp:10
          " | " pl_pat " => " pl_exp:10                         : pl_exp
syntax:100 "alloc(" pl_exp ")"                                  : pl_exp
syntax:80 "!" pl_exp:80                                         : pl_exp
syntax:80 pl_exp:80 " ← " pl_exp:80                            : pl_exp
syntax:100 "tape(" pl_exp ")"                                   : pl_exp
syntax:100 "rand(" pl_exp ", " pl_exp ")"                       : pl_exp
syntax:10 "scrut " pl_exp " with " pl_pat                       : pl_exp
syntax:max "fail"                                               : pl_exp
syntax:max "urand"                                              : pl_exp
syntax:10 "let! " pl_pat " := " pl_exp:10 "; " pl_exp:1         : pl_exp
syntax:100 "assert(" pl_exp ")"                                 : pl_exp
-- Display-only: a bare `Exp.bvar n` left by `open'`/`openRec`, which erase binder name hints.
syntax:max "⟪bvar " term:max "⟫"                                : pl_exp

/-! ## Category parenthesizers

As in HeapLang's `hl_exp.parenthesizer`: the delaborator emits unparenthesized syntax and
the pretty-printer adds parentheses only where precedence demands (`int × (bool + unit)`). -/

open Lean.PrettyPrinter.Parenthesizer in
@[category_parenthesizer pl_exp]
meta def pl_exp.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `pl_exp false (fun stx => Unhygienic.run `(pl_exp|($(⟨stx⟩)))) prec <|
    parenthesizeCategoryCore `pl_exp prec

open Lean.PrettyPrinter.Parenthesizer in
@[category_parenthesizer pl_ty]
meta def pl_ty.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `pl_ty false (fun stx => Unhygienic.run `(pl_ty|($(⟨stx⟩)))) prec <|
    parenthesizeCategoryCore `pl_ty prec

/-- Words that cannot name a ProbLang variable. -/
meta def reservedKeywords : List String :=
  ["fst", "snd", "inl", "inr", "alloc", "tape", "rand", "fail", "urand", "scrut",
   "if", "then", "else", "let", "fun", "rec", "case"]

/-- Rejects an identifier that is a `reservedKeywords` entry. -/
meta def checkNotReserved (i : Lean.Ident) : TermElabM Unit := do
  let s := i.getId.toString
  if reservedKeywords.contains s then
    throwErrorAt i "'{s}' is a reserved keyword in ProbLang and cannot be used as an identifier"

/-! ## Type elaboration -/

macro_rules
  | `(pl_ty(int))          => `(Ty.int)
  | `(pl_ty(bool))         => `(Ty.bool)
  | `(pl_ty(unit))         => `(Ty.unit)
  | `(pl_ty(real))         => `(Ty.real)
  | `(pl_ty(($τ)))         => `(pl_ty($τ))
  | `(pl_ty($τ1 × $τ2))    => `(Ty.prod pl_ty($τ1) pl_ty($τ2))
  | `(pl_ty($τ1 + $τ2))    => `(Ty.sum pl_ty($τ1) pl_ty($τ2))
  | `(pl_ty($τ1 → $τ2))   => `(Ty.arrow pl_ty($τ1) pl_ty($τ2))
  | `(pl_ty(ref($τ)))      => `(Ty.ref pl_ty($τ))
  | `(pl_ty(tape))         => `(Ty.tape)

/-! ## Pattern elaboration -/

macro_rules
  | `(pl_pat(_))                  => `(Pat.wildcard)
  -- A variable matches anything; `projectPattern` binds it from the bindings `scrut` returns.
  | `(pl_pat($_:ident))           => `(Pat.wildcard)
  | `(pl_pat(# $e))               => `(Pat.lit $e)
  | `(pl_pat(($p)))               => `(pl_pat($p))
  | `(pl_pat(($p1, $p2)))         => `(Pat.pair pl_pat($p1) pl_pat($p2))
  | `(pl_pat(inl($p)))            => `(Pat.inl pl_pat($p))
  | `(pl_pat(inr($p)))            => `(Pat.inr pl_pat($p))

/-! ## Expression elaboration

`case` compiles to `scrut` plus a chain of `Exp.case`. -/

/-- Source names in scope, mapped to their fresh atoms. -/
abbrev NameEnv := Lean.NameMap Var

/-- Fresh-atom counter for one `pl(…)` elaboration. -/
structure AtomState where
  next : Nat := 0

/-- Returns a fresh `Var.internal` atom. -/
meta def genAtom (st : IO.Ref AtomState) : TermElabM Var := do
  let s ← st.get
  st.set { next := s.next + 1 }
  return .internal s.next

/-- A user-named binder: its identifier, fresh atom and optional type annotation. -/
structure NamedBinder where
  ident : Lean.Ident
  atom  : Var
  ty    : Option (TSyntax `pl_ty)

/-- Binds `i` to a fresh atom, extending `env`. -/
meta def bindNamed (st : IO.Ref AtomState) (env : NameEnv) (i : Lean.Ident)
    (ty : Option (TSyntax `pl_ty)) :
    TermElabM (NamedBinder × NameEnv) := do
  checkNotReserved i
  let atom ← genAtom st
  return ({ ident := i, atom, ty }, env.insert i.getId atom)

/-- The `Var` as a syntax term. -/
meta def quoteVar : Var → TermElabM Term
  | .named s    => `(Var.named $(Syntax.mkStrLit s))
  | .internal n => `(Var.internal $(Syntax.mkNatLit n))

/-! ### Binder constructors, each wrapped in `plBinderHint!` -/

/-- An optional type annotation as an `Option Ty` term. -/
meta def tyOptTerm (τ : Option (TSyntax `pl_ty)) : TermElabM Term := do
  match τ with
  | some τ' => `((some pl_ty($τ')))
  | none    => `((none : Option Ty))

/-- `head body` wrapped in `plBinderHint!` with the binder's display name. -/
meta def wrapHint (head : Term) (name : Option String) (τ : Option (TSyntax `pl_ty))
    (body : Term) : TermElabM Term := do
  let nm := name.getD "_"
  `(plBinderHint! $(Syntax.mkStrLit nm) $(← tyOptTerm τ) ($head $body))

/-- A binder that binds nothing: the body has no dangling indices (inner binders are closed as they
are built), so no `close`/shift is needed. -/
meta def mkAnonLam (body : Term) : TermElabM Term := do
  wrapHint (← `(Exp.lam)) none none body

/-- Binder for a synthetic atom (the `case`/`let!` scrutinee): no user name to display. -/
meta def closeAnonLam (body : Term) (atom : Var) : TermElabM Term := do
  let closed ← ``(Exp.close $body $(← quoteVar atom))
  wrapHint (← `(Exp.lam)) none none closed

/-- `head (Exp.close body atom)` for a named binder, hinted with its name. -/
meta def closeNamedHead (head : Term) (b : NamedBinder) (body : Term) : TermElabM Term := do
  let closed ← ``(Exp.close $body $(← quoteVar b.atom))
  wrapHint head (some b.ident.getId.toString) b.ty closed

/-- `fun b, body`: `Exp.lam` over `body` closed at `b`. -/
meta def mkNamedLam (b : NamedBinder) (body : Term) : TermElabM Term := do
  closeNamedHead (← `(Exp.lam)) b body

/-- `Exp.fix` over `body` closed at `b`. -/
meta def mkNamedFix (b : NamedBinder) (body : Term) : TermElabM Term := do
  closeNamedHead (← `(Exp.fix)) b body

mutual

/-- Translates `pl_exp` syntax to an `Exp` term. `env` maps in-scope source names to fresh
`.internal` atoms; each binder `Exp.close`s its atom right away, so atoms never escape. An unbound
identifier `x` becomes `fvar (.named "x")`. -/
meta partial def elabPL (env : NameEnv) (st : IO.Ref AtomState) :
    TSyntax `pl_exp → TermElabM Term
  | `(pl_exp|($e : $τ)) => do
      `(Exp.annotated pl_ty($τ) $(← elabPL env st e))
  | `(pl_exp|($e))         => elabPL env st e
  | `(pl_exp|{$t})         => `(($t))
  | `(pl_exp|&$t)          => `(($t))
  | `(pl_exp|# $n:num)     => `(Exp.lit (.int $n))
  | `(pl_exp|#true)        => `(Exp.lit (.bool true))
  | `(pl_exp|#false)       => `(Exp.lit (.bool false))
  | `(pl_exp|# $e)         => `(Exp.lit $e)
  | `(pl_exp|$i:ident)     => do
      checkNotReserved i
      let atomStr := env.find? i.getId |>.getD i.getId.toString
      `(Exp.fvar $(← quoteVar atomStr))
  | `(pl_exp|$e1 + $e2)    => do `(Exp.binop .plus  $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 - $e2)    => do `(Exp.binop .minus $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 * $e2)    => do `(Exp.binop .mult  $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 / $e2)    => do `(Exp.binop .div   $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 % $e2)    => do `(Exp.binop .mod   $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 < $e2)    => do `(Exp.binop .lt    $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 <= $e2)   => do `(Exp.binop .le    $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 && $e2)   => do `(Exp.binop .and   $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 || $e2)   => do `(Exp.binop .or    $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 ^^ $e2)   => do `(Exp.binop .xor   $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 = $e2)    => do `(Exp.binop .eq    $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|~$e)          => do `(Exp.unop  .neg   $(← elabPL env st e))
  | `(pl_exp|-$e)          => do `(Exp.unop  .minus $(← elabPL env st e))
  | `(pl_exp|toReal($e))   => do `(Exp.unop  .toReal $(← elabPL env st e))
  | `(pl_exp|frac($e))     => do `(Exp.unop  .frac  $(← elabPL env st e))
  | `(pl_exp|if $ec then $et else $ef) => do
      `(Exp.cond $(← elabPL env st ec) $(← elabPL env st et) $(← elabPL env st ef))
  | `(pl_exp|$e1 $e2)      => do `(Exp.app $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|fun $x:pl_arg $xs:pl_arg* , $body) => do
      let body' ← if xs.size = 0 then pure body else `(pl_exp|fun $xs*, $body)
      elabBindArg env st x body' mkNamedLam
  | `(pl_exp|rec $f:pl_arg $x:pl_arg $xs:pl_arg* := $body) => do
      -- `rec f x ... := b` is `Exp.fix` over `fun x ..., b`.
      let lamBody : TSyntax `pl_exp ← `(pl_exp|fun $x $xs*, $body)
      elabBindArg env st f lamBody mkNamedFix
  | `(pl_exp|($e1, $e2))         => do `(Exp.pair $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|($e1, $e2, $es,*))  => do
      let rest ← `(pl_exp|($e2, $es,*))
      `(Exp.pair $(← elabPL env st e1) $(← elabPL env st rest))
  | `(pl_exp|fst($e))            => do `(Exp.fst $(← elabPL env st e))
  | `(pl_exp|snd($e))            => do `(Exp.snd $(← elabPL env st e))
  | `(pl_exp|inl($e))            => do `(Exp.inl $(← elabPL env st e))
  | `(pl_exp|inr($e))            => do `(Exp.inr $(← elabPL env st e))
  | `(pl_exp|alloc($e))          => do `(Exp.alloc $(← elabPL env st e))
  | `(pl_exp|! $e)               => do `(Exp.load $(← elabPL env st e))
  | `(pl_exp|$e1 ← $e2)         => do `(Exp.store $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|tape($e))           => do `(Exp.tape $(← elabPL env st e))
  | `(pl_exp|rand($e1, $e2))     => do `(Exp.rand $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|let $a:pl_arg := $e1; $e2) => do
      let v1 ← elabPL env st e1
      let lam ← elabBindArg env st a e2 mkNamedLam
      `(Exp.app $lam $v1)
  | `(pl_exp|$e1; $e2) => do
      let v1 ← elabPL env st e1
      let lam ← mkAnonLam (← elabPL env st e2)
      `(Exp.app $lam $v1)
  | `(pl_exp|case! $e | $p1 => $bl | $p2 => $br) => do
      let patToArg (p : TSyntax `pl_pat) : TermElabM (TSyntax `pl_arg) := do
        match p with
        | `(pl_pat|$i:ident) => `(pl_arg|$i:ident)
        | `(pl_pat|_) => `(pl_arg|_)
        | _ => throwErrorAt p "case!: branch binder must be a variable or `_`"
      let xl ← match p1 with
        | `(pl_pat|inl($q)) => patToArg q
        | _ => throwErrorAt p1 "case!: first branch must be `inl(x)`"
      let xr ← match p2 with
        | `(pl_pat|inr($q)) => patToArg q
        | _ => throwErrorAt p2 "case!: second branch must be `inr(x)`"
      let brL ← elabBindArg env st xl bl mkNamedLam
      let brR ← elabBindArg env st xr br mkNamedLam
      `(Exp.case $(← elabPL env st e) $brL $brR)
  | `(pl_exp|scrut $e with $p)   => do `(Exp.scrut $(← elabPL env st e) pl_pat($p))
  | `(pl_exp|let! $p:pl_pat := $e; $body) => do
      elabPL env st (← `(pl_exp|case $e | $p => $body))
  | `(pl_exp|case $e | $p:pl_pat => $b $[| $ps:pl_pat => $bs]*) => do
      -- `(λ scrut. <chain>) e`, where `<chain>` tries each pattern and falls through to `fail`.
      let scrutAtom ← genAtom st
      let chain ← buildCaseChain env st scrutAtom (#[p] ++ ps) (#[b] ++ bs)
      let lam ← closeAnonLam chain scrutAtom
      `(Exp.app $lam $(← elabPL env st e))
  | `(pl_exp|⟪bvar $n⟫)          => `(Exp.bvar $n)
  | `(pl_exp|fail)               => `(Exp.fail)
  | `(pl_exp|urand)              => `(Exp.urand)
  | `(pl_exp|assert($e))         => do
      elabPL env st (← `(pl_exp|if $e then #.unit else fail))
  | e => throwErrorAt e s!"unrecognised pl expression: {e}"

/-- Elaborates the body of a binder under its argument pattern, building the lambda with `named`. -/
meta partial def elabBindArg (env : NameEnv) (st : IO.Ref AtomState)
    (arg : TSyntax `pl_arg) (body : TSyntax `pl_exp)
    (named : NamedBinder → Term → TermElabM Term) : TermElabM Term := do
  match arg with
  | `(pl_arg|$i:ident) =>
      let (b, env') ← bindNamed st env i none
      named b (← elabPL env' st body)
  | `(pl_arg|$_:binderIdent) => mkAnonLam (← elabPL env st body)
  | `(pl_arg|($i:ident : $τ)) =>
      let (b, env') ← bindNamed st env i (some τ)
      named b (← elabPL env' st body)
  | _ => throwErrorAt arg "unrecognised pl_arg"

/-- A `case` branch: a lambda over the bindings tree that `scrut` returns, projecting each
pattern variable out of it (`projectPattern`). -/
meta partial def mkCaseBranch (env : NameEnv) (st : IO.Ref AtomState)
    (pat : TSyntax `pl_pat) (body : TSyntax `pl_exp) : TermElabM Term := do
  let atom ← genAtom st
  let projected ← projectPattern env st pat atom body
  closeAnonLam projected atom

/-- Destructure `scrutAtom` by `pat` around `body`: `collect` binds every pattern variable
(so `body` elaborates under all of them), then `emit` wraps `body` in one `(λ v. …) proj`
per variable, `proj` a `fst`/`snd` path into `scrutAtom`. -/
meta partial def projectPattern (env : NameEnv) (st : IO.Ref AtomState)
    (pat : TSyntax `pl_pat) (scrutAtom : Var)
    (body : TSyntax `pl_exp) : TermElabM Term := do
  let rec collect (env : NameEnv) (acc : Lean.NameMap NamedBinder)
      (pat : TSyntax `pl_pat) : TermElabM (NameEnv × Lean.NameMap NamedBinder) := do
    match pat with
    | `(pl_pat|$i:ident) => do
        let (b, env') ← bindNamed st env i none
        return (env', acc.insert i.getId b)
    | `(pl_pat|($p)) | `(pl_pat|($p : $_))
    | `(pl_pat|inl($p)) | `(pl_pat|inr($p)) => collect env acc p
    | `(pl_pat|($p1, $p2)) => do
        let (env1, acc1) ← collect env acc p1
        collect env1 acc1 p2
    | _ => return (env, acc)
  let (envFull, binders) ← collect env ∅ pat
  let bodyTerm ← elabPL envFull st body
  let scrutExp : TSyntax `pl_exp ← `(pl_exp|{Exp.fvar $(← quoteVar scrutAtom)})
  let rec emit (pat : TSyntax `pl_pat) (proj : TSyntax `pl_exp)
      (inner : Term) : TermElabM Term := do
    match pat with
    | `(pl_pat|$i:ident) => do
        let some b := binders.find? i.getId
          | throwError "projectPattern: atom not found for {i.getId}"
        `(Exp.app $(← mkNamedLam b inner) $(← elabPL env st proj))
    | `(pl_pat|($p)) | `(pl_pat|($p : $_))
    | `(pl_pat|inl($p)) | `(pl_pat|inr($p)) => emit p proj inner
    | `(pl_pat|($p1, $p2)) => do
        let rhs ← emit p2 (← `(pl_exp|snd($proj))) inner
        emit p1 (← `(pl_exp|fst($proj))) rhs
    | _ => return inner
  emit pat scrutExp bodyTerm

/-- Fold `case v | p₁ => b₁ | … | pₙ => bₙ` right-to-left into nested `Exp.case`, ending in
`Exp.fail`. -/
meta partial def buildCaseChain (env : NameEnv) (st : IO.Ref AtomState)
    (scrutAtom : Var)
    (pats : Array (TSyntax `pl_pat)) (bodies : Array (TSyntax `pl_exp)) : TermElabM Term := do
  let scrutExp : Term ← `(Exp.fvar $(← quoteVar scrutAtom))
  let mut result : Term ← `(Exp.fail)
  for i in List.range pats.size |>.reverse do
    let branch ← mkCaseBranch env st pats[i]! bodies[i]!
    let fallback ← mkAnonLam result
    result ← `(Exp.case (Exp.scrut $scrutExp pl_pat($(pats[i]!))) $branch $fallback)
  return result

end

/-! ### Entry point -/

/-- `pl(e)`: elaborate `e` with a fresh atom counter and an empty name environment. -/
elab_rules : term
  | `(pl($e)) => do
      let st ← IO.mkRef ({} : AtomState)
      let t ← elabPL {} st e
      Lean.Elab.Term.elabTerm t none

end ProbLang

/-! ## Pretty-printing

Unexpanders print the constructors; delaborators recover binder and variable names for
`Exp.lam`, `Exp.fix`, `Exp.close`, `Exp.bvar` and `Exp.fvar`. -/

namespace ProbLang

open Lean Lean.PrettyPrinter

/-- Strip `pl(...)`; escape any other term as `&i` (identifier) or `{t}`. -/
meta def unpackPLExp [Monad m] [MonadQuotation m] : Term → m (TSyntax `pl_exp)
  | `(pl($e))     => `(pl_exp|$e)
  | `($i:ident)   => `(pl_exp|&$i)
  | `($t)         => `(pl_exp|{$t})

/-- Strips `pl_ty(...)`; panics on any other term. -/
meta def unpackPLTy [Monad m] [MonadQuotation m] : Term → m (TSyntax `pl_ty)
  | `(pl_ty($τ)) => pure τ
  | `($_)        => panic! "unknown type"

/-- Strips `pl_pat(...)`; panics on any other term. -/
meta def unpackPLPat [Monad m] [MonadQuotation m] : Term → m (TSyntax `pl_pat)
  | `(pl_pat($p)) => pure p
  | `($_)         => panic! "unknown pattern"

@[app_unexpander Cfg.mk]
meta def unexpCfg : Unexpander
  | `($_ $e $s) => do
    match e with
    | `(pl($_)) => `(⟨pl($(← unpackPLExp e)), $s⟩)
    | _         => `(⟨$e, $s⟩)
  | _ => throw ()

/-! ### Types -/

@[app_unexpander Ty.int]
meta def unexpTyInt : Unexpander | `($_) => `(pl_ty(int))
@[app_unexpander Ty.bool]
meta def unexpTyBool : Unexpander | `($_) => `(pl_ty(bool))
@[app_unexpander Ty.unit]
meta def unexpTyUnit : Unexpander | `($_) => `(pl_ty(unit))
@[app_unexpander Ty.prod]
meta def unexpTyProd : Unexpander
  | `($_ $τ1 $τ2) => do `(pl_ty($(← unpackPLTy τ1) × $(← unpackPLTy τ2)))
  | _ => throw ()
@[app_unexpander Ty.sum]
meta def unexpTySum : Unexpander
  | `($_ $τ1 $τ2) => do `(pl_ty($(← unpackPLTy τ1) + $(← unpackPLTy τ2)))
  | _ => throw ()
@[app_unexpander Ty.arrow]
meta def unexpTyArrow : Unexpander
  | `($_ $τ1 $τ2) => do `(pl_ty($(← unpackPLTy τ1) → $(← unpackPLTy τ2)))
  | _ => throw ()
@[app_unexpander Ty.ref]
meta def unexpTyRef : Unexpander
  | `($_ $τ) => do `(pl_ty(ref($(← unpackPLTy τ))))
  | _ => throw ()
@[app_unexpander Ty.tape]
meta def unexpTyTape : Unexpander
  | `($_) => do `(pl_ty(tape))
@[app_unexpander Ty.real]
meta def unexpTyReal : Unexpander
  | `($_) => do `(pl_ty(real))

/-! ### Patterns -/

@[app_unexpander Pat.wildcard]
meta def unexpPatWildcard : Unexpander
  | `($_) => `(pl_pat(_))

@[app_unexpander Pat.lit]
meta def unexpPatLit : Unexpander
  | `($_ $b) => `(pl_pat(# $b))
  | _ => throw ()

@[app_unexpander Pat.pair]
meta def unexpPatPair : Unexpander
  | `($_ $p1 $p2) => do `(pl_pat(($(← unpackPLPat p1), $(← unpackPLPat p2))))
  | _ => throw ()

@[app_unexpander Pat.inl]
meta def unexpPatInl : Unexpander
  | `($_ $p) => do `(pl_pat(inl($(← unpackPLPat p))))
  | _ => throw ()

@[app_unexpander Pat.inr]
meta def unexpPatInr : Unexpander
  | `($_ $p) => do `(pl_pat(inr($(← unpackPLPat p))))
  | _ => throw ()

/-! ### Literals / atomic expressions -/

@[app_unexpander Exp.lit]
meta def unexpLit : Unexpander
  | `($_ $arg) => `(pl(# $arg))
  | _ => throw ()

@[app_unexpander BaseLit.int]
meta def unexpBLInt : Unexpander
  | `($_ (Int.ofNat $n:num)) => `($n)
  | `($_ $z)                 => pure z
  | _                        => throw ()

@[app_unexpander BaseLit.bool]
meta def unexpBLBool : Unexpander
  | `($_ $b) => pure b
  | _ => throw ()

@[app_unexpander BaseLit.unit]
meta def unexpBLUnit : Unexpander := fun _ => `(())

@[app_unexpander Exp.fail]
meta def unexpFail : Unexpander
  | `($_) => do `(pl(fail))

@[app_unexpander Exp.urand]
meta def unexpUrand : Unexpander
  | `($_) => do `(pl(urand))

/-! ### Operators -/

@[app_unexpander Exp.binop]
meta def unexpBinop : Unexpander
  | `($_ BinOp.plus  $e1 $e2) => do `(pl($(← unpackPLExp e1) + $(← unpackPLExp e2)))
  | `($_ BinOp.minus $e1 $e2) => do `(pl($(← unpackPLExp e1) - $(← unpackPLExp e2)))
  | `($_ BinOp.mult  $e1 $e2) => do `(pl($(← unpackPLExp e1) * $(← unpackPLExp e2)))
  | `($_ BinOp.div   $e1 $e2) => do `(pl($(← unpackPLExp e1) / $(← unpackPLExp e2)))
  | `($_ BinOp.mod   $e1 $e2) => do `(pl($(← unpackPLExp e1) % $(← unpackPLExp e2)))
  | `($_ BinOp.lt    $e1 $e2) => do `(pl($(← unpackPLExp e1) < $(← unpackPLExp e2)))
  | `($_ BinOp.le    $e1 $e2) => do `(pl($(← unpackPLExp e1) <= $(← unpackPLExp e2)))
  | `($_ BinOp.and   $e1 $e2) => do `(pl($(← unpackPLExp e1) && $(← unpackPLExp e2)))
  | `($_ BinOp.or    $e1 $e2) => do `(pl($(← unpackPLExp e1) || $(← unpackPLExp e2)))
  | `($_ BinOp.xor   $e1 $e2) => do `(pl($(← unpackPLExp e1) ^^ $(← unpackPLExp e2)))
  | `($_ BinOp.eq    $e1 $e2) => do `(pl($(← unpackPLExp e1) = $(← unpackPLExp e2)))
  | _ => throw ()

@[app_unexpander Exp.unop]
meta def unexpUnop : Unexpander
  | `($_ UnOp.neg    $e) => do `(pl(~$(← unpackPLExp e)))
  | `($_ UnOp.minus  $e) => do `(pl(- $(← unpackPLExp e)))
  | `($_ UnOp.toReal $e) => do `(pl(toReal($(← unpackPLExp e))))
  | `($_ UnOp.frac   $e) => do `(pl(frac($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.cond]
meta def unexpCond : Unexpander
  | `($_ $ec $et $ef) => do
    `(pl(if $(← unpackPLExp ec) then $(← unpackPLExp et) else $(← unpackPLExp ef)))
  | _ => throw ()

/-! ### Pairs / sums / projections -/

/-- Flattens nested pairs `(a, (b, c))` into `(a, b, c)`. -/
meta partial def unexpPair' : Term → UnexpandM Term
  | `(pl(($e1, ($e2, $e3,*)))) => do unexpPair' (← `(pl(($e1, $e2, $e3,*))))
  | x => return x

@[app_unexpander Exp.pair]
meta def unexpPair : Unexpander
  | `($_ $e1 $e2) => do
    unexpPair' (← `(pl(($(← unpackPLExp e1), $(← unpackPLExp e2)))))
  | _ => throw ()

@[app_unexpander Exp.fst]
meta def unexpFst : Unexpander
  | `($_ $e) => do `(pl(fst($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.snd]
meta def unexpSnd : Unexpander
  | `($_ $e) => do `(pl(snd($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.inl]
meta def unexpInl : Unexpander
  | `($_ $e) => do `(pl(inl($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.inr]
meta def unexpInr : Unexpander
  | `($_ $e) => do `(pl(inr($(← unpackPLExp e))))
  | _ => throw ()

/-! ### State / random / scrut -/

@[app_unexpander Exp.alloc]
meta def unexpAlloc : Unexpander
  | `($_ $e) => do `(pl(alloc($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.load]
meta def unexpLoad : Unexpander
  | `($_ $e) => do `(pl(!$(← unpackPLExp e)))
  | _ => throw ()

@[app_unexpander Exp.store]
meta def unexpStore : Unexpander
  | `($_ $e1 $e2) => do `(pl($(← unpackPLExp e1) ← $(← unpackPLExp e2)))
  | _ => throw ()

@[app_unexpander Exp.tape]
meta def unexpTape : Unexpander
  | `($_ $e) => do `(pl(tape($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.rand]
meta def unexpRand : Unexpander
  | `($_ $e1 $e2) => do `(pl(rand($(← unpackPLExp e1), $(← unpackPLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.scrut]
meta def unexpScrut : Unexpander
  | `($_ $e $p) => do `(pl(scrut $(← unpackPLExp e) with $(← unpackPLPat p)))
  | _ => throw ()

/-! ### Binder naming machinery -/

/-- The `pl_arg` for a binder name (`_` for an anonymous one). -/
meta def buildArgFromName [Monad m] [MonadQuotation m]
    (name : String) : m (TSyntax `pl_arg) := do
  if name = "_" then
    `(pl_arg|_)
  else
    let ident := Lean.mkIdent (Name.mkSimple name)
    `(pl_arg|$ident:ident)

/-! ### Names for de Bruijn binders left by stepping

`open'` strips `plBinderName` mdata. The `Exp.lam`/`Exp.fix` delaborators push a fresh name
as a `PLBinderMarker` local; the `Exp.bvar` delaborator looks it up by index. -/

/-- Sentinel type tagging a delaborator-introduced ProbLang binder local. -/
def PLBinderMarker : Type := Unit

open Lean Lean.PrettyPrinter.Delaborator in
/-- PL binder names in scope, innermost first. -/
meta def plBinderStack : DelabM (List Name) := do
  let names := (← Lean.getLCtx).decls.toList.filterMap fun d? =>
    d?.bind fun d =>
      if d.type.isConstOf ``ProbLang.PLBinderMarker then some d.userName else none
  return names.reverse

open Lean Lean.Meta Lean.PrettyPrinter.Delaborator in
/-- Runs `k` with a `PLBinderMarker` local named `nm` in scope. -/
meta def withPLBinder {α} (nm : Name) (k : DelabM α) : DelabM α :=
  controlAt MetaM fun run =>
    Lean.Meta.withLocalDeclD nm (Lean.mkConst ``ProbLang.PLBinderMarker) fun _ => run k

open Lean Lean.PrettyPrinter.Delaborator in
/-- The next unused display name (`a`, `b`, …) at the current binder depth. -/
meta def freshPLBinderName : DelabM Name := do
  let pool := #["a", "b", "c", "d", "e", "g", "h", "i", "j", "k"]
  let d := (← plBinderStack).length
  return Name.mkSimple (if h : d < pool.size then pool[d] else s!"v{d}")

/-! ### Source names for `Exp.close BODY atom` binders

The binder delaborator records `atom ↦ name` (from `plBinderName` mdata) as a
`PLAtomMarker atom` local; the `Exp.fvar` delaborator looks it up. -/

/-- Sentinel type tagging a delaborator-introduced local that names a closed atom. -/
def PLAtomMarker (_ : Var) : Type := Unit

open Lean Lean.Meta Lean.PrettyPrinter.Delaborator in
/-- Runs `k` with a `PLAtomMarker atom` local named `nm` in scope. -/
meta def withAtomBinder {α} (nm : Name) (atom : Lean.Expr) (k : DelabM α) : DelabM α :=
  controlAt MetaM fun run =>
    Lean.Meta.withLocalDeclD nm (Lean.mkApp (Lean.mkConst ``ProbLang.PLAtomMarker) atom) fun _ =>
      run k

open Lean Lean.Meta Lean.PrettyPrinter.Delaborator in
/-- The name recorded for `atom` by an enclosing binder, if any. -/
meta def atomName? (atom : Lean.Expr) : DelabM (Option Name) := do
  for d in (← Lean.getLCtx) do
    match d.type with
    | .app (.const ``ProbLang.PLAtomMarker _) a => if ← isDefEq a atom then return some d.userName
    | _ => pure ()
  return none

open Lean.PrettyPrinter.Delaborator in
/-- Lean routes `mdata` with the single key `ProbLang.plBinderName` here. -/
@[delab mdata.ProbLang.plBinderName]
meta def delabPlBinderMeta : Delab := do
  let e ← SubExpr.getExpr
  let .mdata kv inner := e | failure
  let name := kv.getString plBinderNameKey ""
  if name.isEmpty then failure
  let nm := Name.mkSimple name
  let arg ← buildArgFromName name
  let closeArg := inner.appArg!
  let delabBody : Delab :=
    if closeArg.isAppOf ``Exp.close then
      withAtomBinder nm closeArg.appArg! (SubExpr.withMDataExpr (SubExpr.withAppArg delab))
    else
      withPLBinder nm (SubExpr.withMDataExpr (SubExpr.withAppArg delab))
  -- `isAppOf`, not `.app (.const ``Exp.lam) _`: `Exp.lam` carries an implicit `rT`.
  if inner.isAppOf ``Exp.lam then
    `(pl(fun $arg, $(← unpackPLExp (← delabBody))))
  else if inner.isAppOf ``Exp.fix then
    -- Merge an immediately-nested binder so `rec f` + `fun x, …` prints `rec f x := …`.
    match ← delabBody with
    | `(pl(fun $a:pl_arg, $body)) => `(pl(rec $arg $a := $body))
    | b => `(pl(rec $arg _ := $(← unpackPLExp b)))
  else failure

/-! ### Applications: `(fun x, b) a` shows as `let x := a; b`, `(fun _, b) a` as `a; b` -/

@[app_unexpander Exp.app]
meta def unexpApp : Unexpander
  | `($_ $fn $arg) => do
    let rhs ← unpackPLExp arg
    match fn with
    | `(pl(fun $a:pl_arg, $body)) =>
        match a with
        | `(pl_arg|$_:ident)        => `(pl(let $a := $rhs; $body))
        | `(pl_arg|($_:ident : $_)) => `(pl(let $a := $rhs; $body))
        | _                         => `(pl($rhs; $body))
    | _ => `(pl($(← unpackPLExp fn) $rhs))
  | _ => throw ()

/-! ### `Exp.annotated` delab (gated by `pp.problang.annot`) -/

open Lean.PrettyPrinter.Delaborator in
@[delab app.ProbLang.Exp.annotated]
meta def delabExpAnnotated : Delab := do
  let e ← SubExpr.getExpr
  unless e.getAppNumArgs == 2 do failure
  let mode := pp.problang.annot.get (← getOptions)
  let eStx ← SubExpr.withAppArg delab
  if mode ≥ 2 then
    let τStx ← SubExpr.withAppFn (SubExpr.withAppArg delab)
    let eSyn ← unpackPLExp eStx
    let τSyn ← unpackPLTy τStx
    `(pl(($eSyn : $τSyn)))
  else
    pure eStx

/-! ### `@[pl_fold]`: show a recursive constant by name

Stepping (`twp_pure`) substitutes a recursive definition's unfolded, opened body for its
self-reference, which `rw [← C]` cannot refold. The `Exp.fix` delaborator prints any
subterm defeq to a `@[pl_fold]` constant by name (`&GeometricTrial`). Display-only. -/

/-- The constants marked `@[pl_fold]`. -/
meta initialize plFoldExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun es => es.foldl (fun s arr => arr.foldl (·.insert ·) s) {}
    addEntryFn    := fun s n => s.insert n
    toArrayFn     := fun es => es.toArray
  }

syntax (name := pl_fold) "pl_fold" : attr

meta initialize registerBuiltinAttribute {
  name  := `pl_fold
  descr := "Display this recursive `Exp` constant by name where it appears unfolded."
  add   := fun decl _stx _kind => do
    modifyEnv fun env => plFoldExt.addEntry env decl
}

/-! ### `@[pl_names]`: show an unfolded recursive constant with its source binder names

Records the constant's `plBinderName` hints once; the `Exp.fix` delaborator, on a defeq
match, prints `rec geo n := …` instead of fresh `rec a b := …`. -/

/-- Binder names recorded by `@[pl_names]`, outermost first, per constant. -/
meta initialize plBinderNamesExt :
    SimplePersistentEnvExtension (Name × Array Name) (Lean.NameMap (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun es =>
      es.foldl (fun m arr => arr.foldl (fun m p => m.insert p.1 p.2) m) {}
    addEntryFn    := fun m p => m.insert p.1 p.2
    toArrayFn     := fun m => m.toArray
  }

/-- The `plBinderName` hints in `e`, in binder order. -/
meta partial def collectBinderNames : Lean.Expr → Array Name → Array Name
  | .mdata kv inner, acc =>
      match kv.getString plBinderNameKey "" with
      | "" => collectBinderNames inner acc
      | s  => collectBinderNames inner (acc.push (Name.mkSimple s))
  -- A pre-order walk meets hints in binder order whatever the wrappers' argument order.
  | .app f a, acc => collectBinderNames a (collectBinderNames f acc)
  | .lam _ t body _, acc => collectBinderNames body (collectBinderNames t acc)
  | _, acc => acc

syntax (name := pl_names) "pl_names" : attr

meta initialize registerBuiltinAttribute {
  name  := `pl_names
  descr := "Display this recursive `Exp` constant's unfolded body with its source binder names."
  add   := fun decl _stx _kind => do
    let ci ← getConstInfo decl
    let names := collectBinderNames ci.value! #[]
    modifyEnv fun env => plBinderNamesExt.addEntry env (decl, names)
}

/-! ### `Exp.lam` / `Exp.fix` delaborators -/

open Lean.PrettyPrinter.Delaborator Lean.Meta in
/-- Prints `Exp.lam` as `fun x, body` with a fresh name. -/
@[delab app.ProbLang.Exp.lam]
meta def delabExpLam : Delab := do
  let e ← SubExpr.getExpr
  guard <| e.getAppNumArgs == 2
  let nm ← freshPLBinderName
  let arg ← buildArgFromName nm.toString
  let bodyPL ← unpackPLExp (← withPLBinder nm (SubExpr.withAppArg delab))
  `(pl(fun $arg, $bodyPL))

open Lean.PrettyPrinter.Delaborator Lean.Meta in
/-- Binder args and innermost body of a `Exp.fix`/`Exp.lam` chain, named from `names`
and then fresh names. -/
meta partial def descendNamed (names : List Name) :
    DelabM (Array (TSyntax `pl_arg) × TSyntax `pl_exp) := do
  let cur ← SubExpr.getExpr
  -- `Exp.close BODY atom` consumes no name; BODY is the second-to-last argument.
  if cur.isAppOf ``Exp.close then
    return ← SubExpr.withAppFn (SubExpr.withAppArg (descendNamed names))
  if cur.isAppOf ``Exp.fix || cur.isAppOf ``Exp.lam then
    let nm ← match names with
      | nm :: _ => pure nm
      | []      => freshPLBinderName
    let arg ← buildArgFromName nm.toString
    let (args, body) ← withPLBinder nm (SubExpr.withAppArg (descendNamed names.tail))
    return (#[arg] ++ args, body)
  else
    return (#[], ← unpackPLExp (← delab))

open Lean.PrettyPrinter.Delaborator Lean.Meta in
/-- Print by name (`@[pl_fold]`), else with source binder names (`@[pl_names]`), else with
fresh names. -/
@[delab app.ProbLang.Exp.fix]
meta def delabExpFix : Delab := do
  let e ← SubExpr.getExpr
  let env ← getEnv
  let matchesConst (c : Name) : DelabM Bool := withNewMCtxDepth do
    let cExpr ← mkConstWithFreshMVarLevels c
    let (mvars, _, _) ← forallMetaTelescopeReducing (← inferType cExpr)
    isDefEq e (mkAppN cExpr mvars)
  -- The matched application `c a₁ … aₙ`, when its arguments are determined.
  let matchApp (c : Name) : DelabM (Option Lean.Expr) := withNewMCtxDepth do
    let cExpr ← mkConstWithFreshMVarLevels c
    let (mvars, _, _) ← forallMetaTelescopeReducing (← inferType cExpr)
    unless ← isDefEq e (mkAppN cExpr mvars) do return none
    let app ← instantiateMVars (mkAppN cExpr mvars)
    return if app.hasMVar then some cExpr else some app
  for c in (plFoldExt.getState env).toList do
    if let some app ← matchApp c then
      let stx ← if app.isConst then pure ⟨mkIdent (← unresolveNameGlobal c)⟩
        else Lean.PrettyPrinter.delab app
      if let `($i:ident) := stx then return ← `(pl(&$i))
      return ← `(pl(&($stx)))
  for (c, names) in (plBinderNamesExt.getState env).toList do
    if ← matchesConst c then
      let (args, body) ← descendNamed names.toList
      if h : 2 ≤ args.size then
        return ← `(pl(rec $(args[0]) $(args[1:])* := $body))
  -- `fix (lam B)` merges into `rec f x := B`; otherwise `rec f _ := body`.
  guard <| e.getAppNumArgs == 2
  let fName ← freshPLBinderName
  withPLBinder fName do
    let fArg ← buildArgFromName fName.toString
    if e.appArg!.isAppOf ``ProbLang.Exp.lam then
      let xName ← freshPLBinderName
      let xArg ← buildArgFromName xName.toString
      let innerPL ← unpackPLExp
        (← withPLBinder xName (SubExpr.withAppArg (SubExpr.withAppArg delab)))
      `(pl(rec $fArg $xArg := $innerPL))
    else
      let bodyPL ← unpackPLExp (← SubExpr.withAppArg delab)
      `(pl(rec $fArg _ := $bodyPL))

open Lean.PrettyPrinter.Delaborator in
/-- Display-only: shows the raw `Exp.case` (whose branches are functions of the payload) with `_`
patterns; it does not round-trip to `case`/`case!`. -/
@[delab app.ProbLang.Exp.case]
meta def delabExpCase : Delab := do
  let e ← SubExpr.getExpr
  guard <| e.getAppNumArgs == 4
  let ecPL ← unpackPLExp (← SubExpr.withAppFn (SubExpr.withAppFn (SubExpr.withAppArg delab)))
  let elPL ← unpackPLExp (← SubExpr.withAppFn (SubExpr.withAppArg delab))
  let erPL ← unpackPLExp (← SubExpr.withAppArg delab)
  let wild ← `(pl_pat|_)
  `(pl(case $ecPL | $wild => $elPL | $wild => $erPL))

open Lean.PrettyPrinter.Delaborator in
/-- Show `Exp.ofVal ⟨e, _⟩` (left by `twp_bind`) as `e`. Only fires on a literal `Val.mk`. -/
@[delab app.ProbLang.Exp.ofVal]
meta def delabExpOfVal : Delab := do
  let e ← SubExpr.getExpr
  guard <| e.getAppNumArgs == 2
  guard <| e.appArg!.isAppOf ``ProbLang.Val.mk
  -- `Val.mk α fst snd lc`: skip `lc` and `snd` to reach `fst`.
  SubExpr.withAppArg (SubExpr.withAppFn (SubExpr.withAppFn (SubExpr.withAppArg delab)))

/-! ### Variables -/

open Lean.PrettyPrinter.Delaborator in
/-- `⟪bvar n⟫` only when `n` escapes the tracked binders. -/
@[delab app.ProbLang.Exp.bvar]
meta def delabExpBvar : Delab := do
  let e ← SubExpr.getExpr
  guard <| e.getAppNumArgs == 2
  match e.appArg!.nat? with
  | some idx =>
    match (← plBinderStack)[idx]? with
    | some nm => `(pl($(Lean.mkIdent nm):ident))
    | none    => `(pl(⟪bvar $(Lean.quote idx)⟫))
  | none =>
    let idxStx ← SubExpr.withAppArg delab
    `(pl(⟪bvar $idxStx⟫))

open Lean.PrettyPrinter.Delaborator in
/-- Show `Exp.close BODY atom` as `BODY`; `delabExpFvar` names `atom`. -/
@[delab app.ProbLang.Exp.close]
meta def delabExpClose : Delab := do
  let e ← SubExpr.getExpr
  guard <| e.getAppNumArgs == 3
  SubExpr.withAppFn (SubExpr.withAppArg delab)

open Lean.PrettyPrinter.Delaborator in
@[delab app.ProbLang.Exp.fvar]
meta def delabExpFvar : Delab := do
  let e ← SubExpr.getExpr
  let v := e.appArg!
  if let some nm ← atomName? v then
    return ← `(pl($(Lean.mkIdent nm):ident))
  let_expr Var.named sLit := v | failure
  let .lit (.strVal s) := sLit | failure
  `(pl($(Lean.mkIdent (Name.mkSimple s)):ident))

end ProbLang
