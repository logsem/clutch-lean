module

public import Lean

@[expose] public section

open Lean Meta

/-!
# Building terms

Generic helpers for building terms as `Expr`s (nested tuples, `casesOn` with a constant motive,
uncurrying, instantiating a lemma at a goal, `hasInstance`), and for declaring them.
-/

namespace Metrology.Meta

/-! ## Terms -/

/-- `A × B × C`, or `empty` for no types. -/
def mkNestedProdType (types : List Expr) (empty : Expr := .const ``Unit []) : MetaM Expr :=
  if types.isEmpty then pure empty
  else types.dropLast.foldrM (fun ty acc => mkAppM ``Prod #[ty, acc]) types.getLast!

/-- `(a, b, c)`, or `empty` for no values. -/
def mkNestedProdValue (exprs : List Expr) (empty : Expr := .const ``Unit.unit []) : MetaM Expr :=
  if exprs.isEmpty then pure empty
  else exprs.dropLast.foldrM (fun e acc => mkAppM ``Prod.mk #[e, acc]) exprs.getLast!

/-- The projections reaching component `i` of a right-nested `n`-tuple, `true` for `Prod.fst`:
`Prod.snd` `i` times, then `Prod.fst` unless it is the last component. -/
def nestedProdPath (i n : Nat) : List Bool :=
  List.replicate i false ++ if i + 1 < n then [true] else []

/-- Component `i` of a right-nested `n`-tuple `p`. -/
def mkNestedProdProj (p : Expr) (i n : Nat) : MetaM Expr :=
  (nestedProdPath i n).foldlM (fun t fst => mkAppM (if fst then ``Prod.fst else ``Prod.snd) #[t]) p

/-- `f` as a function of the tuple of its arguments, of types `tys`: constant on `Unit`, itself,
uncurried, or of a nested tuple. -/
def uncurryN (f : Expr) (tys : Array Expr) : MetaM Expr := do
  match tys.size with
  | 0 => withLocalDeclD `x (mkConst ``Unit) fun x => mkLambdaFVars #[x] f
  | 1 => pure f
  | 2 => mkAppM ``Function.uncurry #[f]
  | n => withLocalDeclD `p (← mkNestedProdType tys.toList) fun p => do
      mkLambdaFVars #[p] (mkAppN f (← (Array.range n).mapM (mkNestedProdProj p · n)))

/-- `I.casesOn` on `x : I params`, with result type `α` and the arms `alts`. -/
def mkCasesOnConst (I : Name) (levels : List Level) (params : Array Expr) (α x : Expr)
    (alts : Array Expr) : MetaM Expr := do
  let motive ← withLocalDeclD `x (← inferType x) fun y => mkLambdaFVars #[y] α
  let casesOn := mkConst (mkCasesOnName I) ((← getLevel α) :: levels)
  return mkAppN casesOn (params ++ #[motive, x] ++ alts)

/-- The lemma or definition `c`, instantiated so that it has type `goal`: by `apply`, which finds
its arguments by unification and its instances by synthesis. -/
def instantiateFor (c : Name) (goal : Expr) : MetaM Expr := do
  let m ← mkFreshExprMVar goal
  let goals ← m.mvarId!.apply (← mkConstWithFreshMVarLevels c)
  let e ← instantiateMVars m
  unless goals.isEmpty && !e.hasMVar do
    throwError "instantiateFor: could not instantiate `{c}` for {goal}"
  return e

/-- Whether the class `cls` applied to `args` has an instance. -/
def hasInstance (cls : Name) (args : Array (Option Expr)) : MetaM Bool := do
  return (← synthInstance? (← mkAppOptM cls args)).isSome

/-! ## Declarations -/

/-- A binder of a statement, of type `type`, for `withLocalDecls`. -/
def decl (name : Name) (bi : BinderInfo) (type : MetaM Expr) :
    Name × BinderInfo × (Array Expr → MetaM Expr) :=
  (name, bi, fun _ => type)

/-- `n`, or the first of `n'`, `n''`, … not in `taken`. -/
def fresh (n : Name) (taken : List Name) : Name := Id.run do
  let mut m := n
  while taken.contains m do m := m.appendAfter "'"
  return m

/-- `type` with its first `n` binders implicit. -/
def implicitPrefix : Nat → Expr → Expr
  | n + 1, .forallE x t b _ => .forallE x t (implicitPrefix n b) .implicit
  | _, e => e

/-- Adds the attribute `attr` (without arguments) to `decl`. -/
def addAttribute (attr decl : Name) : MetaM Unit := do
  (← ofExcept (getAttributeImpl (← getEnv) attr)).add decl .missing .global

end Metrology.Meta
