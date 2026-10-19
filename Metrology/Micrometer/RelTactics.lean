module

public import Metrology.Micrometer.AppRelRules
public import Metrology.Micrometer.ContinuousSampler
public import Metrology.Micrometer.WpTactics
public meta import Metrology.Micrometer.WpTactics
public meta import Metrology.TotalEris.WpTactics
public import Metrology.ProbLang.Syntax.Notation
public meta import Metrology.ProbLang.Syntax.Notation
public import Iris.ProofMode.ProofModeM
public import Iris.ProofMode.Tactics.Basic
public import Lean
public import Qq

/-! # Relational tactics

`rel_*` tactics for goals `REL[L] e << e' @ E : A`, after Approxis's `rel_tactics.v`, for any
lifting `L`. Each tactic finds its redex inside the evaluation context of its side (left, right,
or both), applies the matching rule of `AppRelRules.lean` at that context, and shows the premise
with the context filled back in. -/

namespace ProbLang.RelTactics

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Meta Elab Tactic Qq Iris Iris.ProofMode ProbLang.TotalEris ProbLang.MicrometerWpGS

/-! ## Goal decomposition -/

/-- The side of a refinement a tactic works on. -/
inductive Side where
  | l | r

/-- Whether `s` is the left side. -/
meta def Side.isL : Side → Bool
  | .l => true
  | .r => false

/-- A proof-mode goal `hyps ⊢ refines L E e t A`. -/
meta structure RelGoal where
  {u : Level}
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  /-- The full `refines` application, with `E e t A` as its trailing arguments. -/
  app : LeanExpr
  α : Q(Type)
  E : LeanExpr
  e : Q(Exp $α)
  t : Q(Exp $α)

/-- The program on `side`. -/
meta def RelGoal.side (g : RelGoal) : Side → Q(Exp $(g.α))
  | .l => g.e
  | .r => g.t

/-- The goal with the program on `side` replaced by `x`. -/
meta def RelGoal.withSide (g : RelGoal) (side : Side) (x : LeanExpr) : LeanExpr :=
  let args := g.app.getAppArgs
  let i := args.size - (if side.isL then 3 else 2)
  mkAppN g.app.getAppFn (args.set! i x)

/-- Run `k` on the `refines` goal of the proof-mode context. -/
meta def runTacticRel {β : Type} (name : Name) (k : MVarId → RelGoal → ProofModeM β) :
    TacticM β :=
  ProofModeM.runTactic name fun mvar {hyps, goal, ..} => do
    let app := (← instantiateMVars goal).consumeMData
    unless app.isAppOf ``ProbLang.refines do
      throwError "{name}: the goal {goal} is not a refinement `REL[L] e << e' : A`"
    let args := app.getAppArgs
    let n := args.size
    have α : Q(Type) := args[0]!
    k mvar { hyps, app, α, E := args[n-4]!, e := args[n-3]!, t := args[n-2]! }

/-! ## Cleanup: compute `Ectx.fill` on concrete contexts -/

/-- Whether `K` is a literal list. -/
meta partial def isLiteralCtx (K : LeanExpr) : Bool :=
  if K.isAppOfArity ``List.nil 1 then true
  else if K.isAppOfArity ``List.cons 3 then isLiteralCtx K.appArg! else false

/-- `Ectx.fill K x` with `K` a literal list (possibly `++` an abstract tail), filled in. -/
meta def fillLiteral? (e : LeanExpr) : MetaM (Option LeanExpr) := do
  unless e.isAppOfArity ``Ectx.fill 3 do return none
  have α : Q(Type) := e.getArg! 0
  let K ← instantiateMVars (e.getArg! 1)
  have x : Q(Exp $α) := e.getArg! 2
  if isLiteralCtx K then
    have K : Q(Ectx $α) := K
    return some (← fill K x)
  if K.isAppOfArity ``HAppend.hAppend 6 && isLiteralCtx (K.getArg! 4) then
    have Kd : Q(Ectx $α) := K.getArg! 4
    have Kabs : Q(Ectx $α) := K.getArg! 5
    let inner : Q(Exp $α) ← fill Kd x
    return some q(Ectx.fill $Kabs $inner)
  return none

/-- `Exp.ofVal v` for a value built by `exprAsVal?`, as the plain expression. -/
meta partial def unVal? (e : LeanExpr) : Option LeanExpr :=
  if e.isAppOfArity ``Exp.ofVal 2 || e.isAppOfArity ``Val.fst 2 then
    let v := e.appArg!.consumeMData
    let α := e.getArg! 0
    if v.isAppOfArity ``Val.ofBaseLit 3 then some (mkApp2 (.const ``Exp.lit []) α v.appArg!)
    else if v.isAppOfArity ``Val.mk 4 then some (v.getArg! 1)
    else if v.isAppOfArity ``Val.pair 3 then
      some (mkApp3 (.const ``Exp.pair []) α (ofV α (v.getArg! 1)) (ofV α (v.getArg! 2)))
    else if v.isAppOfArity ``Val.inl 2 then some (mkApp2 (.const ``Exp.inl []) α (ofV α v.appArg!))
    else if v.isAppOfArity ``Val.inr 2 then some (mkApp2 (.const ``Exp.inr []) α (ofV α v.appArg!))
    else none
  else none
where
  ofV (α v : LeanExpr) : LeanExpr :=
    let e := mkApp2 (.const ``Exp.ofVal []) α v
    (unVal? e).getD e

/-- Fill every concrete `Ectx.fill` of `P` and unfold value embeddings of literals. -/
meta def cleanFills (P : LeanExpr) : MetaM LeanExpr :=
  Meta.transform P (post := fun e => do
    if let some e' ← fillLiteral? e then return .visit e'
    if let some e' := unVal? e then return .visit e'
    return .continue)

/-! ## Applying a rule at a discovered context -/

/-- The premise and conclusion of an entailment `P ⊢ Q`. -/
meta def entailsParts? (ty : LeanExpr) : Option (LeanExpr × LeanExpr) :=
  let ty := ty.consumeMData
  if ty.isAppOfArity ``Iris.BI.BIBase.Entails 4 then some (ty.getArg! 2, ty.getArg! 3)
  else none

/-- Unify a rule's redex pattern with `e`, matching value holes `?v.1` against any value. -/
meta partial def unifyExp (pat e : LeanExpr) : MetaM Bool := do
  let pat ← instantiateMVars pat
  let p := pat.consumeMData
  if !p.hasExprMVar then return ← isDefEq pat e
  if p.isAppOfArity ``Val.fst 2 || p.isAppOfArity ``Exp.ofVal 2 then
    if (← instantiateMVars p.appArg!).getAppFn.isMVar then
      have α : Q(Type) := p.getArg! 0
      if let some v ← exprAsVal? (α := α) e then return ← isDefEq p.appArg! v
  let e' := (← whnf e).consumeMData
  let f := p.getAppFn
  if f.isConst && f == e'.getAppFn && p.getAppNumArgs == e'.getAppNumArgs then
    for a in p.getAppArgs, b in e'.getAppArgs do
      let ok ← if (← whnfR (← inferType a)).isAppOf ``Exp then unifyExp a b else isDefEq a b
      unless ok do return false
    return true
  isDefEq pat e

/-- The context hole of one side of a rule's conclusion: `Ectx.fill ?K pat`. -/
meta def fillHole? (e : LeanExpr) : MetaM (Option (LeanExpr × LeanExpr)) := do
  let e := (← instantiateMVars e).consumeMData
  unless e.isAppOfArity ``Ectx.fill 3 do return none
  unless (e.getArg! 1).getAppFn.isMVar do return none
  return some (e.getArg! 1, e.getArg! 2)

/-- Try `pred K e₀` at each focus `K.fill e₀` of `side`, innermost first, restoring the state
after each failure; the context includes any abstract tail the side is written with. -/
meta partial def searchSide {β : Type} (g : RelGoal) (side : Side)
    (pred : Q(Ectx $(g.α)) → Q(Exp $(g.α)) → ProofModeM β) : ProofModeM (Option β) := do
  let (Kabs?, inner) ← splitAbstractCtx (β := g.α) (g.side side)
  let (Kis, e₀) ← extractAllEctxItems inner
  let rec go (e₀ : Q(Exp $(g.α))) : List Q(EctxItem $(g.α)) → ProofModeM (Option β)
    | Kis => do
      if let some b ← observing? (pred (appendAbstractCtx (quoteList Kis) Kabs?) e₀) then
        return some b
      let Ki :: Kis' := Kis | return none
      go (← fillItem e₀ Ki) Kis'
  go e₀ Kis

/-- Discharge the leftover propositional holes of a rule cheaply, else keep them as goals. -/
meta def addSideGoals (val : LeanExpr) : ProofModeM Unit := do
  for m in ← getMVarsNoDelayed val do
    unless ← m.isAssigned do
      if ← isProp (← m.getType) then
        let gs ← try evalTacticAt (← `(tactic| first | omega | is_value | decide)) m
          catch _ => pure [m]
        gs.forM addMVarGoal
      else addMVarGoal m

/-- Close the goal by the rule `val : P ⊢ Q`, whose conclusion must already unify with the goal,
and leave `P` with its contexts filled (after `pre`). -/
meta def finishRule (mvar : MVarId) (g : RelGoal) (val : LeanExpr)
    (pre : LeanExpr → MetaM LeanExpr := pure) : ProofModeM Unit := do
  let ty ← instantiateMVars (← inferType val)
  let some (P, _) := entailsParts? ty | throwError "rel: {ty} is not an entailment"
  let P ← cleanFills (← pre (← instantiateMVars P))
  have P : Q($(g.prop)) := P
  let pf ← addBIGoal g.hyps P
  mvar.assign (← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, val])
  addSideGoals (← instantiateMVars val)

/-- Elaborate a rule term, instantiating its remaining arguments with metavariables. -/
meta def elabRule (stx : Term) : ProofModeM LeanExpr := do
  let val ← Tactic.elabTerm stx none (mayPostpone := true)
  let ty ← instantiateMVars (← inferType val)
  let (mvs, _, _) ← forallMetaTelescope ty
  for m in mvs do
    if (← isSyntheticMVar m) && !(← m.mvarId!.isAssignedOrDelayedAssigned) then
      Term.registerSyntheticMVarWithCurrRef m.mvarId! (.typeClass .none)
  return mkAppN val mvs

/-- Close the goal by the rule `stx`, whose conclusion must unify with the goal as it stands. -/
meta def applyRule (tac : Name) (mvar : MVarId) (g : RelGoal) (stx : Term)
    (pre : LeanExpr → MetaM LeanExpr := pure) : ProofModeM Unit := do
  let val ← elabRule stx
  let some (_, Q) := entailsParts? (← instantiateMVars (← inferType val))
    | throwError "{tac}: {stx} does not conclude an entailment"
  unless ← isDefEq Q g.app do throwError "{tac}: cannot apply {stx} to {← ppExpr g.app}"
  Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
  finishRule mvar g val pre

/-- Apply the rule `stx` at a redex found on `sides`: each side of its conclusion of the form
`Ectx.fill ?K pat` is matched against the foci of that side, innermost first. -/
meta partial def relApplyCore (tac : Name) (sides : List Side) (stx : Term) : TacticM Unit :=
  runTacticRel tac fun mvar g => do
    let val ← elabRule stx
    let some (_, Q) := entailsParts? (← instantiateMVars (← inferType val))
      | throwError "{tac}: {stx} does not conclude an entailment"
    let Q ← instantiateMVars Q
    unless Q.consumeMData.isAppOf ``ProbLang.refines do
      throwError "{tac}: {stx} does not conclude a refinement"
    let qargs := Q.consumeMData.getAppArgs
    let holes ← sides.filterMapM fun s => do
      let some h ← fillHole? qargs[qargs.size - (if s.isL then 3 else 2)]! | return none
      return some (s, h)
    if holes.isEmpty then
      throwError "{tac}: {stx} has no context hole `Ectx.fill ?K _` on the requested side"
    let rec go : List (Side × LeanExpr × LeanExpr) → ProofModeM Unit
      | [] => do unless ← isDefEq Q g.app do failure
      | (s, K, pat) :: rest => do
        let some _ ← searchSide g s fun Kc e₀ => do
            unless ← unifyExp pat e₀ do failure
            unless ← isDefEq K Kc do failure
            go rest
          | failure
    unless (← observing? (go holes)).isSome do
      throwError "{tac}: cannot apply {stx} to {← ppExpr g.e} << {← ppExpr g.t}"
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
    finishRule mvar g val

/-! ## `rel_apply` -/

/-- `rel_apply_l lem` applies `lem : P ⊢ REL K.fill e << t : A` at a redex of the left program
(Rocq `rel_apply_l`). -/
elab "rel_apply_l " colGt lem:term : tactic => relApplyCore `rel_apply_l [.l] lem

/-- `rel_apply_r lem` applies `lem : P ⊢ REL e << K.fill t : A` at a redex of the right
program (Rocq `rel_apply_r`). -/
elab "rel_apply_r " colGt lem:term : tactic => relApplyCore `rel_apply_r [.r] lem

/-- `rel_apply lem` applies `lem`, finding a redex on each side with a context hole
(Rocq `rel_apply`). -/
elab "rel_apply " colGt lem:term : tactic => relApplyCore `rel_apply [.l, .r] lem

/-! ## Pure steps -/

/-- The reduct of a boolean negation of an opaque bool, kept folded as `decide ¬b = true` (which
`pl_step_simp` shows as `!b`) rather than `pureStepResult`'s reduced `Decidable.rec` term. -/
meta def foldSymbolicNot {α : Q(Type)} (instPL : Q(LawfulProbLangℝ $α)) (e₁ e₂ : Q(Exp $α)) :
    MetaM Q(Exp $α) := do
  let ~q(Exp.unop $op $v) := e₁ | return e₂
  let ~q(Exp.lit (.bool $b)) := e₂ | return e₂
  if b.isConstOf ``Bool.true || b.isConstOf ``Bool.false then return e₂
  let r : Q(Option (Exp $α)) ← whnf q(@UnOp.eval $α
    (@LawfulProbLangℝ.toProbLangℝ $α $instPL) $op $v)
  let ~q(some (Exp.lit (.bool $b'))) := r | return e₂
  return q(Exp.lit (.bool $b'))

/-- One pure step on `side`, at the innermost redex (defeq to `focus?` if given). -/
meta def relPureCore (side : Side) (focus? : Option Term) : TacticM Unit :=
  runTacticRel (if side.isL then `rel_pure_l else `rel_pure_r) fun mvar g => do
    have α : Q(Type) := g.α
    let instPL : Q(LawfulProbLangℝ $α) ← synthInstanceQ q(LawfulProbLangℝ $α)
    let focusE? : Option Q(Exp $α) ← focus?.mapM fun f => elabTermEnsuringTypeQ f q(Exp $α)
    let res? : Option (Q(Ectx $α) × PureStepAt α instPL) ← searchSide g side fun K e₁ => do
        if let some focusE := focusE? then guard (← isDefEq e₁ focusE)
        let some (e₁', e₂syn, names) ← pureStepResult instPL e₁ | failure
        let e₂syn ← foldSymbolicNot instPL e₁' e₂syn
        let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
        let n : Q(Nat) ← mkFreshExprMVarQ q(Nat)
        let some inst ← ProofModeM.trySynthInstanceQ q(ProbLang.PureExec $φ $n $e₁' $e₂syn)
          | failure
        return (K, { e₁ := e₁', e₂syn, names, φ, n, inst })
    let some (K, step) := res?
      | throwError "rel_pure: no pure step applies to {← ppExpr (g.side side)}"
    let φ : Q(Prop) ← instantiateMVars step.φ
    let e₂syn : Q(Exp $α) ← instantiateMVars step.e₂syn
    let e₂ : Q(Exp $α) ← reduceExp e₂syn
    let e₂ : LeanExpr ←
      if step.names.isEmpty then pure e₂ else pure (← reattachNames step.names 0 e₂).1
    let HΦ : Q($φ) ← mkFreshExprSyntheticOpaqueMVar q($φ)
    let rule := if side.isL then ``refines_pure_l else ``refines_pure_r
    let stx ← `($(mkIdent rule) (K := $(← Term.exprToSyntax K))
      (e := $(← Term.exprToSyntax step.e₁)) (e' := $(← Term.exprToSyntax e₂syn))
      (Hex := $(← Term.exprToSyntax step.inst)) $(← Term.exprToSyntax HΦ))
    applyRule `rel_pure mvar g stx (pre := fun P => pure (P.replace fun x =>
      if x == e₂syn then some e₂ else none))

/-- `rel_pure_l_core [e]` takes one pure step on the left, keeping the `▷` it earns. -/
elab "rel_pure_l_core" focus:(ppSpace colGt term:max)? : tactic => relPureCore .l focus

/-- `rel_pure_r_core [e]` takes one pure step on the right. -/
elab "rel_pure_r_core" focus:(ppSpace colGt term:max)? : tactic => relPureCore .r focus

/-- `rel_finish` tidies the goal after a step with `pl_step_simp` (Rocq `rel_finish`). -/
macro "rel_finish" : tactic => `(tactic| pl_step_finish)

/-- `rel_pure_l [e]` takes one pure step on the left program, at `e` if given
(Rocq `rel_pure_l`). -/
macro "rel_pure_l" focus:(ppSpace colGt term:max)? : tactic =>
  `(tactic| (rel_pure_l_core $[$focus]?; inext; rel_finish))

/-- `rel_pure_r [e]` takes one pure step on the right program, at `e` if given
(Rocq `rel_pure_r`). -/
macro "rel_pure_r" focus:(ppSpace colGt term:max)? : tactic =>
  `(tactic| (rel_pure_r_core $[$focus]?; rel_finish))

/-- `rel_pure_l n` takes exactly `n` pure steps on the left, e.g. to unfold one iteration of a
loop and stop at its recursive call. -/
macro "rel_pure_l " n:num : tactic => `(tactic| iterate $n rel_pure_l)

/-- `rel_pure_r n` takes exactly `n` pure steps on the right. -/
macro "rel_pure_r " n:num : tactic => `(tactic| iterate $n rel_pure_r)

/-- `rel_pures_l` takes pure steps on the left until none applies (Rocq `rel_pures_l`). -/
macro "rel_pures_l" : tactic => `(tactic| repeat rel_pure_l)

/-- `rel_pures_r` takes pure steps on the right until none applies (Rocq `rel_pures_r`). -/
macro "rel_pures_r" : tactic => `(tactic| repeat rel_pure_r)

/-- `rel_pures` takes pure steps on both sides until none applies. -/
macro "rel_pures" : tactic => `(tactic| (rel_pures_l; rel_pures_r))

/-! ## Values -/

/-- `e` as a value `v` with `e` definitionally `v.1`. -/
meta def asVal? {α : Q(Type)} (e : Q(Exp $α)) : MetaM (Option Q(Val $α)) := do
  have e0 : Q(Exp $α) := e.consumeMData
  match e0 with
  | ~q(Exp.ofVal $v) => return some v
  | ~q(Val.fst $v) => return some v
  | _ => exprAsVal? e

/-- `rel_values_core` reduces `REL v << v' @ E : A` to `|={⊤}=> A v v'` (at `E = ⊤`) or to
`naOwnP E ={⊤}=∗ naOwnP ⊤ ∗ A v v'`. -/
elab "rel_values_core" : tactic => runTacticRel `rel_values fun mvar g => do
  have α : Q(Type) := g.α
  let some v₁ ← asVal? (α := α) g.e | throwError "rel_values: {← ppExpr g.e} is not a value"
  let some v₂ ← asVal? (α := α) g.t | throwError "rel_values: {← ppExpr g.t} is not a value"
  let rule := if ← isDefEq g.E q((⊤ : CoPset)) then ``refines_ret else ``refines_ret_na
  let stx ← `($(mkIdent rule) (v1 := $(← Term.exprToSyntax v₁))
    (v2 := $(← Term.exprToSyntax v₂)) (by kernel_rfl) (by kernel_rfl))
  applyRule `rel_values mvar g stx

/-- `rel_values` closes a refinement between values, discharging base relations at equal
literals, else leaving `|={⊤}=> A v v'` (Rocq `rel_values`). -/
macro "rel_values" : tactic => `(tactic| (
  rel_values_core
  try (imodintro; first
    | iapply lrel_int_lit
    | iapply lrel_bool_lit
    | iapply lrel_unit_lit
    | iapply lrel_real_lit)))

/-! ## Binding -/

/-- `g`'s goal with `side` rewritten as `Ectx.fill K focus` for the discovered `K`. -/
meta def reshapeSide (tac : Name) (g : RelGoal) (side : Side) (focus : Term) :
    ProofModeM (Q(Ectx $(g.α)) × Q(Exp $(g.α)) × LeanExpr) := do
  have α : Q(Type) := g.α
  let f : Q(Exp $α) ← elabTermEnsuringTypeQ focus q(Exp $α)
  let some K ← searchSide g side fun K e₀ => do guard (← isDefEq e₀ f); return K
    | throwError "{tac}: cannot find {← ppExpr f} in an evaluation context of \
        {← ppExpr (g.side side)}"
  have K : Q(Ectx $α) := K
  let f : Q(Exp $α) ← instantiateMVars f
  return (K, f, g.withSide side q(Ectx.fill $K $f))

/-- Replace the goal by the definitionally equal `goal'`. -/
meta def changeGoal (mvar : MVarId) (g : RelGoal) (goal' : LeanExpr) : ProofModeM Unit := do
  have goal' : Q($(g.prop)) := goal'
  mvar.assign (← addBIGoal g.hyps goal')

/-- `rel_bind_l e` shows the left program as `Ectx.fill K e` (Rocq `rel_bind_l`). -/
elab "rel_bind_l " colGt e:term:max : tactic => runTacticRel `rel_bind_l fun mvar g => do
  let (_, _, goal') ← reshapeSide `rel_bind_l g .l e
  changeGoal mvar g goal'

/-- `rel_bind_r e` shows the right program as `Ectx.fill K e` (Rocq `rel_bind_r`). -/
elab "rel_bind_r " colGt e:term:max : tactic => runTacticRel `rel_bind_r fun mvar g => do
  let (_, _, goal') ← reshapeSide `rel_bind_r g .r e
  changeGoal mvar g goal'

/-- `rel_bind e e'` applies `refines_bind` at the subprograms `e` and `e'`, leaving the
refinement `REL e << e' : A` and its continuation as a separating conjunction. -/
elab "rel_bind " colGt e:term:max ppSpace colGt e':term:max : tactic =>
  runTacticRel `rel_bind fun mvar g => do
    let (K, f, goal₁) ← reshapeSide `rel_bind g .l e
    let g₁ := { g with app := goal₁, e := q(Ectx.fill $K $f) }
    let (K', f', _) ← reshapeSide `rel_bind g₁ .r e'
    let stx ← `(refines_bind_sep $(← Term.exprToSyntax K) $(← Term.exprToSyntax K')
      (e := $(← Term.exprToSyntax f)) (e' := $(← Term.exprToSyntax f')))
    applyRule `rel_bind mvar g stx

/-- `e` with every `Exp.fix` subterm that is definitionally a `@[pl_fold]` constant replaced by
that constant. -/
meta def foldPlConsts (e : LeanExpr) : MetaM LeanExpr := do
  let consts := (plFoldExt.getState (← getEnv)).toList
  Meta.transform e (pre := fun x => do
    unless x.isAppOfArity ``Exp.fix 2 do return .continue
    for c in consts do
      let some app ← withNewMCtxDepth (allowLevelAssignments := true) do
          let cE ← mkConstWithFreshMVarLevels c
          let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType cE)
          let app := mkAppN cE mvs
          unless ← isDefEq x app do return none
          let app ← instantiateMVars app
          return if app.hasMVar then none else some app
        | continue
      return .done app
    return .continue)

/-- `rel_fold` shows recursive calls on both sides by their `@[pl_fold]` names, e.g. after
stepping into a loop body, so the goal matches a hypothesis about the loop. -/
elab "rel_fold" : tactic => runTacticRel `rel_fold fun mvar g => do
  let g' := { g with app := g.withSide .l (← foldPlConsts g.e) }
  changeGoal mvar g (g'.withSide .r (← foldPlConsts g.t))

/-! ## Heap and tape operations -/

/-- The first explicit argument of an application (the location of a points-to or tape). -/
meta def firstExplicitArg? (e : LeanExpr) : MetaM (Option LeanExpr) := do
  let args := e.getAppArgs
  forallBoundedTelescope (← inferType e.getAppFn) args.size fun xs _ => do
    for x in xs, a in args do
      if (← x.fvarId!.getBinderInfo).isExplicit then return some a
    return none

/-- The name of the hypothesis owning the resource that the goal `(∃ v,)? R ∗ (R' -∗ Q)` asks
for: same head as `R` and the same first location argument. -/
meta def findResourceHyp (g : IrisGoal) : ProofModeM Name := do
  let mut goal := (← instantiateMVars g.goal).consumeMData
  if goal.isAppOfArity ``Iris.BI.BIBase.exists 4 then
    let .lam _ ty body _ := goal.appArg!.consumeMData | throwError "rel: unexpected goal {goal}"
    goal := body.instantiate1 (← mkFreshExprMVar ty)
  unless goal.isAppOfArity ``Iris.BI.BIBase.sep 4 do throwError "rel: unexpected goal {goal}"
  let R := (goal.getArg! 2).consumeMData
  let some loc ← firstExplicitArg? R | throwError "rel: no location in {R}"
  let some (name, _) ← g.hyps.findM? fun _ _ _ ty => do
      let ty := ty.consumeMData
      unless ty.getAppFn == R.getAppFn do return false
      let some l ← firstExplicitArg? ty | return false
      isDefEq l loc
    | throwError "rel: no hypothesis owns {R}"
  return name

/-- `rel_frame_resource` gives the resource asked by `(∃ v,)? R ∗ (R' -∗ Q)` from the context and
reintroduces the updated one under the same name. -/
elab "rel_frame_resource" : tactic => do
  let (tac : TSyntax `tactic) ← ProofModeM.runTactic `rel fun mvar g => do
    addMVarGoal mvar
    let H := mkIdent (← findResourceHyp g)
    let ex := (← instantiateMVars g.goal).consumeMData.isAppOfArity ``Iris.BI.BIBase.exists 4
    if ex then `(tactic| (iexists _; isplitl [$H:ident]; iexact $H:ident; iintro $H:ident))
    else `(tactic| (isplitl [$H:ident]; iexact $H:ident; iintro $H:ident))
  evalTactic tac

/-- `rel_alloc_l l as H` allocates on the left, naming the location and points-to
(Rocq `rel_alloc_l`). -/
macro "rel_alloc_l " l:ident " as " H:ident : tactic =>
  `(tactic| (rel_pures_l; rel_apply_l refines_alloc_l; iintro %$l $H:ident))

/-- `rel_alloc_r l as H` allocates on the right (Rocq `rel_alloc_r`). -/
macro "rel_alloc_r " l:ident " as " H:ident : tactic =>
  `(tactic| (rel_pures_r; rel_apply_r refines_alloc_r; iintro %$l $H:ident))

/-- `rel_load_l` loads on the left with the points-to from the context (Rocq `rel_load_l`). -/
macro "rel_load_l" : tactic =>
  `(tactic| (rel_pures_l; rel_apply_l refines_load_l; rel_frame_resource))

/-- `rel_load_r` loads on the right with the points-to from the context (Rocq `rel_load_r`). -/
macro "rel_load_r" : tactic =>
  `(tactic| (rel_pures_r; rel_apply_r refines_load_r; rel_frame_resource))

/-- `rel_store_l` stores on the left, updating the points-to in the context
(Rocq `rel_store_l`). -/
macro "rel_store_l" : tactic =>
  `(tactic| (rel_pures_l; rel_apply_l refines_store_l; rel_frame_resource))

/-- `rel_store_r` stores on the right, updating the points-to in the context
(Rocq `rel_store_r`). -/
macro "rel_store_r" : tactic =>
  `(tactic| (rel_pures_r; rel_apply_r refines_store_r; rel_frame_resource))

/-- `rel_alloctape_l α as H` allocates a tape on the left (Rocq `rel_alloctape_l`). -/
macro "rel_alloctape_l " l:ident " as " H:ident : tactic =>
  `(tactic| (rel_pures_l; rel_apply_l refines_alloctape_nat_l; iintro %$l $H:ident))

/-- `rel_alloctape_r α as H` allocates a tape on the right (Rocq `rel_alloctape_r`). -/
macro "rel_alloctape_r " l:ident " as " H:ident : tactic =>
  `(tactic| (rel_pures_r; rel_apply_r refines_alloctape_r; iintro %$l $H:ident))

/-- `rel_rand_l` samples on the left: from the tape in the context for a labelled `rand`, else
leaving `∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ _` (Rocq `rel_rand_l`). -/
macro "rel_rand_l" : tactic => `(tactic| (rel_pures_l; first
  | rel_apply_l (refines_randU_l ?_)
  | (rel_apply_l refines_randT_l; rel_frame_resource)))

/-- `rel_rand_r` samples on the right, as `rel_rand_l` (Rocq `rel_rand_r`). -/
macro "rel_rand_r" : tactic => `(tactic| (rel_pures_r; first
  | rel_apply_r (refines_randU_r ?_)
  | (rel_apply_r refines_randT_r; rel_frame_resource)))

/-- `rel_alloc_l_atomic` applies `refines_alloc_l` at its redex, leaving its premise. -/
macro "rel_alloc_l_atomic" : tactic => `(tactic| rel_apply_l refines_alloc_l)
/-- `rel_load_l_atomic` applies `refines_load_l` at its redex, leaving its premise. -/
macro "rel_load_l_atomic" : tactic => `(tactic| rel_apply_l refines_load_l)
/-- `rel_store_l_atomic` applies `refines_store_l` at its redex, leaving its premise. -/
macro "rel_store_l_atomic" : tactic => `(tactic| rel_apply_l refines_store_l)
/-- `rel_alloctape_l_atomic` applies `refines_alloctape_l` at its redex, leaving its premise. -/
macro "rel_alloctape_l_atomic" : tactic => `(tactic| rel_apply_l refines_alloctape_l)
/-- `rel_rand_l_atomic` applies `refines_randT_l` at its redex, leaving its premise. -/
macro "rel_rand_l_atomic" : tactic => `(tactic| rel_apply_l refines_randT_l)

/-! ## Couplings -/

/-- The bijection arguments `f hdom hbij` of a coupling rule: `id` when none is given, and
side goals for the missing proofs. -/
meta def bijArgs (args : Array Term) : MacroM (Array Term) :=
  match args with
  | #[] => return #[← `(id), ← `(id_dom_range), ← `(id_bij_range)]
  | #[f] => return #[f, ← `(?_), ← `(?_)]
  | #[f, hdom, hbij] => return #[f, hdom, hbij]
  | _ => Macro.throwError "expected `f`, or `f hdom hbij`"

/-- `rel_couple_UU [f [hdom hbij]]` couples `rand z ~ rand z` along the bijection `f` (default
`id`); missing proofs are left as goals (Rocq `refines_couple_UU`). -/
syntax "rel_couple_UU" (ppSpace colGt term:max)* : tactic
macro_rules
  | `(tactic| rel_couple_UU $args*) => do
    let a ← bijArgs args
    let t ← `(tactic| rel_apply (refines_couple_rands_lr $(a[0]!) $(a[1]!) $(a[2]!) ?_))
    `(tactic| ($t; try simp only [id_eq]))

/-- `rel_couple_TU α [f [hdom hbij]]` couples a draw from the empty tape `α` with an
unlabelled draw (Rocq `refines_couple_TU`). -/
syntax "rel_couple_TU " term:max (ppSpace colGt term:max)* : tactic
macro_rules
  | `(tactic| rel_couple_TU $α $args*) => do
    let a ← bijArgs args
    let t ← `(tactic| rel_apply (refines_couple_TU $α $(a[0]!) $(a[1]!) $(a[2]!) ?_))
    `(tactic| ($t; try simp only [id_eq]))

/-- `rel_couple_UT α' [f [hdom hbij]]` couples an unlabelled draw with a draw from the empty
spec tape `α'` (Rocq `refines_couple_UT`). -/
syntax "rel_couple_UT " term:max (ppSpace colGt term:max)* : tactic
macro_rules
  | `(tactic| rel_couple_UT $α $args*) => do
    let a ← bijArgs args
    let t ← `(tactic| rel_apply (refines_couple_UT $α $(a[0]!) $(a[1]!) $(a[2]!) ?_))
    `(tactic| ($t; try simp only [id_eq]))

/-- `rel_couple_TT α α' [f [hdom hbij]]` couples draws from two empty tapes
(Rocq `refines_couple_TT`). -/
syntax "rel_couple_TT " term:max ppSpace term:max (ppSpace colGt term:max)* : tactic
macro_rules
  | `(tactic| rel_couple_TT $α $α' $args*) => do
    let a ← bijArgs args
    let t ← `(tactic| rel_apply (refines_couple_TT $α $α' $(a[0]!) $(a[1]!) $(a[2]!) ?_))
    `(tactic| ($t; try simp only [id_eq]))

/-- `rel_couple_UU_spend S c hc Hcpl` couples `rand N ~ rand N` along `S`, spending `↯b c`
(relational `wp_couple_rand_rand_spend`). -/
macro "rel_couple_UU_spend " S:term:max ppSpace c:term:max ppSpace hc:term:max ppSpace
    H:term:max : tactic =>
  `(tactic| rel_apply (refines_couple_rands_spend _ _ $S $c $hc $H))

/-- `rel_couple_urands f hmp` couples `urand ~ urand` along the measure-preserving `f`. -/
macro "rel_couple_urands " f:term:max ppSpace hmp:term:max : tactic =>
  `(tactic| rel_apply (refines_couple_urands_lr $f $hmp))

/-! ## Closures -/

/-- `rel_arrow_val_core` applies `refines_arrow_val` to a refinement between closures. -/
elab "rel_arrow_val_core" : tactic => runTacticRel `rel_arrow_val fun mvar g => do
  have α : Q(Type) := g.α
  let some v₁ ← asVal? (α := α) g.e | throwError "rel_arrow_val: {← ppExpr g.e} is not a value"
  let some v₂ ← asVal? (α := α) g.t | throwError "rel_arrow_val: {← ppExpr g.t} is not a value"
  let stx ← `(refines_arrow_val (v := $(← Term.exprToSyntax v₁)) (v' := $(← Term.exprToSyntax v₂))
    ⟨⟨by is_lc, by simp⟩, ⟨by is_lc, by simp⟩⟩)
  applyRule `rel_arrow_val mvar g stx

/-- `rel_arrow_val` reduces a refinement between closures at `A → A'` to their applications
(Rocq `rel_arrow_val`). -/
macro "rel_arrow_val" : tactic =>
  `(tactic| (rel_pures_l; rel_pures_r; rel_arrow_val_core; imodintro))
