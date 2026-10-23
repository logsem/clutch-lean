module

public import Metrology.ProbLang.DetStep
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Metrology.ProbLang.Syntax.Notation
public import Iris.ProofMode.ProofModeM
public import Iris.ProofMode.Tactics.Basic
public import Lean
public import Qq

/-! # Evaluation-context engine for the `wp_*`, `rel_*` and `twp_*` tactics

Finds the context around a redex, refills it, and computes the pure reduct.
-/

namespace ProbLang

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Meta Elab Tactic Qq Iris Iris.ProofMode
open Term (exprToSyntax synthesizeSyntheticMVarsNoPostponing)
open Exp (toVal? closedFunVal? openRec open_lc)

/-! ## Evaluation-context engine -/

variable {α : Q(Type)}

/-- Read a quoted expression as a value, accepting abstract leaves such as `Exp.ofVal v` and
`v.fst`. -/
public meta partial def exprAsVal? (e : Q(Exp $α)) : MetaM (Option Q(Val $α)) := do
  let e : Q(Exp $α) ← pure e.consumeMData
  match e with
  | ~q(.ofVal $v) => return some v
  | ~q(Val.fst $v) => return some v
  | ~q(.lit $b) => return some q(.ofBaseLit $b)
  | ~q(.pair $a $b) => do
    let some va ← exprAsVal? a | return none
    let some vb ← exprAsVal? b | return none
    return some q(.pair $va $vb)
  | ~q(.inl $a) => do
    let some va ← exprAsVal? a | return none
    return some q(.inl $va)
  | ~q(.inr $a) => do
    let some va ← exprAsVal? a | return none
    return some q(.inr $va)
  | _ => do
    -- Closures go to the kernel: `whnf` of `toVal?` re-evaluates `lcb` through every
    -- inlined library body.
    if let some r ← closedFunVal? α e then return r
    -- Time-boxed; a timeout counts as "not a value", so decomposition descends past it.
    let tv? : Option Q(Option (Val $α)) ← controlAt CoreM fun runInBase =>
      Core.tryCatchRuntimeEx
        (runInBase do
          let tv : Q(Option (Val $α)) ←
            -- Raised because `whnf` on `toVal?` can be slow on large closures.
            withOptions (fun o => o.set `maxHeartbeats (400000 : Nat)) <|
              withCurrHeartbeats <| whnf q(toVal? $e)
          pure (some tv))
        (fun _ => runInBase (pure none))
    let some tv := tv? | return none
    let ~q(some $v) := tv | return none
    return some v

/-- Peel one evaluation-context frame off `e`, or return `(none, e)`. -/
public meta def extractEctxItem (e : Q(Exp $α)) :
    MetaM (Option Q(EctxItem $α) × Q(Exp $α)) := do
  let e' : Q(Exp $α) ← whnf e.consumeMData
  let e : Q(Exp $α) ← pure e'.consumeMData
  let binlike (mk : Q(Exp $α) → MetaM Q(EctxItem $α))
      (mkV : Q(Val $α) → MetaM Q(EctxItem $α)) (e1 e2 : Q(Exp $α)) :
      MetaM (Option Q(EctxItem $α) × Q(Exp $α)) := do
    match ← exprAsVal? e2 with
    | none => return (some (← mk e1), e2)
    | some v2 =>
      match ← exprAsVal? e1 with
      | none => return (some (← mkV v2), e1)
      | some _ => return (none, e)
  let unlike (Ki : Q(EctxItem $α)) (e1 : Q(Exp $α)) :
      MetaM (Option Q(EctxItem $α) × Q(Exp $α)) := do
    match ← exprAsVal? e1 with
    | none => return (some Ki, e1)
    | some _ => return (none, e)
  match e with
  | ~q(.app $e1 $e2) =>
    binlike (fun e1 => pure q(.appR $e1)) (fun v2 => pure q(.appL $v2)) e1 e2
  | ~q(.unop $op $e1) => unlike q(.unop $op) e1
  | ~q(.binop $op $e1 $e2) =>
    binlike (fun e1 => pure q(.binopR $op $e1)) (fun v2 => pure q(.binopL $op $v2)) e1 e2
  | ~q(.cond $ec $et $ef) => unlike q(.condC $et $ef) ec
  | ~q(.pair $e1 $e2) =>
    binlike (fun e1 => pure q(.pairR $e1)) (fun v2 => pure q(.pairL $v2)) e1 e2
  | ~q(.fst $e1) => unlike q(.fst) e1
  | ~q(.snd $e1) => unlike q(.snd) e1
  | ~q(.inl $e1) => unlike q(.inl) e1
  | ~q(.inr $e1) => unlike q(.inr) e1
  | ~q(.case $ec $el $er) => unlike q(.case $el $er) ec
  | ~q(.alloc $e1) => unlike q(.alloc) e1
  | ~q(.load $e1) => unlike q(.load) e1
  | ~q(.store $e1 $e2) =>
    binlike (fun e1 => pure q(.storeR $e1)) (fun v2 => pure q(.storeL $v2)) e1 e2
  | ~q(.tape $e1) => unlike q(.tape) e1
  | ~q(.rand $e1 $e2) =>
    binlike (fun e1 => pure q(.randR $e1)) (fun v2 => pure q(.randL $v2)) e1 e2
  | ~q(.scrut $e1 $p) => unlike q(.scrut $p) e1
  | _ => return (none, e)

/-- Decompose `e` into its frame stack `[innermost, …, outermost]`, in the order of `Ectx.fill`,
and the innermost non-context sub-expression. -/
public meta partial def extractAllEctxItems (e : Q(Exp $α))
    (acc : List Q(EctxItem $α) := []) : MetaM (List Q(EctxItem $α) × Q(Exp $α)) := do
  match ← extractEctxItem e with
  | (some Ki, e') => extractAllEctxItems e' (Ki :: acc)
  | (none, e) => return (acc, e)

/-- Plug `e` into a single frame `Ki` (mirrors `EctxItem.fillItem`). -/
public meta def fillItem (e : Q(Exp $α)) : Q(EctxItem $α) → MetaM Q(Exp $α)
  | ~q(.appL $v₂) => return q(.app $e (.ofVal $v₂))
  | ~q(.appR $e₁) => return q(.app $e₁ $e)
  | ~q(.unop $op) => return q(.unop $op $e)
  | ~q(.binopL $op $v₂) => return q(.binop $op $e (.ofVal $v₂))
  | ~q(.binopR $op $e₁) => return q(.binop $op $e₁ $e)
  | ~q(.condC $e₁ $e₂) => return q(.cond $e $e₁ $e₂)
  | ~q(.pairL $v₂) => return q(.pair $e (.ofVal $v₂))
  | ~q(.pairR $e₁) => return q(.pair $e₁ $e)
  | ~q(.fst) => return q(.fst $e)
  | ~q(.snd) => return q(.snd $e)
  | ~q(.inl) => return q(.inl $e)
  | ~q(.inr) => return q(.inr $e)
  | ~q(.case $e₁ $e₂) => return q(.case $e $e₁ $e₂)
  | ~q(.alloc) => return q(.alloc $e)
  | ~q(.load) => return q(.load $e)
  | ~q(.storeL $v₂) => return q(.store $e (.ofVal $v₂))
  | ~q(.storeR $e₁) => return q(.store $e₁ $e)
  | ~q(.tape) => return q(.tape $e)
  | ~q(.randL $v₂) => return q(.rand $e (.ofVal $v₂))
  | ~q(.randR $e₁) => return q(.rand $e₁ $e)
  | ~q(.scrut $p) => return q(.scrut $e $p)

/-- Quote a `List` of quoted `EctxItem`s as a quoted `Ectx`. -/
public meta def quoteList : List Q(EctxItem $α) → Q(Ectx $α)
  | [] => q([])
  | x :: xs => q($x :: $(quoteList xs))

/-- Fill `e` into `K` at the meta level, defeq to `Ectx.fill K e`. -/
public meta partial def fillQ (K : Q(Ectx $α)) (e : Q(Exp $α)) : MetaM Q(Exp $α) :=
  match K with
  | ~q([]) => pure e
  | ~q($Ki :: $K') => do fillQ K' (← fillItem e Ki)

/-- A decomposition `e = Ectx.fill K e'` with a `result` computed at `e'`. -/
public meta structure ECtxResultOf (α : Q(Type)) (β : Type) where
  /-- The value computed at the focus. -/
  result : β
  /-- The surrounding evaluation context. -/
  K : Q(Ectx $α)
  /-- The focused sub-expression. -/
  e' : Q(Exp $α)

/-- The innermost focus of `ogE` at which `pred` succeeds. -/
public meta partial def findECtx {β : Type} (ogE : Q(Exp $α))
    (pred : Q(Exp $α) → ProofModeM β) : ProofModeM (Option (ECtxResultOf α β)) := do
  let (Kis, inner) ← extractAllEctxItems ogE
  go inner Kis
where
  go (e : Q(Exp $α)) (Kis : List Q(EctxItem $α)) : ProofModeM (Option (ECtxResultOf α β)) := do
    if let some a ← observing? <| pred e then
      return some { result := a, K := quoteList Kis, e' := e }
    let Ki :: Kis' := Kis | return none
    go (← fillItem e Ki) Kis'

/-! ## Pure steps -/

/-- Clears the stuck `openRec k t v.fst` a step leaves on an abstract value. -/
@[pl_step_simp] public theorem openRec_val_fst {α : Type _} (k : Nat) (t : Exp α) (v : Val α) :
    openRec k t v.fst = v.fst := (open_lc k t v.fst v.lc).symm

/-- Unfold `open'`, `close` and `ofVal` and normalize `Int`, `Nat`, `ite` and constructors, up to
defeq. -/
public meta def reduceExp (e : Q(Exp $α)) : MetaM Q(Exp $α) := do
  -- No default simprocs: they over-reduce `Exp.ofVal`/heap forms the heap rules need.
  let mut thms : SimpTheorems := {}
  for d in [``Exp.open', ``Exp.openRec, ``Exp.close, ``Exp.closeRec, ``Exp.ofVal,
      ``Val.ofBaseLit, ``Val.pair, ``Val.inl, ``Val.inr, ``Val.option] do
    thms ← thms.addDeclToUnfold d
  for l in [``Nat.zero_add, ``Var.internal.injEq] do
    thms ← thms.addConst l
  let mut procs : Simprocs := {}
  procs ← procs.add ``reduceIte (post := false)
  for p in [``Nat.reduceAdd, ``Nat.reduceSub, ``Nat.reduceEqDiff, ``Int.reduceAdd,
      ``Int.reduceSub, ``Int.reduceMul, ``Int.reduceDiv, ``Int.reduceMod, ``Int.reduceNeg,
      ``Int.reducePow, ``reduceCtorEq] do
    procs ← procs.add p (post := true)
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let ⟨res, _⟩ ← simp e ctx (simprocs := #[procs])
  return res.expr

/-- Re-attach source binder `names` (pre-order, from index `i`) to the `Exp.lam`/`Exp.fix`
binders of `e` as `plBinderName` mdata. -/
public meta partial def reattachNames (names : Array Name) (i : Nat) (e : LeanExpr) :
    MetaM (LeanExpr × Nat) := do
  if e.isAppOf ``Exp.lam || e.isAppOf ``Exp.fix then
    let args := e.getAppArgs
    let (body', i') ← reattachNames names (i+1) args[args.size-1]!
    let node := mkAppN e.getAppFn (args.set! (args.size-1) body')
    match names[i]? with
    | some nm =>
      return (LeanExpr.mdata (KVMap.empty.insert plBinderNameKey (.ofString nm.toString)) node, i')
    | none => return (node, i')
  else if e.isApp then
    let mut i' := i
    let mut args := e.getAppArgs
    for idx in [0:args.size] do
      if (← inferType args[idx]!).isAppOf ``Exp then
        let (a', i'') ← reattachNames names i' args[idx]!
        args := args.set! idx a'
        i' := i''
    return (mkAppN e.getAppFn args, i')
  else return (e, i)

/-- The redex, its reduct in the syntactic form the `PureExec` instance matches, and the source
binder names, for a pure step at `e`. -/
public meta def pureStepResult (instMS : Q(MeasurableSpace $α))
    (instPL : Q(@LawfulProbLangℝ $α $instMS)) (e : Q(Exp $α)) :
    MetaM (Option (Q(Exp $α) × Q(Exp $α) × Array Name)) := do
  let beta (body v : Q(Exp $α)) : Q(Exp $α) × Q(Exp $α) × Array Name :=
    (q(.app (.lam $body) $v), q(.open' $body $v), collectBinderNames body #[])
  let betaFix (body v : Q(Exp $α)) : Q(Exp $α) × Q(Exp $α) × Array Name :=
    (q(.app (.fix $body) $v), q(.app (.open' $body (.fix $body)) $v), #[])
  match e with
  | ~q(.app $f $v) => do
    -- Without this guard the outward search would β-reduce `f (!l)`.
    let some _ ← exprAsVal? v | return none
    -- `consumeMData`, not `whnf`: the inner binder-name mdata must survive for name recovery.
    let f0 : Q(Exp $α) ← pure f.consumeMData
    match f0 with
    | ~q(.lam $body) => return some (beta body v)
    | ~q(.fix $body) => return some (betaFix body v)
    | _ => do
      -- Head recursive constant (`geometric ()`): `whnf` exposes its `Exp.fix`/`Exp.lam`.
      let fw : Q(Exp $α) ← whnf f
      let f1 : Q(Exp $α) ← pure fw.consumeMData
      match f1 with
      | ~q(.fix $body) => return some (betaFix body v)
      | ~q(.lam $body) => return some (beta body v)
      | _ => return none
  -- The `PureExec` discrimination tree does not see through `Exp.ofVal`: `whnf` the
  -- scrutinee and rebuild the redex with the raw constructor.
  | ~q(.cond $c $et $ef) => do
    let c0 : Q(Exp $α) ← whnf c
    match c0 with
    | ~q(.lit (.bool true)) => return some (q(.cond $c0 $et $ef), et, #[])
    | ~q(.lit (.bool false)) => return some (q(.cond $c0 $et $ef), ef, #[])
    -- Fire only if `reduce` lands on `true`/`false`; a symbolic bool stays put so a
    -- proof can still `rcases hb : …` on it.
    | ~q(.lit (.bool $b)) => do
      let b' : Q(Bool) ← reduce b
      if b'.isConstOf ``Bool.true then
        return some (q(.cond (.lit (.bool $b')) $et $ef), et, #[])
      else if b'.isConstOf ``Bool.false then
        return some (q(.cond (.lit (.bool $b')) $et $ef), ef, #[])
      else
        return none
    | _ => return none
  | ~q(.fst $p) => do
    let p0 : Q(Exp $α) ← whnf p
    match p0 with
    | ~q(.pair $e1 $_e2) => return some (q(.fst $p0), e1, #[])
    | _ => return none
  | ~q(.snd $p) => do
    let p0 : Q(Exp $α) ← whnf p
    match p0 with
    | ~q(.pair $_e1 $e2) => return some (q(.snd $p0), e2, #[])
    | _ => return none
  | ~q(.case $s $el $er) => do
    let s0 : Q(Exp $α) ← whnf s
    match s0 with
    | ~q(.inl $v) => return some (q(.case $s0 $el $er), q(.app $el $v), #[])
    | ~q(.inr $v) => return some (q(.case $s0 $el $er), q(.app $er $v), #[])
    | _ => return none
  | ~q(.binop $op $e1 $e2) => do
    let r : Q(Option (Exp $α)) ← whnf q(@BinOp.eval $α
      (@LawfulProbLangℝ.toProbLangℝ $α $instMS $instPL) $op $e1 $e2)
    match r with
    -- No simproc reduces boolean results, so `reduce` here; keep the folded `b` unless it
    -- lands on `true`/`false` (a stuck `Decidable.rec …` defeats `rcases`).
    | ~q(some (.lit (.bool $b))) => do
      let b' : Q(Bool) ← reduce b
      if b'.isConstOf ``Bool.true || b'.isConstOf ``Bool.false then
        return some (e, q(.lit (.bool $b')), #[])
      else
        return some (e, q(.lit (.bool $b)), #[])
    | ~q(some $res) => return some (e, res, #[])
    | _ => return none
  | ~q(.unop $op $e1) => do
    let r : Q(Option (Exp $α)) ← whnf q(@UnOp.eval $α
      (@LawfulProbLangℝ.toProbLangℝ $α $instMS $instPL) $op $e1)
    match r with
    -- The only bool-valued unop is `neg` on a literal, so `reduce` always lands on `true`/`false`.
    | ~q(some (.lit (.bool $b))) => do
      let b' : Q(Bool) ← reduce b
      return some (e, q(.lit (.bool $b')), #[])
    -- `Int.reduceNeg` matches `Neg.neg`, not `Int.neg`.
    | ~q(some (.lit (.int (Int.neg $z)))) => return some (e, q(.lit (.int (-$z))), #[])
    | ~q(some $res) => return some (e, res, #[])
    | _ => return none
  | ~q(.scrut $v $p) => do
    let r : Q(Option (Exp $α)) ← whnf q(@Pat.tryMatch $α
      (@LawfulProbLangℝ.toProbLangℝ $α $instMS $instPL) $p $v)
    match r with
    | ~q(some $b) => return some (e, q(.inl $b), #[])
    | ~q(none) => return some (e, q(.inr (.lit .unit)), #[])
    | _ => return none

/-- A `PureExec` step `e₁ ⇝ e₂syn` with its instance, side condition `φ` and step count `n`. -/
public meta structure PureStepAt (α : Q(Type)) (instMS : Q(MeasurableSpace $α))
    (instPL : Q(@LawfulProbLangℝ $α $instMS)) where
  /-- The redex. -/
  e₁ : Q(Exp $α)
  /-- Its reduct, in the syntactic form the instance matches. -/
  e₂syn : Q(Exp $α)
  /-- The source binder names of the redex. -/
  names : Array Name
  /-- The side condition. -/
  φ : Q(Prop)
  /-- The step count. -/
  n : Q(Nat)
  /-- The `PureExec` instance. -/
  inst : Q(PureExec $φ $n $e₁ $e₂syn)

/-- The innermost redex of `e` (defeq to `focus?`, if given) with a `PureExec` step. -/
public meta def findPureStep (instMS : Q(MeasurableSpace $α))
    (instPL : Q(@LawfulProbLangℝ $α $instMS))
    (e : Q(Exp $α)) (focus? : Option Q(Exp $α) := none) :
    ProofModeM (Option (ECtxResultOf α (PureStepAt α instMS instPL))) :=
  findECtx e fun e₁ => do
    if let some focus := focus? then guard (← isDefEq e₁ focus)
    let some (e₁', e₂syn, names) ← pureStepResult instMS instPL e₁ | failure
    let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
    let n : Q(Nat) ← mkFreshExprMVarQ q(Nat)
    let some inst ← ProofModeM.trySynthInstanceQ q(PureExec $φ $n $e₁' $e₂syn)
      | failure
    return { e₁ := e₁', e₂syn, names, φ, n, inst }

/-- The reduct as shown to the user: normalized, with source binder names restored. -/
public meta def displayReduct (e₂syn : Q(Exp $α)) (names : Array Name) :
    MetaM Q(Exp $α) := do
  let reduced ← reduceExp e₂syn
  if names.isEmpty then return reduced
  return (← reattachNames names 0 reduced).1

/-! ## `pure_step` / `pure_steps` — drive a plain `PureSteps` goal (outside proof mode) -/

/-- Run `k` on the main goal outside proof mode, for `PureSteps` goals. -/
meta def runPureStepsGoal {β : Type} (k : MVarId → ProofModeM β) : TacticM β := do
  let mvar ← getMainGoal
  mvar.withContext do
    let (res, _) ← StateRefT'.run ((k mvar).run { tacName := `pure_step }) {}
    synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
    return res

/-- `pure_step_core` takes one `PureExec` step on a `PureSteps` goal, without cleanup. -/
elab "pure_step_core" : tactic => do
  let tac ← runPureStepsGoal fun mvar => do
    let goalE := (← instantiateMVars (← mvar.getType)).consumeMData
    unless goalE.isAppOf ``PureSteps do
      throwTacticEx `pure_step mvar m!"goal is not a `PureSteps`"
    let args := goalE.getAppArgs
    unless args.size == 5 do
      throwTacticEx `pure_step mvar m!"unexpected `PureSteps` arity"
    have α : Q(Type) := args[0]!
    have instMS : Q(MeasurableSpace $α) := args[1]!
    have instPL : Q(@LawfulProbLangℝ $α $instMS) := args[2]!
    have X : Q(Exp $α) := args[3]!
    let some res ← findPureStep instMS instPL X
      | throwTacticEx `pure_step mvar m!"no pure step applies"
    have K : Q(Ectx $α) := res.K
    let step := res.result
    let e₁ : Q(Exp $α) ← instantiateMVars step.e₁
    let e₂syn : Q(Exp $α) ← instantiateMVars step.e₂syn
    let e₂ ← displayReduct e₂syn step.names
    let e₂full : Q(Exp $α) ← fillQ K e₂
    let Ks ← exprToSyntax K
    let e₁s ← exprToSyntax e₁
    let e₂s ← exprToSyntax e₂syn
    let e₂fullS ← exprToSyntax e₂full
    `(tacticSeq|
      refine PureSteps.trans (PureSteps.fill $Ks
        (PureSteps.of_pureExec (e1 := $e₁s) (e2 := $e₂s) (by is_value))) ?_
      show PureSteps $e₂fullS _)
  Tactic.evalTactic tac

/-- `pure_step` takes one pure step on a `PureSteps` goal. -/
macro "pure_step" : tactic =>
  `(tactic| (pure_step_core; try simp only [pl_step_simp]))

/-- `pure_step n` takes exactly `n` pure steps on a `PureSteps` goal. -/
macro "pure_step " n:num : tactic =>
  `(tactic| iterate $n pure_step)

/-- `pure_steps` steps until stuck, then tries `PureSteps.refl`. -/
macro "pure_steps" : tactic =>
  `(tactic| ((repeat pure_step); try exact PureSteps.refl _))

end ProbLang
