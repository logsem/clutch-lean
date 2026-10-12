module

public import Metrology.TotalEris.TotalLifting
public import Metrology.ProbLang.Syntax.Notation
public import Iris.ProofMode.ProofModeM
public import Iris.ProofMode.Tactics.Basic
public import Lean
public import Qq

/-!
# Elaborator-based `twp_*` tactics for `tglWp`

The tactics discover the evaluation context `K` themselves. ProbLang has no language
hierarchy, so they match the concrete `tglWp` head rather than iris's `Wp` abstractions.
-/

namespace ProbLang.TotalEris

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Meta Elab Tactic Qq Iris Iris.ProofMode

/-! ## Context-lifted pure step (lemma consumed by `twp_pure`) -/

section
variable {rT : Type _} [LawfulProbLangℝ rT] {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

public theorem ErisWpGS.twp_pure_step_ctx (K : Ectx rT) (φ : Prop) {n : ℕ} {e₁ e₂ : Exp rT}
    [PureExec φ n e₁ e₂] (Hφ : φ) {E : CoPset} {Φ : Val rT → IProp GF} :
    tglWp E (K.fill e₂) Φ ⊢ tglWp E (K.fill e₁) Φ := by
  let : PureExec φ n (K.fill e₁) (K.fill e₂) := PureExec.fill K
  exact twp_pure_step_fupd φ Hφ

end

/-! ## Evaluation-context engine -/

/-- Read a value *structurally*, accepting abstract leaves (`Exp.ofVal v`, `v.fst`) on which
the computational `Exp.toVal?` is stuck. Other heads fall back to the reflective test. -/
public meta partial def exprAsVal? {α : Q(Type)} (e : Q(Exp $α)) :
    MetaM (Option Q(Val $α)) := do
  let e : Q(Exp $α) ← pure e.consumeMData
  match e with
  | ~q(Exp.ofVal $v) => return some v
  | ~q(Val.fst $v) => return some v
  | ~q(Exp.lit $b) => return some q(Val.ofBaseLit $b)
  | ~q(Exp.pair $a $b) => do
    let some va ← exprAsVal? a | return none
    let some vb ← exprAsVal? b | return none
    return some q(Val.pair $va $vb)
  | ~q(Exp.inl $a) => do
    let some va ← exprAsVal? a | return none
    return some q(Val.inl $va)
  | ~q(Exp.inr $a) => do
    let some va ← exprAsVal? a | return none
    return some q(Val.inr $va)
  | _ => do
    -- Closures go to the kernel: `whnf` of `toVal?` re-evaluates `lcb` through every
    -- inlined library body.
    if let some r ← Exp.closedFunVal? α e then return r
    -- Time-boxed; a timeout counts as "not a value", so decomposition descends past it.
    let tv? : Option Q(Option (Val $α)) ← controlAt CoreM fun runInBase =>
      Core.tryCatchRuntimeEx
        (runInBase do
          let tv : Q(Option (Val $α)) ←
            withOptions (fun o => o.set `maxHeartbeats (400000 : Nat)) <|
              withCurrHeartbeats <| whnf q(Exp.toVal? $e)
          pure (some tv))
        (fun _ => runInBase (pure none))
    let some tv := tv? | return none
    let ~q(some $v) := tv | return none
    return some v

/-- Peel one evaluation-context frame off `e`, or return `(none, e)`. Mirrors
`Exp.decompItem` but checks operands with `exprAsVal?`, so it works around abstract
`Val` leaves. -/
public meta def extractEctxItem {α : Q(Type)} (e : Q(Exp $α)) :
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
  | ~q(Exp.app $e1 $e2) =>
    binlike (fun e1 => pure q(EctxItem.appR $e1)) (fun v2 => pure q(EctxItem.appL $v2)) e1 e2
  | ~q(Exp.unop $op $e1) => unlike q(EctxItem.unop $op) e1
  | ~q(Exp.binop $op $e1 $e2) =>
    binlike (fun e1 => pure q(EctxItem.binopR $op $e1))
      (fun v2 => pure q(EctxItem.binopL $op $v2)) e1 e2
  | ~q(Exp.cond $ec $et $ef) => unlike q(EctxItem.condC $et $ef) ec
  | ~q(Exp.pair $e1 $e2) =>
    binlike (fun e1 => pure q(EctxItem.pairR $e1)) (fun v2 => pure q(EctxItem.pairL $v2)) e1 e2
  | ~q(Exp.fst $e1) => unlike q(EctxItem.fst) e1
  | ~q(Exp.snd $e1) => unlike q(EctxItem.snd) e1
  | ~q(Exp.inl $e1) => unlike q(EctxItem.inl) e1
  | ~q(Exp.inr $e1) => unlike q(EctxItem.inr) e1
  | ~q(Exp.case $ec $el $er) => unlike q(EctxItem.case $el $er) ec
  | ~q(Exp.alloc $e1) => unlike q(EctxItem.alloc) e1
  | ~q(Exp.load $e1) => unlike q(EctxItem.load) e1
  | ~q(Exp.store $e1 $e2) =>
    binlike (fun e1 => pure q(EctxItem.storeR $e1)) (fun v2 => pure q(EctxItem.storeL $v2)) e1 e2
  | ~q(Exp.tape $e1) => unlike q(EctxItem.tape) e1
  | ~q(Exp.rand $e1 $e2) =>
    binlike (fun e1 => pure q(EctxItem.randR $e1)) (fun v2 => pure q(EctxItem.randL $v2)) e1 e2
  | ~q(Exp.scrut $e1 $p) => unlike q(EctxItem.scrut $p) e1
  | _ => return (none, e)

/-- Fully decompose `e` into a frame stack `[innermost, …, outermost]` and the
innermost non-context sub-expression. The list order matches `Ectx.fill`
(`foldl (flip fillItem)`), so `Ectx.fill result.1 result.2 = e`. -/
public meta partial def extractAllEctxItems {α : Q(Type)} (e : Q(Exp $α))
    (acc : List Q(EctxItem $α) := []) : MetaM (List Q(EctxItem $α) × Q(Exp $α)) := do
  match ← extractEctxItem e with
  | (some Ki, e') => extractAllEctxItems e' (Ki :: acc)
  | (none, e) => return (acc, e)

/-- Plug `e` into a single frame `Ki` (mirrors `EctxItem.fillItem`). -/
public meta def fillItem {α : Q(Type)} (e : Q(Exp $α)) : Q(EctxItem $α) → MetaM Q(Exp $α)
  | ~q(.appL $v₂)     => return q(.app $e (.ofVal $v₂))
  | ~q(.appR $e₁)     => return q(.app $e₁ $e)
  | ~q(.unop $op)     => return q(.unop $op $e)
  | ~q(.binopL $op $v₂) => return q(.binop $op $e (.ofVal $v₂))
  | ~q(.binopR $op $e₁) => return q(.binop $op $e₁ $e)
  | ~q(.condC $e₁ $e₂) => return q(.cond $e $e₁ $e₂)
  | ~q(.pairL $v₂)    => return q(.pair $e (.ofVal $v₂))
  | ~q(.pairR $e₁)    => return q(.pair $e₁ $e)
  | ~q(.fst)          => return q(.fst $e)
  | ~q(.snd)          => return q(.snd $e)
  | ~q(.inl)          => return q(.inl $e)
  | ~q(.inr)          => return q(.inr $e)
  | ~q(.case $e₁ $e₂) => return q(.case $e $e₁ $e₂)
  | ~q(.alloc)        => return q(.alloc $e)
  | ~q(.load)         => return q(.load $e)
  | ~q(.storeL $v₂)   => return q(.store $e (.ofVal $v₂))
  | ~q(.storeR $e₁)   => return q(.store $e₁ $e)
  | ~q(.tape)         => return q(.tape $e)
  | ~q(.randL $v₂)    => return q(.rand $e (.ofVal $v₂))
  | ~q(.randR $e₁)    => return q(.rand $e₁ $e)
  | ~q(.scrut $p)     => return q(.scrut $e $p)

/-- Quote a `List` of quoted `EctxItem`s as a quoted `Ectx`. -/
public meta def quoteList {α : Q(Type)} : List Q(EctxItem $α) → Q(Ectx $α)
  | [] => q([])
  | x :: xs => q($x :: $(quoteList xs))

/-- Defeq to `Ectx.fill K e`, but computed at the meta level (no residual `Ectx.fill`). -/
public meta partial def fill {α : Q(Type)} (K : Q(Ectx $α)) (e : Q(Exp $α)) : MetaM Q(Exp $α) :=
  match K with
  | ~q([]) => pure e
  | ~q($Ki :: $K') => do fill K' (← fillItem e Ki)

/-- A decomposition `e = Ectx.fill K e'` with a `result` computed at `e'`. -/
public meta structure ECtxResultOf (α : Q(Type)) (β : Type) where
  result : β
  K : Q(Ectx $α)
  e' : Q(Exp $α)

/-- The innermost focus of `ogE` at which `pred` succeeds. -/
public meta partial def findECtx {α : Q(Type)} {β : Type} (ogE : Q(Exp $α))
    (pred : Q(Exp $α) → ProofModeM β) : ProofModeM (Option (ECtxResultOf α β)) := do
  let (Kis, inner) ← extractAllEctxItems ogE
  go inner Kis
where
  go (e : Q(Exp $α)) (Kis : List Q(EctxItem $α)) :
      ProofModeM (Option (ECtxResultOf α β)) := do
    if let some a ← observing? <| pred e then
      return some { result := a, K := quoteList Kis, e' := e }
    let Ki :: Kis' := Kis | return none
    go (← fillItem e Ki) Kis'

/-! ## WP-goal runner -/

meta structure TglWpGoal where
  {u : Level}
  {α : Q(Type)}
  instPL : Q(ProbLang.LawfulProbLangℝ $α)
  {GF : Q(BundledGFunctors.{0, 0, 0})}
  instWp : Q(ErisWpGS (rT := $α) $GF)
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  E : Q(CoPset)
  e : Q(Exp $α)
  Φ : Q(Val $α → IProp $GF)
  hu : QuotedLevelDefEq u 0
  hprop : $prop =Q IProp $GF
  hbi : $bi =Q UPred.instBIUPred

meta def runTacticTglWp {β : Type} (k : MVarId → TglWpGoal → ProofModeM β) : TacticM β := do
  ProofModeM.runTactic `tglWp fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "the goal {goal} must be an `IProp` at universe level 0"
    -- Binding `$GF` refines `prop`, so `hyps`' carrier is concrete for `addBIGoal`.
    let ~q(IProp $GF) := prop
      | throwError "the goal {goal} must be an `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "expected the BI of `IProp` to be `UPred.instBIUPred`"
    -- `tglWp` is `@[reducible]`, so a `~q` match would not refine; read the spine.
    let goalE : LeanExpr := (← instantiateMVars goal).consumeMData
    unless goalE.getAppFn.consumeMData.isConstOf ``ProbLang.TotalEris.ErisWpGS.tglWp do
      throwError "the goal {goal} must be a `tglWp`"
    let args := goalE.getAppArgs
    unless args.size == 7 do
      throwError "unexpected `tglWp` arity ({args.size}) in goal {goal}"
    have α : Q(Type) := args[0]!
    have instPL : Q(ProbLang.LawfulProbLangℝ $α) := args[1]!
    have instWp : Q(ErisWpGS (rT := $α) $GF) := args[3]!
    have E : Q(CoPset) := args[4]!
    have e : Q(Exp $α) := args[5]!
    have Φ : Q(Val $α → IProp $GF) := args[6]!
    k mvar { instPL, instWp, hyps, E, e, Φ, hu := ⟨⟩, hprop := ⟨⟩, hbi := ⟨⟩ }

/-! ## `twp_bind` — focus on a subexpression by auto-discovering its context -/

/-- `twp_bind e` rebases `tglWp E (K.fill e) Φ` to `tglWp E e (…)`, finding `K`. -/
elab "twp_bind" colGt ppSpace focus:term:max : tactic =>
  runTacticTglWp fun mvar { α, GF, instPL, instWp, hyps, E, e, Φ, .. } => do
    let focus ← elabTermEnsuringTypeQ focus q(Exp $α)
    let some res ← findECtx e (fun e => do guard (← isDefEq e focus))
      | throwTacticEx `twp_bind mvar
          m!"cannot unify {← ppExpr focus} with any evaluation context of {← ppExpr e}"
    have K : Q(Ectx $α) := res.K
    -- Use the user's term, not the matched `res.e'`: a recursive call then stays folded
    -- (`geometric ()`) and unifies syntactically with an IH.
    have e' : Q(Exp $α) := focus
    let Φc : Q(Val $α → IProp $GF) ←
      withLocalDeclDQ `v q(Val $α) fun v => do
        let body : Q(Exp $α) ← fill K q(Exp.ofVal $v)
        mkLambdaFVars #[v]
          q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E $body $Φ)
    let pf ← addBIGoal hyps
      q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E $e' $Φc)
    -- `mkAppOptM`, not `q(…)`: Qq would `whnf` the reducible `tglWp` into
    -- `bi_least_fixpoint` (heartbeat blow-up).
    let bindPf ← mkAppOptM ``ProbLang.TotalEris.ErisWpGS.tglWp_bind
      (#[α, instPL, GF, instWp, K, E, e', Φ].map some)
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, bindPf]
    mvar.assign transPf

/-- Clears the stuck `openRec k t v.fst` a step leaves on an abstract value. -/
@[pl_step_simp] public theorem openRec_val_fst {α : Type _} (k : Nat) (t : Exp α) (v : Val α) :
    Exp.openRec k t v.fst = v.fst := (Exp.open_lc k t v.fst v.lc).symm

/-- Unfold `open'`/`close`/`ofVal` and normalize Int/Nat/ite/ctor. The result is defeq to
the input (the `PureExec` instance needs that); binder-name `mdata` is stripped. -/
public meta def reduceExp {α : Q(Type)} (e : Q(Exp $α)) : MetaM Q(Exp $α) := do
  -- No default simprocs: they over-reduce `Exp.ofVal`/heap forms the heap rules need.
  let mut thms : SimpTheorems := {}
  for d in [``ProbLang.Exp.open', ``ProbLang.Exp.openRec, ``ProbLang.Exp.close,
            ``ProbLang.Exp.closeRec, ``ProbLang.Exp.ofVal, ``ProbLang.Val.ofBaseLit,
            ``ProbLang.Val.pair, ``ProbLang.Val.inl, ``ProbLang.Val.inr,
            ``ProbLang.Val.option] do
    thms ← thms.addDeclToUnfold d
  for l in [``Nat.zero_add, ``ProbLang.Var.internal.injEq] do
    thms ← thms.addConst l
  let mut procs : Simprocs := {}
  procs ← procs.add ``reduceIte (post := false)
  for p in [``Nat.reduceAdd, ``Nat.reduceSub, ``Nat.reduceEqDiff,
            ``Int.reduceAdd, ``Int.reduceSub, ``Int.reduceMul, ``Int.reduceDiv,
            ``Int.reduceMod, ``Int.reduceNeg, ``Int.reducePow, ``reduceCtorEq] do
    procs ← procs.add p (post := true)
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let ⟨res, _⟩ ← Lean.Meta.simp e ctx (simprocs := #[procs])
  return res.expr

/-- Re-attach source binder `names` (pre-order, from index `i`) to the `Exp.lam`/`Exp.fix`
binders of `e` as `plBinderName` mdata. -/
public meta partial def reattachNames (names : Array Name) (i : Nat) (e : LeanExpr) :
    MetaM (LeanExpr × Nat) := do
  if e.isAppOf ``ProbLang.Exp.lam || e.isAppOf ``ProbLang.Exp.fix then
    let args := e.getAppArgs
    let (body', i') ← reattachNames names (i+1) args[args.size-1]!
    let node := mkAppN e.getAppFn (args.set! (args.size-1) body')
    match names[i]? with
    | some nm =>
        return (LeanExpr.mdata (KVMap.empty.insert ProbLang.plBinderNameKey
          (.ofString nm.toString)) node, i')
    | none => return (node, i')
  else if e.isApp then
    let mut i' := i
    let mut args := e.getAppArgs
    for idx in [0:args.size] do
      if (← inferType args[idx]!).isAppOf ``ProbLang.Exp then
        let (a', i'') ← reattachNames names i' args[idx]!
        args := args.set! idx a'
        i' := i''
    return (mkAppN e.getAppFn args, i')
  else return (e, i)

/-- Returns `(e₁', e₂syn, names)`: the redex (`e` with a head constant possibly unfolded),
its reduct in the syntactic form the `PureExec` instance matches, and the source binder
names (β only; a `fix` relies on `@[pl_names]`). -/
public meta def pureStepResult {α : Q(Type)} (instPL : Q(ProbLang.LawfulProbLangℝ $α))
    (e : Q(Exp $α)) : MetaM (Option (Q(Exp $α) × Q(Exp $α) × Array Name)) := do
  let beta (body v : Q(Exp $α)) : Q(Exp $α) × Q(Exp $α) × Array Name :=
    (q(Exp.app (Exp.lam $body) $v), q(Exp.open' $body $v),
      ProbLang.collectBinderNames body #[])
  let betaFix (body v : Q(Exp $α)) : Q(Exp $α) × Q(Exp $α) × Array Name :=
    (q(Exp.app (Exp.fix $body) $v), q(Exp.app (Exp.open' $body (.fix $body)) $v), #[])
  match e with
  | ~q(.app $f $v)                        => do
    -- Without this guard the outward search would β-reduce `f (!l)`.
    let some _ ← exprAsVal? v | return none
    -- `consumeMData`, not `whnf`: the inner binder-name mdata must survive for name recovery.
    let f0 : Q(Exp $α) ← pure f.consumeMData
    match f0 with
    | ~q(Exp.lam $body) => return some (beta body v)
    | ~q(Exp.fix $body) => return some (betaFix body v)
    | _ => do
      -- Head recursive constant (`geometric ()`): `whnf` exposes its `Exp.fix`/`Exp.lam`.
      let fw : Q(Exp $α) ← whnf f
      let f1 : Q(Exp $α) ← pure fw.consumeMData
      match f1 with
      | ~q(Exp.fix $body) => return some (betaFix body v)
      | ~q(Exp.lam $body) => return some (beta body v)
      | _ => return none
  -- The `PureExec` discrimination tree does not see through `Exp.ofVal`: `whnf` the
  -- scrutinee and rebuild the redex with the raw constructor.
  | ~q(.cond $c $et $ef)                  => do
    let c0 : Q(Exp $α) ← whnf c
    match c0 with
    | ~q(Exp.lit (.bool true))  => return some (q(Exp.cond $c0 $et $ef), et, #[])
    | ~q(Exp.lit (.bool false)) => return some (q(Exp.cond $c0 $et $ef), ef, #[])
    -- Fire only if `reduce` lands on `true`/`false`; a symbolic bool stays put so a
    -- proof can still `rcases hb : …` on it.
    | ~q(Exp.lit (.bool $b))    => do
        let b' : Q(Bool) ← Lean.Meta.reduce b
        if b'.isConstOf ``Bool.true then
          return some (q(Exp.cond (Exp.lit (.bool $b')) $et $ef), et, #[])
        else if b'.isConstOf ``Bool.false then
          return some (q(Exp.cond (Exp.lit (.bool $b')) $et $ef), ef, #[])
        else
          return none
    | _                         => return none
  | ~q(.fst $p)                           => do
    let p0 : Q(Exp $α) ← whnf p
    match p0 with
    | ~q(Exp.pair $e1 $_e2) => return some (q(Exp.fst $p0), e1, #[])
    | _                     => return none
  | ~q(.snd $p)                           => do
    let p0 : Q(Exp $α) ← whnf p
    match p0 with
    | ~q(Exp.pair $_e1 $e2) => return some (q(Exp.snd $p0), e2, #[])
    | _                     => return none
  | ~q(.case $s $el $er)                  => do
    let s0 : Q(Exp $α) ← whnf s
    match s0 with
    | ~q(Exp.inl $v) => return some (q(Exp.case $s0 $el $er), q(Exp.app $el $v), #[])
    | ~q(Exp.inr $v) => return some (q(Exp.case $s0 $el $er), q(Exp.app $er $v), #[])
    | _              => return none
  | ~q(.binop $op $e1 $e2)                => do
    let r : Q(Option (Exp $α)) ← whnf q(@BinOp.eval $α
      (@LawfulProbLangℝ.toProbLangℝ $α $instPL) $op $e1 $e2)
    match r with
    -- No simproc reduces boolean results, so `reduce` here; keep the folded `b` unless it
    -- lands on `true`/`false` (a stuck `Decidable.rec …` defeats `rcases`).
    | ~q(some (Exp.lit (.bool $b))) => do
        let b' : Q(Bool) ← Lean.Meta.reduce b
        if b'.isConstOf ``Bool.true || b'.isConstOf ``Bool.false then
          return some (e, q(Exp.lit (.bool $b')), #[])
        else
          return some (e, q(Exp.lit (.bool $b)), #[])
    | ~q(some $res)                 => return some (e, res, #[])
    | _                             => return none
  | ~q(.unop $op $e1)                     => do
    let r : Q(Option (Exp $α)) ← whnf q(@UnOp.eval $α
      (@LawfulProbLangℝ.toProbLangℝ $α $instPL) $op $e1)
    match r with
    | ~q(some (Exp.lit (.bool $b)))          => do
        let b' : Q(Bool) ← Lean.Meta.reduce b
        return some (e, q(Exp.lit (.bool $b')), #[])
    -- `Int.reduceNeg` matches `Neg.neg`, not `Int.neg`.
    | ~q(some (Exp.lit (.int (Int.neg $z)))) => return some (e, q(Exp.lit (.int (-$z))), #[])
    | ~q(some $res)                          => return some (e, res, #[])
    | _                                      => return none
  | ~q(.scrut $v $p)                      => do
    let r : Q(Option (Exp $α)) ← whnf q(@Pat.tryMatch $α
      (@LawfulProbLangℝ.toProbLangℝ $α $instPL) $p $v)
    match r with
    | ~q(some $b) => return some (e, q(Exp.inl $b), #[])
    | ~q(none)    => return some (e, q(Exp.inr (.lit .unit)), #[])
    | _           => return none

/-! ## `twp_pure` — take a pure step at a redex, auto-discovering its context -/

public meta structure PureStepAt (α : Q(Type)) (instPL : Q(ProbLang.LawfulProbLangℝ $α)) where
  e₁ : Q(Exp $α)
  e₂syn : Q(Exp $α)
  names : Array Name
  φ : Q(Prop)
  n : Q(Nat)
  inst : Q(ProbLang.PureExec $φ $n $e₁ $e₂syn)

/-- The innermost redex of `e` (defeq to `focus?`, if given) with a `PureExec` step. -/
meta def findPureStep {α : Q(Type)} (instPL : Q(ProbLang.LawfulProbLangℝ $α)) (e : Q(Exp $α))
    (focus? : Option Q(Exp $α) := none) :
    ProofModeM (Option (ECtxResultOf α (PureStepAt α instPL))) :=
  findECtx e fun e₁ => do
    if let some focus := focus? then guard (← isDefEq e₁ focus)
    let some (e₁', e₂syn, names) ← pureStepResult instPL e₁ | failure
    let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
    let n : Q(Nat) ← mkFreshExprMVarQ q(Nat)
    let some inst ← ProofModeM.trySynthInstanceQ q(ProbLang.PureExec $φ $n $e₁' $e₂syn)
      | failure
    return { e₁ := e₁', e₂syn, names, φ, n, inst }

meta def displayReduct {α : Q(Type)} (e₂syn : Q(Exp $α)) (names : Array Name) :
    MetaM Q(Exp $α) := do
  let reduced ← reduceExp e₂syn
  if names.isEmpty then return reduced
  return (← reattachNames names 0 reduced).1

/-- `twp_pure_core [e]` takes one `PureExec` step, at `e` if given. The side condition is
tried with `is_value`, else left as a goal. -/
elab "twp_pure_core" focus:(ppSpace colGt term:max)? : tactic =>
  runTacticTglWp fun mvar { α, GF, instPL, instWp, hyps, E, e, Φ, .. } => do
    let focus? : Option Q(Exp $α) ← focus.mapM fun f => elabTermEnsuringTypeQ f q(Exp $α)
    let some res ← findPureStep instPL e focus?
      | throwTacticEx `twp_pure mvar m!"no pure step applies"
    have K : Q(Ectx $α) := res.K
    let step := res.result
    let φ : Q(Prop) ← instantiateMVars step.φ
    let n : Q(Nat) ← instantiateMVars step.n
    let e₁ : Q(Exp $α) ← instantiateMVars step.e₁
    let e₂syn : Q(Exp $α) ← instantiateMVars step.e₂syn
    let e₂ ← displayReduct e₂syn step.names
    -- An `Ectx.fill` redex would hide the next redex from `twp_pures`.
    let inner : Q(Exp $α) ← fill K e₂
    let pf ← addBIGoal hyps
      q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E $inner $Φ)
    let HΦ : Q($φ) ← mkFreshExprSyntheticOpaqueMVar q($φ)
    (← Tactic.evalTacticAt (← `(tactic| (try is_value))) HΦ.mvarId!).forM addMVarGoal
    let stepPf ← mkAppOptM ``ProbLang.TotalEris.ErisWpGS.twp_pure_step_ctx
      (#[α, instPL, GF, instWp, K, φ, n, e₁, e₂, step.inst, HΦ, E, Φ].map some)
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, stepPf]
    mvar.assign transPf

/-! ## `twp_value` — discharge a value WP (semantic value head) -/

/-- `twp_value` reduces `tglWp E e Φ` to `Φ v` when `e.toVal? = some v`. -/
elab "twp_value" : tactic =>
  runTacticTglWp fun mvar { α, GF, instPL, instWp, hyps, E, e, Φ, .. } => do
    let tv : Q(Option (Val $α)) ← match ← Exp.closedFunVal? α e with
      | some (some v) => have v : Q(Val $α) := v; pure q(some $v)
      | some none => pure q(none)
      | none => whnf q(Exp.toVal? $e)
    let ~q(some $v) := tv
      | throwTacticEx `twp_value mvar m!"{← ppExpr e} is not a value"
    let hproof : Q(Exp.toVal? $e = some $v) ← mkFreshExprSyntheticOpaqueMVar
      q(Exp.toVal? $e = some $v)
    (← Tactic.evalTacticAt (← `(tactic| kernel_rfl)) hproof.mvarId!).forM addMVarGoal
    have goal : Q(IProp $GF) := Expr.headBeta q($Φ $v)
    -- Iris's `iWpValueHead`: drop the `|={E}=>` only if the postcondition absorbs it.
    let c : Q(Prop) ← mkFreshExprMVarQ q(Prop)
    let p' : Q(Bool) ← mkFreshExprMVarQ q(Bool)
    let A' : Q(IProp $GF) ← mkFreshExprMVarQ q(IProp $GF)
    let Q' : Q(IProp $GF) ← mkFreshExprMVarQ q(IProp $GF)
    let useNoFupd : Bool ←
      if (← ProofModeM.trySynthInstanceQ
            q(ElimModal $c false .out $p' iprop(|={$E}=> $goal) $A' $goal $Q')).isSome then
        pure (← observing? (iSolveSidecondition c)).isSome
      else pure false
    have target : Q(IProp $GF) := if useNoFupd then goal else q(iprop(|={$E}=> $goal))
    let valLemma := if useNoFupd then ``ProbLang.TotalEris.ErisWpGS.tglWp_value_of_toVal
      else ``ProbLang.TotalEris.ErisWpGS.tglWp_value_fupd_of_toVal
    let pf ← addBIGoal hyps target
    let valPf ← mkAppOptM valLemma (#[α, instPL, GF, instWp, E, e, v, Φ, hproof].map some)
    mvar.assign (← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, valPf])

/-! ## Cleanup + composite tactics -/

/-- `twp_pure [e]` takes one pure step. `pl_step_simp` is propositional, so it cannot
live in the defeq-only `reduceExp`. -/
macro "twp_pure" focus:(ppSpace colGt term:max)? : tactic =>
  `(tactic| (twp_pure_core $[$focus]?; try simp only [pl_step_simp]))

/-- `twp_pure_at e₁ ↦ e₂` pins both endpoints, for when `PureExec` synthesis cannot see
through an opaque definition in `e₁`. -/
macro "twp_pure_at " e1:term:max " ↦ " e2:term:max : tactic =>
  `(tactic| iapply (ErisWpGS.twp_pure_step_fupd
      (n := 1) (e₁ := $e1) (e₂ := $e2) _ (by is_value)))

/-- `twp_pure_at e₁ ↦ e₂ by hφ` supplies the precondition `is_value` cannot close. -/
macro "twp_pure_at " e1:term:max " ↦ " e2:term:max " by " h:term : tactic =>
  `(tactic| iapply (ErisWpGS.twp_pure_step_fupd
      (n := 1) (e₁ := $e1) (e₂ := $e2) _ $h))

macro "twp_pures" : tactic =>
  `(tactic| ((repeat (twp_pure_core; try simp only [pl_step_simp]));
             try simp only [pl_step_simp]))

/-! ## `pure_step` / `pure_steps` — drive a plain `PureSteps` goal (outside proof mode) -/

meta def runPureStepsGoal {β : Type} (k : MVarId → ProofModeM β) : TacticM β := do
  let mvar ← getMainGoal
  mvar.withContext do
    let (res, _) ← StateRefT'.run ((k mvar).run { tacName := `pure_step }) {}
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
    return res

elab "pure_step_core" : tactic => do
  let tac ← runPureStepsGoal fun mvar => do
    let goalE := (← instantiateMVars (← mvar.getType)).consumeMData
    unless goalE.isAppOf ``ProbLang.PureSteps do
      throwTacticEx `pure_step mvar m!"goal is not a `PureSteps`"
    let args := goalE.getAppArgs
    unless args.size == 4 do
      throwTacticEx `pure_step mvar m!"unexpected `PureSteps` arity"
    have α : Q(Type) := args[0]!
    have instPL : Q(ProbLang.LawfulProbLangℝ $α) := args[1]!
    have X : Q(Exp $α) := args[2]!
    let some res ← findPureStep instPL X
      | throwTacticEx `pure_step mvar m!"no pure step applies"
    have K : Q(Ectx $α) := res.K
    let step := res.result
    let e₁ : Q(Exp $α) ← instantiateMVars step.e₁
    let e₂syn : Q(Exp $α) ← instantiateMVars step.e₂syn
    let e₂ ← displayReduct e₂syn step.names
    let e₂full : Q(Exp $α) ← fill K e₂
    let Ks ← Term.exprToSyntax K
    let e₁s ← Term.exprToSyntax e₁
    let e₂s ← Term.exprToSyntax e₂syn
    let e₂fullS ← Term.exprToSyntax e₂full
    `(tacticSeq|
      refine ProbLang.PureSteps.trans (ProbLang.PureSteps.fill $Ks
        (ProbLang.PureSteps.of_pureExec (e1 := $e₁s) (e2 := $e₂s) (by is_value))) ?_
      show ProbLang.PureSteps $e₂fullS _)
  Tactic.evalTactic tac

macro "pure_step" : tactic =>
  `(tactic| (pure_step_core; try simp only [pl_step_simp]))

/-- `pure_step n` takes exactly `n` steps, e.g. to stop before a recursive call where an IH
composes via `PureSteps.fill`. -/
macro "pure_step " n:num : tactic =>
  `(tactic| iterate $n (pure_step_core; try simp only [pl_step_simp]))

/-- `pure_steps` steps until stuck, then tries `PureSteps.refl`. -/
macro "pure_steps" : tactic =>
  `(tactic| ((repeat (pure_step_core; try simp only [pl_step_simp]));
             (try exact ProbLang.PureSteps.refl _)))

end ProbLang.TotalEris
