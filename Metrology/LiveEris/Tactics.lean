module

public import Metrology.LiveEris.PrimitiveLaws
public import Metrology.ProbLang.Syntax.Notation
public import Iris.ProofMode.ProofModeM
public import Iris.ProofMode.Tactics.Basic
public import Lean
public import Qq
public meta import Metrology.Meta.AppByName

/-!
# Proof-mode tactics for the LiveEris WP

`live_bind`, `live_pure`, `live_pures`, `live_pure_excused` and `live_value` discover the
evaluation context themselves. The context engine is the one of TotalEris's `twp_*` tactics.
-/

namespace ProbLang.LiveEris

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Meta Elab Tactic Qq Iris Iris.ProofMode

section
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT] {GF : BundledGFunctors}
    [LiveWpGS rT Coord GF]

public theorem LiveWpGS.lwp_pure_step_ctx (K : Ectx rT) (φ : Prop) {n : ℕ} {e₁ e₂ : Exp rT}
    [PureExec φ n e₁ e₂] (Hφ : φ) {Q : State rT → State rT → Prop} {E : CoPset}
    {Φ : Val rT → IProp GF} :
    LiveWpGS.lwp Q E (K.fill e₂) Φ ⊢ LiveWpGS.lwp Q E (K.fill e₁) Φ := by
  let : PureExec φ n (K.fill e₁) (K.fill e₂) := PureExec.fill K
  exact LiveWpGS.lwp_pure_step φ Hφ

end

public theorem lwp_pure_step_excused_ctx {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
    {hlc : HasLC}
    {GF : BundledGFunctors} [LiveGS rT hlc GF] (K : Ectx rT) (φ : Prop) {n : ℕ}
    {e₁ e₂ : Exp rT} [PureExec φ n e₁ e₂] (Hφ : φ) (hn : 0 < n)
    {Q : State rT → State rT → Prop} {E : CoPset} {Φ : Val rT → IProp GF} :
    iprop(↻1 ∗ ▷ (↻1 -∗ LiveWpGS.lwp Q E (K.fill e₂) Φ)) ⊢ LiveWpGS.lwp Q E (K.fill e₁) Φ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  let : PureExec φ (m + 1) (K.fill e₁) (K.fill e₂) := PureExec.fill K
  exact lwp_pure_steps_excused φ Hφ

/-! ## Evaluation-context engine -/

/-- Read a value *structurally* off a quoted expression, accepting abstract `Val` leaves
(`Exp.ofVal v`, `v.fst`) on which the computational `Exp.toVal?` is stuck. Concrete
`lam`/`fix` leaves need a closedness check and fall back to the reflective test. -/
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
    -- Kernel reduction decides closedness of a `lam`/`fix`; `whnf` of `toVal?` would
    -- re-evaluate `lcb` through every inlined library body.
    if let some r ← Exp.closedFunVal? α e then return r
    -- Time-boxed reflective fallback. A timeout counts as "not a value": decomposition
    -- descends past the closure, and a supplied focus still matches by lazy δ in `isDefEq`.
    let tv? : Option Q(Option (Val $α)) ← controlAt CoreM fun runInBase =>
      Core.tryCatchRuntimeEx
        (runInBase do
          let tv : Q(Option (Val $α)) ←
            withOptions (fun o => o.set `maxHeartbeats (400000 : Nat)) <|
              withCurrHeartbeats <| whnf q(Exp.toVal? $e)
          pure (some tv))
        (fun _ => runInBase (pure none))
    match tv? with
    | some tv =>
      match tv with
      | ~q(some $v) => return some v
      | _ => return none
    | none => return none

/-- Peel one evaluation-context frame off `e`, or return `(none, e)`. Mirrors `Exp.decompItem`
(same frames, right-to-left order) but checks operands with `exprAsVal?`, so it also works
around abstract `Val` leaves. -/
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

/-- Decompose `e` into frames `[innermost, …, outermost]` and the innermost redex, so that
`Ectx.fill result.1 result.2 = e`. -/
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

/-- `Ectx.fill K e` computed at the meta level, with no residual `Ectx.fill`. -/
public meta partial def fill {α : Q(Type)} (K : Q(Ectx $α)) (e : Q(Exp $α)) : MetaM Q(Exp $α) :=
  match K with
  | ~q([]) => pure e
  | ~q($Ki :: $K') => do fill K' (← fillItem e Ki)

/-- A decomposition `e = Ectx.fill K e'` together with a result `a` computed at
the focus `e'`. -/
public meta structure ECtxResultOf (α : Q(Type)) (β : Type) where
  result : β
  K : Q(Ectx $α)
  e' : Q(Exp $α)

/-- Walk the frame stack of `ogE` from innermost outward, returning the first
focus `e'` at which `pred e'` succeeds, together with the surrounding context. -/
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

/-- A proof-mode goal whose conclusion is `LiveWpGS.lwp Q E e Φ`. -/
meta structure LiveWpGoal where
  {u : Level}
  {α : Q(Type)}
  instMS : Q(MeasurableSpace $α)
  instPL : Q(@ProbLang.LawfulProbLangℝ $α $instMS)
  {GF : Q(BundledGFunctors.{0, 0, 0})}
  instWp : Q(LiveWpGS $α Coord $GF)
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  Q : Q(State $α → State $α → Prop)
  E : Q(CoPset)
  e : Q(Exp $α)
  Φ : Q(Val $α → IProp $GF)
  hu : QuotedLevelDefEq u 0
  hprop : $prop =Q IProp $GF
  hbi : $bi =Q UPred.instBIUPred

/-- Run `k` against the current goal, requiring it to be `ehyps ⊢ LiveWpGS.lwp Q E e Φ`. -/
meta def runTacticLiveWp {β : Type} (k : MVarId → LiveWpGoal → ProofModeM β) : TacticM β := do
  ProofModeM.runTactic `liveWp fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "the goal {goal} must be an `IProp` at universe level 0"
    let ~q(IProp $GF) := prop
      | throwError "the goal {goal} must be an `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "expected the BI of `IProp` to be `UPred.instBIUPred`"
    let goalE : LeanExpr := (← instantiateMVars goal).consumeMData
    unless goalE.getAppFn.consumeMData.isConstOf ``ProbLang.LiveEris.LiveWpGS.lwp do
      throwError "the goal {goal} must be a LiveEris `lwp`"
    let args := goalE.getAppArgs
    unless args.size == 9 do
      throwError "unexpected `lwp` arity ({args.size}) in goal {goal}"
    have α : Q(Type) := args[0]!
    have instMS : Q(MeasurableSpace $α) := args[1]!
    have instPL : Q(@ProbLang.LawfulProbLangℝ $α $instMS) := args[2]!
    have instWp : Q(LiveWpGS $α Coord $GF) := args[4]!
    have Q : Q(State $α → State $α → Prop) := args[5]!
    have E : Q(CoPset) := args[6]!
    have e : Q(Exp $α) := args[7]!
    have Φ : Q(Val $α → IProp $GF) := args[8]!
    k mvar { instMS, instPL, instWp, hyps, Q, E, e, Φ, hu := ⟨⟩, hprop := ⟨⟩, hbi := ⟨⟩ }

/-! ## `live_bind` — focus on a subexpression by auto-discovering its context -/

/-- `live_bind e` rebases the goal `lwp Q E (K.fill e) Φ` to `lwp Q E e (…)`, with the evaluation
context `K` discovered automatically. -/
elab "live_bind" colGt ppSpace focus:term:max : tactic =>
  runTacticLiveWp fun mvar { α, GF, instMS, instPL, instWp, hyps, Q, E, e, Φ, .. } => do
    let focus ← elabTermEnsuringTypeQ focus q(Exp $α)
    let some res ← findECtx e (fun e => do guard (← isDefEq e focus))
      | throwTacticEx `live_bind mvar
          m!"cannot unify {← ppExpr focus} with any evaluation context of {← ppExpr e}"
    have K : Q(Ectx $α) := res.K
    have e' : Q(Exp $α) := focus
    let Φc : Q(Val $α → IProp $GF) ←
      withLocalDeclDQ `v q(Val $α) fun v => do
        let body : Q(Exp $α) ← fill K q(Exp.ofVal $v)
        mkLambdaFVars #[v]
          q(@ProbLang.LiveEris.LiveWpGS.lwp $α $instMS $instPL $GF $instWp $Q $E $body $Φ)
    let pf ← addBIGoal hyps
      q(@ProbLang.LiveEris.LiveWpGS.lwp $α $instMS $instPL $GF $instWp $Q $E $e' $Φc)
    let bindPf ← mkAppByName ``ProbLang.LiveEris.LiveWpGS.lwp_bind
      [(`rT, α), (`GF, GF), (`Q, Q), (`K, K), (`E, E), (`e, e'), (`Φ, Φ)] [instMS, instPL, instWp]
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, bindPf]
    mvar.assign transPf

/-- Clears the stuck `openRec k u v.fst` that a step leaves on an abstract value. -/
@[pl_step_simp] public theorem openRec_val_fst {α : Type _} (k : Nat) (t : Exp α) (v : Val α) :
    Exp.openRec k t v.fst = v.fst := (Exp.open_lc k t v.fst v.lc).symm

/-- Reduce a stepped `Exp`: unfold `open'`/`close`/`ofVal` and normalize Int/Nat/ite/ctor.
The result is defeq to the input; `mdata` is stripped (see `reattachNames`). -/
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
  -- Defeq-only, so `PureExec` still applies to `e₂syn`. The stuck `openRec _ _ v.fst` is
  -- not defeq to `v.fst`; `simp only [pl_step_simp]` in `live_pure` clears it.
  return res.expr

/-- Re-attach source binder names, in pre-order, to the `Exp.lam`/`Exp.fix` binders of `e`
as `plBinderName` mdata. -/
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

/-- `(e₁', e₂syn, names)`: the redex `e₁'` (defeq to `e`, head constant possibly unfolded),
its reduct `e₂syn` in the form the `PureExec` instance matches syntactically, and the binder
names to re-attach (β only; `fix` relies on `@[pl_names]`). -/
public meta def pureStepResult {α : Q(Type)} (instMS : Q(MeasurableSpace $α))
    (instPL : Q(@ProbLang.LawfulProbLangℝ $α $instMS)) (e : Q(Exp $α)) :
    MetaM (Option (Q(Exp $α) × Q(Exp $α) × Array Name)) := do
  let beta (body v : Q(Exp $α)) : Q(Exp $α) × Q(Exp $α) × Array Name :=
    (q(Exp.app (Exp.lam $body) $v), q(Exp.open' $body $v),
      ProbLang.collectBinderNames body #[])
  let betaFix (body v : Q(Exp $α)) : Q(Exp $α) × Q(Exp $α) × Array Name :=
    (q(Exp.app (Exp.fix $body) $v), q(Exp.app (Exp.open' $body (.fix $body)) $v), #[])
  match e with
  | ~q(.app $f $v)                        => do
    -- Without this guard the outward search would β-reduce `f (!l)`.
    let some _ ← exprAsVal? v | return none
    -- `consumeMData`, not `whnf`: keep the inner binder names for `reattachNames`.
    let f0 : Q(Exp $α) ← pure f.consumeMData
    match f0 with
    | ~q(Exp.lam $body) => return some (beta body v)
    | ~q(Exp.fix $body) => return some (betaFix body v)
    | _ => do
      -- A head constant such as `geometric ()`: `whnf` exposes its `Exp.fix`/`Exp.lam`.
      let fw : Q(Exp $α) ← whnf f
      let f1 : Q(Exp $α) ← pure fw.consumeMData
      match f1 with
      | ~q(Exp.fix $body) => return some (betaFix body v)
      | ~q(Exp.lam $body) => return some (beta body v)
      | _ => return none
  -- The scrutinee may be `Exp.ofVal`-wrapped. `PureExec` synthesis is indexed by the head
  -- constructor and does not see through `ofVal`, so rebuild the redex around the `whnf`
  -- scrutinee. An abstract value stays stuck and takes no step.
  | ~q(.cond $c $et $ef)                  => do
    let c0 : Q(Exp $α) ← whnf c
    match c0 with
    | ~q(Exp.lit (.bool true))  => return some (q(Exp.cond $c0 $et $ef), et, #[])
    | ~q(Exp.lit (.bool false)) => return some (q(Exp.cond $c0 $et $ef), ef, #[])
    -- A concrete but unreduced bool such as `decide (0 = 0)`: fire only if `reduce` lands
    -- on a constructor. A symbolic bool (`ProbLangℝ.realLt y x`) stays put for `rcases`.
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
      (@LawfulProbLangℝ.toProbLangℝ $α $instMS $instPL) $op $e1 $e2)
    match r with
    -- No simproc reduces boolean results, so `reduce` here to let `cond` fire. A symbolic
    -- bool would reduce to a stuck `Decidable.rec …`; keep it folded for `rcases`.
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
      (@LawfulProbLangℝ.toProbLangℝ $α $instMS $instPL) $op $e1)
    match r with
    | ~q(some (Exp.lit (.bool $b)))          => do
        let b' : Q(Bool) ← Lean.Meta.reduce b
        return some (e, q(Exp.lit (.bool $b')), #[])
    -- `Int.reduceNeg` matches `-z`, not `Int.neg z`.
    | ~q(some (Exp.lit (.int (Int.neg $z)))) => return some (e, q(Exp.lit (.int (-$z))), #[])
    | ~q(some $res)                          => return some (e, res, #[])
    | _                                      => return none
  | ~q(.scrut $v $p)                      => do
    let r : Q(Option (Exp $α)) ← whnf q(@Pat.tryMatch $α
      (@LawfulProbLangℝ.toProbLangℝ $α $instMS $instPL) $p $v)
    match r with
    | ~q(some $b) => return some (e, q(Exp.inl $b), #[])
    | ~q(none)    => return some (e, q(Exp.inr (.lit .unit)), #[])
    | _           => return none

/-! ## Pure steps -/

/-- A pure step `inst : PureExec φ n e₁ e₂syn` found at one redex, with the binder `names` to
re-attach to the reduct. -/
public meta structure PureStepAt (α : Q(Type)) (instMS : Q(MeasurableSpace $α))
    (instPL : Q(@ProbLang.LawfulProbLangℝ $α $instMS)) where
  e₁ : Q(Exp $α)
  e₂syn : Q(Exp $α)
  names : Array Name
  φ : Q(Prop)
  n : Q(Nat)
  inst : Q(ProbLang.PureExec $φ $n $e₁ $e₂syn)

/-- Locate a pure step at the redex `focusE?` (or the first redex), returning its context `K`,
the step, the display form `e₂` of its reduct, and `inner = K.fill e₂` filled at the meta level. -/
public meta def findPureStep {α : Q(Type)} (instMS : Q(MeasurableSpace $α))
    (instPL : Q(@ProbLang.LawfulProbLangℝ $α $instMS))
    (e : Q(Exp $α)) (focusE? : Option Q(Exp $α)) (mvar : MVarId) :
    ProofModeM (Q(Ectx $α) × PureStepAt α instMS instPL × Q(Exp $α) × Q(Exp $α)) := do
  let some res ← findECtx e fun e₁ => do
    if let some focusE := focusE? then guard (← isDefEq e₁ focusE)
    let some (e₁', e₂syn, names) ← pureStepResult instMS instPL e₁ | failure
    let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
    let n : Q(Nat) ← mkFreshExprMVarQ q(Nat)
    let some inst ← ProofModeM.trySynthInstanceQ q(ProbLang.PureExec $φ $n $e₁' $e₂syn)
      | failure
    return ({ e₁ := e₁', e₂syn, names, φ, n, inst } : PureStepAt α instMS instPL)
    | throwTacticEx `live_pure mvar m!"no pure step applies"
  let step := res.result
  let step : PureStepAt α instMS instPL :=
    { e₁ := ← instantiateMVars step.e₁, e₂syn := ← instantiateMVars step.e₂syn,
      names := step.names, φ := ← instantiateMVars step.φ, n := ← instantiateMVars step.n,
      inst := ← instantiateMVars step.inst }
  let e₂ : Q(Exp $α) ← do
    let cleaned ← reduceExp step.e₂syn
    if step.names.isEmpty then pure cleaned
    else pure (← reattachNames step.names 0 cleaned).1
  return (res.K, step, e₂, ← fill res.K e₂)

/-- Discharge the pure-step side condition `φ` with `is_value`, leaving it as a goal if needed. -/
public meta def pureSideCondition (φ : Q(Prop)) : ProofModeM Q($φ) := do
  let HΦ : Q($φ) ← mkFreshExprSyntheticOpaqueMVar q($φ)
  let gs ← Tactic.evalTacticAt (← `(tactic| (try is_value))) HΦ.mvarId!
  gs.forM addMVarGoal
  return HΦ

/-! ## `live_pure` — take a pure step at a redex, auto-discovering its context -/

/-- `live_pure_core e` takes a single pure (`PureExec`) reduction step at the redex `e`,
discovering the surrounding evaluation context automatically. Leaves the stepped goal
unreduced; `live_pure` is the cleaning wrapper. -/
elab "live_pure_core" focus:(ppSpace colGt term:max)? : tactic =>
  runTacticLiveWp fun mvar { α, GF, instMS, instPL, instWp, hyps, Q, E, e, Φ, .. } => do
    let focusE? : Option Q(Exp $α) ← focus.mapM fun f => elabTermEnsuringTypeQ f q(Exp $α)
    let (K, step, e₂, inner) ← findPureStep instMS instPL e focusE? mvar
    let pf ← addBIGoal hyps
      q(@ProbLang.LiveEris.LiveWpGS.lwp $α $instMS $instPL $GF $instWp $Q $E $inner $Φ)
    let HΦ ← pureSideCondition step.φ
    let stepPf ← mkAppByName ``ProbLang.LiveEris.LiveWpGS.lwp_pure_step_ctx
      [(`rT, α), (`GF, GF), (`K, K), (`φ, step.φ), (`n, step.n), (`e₁, step.e₁), (`e₂, e₂),
        (`Hφ, HΦ), (`Q, Q), (`E, E), (`Φ, Φ)] [instMS, instPL, instWp, step.inst]
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, stepPf]
    mvar.assign transPf

/-- `live_pure_excused_core e` takes a pure step at the redex `e` as an excused checkpoint: the
goal becomes `↻1 ∗ ▷ (↻1 -∗ lwp Q E e' Φ)`. `live_pure_excused` is the cleaning wrapper. -/
elab "live_pure_excused_core" focus:(ppSpace colGt term:max)? : tactic =>
  runTacticLiveWp fun mvar { α, GF, instMS, instPL, instWp, hyps, Q, E, e, Φ, .. } => do
    let focusE? : Option Q(Exp $α) ← focus.mapM fun f => elabTermEnsuringTypeQ f q(Exp $α)
    let (K, step, e₂, inner) ← findPureStep instMS instPL e focusE? mvar
    let some ilc ← ProofModeM.trySynthInstanceQ q(LCGS $GF)
      | throwTacticEx `live_pure_excused mvar m!"no divergence credits (`LCGS`) in scope"
    have div : Q(IProp $GF) := q(@ProbLang.LiveEris.creditFrag $GF $ilc 0 1)
    have wpInner : Q(IProp $GF) :=
      q(@ProbLang.LiveEris.LiveWpGS.lwp $α $instMS $instPL $GF $instWp $Q $E $inner $Φ)
    let pf ← addBIGoal hyps q(iprop($div ∗ ▷ ($div -∗ $wpInner)))
    let HΦ ← pureSideCondition step.φ
    let hn : Q(0 < $(step.n)) ← mkFreshExprSyntheticOpaqueMVar q(0 < $(step.n))
    (← Tactic.evalTacticAt (← `(tactic| decide)) hn.mvarId!).forM addMVarGoal
    let stepPf ← mkAppByName ``ProbLang.LiveEris.lwp_pure_step_excused_ctx
      [(`rT, α), (`GF, GF), (`K, K), (`φ, step.φ), (`n, step.n), (`e₁, step.e₁), (`e₂, e₂),
        (`Hφ, HΦ), (`hn, hn), (`Q, Q), (`E, E), (`Φ, Φ)] [instMS, instPL, instWp, step.inst]
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, stepPf]
    mvar.assign transPf

/-! ## `live_value` — discharge a value WP -/

/-- `live_value` closes a goal `lwp Q E e Φ` when `e` is a value `v`, reducing it to `Φ v` (or
`|={E}=> Φ v` when the postcondition cannot absorb an update). -/
elab "live_value" : tactic =>
  runTacticLiveWp fun mvar { α, GF, instMS, instPL, instWp, hyps, Q, E, e, Φ, .. } => do
    let tv : Q(Option (Val $α)) ← match ← Exp.closedFunVal? α e with
      | some (some v) => have v : Q(Val $α) := v; pure q(some $v)
      | some none => pure q(none)
      | none => whnf q(Exp.toVal? $e)
    let ~q(some $v) := tv
      | throwTacticEx `live_value mvar m!"{← ppExpr e} is not a value"
    let hproof : Q(Exp.toVal? $e = some $v) ← mkFreshExprSyntheticOpaqueMVar
      q(Exp.toVal? $e = some $v)
    (← Tactic.evalTacticAt (← `(tactic| kernel_rfl)) hproof.mvarId!).forM addMVarGoal
    have goal : Q(IProp $GF) := Expr.headBeta q($Φ $v)
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
    let valLemma := if useNoFupd then ``ProbLang.LiveEris.LiveWpGS.lwp_value_of_toVal
      else ``ProbLang.LiveEris.LiveWpGS.lwp_value_fupd_of_toVal
    let pf ← addBIGoal hyps target
    let valPf ← mkAppByName valLemma
      [(`rT, α), (`GF, GF), (`Q, Q), (`E, E), (`e, e), (`v, v), (`Φ, Φ), (`h, hproof)]
      [instMS, instPL, instWp]
    mvar.assign (← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, valPf])

/-! ## Composite tactics -/

/-- `live_pure [e]` takes one pure step and cleans up the result. -/
macro "live_pure" focus:(ppSpace colGt term:max)? : tactic =>
  `(tactic| (live_pure_core $[$focus]?; try simp only [pl_step_simp]))

/-- `live_pure_excused [e]` takes one pure step as an excused checkpoint and cleans up the
result. -/
macro "live_pure_excused" focus:(ppSpace colGt term:max)? : tactic =>
  `(tactic| (live_pure_excused_core $[$focus]?; try simp only [pl_step_simp]))

/-- `pl_closed c` declares, for a closed program `c`, the lemmas `c_lc`, `c_fv`, and the `@[simp]`
lemmas `c_openRec` and `c_closeRec` that let `live_pure` substitute past it. -/
macro "pl_closed " c:ident : command => do
  let n := c.getId
  let lc := mkIdent (n.appendAfter "_lc")
  let fv := mkIdent (n.appendAfter "_fv")
  let oR := mkIdent (n.appendAfter "_openRec")
  let cR := mkIdent (n.appendAfter "_closeRec")
  let c₁ ← `(theorem $lc {rT : Type _} : ($c : Exp rT).IsLocallyClosed :=
      Exp.lcb_imp_lc (by lcb_kernel))
  let c₂ ← `(theorem $fv {rT : Type _} : ($c : Exp rT).fv = ∅ := by simp [$c:ident, Exp.fv])
  let c₃ ← `(@[simp] theorem $oR {rT : Type _} (k : ℕ) (t : Exp rT) :
      Exp.openRec k t ($c : Exp rT) = $c := (Exp.open_lc k t $c $lc).symm)
  let c₄ ← `(@[simp] theorem $cR {rT : Type _} (k : ℕ) (x : Var) :
      Exp.closeRec k x ($c : Exp rT) = $c := Exp.closeRec_fresh x $c k (by simp [$fv:ident]))
  return ⟨mkNullNode #[c₁, c₂, c₃, c₄]⟩

/-- `live_pures` repeatedly takes pure steps until none apply. -/
macro "live_pures" : tactic =>
  `(tactic| ((repeat (live_pure_core; try simp only [pl_step_simp]));
             try simp only [pl_step_simp]))

end ProbLang.LiveEris
