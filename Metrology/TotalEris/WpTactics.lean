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

/-- Read a value *structurally* off a quoted expression, accepting abstract `Val`
projections (`Exp.ofVal v`, `v.fst`) at the leaves. `Exp.toVal?` is a computation, so
on a term with abstract leaves (e.g. an `(assocVal m).fst` induction tail) it is stuck
— a reflective `whnf` check would wrongly report "not a value" and derail context
discovery. Concrete `lam`/`fix` leaves (which need a closedness check) fall back to
the reflective test. -/
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
    -- Fast path: a concrete `lam`/`fix` (possibly behind a library constant) is a value
    -- iff it is locally closed, decided by kernel reduction (`Exp.closedFunVal?`) —
    -- `whnf` of `toVal?` re-evaluates `lcb` through every inlined library body.
    if let some r ← Exp.closedFunVal? α e then return r
    -- Reflective fallback, time-boxed: other heads (where `toVal?` is cheap) and
    -- closures the kernel cannot decide (metavariables). A timeout is reported as
    -- "not a value": decomposition then descends past the closure, and a supplied focus
    -- term still matches the rebuilt candidate by lazy δ in `isDefEq`.
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

/-- Peel one evaluation-context frame off `e`, returning the frame and the
sub-expression in its hole, or `(none, e)` if `e` is not decomposable. This mirrors
ProbLang's `Exp.decompItem` (same frames, same right-to-left evaluation order) but
performs the operand value checks with `exprAsVal?`, so decomposition also succeeds
around abstract `Val` leaves where the computational `toVal?` is stuck. -/
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

/-- Plug `e` into the (quoted) context `K`, computing the filled expression at the meta
level. Result is defeq to `Ectx.fill K e` but β-reduced (no residual `Ectx.fill`). -/
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

/-- A proof-mode goal whose conclusion is `tglWp E e Φ`. -/
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

/-- Run `k` against the current goal, requiring it to be `ehyps ⊢ tglWp E e Φ`. -/
meta def runTacticTglWp {β : Type} (k : MVarId → TglWpGoal → ProofModeM β) : TacticM β := do
  ProofModeM.runTactic `tglWp fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "the goal {goal} must be an `IProp` at universe level 0"
    -- Binding `$GF` here refines `prop` to `IProp GF`, so `hyps`' carrier is concrete
    -- for `addBIGoal` downstream.
    let ~q(IProp $GF) := prop
      | throwError "the goal {goal} must be an `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "expected the BI of `IProp` to be `UPred.instBIUPred`"
    -- Extract the `tglWp` arguments structurally (`tglWp` is `@[reducible]`, so a
    -- typed `~q` match against `$prop` does not refine; read the application spine).
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

/-- `twp_bind e` rebases the goal `tglWp E (K.fill e) Φ` to `tglWp E e (…)`, with
the evaluation context `K` discovered automatically (no manual `K`). -/
elab "twp_bind" colGt ppSpace focus:term:max : tactic =>
  runTacticTglWp fun mvar { α, GF, instPL, instWp, hyps, E, e, Φ, .. } => do
    let focus ← elabTermEnsuringTypeQ focus q(Exp $α)
    let some res ← findECtx e (fun e => do guard (← isDefEq e focus))
      | throwTacticEx `twp_bind mvar
          m!"cannot unify {← ppExpr focus} with any evaluation context of {← ppExpr e}"
    have K : Q(Ectx $α) := res.K
    -- Refocus on the user's term, not the defeq matched subterm `res.e'`: a recursive call
    -- then stays folded (`geometric ()`) and unifies syntactically with a recursion IH.
    have e' : Q(Exp $α) := focus
    let Φc : Q(Val $α → IProp $GF) ←
      withLocalDeclDQ `v q(Val $α) fun v => do
        let body : Q(Exp $α) ← fill K q(Exp.ofVal $v)
        mkLambdaFVars #[v]
          q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E $body $Φ)
    let pf ← addBIGoal hyps
      q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E $e' $Φc)
    -- Build the proof with raw `mkApp*` rather than `q(…)`: `tglWp` is
    -- `@[reducible, expose]`, so quoting `tglWp_bind`'s statement makes Qq `whnf` it
    -- into `bi_least_fixpoint` at elaboration time (heartbeat blow-up). `mkAppOptM`
    -- type-checks lazily and avoids that.
    let bindPf ← mkAppOptM ``ProbLang.TotalEris.ErisWpGS.tglWp_bind
      (#[α, instPL, GF, instWp, K, E, e', Φ].map some)
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, bindPf]
    mvar.assign transPf

/-- Opening any expression of a `Val` is the identity — values are locally closed.
Lets `reduceExp` discharge the stuck `openRec k u v.fst` that a step leaves on an
abstract value (which `openRec`'s recursion can't reduce, since `v.fst` is opaque),
so proofs no longer need a manual `rw [← Exp.open_lc … v.lc]`. -/
@[pl_step_simp] public theorem openRec_val_fst {α : Type _} (k : Nat) (t : Exp α) (v : Val α) :
    Exp.openRec k t v.fst = v.fst := (Exp.open_lc k t v.fst v.lc).symm

/-- Reduce a stepped `Exp`: unfold `open'`/`close`/`ofVal` and normalize Int/Nat/ite/ctor.
All rewrites are computational, so the result is defeq to the input. `mdata` is stripped
(re-attached by `reattachNames`). -/
public meta def reduceExp {α : Q(Type)} (e : Q(Exp $α)) : MetaM Q(Exp $α) := do
  -- Exactly this set, and no broader default simprocs: those would over-reduce e.g.
  -- `Exp.ofVal`/heap forms that the heap rules still need to see.
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
  -- NB: only defeq-preserving reductions here (the result must be defeq to the synthesis
  -- form `e₂syn` for the `PureExec` instance to apply). The stuck `openRec _ _ v.fst` on
  -- an abstract value is NOT defeq to `v.fst` (needs the `open_lc` proof), so it is
  -- cleared by a *propositional* `simp only [pl_step_simp]` in `twp_pure`/`twp_pures`.
  return res.expr

/-- Pre-order re-attach source binder names (from `collectBinderNames` of the redex
body) to the reduced result's `Exp.lam`/`Exp.fix` binders, as `plBinderName` mdata, so
they render with their source names. `i` threads through in binder pre-order. -/
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

/-- Returns `(e₁', e₂syn, names)`: the redex to step (`e₁'`, defeq to `e` but possibly
with a head recursive constant unfolded), the reduct `e₂syn` in the `Exp.open'` form the
`PureExec` instance matches syntactically, and the source binder `names` to re-attach to
the reduced result (β only; a `fix` relies on `@[pl_names]`). -/
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
  -- The scrutinee may be `Exp.ofVal`-wrapped, which the `PureExec` discrimination tree does
  -- not see through. So `whnf` it and rebuild the redex with the raw `.lit`/`.pair`/`.inl`
  -- constructor; an abstract value stays stuck and yields `none`.
  | ~q(.cond $c $et $ef)                  => do
    let c0 : Q(Exp $α) ← whnf c
    match c0 with
    | ~q(Exp.lit (.bool true))  => return some (q(Exp.cond $c0 $et $ef), et, #[])
    | ~q(Exp.lit (.bool false)) => return some (q(Exp.cond $c0 $et $ef), ef, #[])
    -- A concrete-but-unreduced discriminant (`decide (0 = 0)`): fully `reduce` it and fire
    -- only on a `true`/`false` constructor. A symbolic bool (`ProbLangℝ.realLt y x`) stays
    -- put, so a sampler proof can still `rcases hb : …` on it.
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
    -- No simproc reduces boolean results (`b₁ && b₂`, `decide (z₁ < z₂)`), so `reduce`
    -- here to let `cond` fire. Keep the folded `b` when that does not land on `true`/`false`:
    -- a symbolic `ProbLangℝ.realLt y x` would become a stuck `Decidable.rec …` that no
    -- `rcases` can branch on.
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
    -- `UnOp.eval minus` yields `z.neg` (`Int.neg z`), which `Int.reduceNeg` (matching
    -- `Neg.neg`) won't catch; rewrite to the defeq `-z` so the simproc renders `#(-5)`.
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

/-- The pure step found at one redex: `e₁` is the redex actually stepped, `e₂syn` its
reduct in the form the `PureExec` instance `inst` (with precondition `φ` and step count
`n`) matches syntactically, and `names` are the source binder names to re-attach to the
reduced result. -/
public meta structure PureStepAt (α : Q(Type)) (instPL : Q(ProbLang.LawfulProbLangℝ $α)) where
  e₁ : Q(Exp $α)
  e₂syn : Q(Exp $α)
  names : Array Name
  φ : Q(Prop)
  n : Q(Nat)
  inst : Q(ProbLang.PureExec $φ $n $e₁ $e₂syn)

/-- Search the evaluation contexts of `e`, innermost first, for a redex with a `PureExec`
step, restricted to redexes defeq to `focus?` when given. -/
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

/-- The display form of a reduct: reduced (defeq), with source binder names re-attached. -/
meta def displayReduct {α : Q(Type)} (e₂syn : Q(Exp $α)) (names : Array Name) :
    MetaM Q(Exp $α) := do
  let reduced ← reduceExp e₂syn
  if names.isEmpty then return reduced
  return (← reattachNames names 0 reduced).1

/-- `twp_pure_core e` takes a single pure (`PureExec`) reduction step at the redex `e`,
discovering the surrounding evaluation context `K` automatically. The pure-step side
condition `φ` (e.g. value-hood) is discharged if trivial, else left as a goal. Leaves the
stepped goal *unreduced*; `twp_pure` is the cleaning wrapper. -/
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
    -- `inst` proves the step to `e₂syn`; it is accepted for `e₂` by defeq.
    let e₂ ← displayReduct e₂syn step.names
    -- Fill `K` at the meta level: an `Ectx.fill` redex would hide the next redex from
    -- `twp_pures`.
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

/-- `twp_value` closes a goal `tglWp E e Φ` when `e` is a value `v` (detected via
`e.toVal?`, so it works on raw `.lit`/`.lam`/… values, not just `Exp.ofVal v`),
reducing it to the postcondition `Φ v`. -/
elab "twp_value" : tactic =>
  runTacticTglWp fun mvar { α, GF, instPL, instWp, hyps, E, e, Φ, .. } => do
    -- A closure's value check goes through the kernel (`Exp.closedFunVal?`).
    let tv : Q(Option (Val $α)) ← match ← Exp.closedFunVal? α e with
      | some (some v) => have v : Q(Val $α) := v; pure q(some $v)
      | some none => pure q(none)
      | none => whnf q(Exp.toVal? $e)
    let ~q(some $v) := tv
      | throwTacticEx `twp_value mvar m!"{← ppExpr e} is not a value"
    -- `e.toVal? = some v` holds definitionally (`v` came from whnf of `e.toVal?`);
    -- discharge it with `rfl`.
    let hproof : Q(Exp.toVal? $e = some $v) ← mkFreshExprSyntheticOpaqueMVar
      q(Exp.toVal? $e = some $v)
    (← Tactic.evalTacticAt (← `(tactic| kernel_rfl)) hproof.mvarId!).forM addMVarGoal
    have goal : Q(IProp $GF) := Expr.headBeta q($Φ $v)
    -- iWpValueHead: if the postcondition can absorb a `|={E}=>` (an `ElimModal` exists
    -- whose side condition is dischargeable), leave the clean goal `Φ v`; otherwise hand
    -- back `|={E}=> Φ v` so the user can still update ghost state.
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

/-- `twp_pure [e]` takes one pure step. `twp_pure_core` reduces + re-attaches source
binder names internally; the trailing `simp only [pl_step_simp]` is a *propositional*
rewrite (not defeq, so it can't be in `reduceExp`) that clears a stuck `openRec _ _ v.fst`
left when a substitution flows over an abstract value — replacing a manual
`rw [← Exp.open_lc … v.lc]`. -/
macro "twp_pure" focus:(ppSpace colGt term:max)? : tactic =>
  `(tactic| (twp_pure_core $[$focus]?; try simp only [pl_step_simp]))

/-- `twp_pure_at <e₁> ↦ <e₂>` — explicit pure step with both endpoints pinned. Use when
`twp_pure`'s implicit `PureExec` synthesis fails because typeclass search can't see
through an opaque definition in the LHS. The precondition `φ` stays implicit (synthesized
from the chosen `PureExec` instance) and is discharged by the shared `is_value` tactic,
which covers `True`, value-hood, and the binop/unop/scrut `∧`-conjunctions. -/
macro "twp_pure_at " e1:term:max " ↦ " e2:term:max : tactic =>
  `(tactic| iapply (ErisWpGS.twp_pure_step_fupd
      (n := 1) (e₁ := $e1) (e₂ := $e2) _ (by is_value)))

/-- `twp_pure_at <e₁> ↦ <e₂> by <hφ>` — variant with an explicit proof of the `PureExec`
precondition, for a side condition `is_value` cannot close. -/
macro "twp_pure_at " e1:term:max " ↦ " e2:term:max " by " h:term : tactic =>
  `(tactic| iapply (ErisWpGS.twp_pure_step_fupd
      (n := 1) (e₁ := $e1) (e₂ := $e2) _ $h))

/-- `twp_pures` repeatedly takes pure steps (cleaning up after each) until none apply. -/
macro "twp_pures" : tactic =>
  `(tactic| ((repeat (twp_pure_core; try simp only [pl_step_simp]));
             try simp only [pl_step_simp]))

/-! ## `pure_step` / `pure_steps` — drive a plain `PureSteps` goal

`PureSteps X Y` goals (pure library recursions, e.g. the list/map operations of
`Metrology/Code/Switching.lean`) live entirely outside the Iris proof mode, so these are
ordinary `TacticM` tactics reusing the evaluation-context engine above. -/

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

/-- `pure_step` takes one pure step on a `PureSteps X Y` goal (display cleanup after). -/
macro "pure_step" : tactic =>
  `(tactic| (pure_step_core; try simp only [pl_step_simp]))

/-- `pure_step n` takes exactly `n` pure steps — for stopping right before a recursive
call so that an induction hypothesis can be composed in via `PureSteps.fill`. -/
macro "pure_step " n:num : tactic =>
  `(tactic| iterate $n (pure_step_core; try simp only [pl_step_simp]))

/-- `pure_steps` takes pure steps until none apply, then closes the goal by
reflexivity if the two sides have converged. -/
macro "pure_steps" : tactic =>
  `(tactic| ((repeat (pure_step_core; try simp only [pl_step_simp]));
             (try exact ProbLang.PureSteps.refl _)))

end ProbLang.TotalEris
