module

public import Metrology.TotalEris.TotalLifting
public import Metrology.ProbLang.EctxTactic
public meta import Metrology.ProbLang.EctxTactic
public import Metrology.ProbLang.Syntax.Notation
public import Iris.ProofMode.ProofModeM
public import Iris.ProofMode.Tactics.Basic
public import Lean
public import Qq

/-!
# `twp_*` tactics

`twp_bind`, `twp_pure`, `twp_pures`, `twp_pure_at` and `twp_value` for `tglWp` goals, on the
evaluation-context engine of `ProbLang/EctxTactic.lean`.
-/

namespace ProbLang.TotalEris

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Meta Elab Tactic Qq Iris Iris.ProofMode

/-! ## Context-lifted pure step -/

section
variable {rT : Type _} [LawfulProbLangℝ rT] {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-- A pure step under an evaluation context `K`; the lemma behind `twp_pure`. -/
public theorem ErisWpGS.twp_pure_step_ctx (K : Ectx rT) (φ : Prop) {n : ℕ} {e₁ e₂ : Exp rT}
    [PureExec φ n e₁ e₂] (Hφ : φ) {E : CoPset} {Φ : Val rT → IProp GF} :
    tglWp E (K.fill e₂) Φ ⊢ tglWp E (K.fill e₁) Φ := by
  let : PureExec φ n (K.fill e₁) (K.fill e₂) := PureExec.fill K
  exact twp_pure_step_fupd φ Hφ

end

/-! ## Goal parsing -/

/-- The pieces of a `tglWp E e Φ` proof-mode goal, with its typeclass instances. -/
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

/-- Run `k` on the main goal, parsed as a `tglWp` goal. -/
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

/-! ## `twp_bind` -/

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
        let body : Q(Exp $α) ← fillQ K q(Exp.ofVal $v)
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

/-! ## `twp_pure` -/

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
    let inner : Q(Exp $α) ← fillQ K e₂
    let pf ← addBIGoal hyps
      q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E $inner $Φ)
    let HΦ : Q($φ) ← mkFreshExprSyntheticOpaqueMVar q($φ)
    (← Tactic.evalTacticAt (← `(tactic| (try is_value))) HΦ.mvarId!).forM addMVarGoal
    let stepPf ← mkAppOptM ``ProbLang.TotalEris.ErisWpGS.twp_pure_step_ctx
      (#[α, instPL, GF, instWp, K, φ, n, e₁, e₂, step.inst, HΦ, E, Φ].map some)
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, stepPf]
    mvar.assign transPf

/-! ## `twp_value` -/

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

/-! ## Composite tactics -/

-- `pl_step_simp` is propositional, so it cannot live in the defeq-only `reduceExp`.
/-- `twp_pure [e]` takes one pure step. -/
macro "twp_pure" focus:(ppSpace colGt term:max)? : tactic =>
  `(tactic| (twp_pure_core $[$focus]?; try simp only [pl_step_simp]))

/-- `twp_pure_at e₁ ↦ e₂` takes one `PureExec` step from `e₁` to `e₂`, given explicitly, for when
synthesis cannot see through an opaque definition in `e₁`. -/
macro "twp_pure_at " e1:term:max " ↦ " e2:term:max : tactic =>
  `(tactic| iapply (ErisWpGS.twp_pure_step_fupd
      (n := 1) (e₁ := $e1) (e₂ := $e2) _ (by is_value)))

/-- `twp_pure_at e₁ ↦ e₂ by hφ` supplies the precondition `is_value` cannot close. -/
macro "twp_pure_at " e1:term:max " ↦ " e2:term:max " by " h:term : tactic =>
  `(tactic| iapply (ErisWpGS.twp_pure_step_fupd
      (n := 1) (e₁ := $e1) (e₂ := $e2) _ $h))

/-- `twp_pures` takes pure steps until none applies. -/
macro "twp_pures" : tactic =>
  `(tactic| ((repeat (twp_pure_core; try simp only [pl_step_simp]));
             try simp only [pl_step_simp]))

end ProbLang.TotalEris
