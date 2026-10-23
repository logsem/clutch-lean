module

public import Metrology.ProbLang.Syntax.Types
public meta import Metrology.ProbLang.Syntax.Types

@[expose] public section

/-!
# `typecheck`: a bidirectional elaborator for `Typed Γ e τ`

Check mode (`checkMVar`) handles pair, inl, inr; synth mode (`synth`) handles fvar, lit, fst, snd.
Other forms are still TODO.
-/

namespace ProbLang

open Lean Elab Term Tactic Meta

/-- Splits a goal `Typed Γ e τ` into `Γ`, the weak-head normal `e`, and `τ`. -/
meta def asTypedGoal (goal : Expr) : TermElabM (Expr × Expr × Expr) := do
  let goal ← whnf goal
  unless goal.isAppOf ``Typed && 3 ≤ goal.getAppNumArgs do
    throwError "typecheck: expected type is not `Typed Γ e τ`:{indentExpr goal}"
  let n := goal.getAppNumArgs
  return (goal.getArg! (n - 3), ← whnf (goal.getArg! (n - 2)), goal.getArg! (n - 1))

mutual

/-- Returns `τ` and a proof of `Typed Γ e τ`, with `τ` determined by the head of `e`. -/
meta partial def synth (Γ e : Expr) : TermElabM (Expr × Expr) := do
  let e ← whnf e
  let rT := (← inferType e).getArg! 0
  match e.getAppFn.constName? with
  | some ``Exp.fvar =>
      -- `rfl` on `Γ x = some ?τ` assigns `?τ`.
      let τ ← mkFreshExprMVar (mkConst ``Ty)
      let lookupTy ← mkAppM ``Eq #[← mkAppM' Γ #[e.getArg! 1], ← mkAppM ``Option.some #[τ]]
      let lookup ← mkFreshExprMVar lookupTy
      lookup.mvarId!.refl
      let proof ← mkAppOptM ``Typed.fvar #[rT, Γ, none, τ, lookup]
      return (← instantiateMVars τ, proof)
  | some ``Exp.lit =>
      let arg := (e.getArg! 1).consumeMData
      match arg.getAppFn.constName? with
      | some ``BaseLit.int  =>
          return (mkConst ``Ty.int,  ← mkAppOptM ``Typed.lit_int  #[rT, Γ, arg.getArg! 1])
      | some ``BaseLit.bool =>
          return (mkConst ``Ty.bool, ← mkAppOptM ``Typed.lit_bool #[rT, Γ, arg.getArg! 1])
      | some ``BaseLit.unit =>
          return (mkConst ``Ty.unit, ← mkAppOptM ``Typed.lit_unit #[rT, Γ])
      | _ => throwError "typecheck/synth: unsupported literal {arg}"
  | some ``Exp.fst | some ``Exp.snd =>
      let τ1 ← mkFreshExprMVar (mkConst ``Ty)
      let τ2 ← mkFreshExprMVar (mkConst ``Ty)
      let h ← checkSub Γ (e.getArg! 1) (← mkAppM ``Ty.prod #[τ1, τ2])
      if e.isAppOf ``Exp.fst then
        return (← instantiateMVars τ1, ← mkAppM ``Typed.fst #[h])
      else
        return (← instantiateMVars τ2, ← mkAppM ``Typed.snd #[h])
  | some c => throwError "typecheck/synth: TODO `{c}` is not yet in synth mode"
  | none   => throwError "typecheck/synth: cannot determine head:{indentExpr e}"

/-- Closes `mvar : Typed Γ e τ` with `τ` fixed. -/
meta partial def checkMVar (mvar : MVarId) : TermElabM Unit := mvar.withContext do
  let (Γ, e, τ) ← asTypedGoal (← mvar.getType)
  let τ ← whnf τ
  match e.getAppFn.constName? with
  | some ``Exp.pair =>
      let some (τ1, τ2) := τ.app2? ``Ty.prod
        | throwError "typecheck/check pair: expected a product type, got{indentExpr τ}"
      let h1 ← checkSub Γ (e.getArg! 1) τ1
      let h2 ← checkSub Γ (e.getArg! 2) τ2
      mvar.assign (← mkAppM ``Typed.pair #[h1, h2])
  | some ``Exp.inl =>
      let some (τ1, τ2) := τ.app2? ``Ty.sum
        | throwError "typecheck/check inl: expected a sum type, got{indentExpr τ}"
      let h ← checkSub Γ (e.getArg! 1) τ1
      mvar.assign (← mkAppOptM ``Typed.inl #[none, Γ, e.getArg! 1, τ1, τ2, h])
  | some ``Exp.inr =>
      let some (τ1, τ2) := τ.app2? ``Ty.sum
        | throwError "typecheck/check inr: expected a sum type, got{indentExpr τ}"
      let h ← checkSub Γ (e.getArg! 1) τ2
      mvar.assign (← mkAppOptM ``Typed.inr #[none, Γ, e.getArg! 1, τ1, τ2, h])
  | some ``Exp.fvar | some ``Exp.lit | some ``Exp.fst | some ``Exp.snd =>
      let (τ', proof) ← synth Γ e
      unless ← isDefEq τ τ' do
        throwError "typecheck/switch: inferred type{indentExpr τ'}\n\
                    does not match expected{indentExpr τ}"
      mvar.assign proof
  | some c => throwError "typecheck/check: TODO unsupported expression head `{c}`"
  | none   => throwError "typecheck/check: cannot determine head:{indentExpr e}"

/-- Checks `Typed Γ e τ` for a fresh goal and returns its proof. -/
meta partial def checkSub (Γ e τ : Expr) : TermElabM Expr := do
  let sub ← mkFreshExprMVar (← mkAppM ``Typed #[Γ, e, τ])
  checkMVar sub.mvarId!
  return sub

end

elab "typecheck" : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  let mvar ← mkFreshExprMVar expectedType
  checkMVar mvar.mvarId!
  instantiateMVars mvar

elab "typecheck" : tactic => do
  let mvar ← getMainGoal
  TermElabM.run' (checkMVar mvar)

section Examples

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]

example : Typed (rT := rT) Tctx.empty (.lit (.int 42)) .int := typecheck
example : Typed (rT := rT) Tctx.empty (.pair (.lit (.int 1)) (.lit .unit)) (.prod .int .unit) :=
  typecheck
example : Typed (rT := rT) (Tctx.empty.insert "x" .bool) (.fvar "x") .bool := typecheck
example : Typed (rT := rT) Tctx.empty (.inl (.lit (.bool true))) (.sum .bool .int) := typecheck

example : Typed (rT := rT) Tctx.empty
    (.fst (.pair (.lit (.int 7)) (.lit (.bool false)))) .int := typecheck

example : Typed (rT := rT) Tctx.empty (.lit (.int 42)) .int := by typecheck

end Examples

end ProbLang
