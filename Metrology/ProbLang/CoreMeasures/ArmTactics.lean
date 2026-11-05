module

public meta import Lean
public import Mathlib.Tactic.FunProp

@[expose] public section

open Lean Elab Meta

/-! # Reading the arms of a recursion lemma off a definition

`read_arm` reads an arm off a definition, and `apply_arms` applies a recursion lemma with all
arms read. -/

namespace Metrology.CylinderGen

meta section

/-- The branch of `f`'s definition that `f (T.k xs)` takes, by smart unfolding. -/
def unfoldBranch (e : Expr) : MetaM Expr := do
  let some e' ← unfoldDefinition? e.headBeta | throwError "read_arm: cannot unfold {e}"
  whnfCore e'

/-- Proves `∀ xs, f (T.k xs) = ?c a₁ … aₙ` by taking `?c` from the branch of `f` for `k`, with
fields and recursive calls abstracted, and fails if the branch does not factor that way. -/
elab "read_arm" : tactic => Tactic.liftMetaTactic fun g => do
  let (_, g) ← g.intros
  g.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
      | throwError "read_arm: not an equation"
    let .mvar arm := rhs.getAppFn | throwError "read_arm: the arm is already given"
    let branch ← unfoldBranch lhs
    let args := rhs.getAppArgs
    -- abstract the recursive calls `f x` (non-fvar args) before the fields `x`; abstracting `x`
    -- first would destroy the `f x` subterms
    let idxs := Array.range args.size
    let order := idxs.filter (!args[·]!.isFVar) ++ idxs.filter (args[·]!.isFVar)
    let body ← withLocalDeclsD (← args.mapM fun a => return (`y, fun _ => inferType a)) fun ys => do
      let mut b := branch
      for i in order do b := (← kabstract b args[i]!).instantiate1 ys[i]!
      mkLambdaFVars ys b
    unless ← isDefEq (.mvar arm) body do
      throwError "read_arm: the branch {branch} does not factor through {rhs}"
    g.refl
    return []

/-- `apply_arms e` applies a `measurable_struct_rec` or `measurable_cases` lemma `e`, reads every
arm off the definition, and proves the arms measurable with `fun_prop` where it can. -/
macro "apply_arms " e:term : tactic =>
  `(tactic| focus (apply $e; all_goals try first | read_arm | fun_prop))

end

end Metrology.CylinderGen
