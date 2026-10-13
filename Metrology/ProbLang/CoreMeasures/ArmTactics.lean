module

public meta import Lean
public import Mathlib.Tactic.FunProp

@[expose] public section

open Lean Elab Meta

/-!
# Reading the arms of a recursion lemma off a definition

`T.measurable_struct_rec` and `T.measurable_cases` (from deriving `MeasurableSpace`) ask for one arm `c_k` per
constructor, with an equation `f (T.k xs) = c_k …`. The arms are the branches of `f`'s own
definition: `read_arm` reads one off it, and `apply_arms` applies such a lemma with all its
arms read off and their measurability proved by `fun_prop`.
-/

namespace Metrology.CylinderGen

meta section

/-- The branch of `f`'s definition that `f (T.k xs)` takes, by smart unfolding. -/
def unfoldBranch (e : Expr) : MetaM Expr := do
  let some e' ← unfoldDefinition? e.headBeta | throwError "read_arm: cannot unfold {e}"
  whnfCore e'

/-- Proves `∀ xs, f (T.k xs) = ?c a₁ … aₙ` by taking `?c` from the branch of `f` for `k`, with the
arguments `aᵢ` (fields, and `f` of the recursive fields) abstracted. Fails if the branch does not
factor that way, such as when it uses a recursive field other than through `f`. -/
elab "read_arm" : tactic => Tactic.liftMetaTactic fun g => do
  let (_, g) ← g.intros
  g.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
      | throwError "read_arm: not an equation"
    let .mvar arm := rhs.getAppFn | throwError "read_arm: the arm is already given"
    let branch ← unfoldBranch lhs
    let args := rhs.getAppArgs
    -- abstract the recursive calls before the fields they mention
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
arm off the definition, and proves the arms measurable with `fun_prop` where it can. The goals left
are the equations `read_arm` cannot factor, the measurability goals `fun_prop` cannot prove, and the
shifts `t_c` that unification does not determine. -/
macro "apply_arms " e:term : tactic =>
  `(tactic| focus (apply $e; all_goals try first | read_arm | fun_prop))

end

end Metrology.CylinderGen
