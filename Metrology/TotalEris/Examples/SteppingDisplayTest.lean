module

public import Metrology.TotalEris
public import Metrology.TotalEris.Examples.GeometricTotal
public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric
import Metrology.Iris.LocalBI

@[expose] public section

/-!
# Display-golden tests for `twp_*` stepping

Each stepped goal must render with named binders, folded recursive constants, and
normalized literals: no `⟪bvar n⟫`, raw `.lam`/`.fix`/`.case`, or `#(1 + 2)`.
-/

open Iris ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS

-- `show_goal_render` leaves the proof state unchanged by design.
set_option linter.unusedTactic false

namespace ProbLang
namespace TotalEris
namespace SteppingDisplayTest

open Lean Elab Tactic in
/-- Log the main-goal target without the hypotheses. -/
elab "show_goal_render" : tactic => do
  logInfo m!"{← getMainTarget}"

set_option pp.unicode.fun true

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi IProp GF
variable (E : CoPset) (Φ : Val rT → IProp GF)

-- Closes the (generally unprovable) residual goals without `sorry`.
variable (hstop : ∀ Q : IProp GF, ⊢ Q)

/-! ## β-reduction -/

/-- info: ⊢ tglWp E pl(#2 + #1) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl((fun x, x + #1) #2) Φ := by
  twp_pure pl((fun x, x + #1) #2)
  show_goal_render
  exact hstop _

/-! ## β-reduction keeps the source name of an inner binder -/

/-- info: ⊢ tglWp E pl(fun y, #1) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl((fun x, fun y, x) #1) Φ := by
  twp_pure pl((fun x, fun y, x) #1)
  show_goal_render
  exact hstop _

/-! ## Conditionals -/

/-- info: ⊢ tglWp E pl(#1) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(if #true then #1 else #2) Φ := by
  twp_pure pl(if #true then #1 else #2)
  show_goal_render
  exact hstop _

/-- info: ⊢ tglWp E pl(#2) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(if #false then #1 else #2) Φ := by
  twp_pure pl(if #false then #1 else #2)
  show_goal_render
  exact hstop _

/-! ## Binary operators -/

/-- info: ⊢ tglWp E pl(#3) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#1 + #2) Φ := by
  twp_pure pl(#1 + #2)
  show_goal_render
  exact hstop _

/-! ## Projections -/

/-- info: ⊢ tglWp E pl(#1) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(fst((#1, #2))) Φ := by
  twp_pure pl(fst((#1, #2)))
  show_goal_render
  exact hstop _

/-- info: ⊢ tglWp E pl(#2) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(snd((#1, #2))) Φ := by
  twp_pure pl(snd((#1, #2)))
  show_goal_render
  exact hstop _

/-! ## Let-binding -/

/-- info: ⊢ tglWp E pl(#1 + #2) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(let x := #1; x + #2) Φ := by
  twp_pure pl((fun x, x + #2) #1)
  show_goal_render
  exact hstop _

/-! ## Recursive constants -/

@[pl_fold]
def loopFolded : Exp rT := pl% rec f n := if n = #0 then #0 else f (n - #1)

-- Not defeq to any `@[pl_fold]` constant.
def loopBare : Exp rT := pl% rec f n := if n = #0 then #7 else f (n - #2)

/-- info: ⊢ tglWp E pl(#0) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(&loopFolded #2) Φ := by
  twp_pures
  show_goal_render
  exact hstop _

/-- info: ⊢ tglWp E pl(#0) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(&loopFolded #2) Φ := by
  rw [loopFolded]
  twp_pures
  show_goal_render
  exact hstop _

/-- info: ⊢ tglWp E pl(#7) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(&loopBare #2) Φ := by
  twp_pures
  show_goal_render
  exact hstop _

/-! ## β-reduction keeps a surviving binder used in the body -/

/-- info: ⊢ tglWp E pl(fun y, #1 + y) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl((fun x, fun y, x + y) #1) Φ := by
  twp_pure pl((fun x, fun y, x + y) #1)
  show_goal_render
  exact hstop _

/-! ## Unary operators -/

/-- info: ⊢ tglWp E pl(#false) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(~#true) Φ := by
  twp_pure pl(~#true); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#(-5)) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(-#5) Φ := by
  twp_pure pl(-#5); show_goal_render; exact hstop _

/-! ## More binary operators -/

/-- info: ⊢ tglWp E pl(#3) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#5 - #2) Φ := by
  twp_pure pl(#5 - #2); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#12) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#3 * #4) Φ := by
  twp_pure pl(#3 * #4); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#true) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#2 < #3) Φ := by
  twp_pure pl(#2 < #3); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#false) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#true && #false) Φ := by
  twp_pure pl(#true && #false); show_goal_render; exact hstop _

/-! ## `scrut` and `case` -/

/-- info: ⊢ tglWp E pl(inl(#1)) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(scrut inl(#1) with inl(x)) Φ := by
  twp_pure pl(scrut inl(#1) with inl(x))
  show_goal_render
  exact hstop _

/--
info:
⊢
tglWp E
  pl(case scrut inl(#1) with inl(_) | _ => fun _, let x := _; x + #1 | _ =>
      fun _, case scrut inl(#1) with inr(_) | _ => fun _, let y := _; y | _ => fun _, fail)
  Φ
-/
#guard_msgs (info) in
example : ⊢ tglWp E pl(case inl(#1) | inl(x) => x + #1 | inr(y) => y) Φ := by
  twp_pure pl(case inl(#1) | inl(x) => x + #1 | inr(y) => y)
  show_goal_render
  exact hstop _

/-! ## Multi-step `twp_pures` -/

/-- info: ⊢ tglWp E pl(#3) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(let x := #1; let y := #2; x + y) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## End-to-end -/

example : ⊢ tglWp E pl(fst(((fun x, x) #1, #2)))
    (fun w : Val rT => iprop(⌜w = .int 1⌝)) := by
  twp_pures; twp_value; ipureintro; rfl

/-! ## `twp_bind`

An opaque bound value has no surface syntax, so it renders as `{Exp.ofVal v}`. -/

/--
info:
⊢ tglWp E pl(fst((#2, #3))) fun v ↦ tglWp E pl(#1 + {Exp.ofVal v}) Φ
-/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#1 + fst((#2, #3))) Φ := by
  twp_bind pl(fst((#2, #3))); show_goal_render; exact hstop _

/-! ## `twp_value` -/

/-- info: ⊢ |={E}=> True -/
#guard_msgs (info) in
example : ⊢ tglWp E pl((#1, #2))
    (fun _ : Val rT => iprop(⌜True⌝)) := by
  twp_value; show_goal_render; exact hstop _

/-! ## `@[pl_names]` sampler stalled at `rand` -/

@[pl_names]
def randLoop : Exp rT := pl% rec f n := if rand(#2, #()) = #0 then n else f (n + #1)

/--
info:
⊢ tglWp E pl(if rand(#2, #()) = #0 then #0 else (rec f n := if rand(#2, #()) = #0 then n else f (n + #1)) (#0 + #1)) Φ
-/
#guard_msgs (info) in
example : ⊢ tglWp E pl(&randLoop #0) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## More binary operators -/

/-- info: ⊢ tglWp E pl(#3) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#6 / #2) Φ := by
  twp_pure pl(#6 / #2); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#1) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#7 % #3) Φ := by
  twp_pure pl(#7 % #3); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#true) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#true || #false) Φ := by
  twp_pure pl(#true || #false); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#true) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#true ^^ #false) Φ := by
  twp_pure pl(#true ^^ #false); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#true) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#2 <= #3) Φ := by
  twp_pure pl(#2 <= #3); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#true) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#1 = #1) Φ := by
  twp_pure pl(#1 = #1); show_goal_render; exact hstop _

/-! ## Division and modulo by zero (`Int` semantics) -/

/-- info: ⊢ tglWp E pl(#0) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#6 / #0) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#7) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(#7 % #0) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## `fail` is stuck -/

/-- info: ⊢ tglWp E pl(fail) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(fail) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## `let!` and `assert` -/

/-- info: ⊢ tglWp E pl(#3) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(let! (a, b) := (#1, #2); a + b) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#()) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(assert(#true)) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## Free-variable application -/

/-- info: ⊢ tglWp E pl(f x y) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(f x y) Φ := by
  show_goal_render; exact hstop _

/-! ## Recursion after explicit unfolding -/

/-- info: ⊢ tglWp E pl(#0) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(&loopFolded #2) Φ := by
  rw [loopFolded]; twp_pures; twp_pures; show_goal_render; exact hstop _

/-! ## `twp_bind` on `alloc` -/

/--
info:
⊢ tglWp E pl(alloc(#1)) fun v ↦ tglWp E pl(!{Exp.ofVal v}) Φ
-/
#guard_msgs (info) in
example : ⊢ tglWp E pl(!alloc(#1)) Φ := by
  twp_bind pl(alloc(#1)); show_goal_render; exact hstop _

/-! ## `twp_bind` on `urand` -/

/--
info:
⊢ tglWp E pl(urand) fun v ↦ tglWp E pl({Exp.ofVal v} + {Exp.ofVal ↑1}) Φ
-/
#guard_msgs (info) in
example : ⊢ tglWp E pl(urand + #1) Φ := by
  twp_bind pl(urand); show_goal_render; exact hstop _

/-! ## Library samplers `geometric` and `GeometricTrial` -/

/--
info:
⊢ tglWp E pl(if rand(#2, #()) = #0 then #0 else (rec geo n := if rand(#2, #()) = #0 then #0 else geo n + #1) #() + #1) Φ
-/
#guard_msgs (info) in
example : ⊢ tglWp E (Exp.app Examples.geometric (.lit .unit)) Φ := by
  twp_pures; show_goal_render; exact hstop _

-- `f` is not a value, so β does not fire.
/-- info: ⊢ tglWp E pl(&Examples.GeometricTrial f #0) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl(&Examples.GeometricTrial f #0) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## β-reduction keeps both substituted and surviving binder names -/

/-- info: ⊢ tglWp E pl((fun z, #3, fun y, #2)) Φ -/
#guard_msgs (info) in
example : ⊢ tglWp E pl((fun x, (x, fun y, #2)) (fun z, #3)) Φ := by
  twp_pure pl((fun x, (x, fun y, #2)) (fun z, #3))
  show_goal_render
  exact hstop _

end SteppingDisplayTest

end TotalEris
end ProbLang
