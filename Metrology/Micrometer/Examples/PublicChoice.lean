module

public import Metrology.Code.PublicChoice
public import Metrology.Micrometer.CouplingRulesLaw
public import Metrology.Micrometer.Examples.RandomizedResponse.Dp
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Algebra.Regular.Prod

@[expose] public section

/-! # The DP choice law: a public coin picks one of two mechanisms

`choice_refines` proves `choice b ≲ choice b'` from the budget `(ln 3, 0)` via the DP choice law
(which charges the larger branch cost); `choice_DP` turns it into `(ln 3, 0)`-DP of `choice`. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp codensity)
open scoped ENNReal

namespace ProbLang
namespace PublicChoice

open RandomizedResponse (budget rr_refines)

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- `choice b` refines `choice b'` at equal reports, spending `(ln 3, 0)` by the choice law. -/
theorem choice_refines {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b b' : Bool) :
    ⊢@{IProp GF} ↯b budget -∗ REL[codensity dp] (choice (rT := rT) b) << choice b' : lrel_bool := by
  -- put `budget` in the choice law's shape `(max (ε₁+ε₂) (ε₁'+ε₂'), δ₁+δ₁'+δ₂)`
  rw [show budget = (max (0 + ENNReal.ofReal (Real.log 3)) (0 + 0), 0 + 0 + 0) by simp]
  iintro Hb
  -- identity coupling; `P = T = {0}` are the draws that run `rr` and get `ε₂ = ln 3`, the rest
  -- get `ε₂' = 0` (the two `e ▸ h` proofs keep `{0}` in `{0}` and its complement out)
  rel_apply (refines_couple_rands_dpChoice (ε₁ := 0) (δ₁ := 0) (ε₁' := 0) (δ₁' := 0)
    (ε₂ := ENNReal.ofReal (Real.log 3)) (ε₂' := 0) (δ₂ := 0) (P := {0}) (T := {0}) 2 (by norm_num)
    (IsReflexive.refl _) (IsReflexive.refl _) (fun _ _ h e ↦ e ▸ h) (fun _ _ h e ↦ e ▸ h)
    (by simp))
  iframe Hb
  -- either coupling is equality
  iintro %r %_ %(rfl | rfl) Hr
  all_goals
    obtain rfl | h0 := eq_or_ne r 0
    · simp only [choiceBudget, Set.mem_singleton_iff, ↓reduceIte]
      rel_pures
      iapply rr_refines b b' $$ Hr
    · rel_pures
      rel_values

/-- The mechanism running `choice` on a private bit from state `σ`. -/
noncomputable abbrev choiceMech (σ : State rT) : Mechanism Bool (Exp rT) :=
  progMech choice σ

/-- The public choice is `(ln 3, 0)`-DP for any two bits (Def. 2.1). -/
theorem choice_DP (σ : State rT) : (choiceMech σ).DP ⊤ (ENNReal.ofReal (Real.log 3)) 0 :=
  progMech_isPrivate (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) (L := codensity dp) choice σ budget
    (fun _ _ ↦ lrel_bool) (fun _ _ ↦ lrel_bool_car_eq) fun b b' _ _ _ ↦ choice_refines b b'

end PublicChoice
end ProbLang
