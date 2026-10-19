module

public import Metrology.Code.PublicChoice
public import Metrology.Micrometer.ChoiceRules
public import Metrology.Micrometer.Examples.RandomizedResponse
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Algebra.Regular.Prod

@[expose] public section

/-! # The DP choice law: a public coin picks one of two mechanisms

The coin is coupled along equality at no cost; the choice law then leaves `↯b (ln 3, 0)` to the
randomized response branch and `↯b 0` to the constant branch, so the program is `ln 3`-DP, the
larger of the two costs rather than their sum. -/

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
  rw [show budget = (max (0 + ENNReal.ofReal (Real.log 3)) (0 + 0), 0 + 0 + 0) by simp]
  iintro Hb
  rel_apply (refines_couple_rands_dpChoice (ε₁ := 0) (δ₁ := 0) (ε₁' := 0) (δ₁' := 0)
    (ε₂ := ENNReal.ofReal (Real.log 3)) (ε₂' := 0) (δ₂ := 0) (P := {0}) (T := {0}) 2 (by norm_num)
    (IsReflexive.refl _) (IsReflexive.refl _) (fun _ _ h e ↦ e ▸ h) (fun _ _ h e ↦ e ▸ h)
    (by simp))
  iframe Hb
  iintro %r %_ %(rfl | rfl) Hr
  all_goals
    rel_pures
    by_cases h0 : r = 0
    · subst h0
      simp only [choiceBudget, Set.mem_singleton_iff, ↓reduceIte, beq_self_eq_true]
      rel_pures
      iapply rr_refines b b' $$ Hr
    · rw [beq_eq_false_iff_ne.2 (by simpa using h0)]
      rel_pures
      rel_values

/-- `choice` on private bits, started from state `σ`. -/
noncomputable def choiceMech (σ : State rT) : Mechanism Bool (Exp rT) :=
  ⟨fun b ↦ limExecV ⟨choice b, σ⟩, .of_discrete⟩

/-- The public choice is `(ln 3, 0)`-DP for any two bits (Def. 2.1). -/
theorem choice_DP (σ : State rT) : (choiceMech σ).DP ⊤ (ENNReal.ofReal (Real.log 3)) 0 :=
  fun b b' _ ↦ approximates_div (GF := MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) (L := codensity dp)
    (fun _ _ ↦ lrel_bool) _ _ σ σ budget
    (fun _ _ _ _ ↦ by iunfold lrel_bool; iintro ⟨%c, %⟨rfl, rfl⟩⟩; ipureintro; rfl)
    fun _ _ ↦ choice_refines b b'

end PublicChoice
end ProbLang
