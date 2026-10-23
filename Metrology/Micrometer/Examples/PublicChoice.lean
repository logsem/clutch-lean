module

public import Metrology.Code.PublicChoice
public import Metrology.Micrometer.CouplingRulesLaw
public import Metrology.Micrometer.Examples.RandomizedResponse.Dp
public import Metrology.Micrometer.MechanismZcdp
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Algebra.Regular.Prod
import Metrology.Iris.LocalBI

@[expose] public section

/-! # The DP choice law: a public coin picks one of two mechanisms

`choice_refines` proves `choice b ≲ choice b'` from the budget `(ln 3, 0)` via the DP choice law,
giving `(ln 3, 0)`-DP (`choice_DP`) and, refining both ways, zCDP (`choice_zCDP`). -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting ProbabilityTheory
open GradedDivergence (dp codensity)
open scoped ENNReal

namespace ProbLang
namespace PublicChoice

open RandomizedResponse (budget rr_refines)
open ENNReal (ofReal)
open Real (log coe_toNNReal log_nonneg)
open IsReflexive (refl)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF]
local bi IProp GF

/-- `choice b` refines `choice b'` at equal reports, spending `(ln 3, 0)` by the choice law. -/
theorem choice_refines (b b' : Bool) :
    ⊢ ↯b budget -∗ REL[codensity dp] (choice (rT := rT) b) << choice b' : lrel_bool := by
  -- put `budget` in the choice law's shape `(max (ε₁+ε₂) (ε₁'+ε₂'), δ₁+δ₁'+δ₂)`
  rw [show budget = (max (0 + ofReal (log 3)) (0 + 0), 0 + 0 + 0) by simp]
  iintro Hb
  -- identity coupling; `P = T = {0}` are the draws that run `rr` and get `ε₂ = ln 3`, the rest
  -- get `ε₂' = 0` (the two `e ▸ h` proofs keep `{0}` in `{0}` and its complement out)
  rel_apply (refines_couple_rands_dpChoice
    (ε₂ := ofReal (log 3)) (ε₂' := 0) (δ₂ := 0) (T := {0}) 2 (by norm_num)
    (refl _) (refl _) (fun _ _ h e ↦ e ▸ h) (fun _ _ h e ↦ e ▸ h)
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

section Mech

variable (σ : State rT)

/-- The mechanism running `choice` on a private bit from state `σ`. -/
noncomputable abbrev choiceMech : Mechanism Bool (Exp rT) :=
  progMech choice σ

/-- The public choice is `(ln 3, 0)`-DP for any two bits (Def. 2.1). -/
theorem choice_DP : (choiceMech σ).DP ⊤ (ofReal (log 3)) 0 :=
  progMech_isPrivate (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) choice σ budget
    (fun _ _ ↦ lrel_bool) (fun _ _ ↦ lrel_bool_car_eq) fun b b' _ _ _ ↦ choice_refines b b'

variable [IsMarkovKernel (choiceMech σ)]

/-- The public choice is `(0, (ln 3)² / 2)`-zCDP, given that it terminates almost surely: it
refines both ways at `(ln 3, 0)` (Bun–Steinke 2016, Prop. 3.3). -/
theorem choice_zCDP : (choiceMech σ).zCDP ⊤ 0 (ofReal (log 3 ^ 2 / 2)) := by
  have := progMech_zCDP_of_dp (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) choice σ (adj := ⊤)
    (log 3).toNNReal (fun _ _ ↦ lrel_bool) (fun _ _ ↦ lrel_bool_car_eq)
    (fun b b' _ _ _ ↦ choice_refines b b') fun b b' _ _ _ ↦ choice_refines b' b
  rwa [coe_toNNReal _ (log_nonneg (by norm_num))] at this

/-- The public choice is `((ln 3)² / 2 + 2 √((ln 3)² / 2 · log (1 / δ)), δ)`-DP at every slack
`0 < δ < 1`, given that it terminates almost surely. -/
theorem choice_DP_sqrt {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    (choiceMech σ).DP ⊤
      (ofReal (log 3 ^ 2 / 2 + 2 * √(log 3 ^ 2 / 2 * log (1 / δ)))) (ofReal δ) := by
  have := Kernel.DP_of_zCDP_sq (ε := (log 3).toNNReal) hδ hδ₁
    (by rw [coe_toNNReal _ (log_nonneg (by norm_num))]; exact choice_zCDP σ)
  rwa [coe_toNNReal _ (log_nonneg (by norm_num))] at this

end Mech

end PublicChoice
end ProbLang
