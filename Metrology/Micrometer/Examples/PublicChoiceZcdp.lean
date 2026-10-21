module

public import Metrology.Micrometer.Examples.PublicChoice
public import Metrology.TotalEris
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # The public choice terminates, so it is zCDP

Over `ℝ`, `choice b` terminates almost surely (`isProbabilityMeasure_choice`, by a total weakest
precondition in TotalEris), so the two-way pure-DP refinement makes it `(0, (ln 3)² / 2)`-zCDP
(`choice_zCDP_real`) and DP at the `√`-style budget (`choice_DP_sqrt_real`). -/

open Iris Iris.BI Iris.ProofMode ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

namespace ProbLang.PublicChoice

/-- `choice b` terminates: both coins and both branches step to a value. -/
theorem twp_choice {GF : BundledGFunctors} [ErisGS ℝ .hasNoLC GF] (b : Bool) :
    ⊢@{IProp GF} tglWp ⊤ (choice (rT := ℝ) b) (fun _ ↦ iprop(⌜True⌝)) := by
  simp only [choice, RandomizedResponse.rr]
  cases b
  all_goals
    twp_bind pl(rand(#2, #()))
    iapply twp_rand (by norm_num)
    iintro %n %hn
    twp_pures
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · simp only [beq_self_eq_true]
      twp_pures
      twp_bind pl(rand(#4, #()))
      iapply twp_rand (by norm_num)
      iintro %m %hm
      twp_pures
      by_cases hm3 : m < 3
      · simp only [hm3, decide_true]
        twp_pures
        twp_value
        imodintro
        itrivial
      · simp only [hm3, decide_false]
        twp_pures
        twp_value
        imodintro
        itrivial
    · twp_pures
      twp_value
      imodintro
      itrivial

/-- `choice b` terminates almost surely, from every state. -/
theorem isProbabilityMeasure_choice (b : Bool) (σ : State ℝ) :
    MeasureTheory.IsProbabilityMeasure (limExecV ⟨choice (rT := ℝ) b, σ⟩) := by
  have h := twp_mass_lim_exec (GF := erisGF) (e := choice b) (σ := σ) (ε := 0)
    (φ := fun _ => True) (MeasurableSet.const True) fun {_} => by
      iintro -
      iapply twp_choice
  refine ⟨le_antisymm (MeasureTheory.IsSubProbabilityMeasure.measure_le_one _) ?_⟩
  rw [limExecV, asExpr, MeasureTheory.Measure.map_apply Cfg.measurable_expr MeasurableSet.univ,
    Set.preimage_univ]
  simpa using h

/-- The public choice is a Markov kernel. -/
instance isMarkovKernel_choiceMech (σ : State ℝ) :
    ProbabilityTheory.IsMarkovKernel (choiceMech σ) :=
  ⟨fun b ↦ isProbabilityMeasure_choice b σ⟩

/-- The public choice is `(0, (ln 3)² / 2)`-zCDP for any two bits (Def. 2.4). -/
theorem choice_zCDP_real (σ : State ℝ) :
    (choiceMech σ).zCDP ⊤ 0 (ENNReal.ofReal (Real.log 3 ^ 2 / 2)) :=
  choice_zCDP σ

/-- The public choice is `((ln 3)² / 2 + 2 √((ln 3)² / 2 · log (1 / δ)), δ)`-DP at every slack
`0 < δ < 1`. -/
theorem choice_DP_sqrt_real (σ : State ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    (choiceMech σ).DP ⊤
      (ENNReal.ofReal (Real.log 3 ^ 2 / 2 + 2 * √(Real.log 3 ^ 2 / 2 * Real.log (1 / δ))))
      (ENNReal.ofReal δ) :=
  choice_DP_sqrt σ hδ hδ₁

end ProbLang.PublicChoice
