module

public import Metrology.TotalEris
public import Metrology.ProbLang.Test.Rv
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-! # Two worlds: testing a random variable

A random variable equally likely to be `x₀` or `x₁`, tested by an observation that tells them
apart: a first test returns `1` at error `1/2`; after observing `1`, a second test returns `1`. -/

@[expose] public section

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
  ErrorCredit
open MeasureTheory (lintegral_smul_measure lintegral_add_measure lintegral_dirac)
open MeasureTheory.Measure (dirac map_dirac' dirac_apply')
open RvCell (predictive fresh)
open scoped ENNReal AppGS

namespace ProbLang.TotalEris.Examples.TwoWorlds

variable {rT : Type} [MeasurableSpace rT] [ProbLangDist rT] [ProbLangObs rT]
  {n k : ℕ} {v a x₀ x₁ : Val rT}
  (hD : ProbLangDist.dist n v = (2⁻¹ : ℝ≥0∞) • (dirac x₀ + dirac x₁))
  (h₀ : ProbLangObs.obs k (a, x₀) = 0) (h₁ : ProbLangObs.obs k (a, x₁) = 1)
include hD h₀ h₁

/-- A fresh two-world variable predicts `0` and `1` with probability one half each. -/
theorem predictive_fresh :
    predictive ProbLangDist.dist k a (fresh n v) =
      (2⁻¹ : ℝ≥0∞) • (dirac 0 + dirac 1 : MeasureTheory.Measure ℤ) := by
  have := Test.Rv.isProbabilityMeasure_prior hD
  have hm := RvCell.measurable_obs_apply k a
  rw [predictive, RvCell.post_fresh, hD, MeasureTheory.Measure.map_smul,
    MeasureTheory.Measure.map_add _ _ hm, map_dirac' hm, map_dirac' hm, h₀, h₁]
  exact hm.aemeasurable

variable [LawfulProbLangℝ rT] [ProbLangFFI rT] {hlc : HasLC} {GF : BundledGFunctors}
  [ErisGS rT hlc GF] {E : CoPset} {l : Loc}
local bi (IProp GF)

/-- A first test of a fresh two-world variable returns `1`, at error `1/2`. -/
theorem twp_test_fresh :
    iprop(↯(2⁻¹ : ℝ≥0∞) ∗ l ↦ᵣ fresh n v) ⊢
      tglWp E (.test k (.lit (.lbl l)) (.ofVal a)) (fun r => iprop(⌜r = .int 1⌝)) := by
  have := Test.Rv.isProbabilityMeasure_prior hD
  have hε : ∫⁻ y, (if y = 1 then 0 else 1) ∂predictive ProbLangDist.dist k a (fresh n v) ≤
      (2⁻¹ : ℝ≥0∞) := by
    rw [predictive_fresh hD h₀ h₁, lintegral_smul_measure, lintegral_add_measure,
      lintegral_dirac, lintegral_dirac]
    simp
  iintro ⟨Herr, Hl⟩
  iapply twp_test_exp hε
  iframe Herr Hl
  iintro %y Hε -
  by_cases hy : y = 1
  · ipureintro
    rw [hy]
  · simp only [hy, ↓reduceIte]
    iexfalso
    iapply contradict le_rfl $$ Hε

/-- After observing `1`, testing the two-world variable again returns `1`. -/
theorem twp_test_again [ProbLangDist.IsIntValued rT] :
    iprop(l ↦ᵣ (fresh n v).observe k a 1) ⊢
      tglWp E (.test k (.lit (.lbl l)) (.ofVal a)) (fun r => iprop(⌜r = .int 1⌝)) := by
  have hpost := Test.Rv.post_observe_one hD h₀ h₁
  iintro Hl
  iapply twp_test
  iframe Hl
  iintro %y %hy -
  ipureintro
  rw [RvCell.predictive_singleton, hpost,
    dirac_apply' _ (RvCell.measurableSet_obs_fiber k a y)] at hy
  have : ProbLangObs.obs k (a, x₁) = y := by simpa using hy
  rw [← this, h₁]

end ProbLang.TotalEris.Examples.TwoWorlds
