module

public import Metrology.ProbLang.Erasure.RvResolve

/-! # Random variables: a two-world example

A uniform random variable tested by an observation that tells its two values apart. -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory ENNReal

namespace ProbLang.Test.Rv

open ProbLangObs RvCell Cfg

variable {rT : Type} [MeasurableSpace rT] {σ : State rT} {l : Lbl} {n k : ℕ} {v a x₀ x₁ : Val rT}

/-- The two-world prior is a probability measure. -/
theorem isProbabilityMeasure_prior [ProbLangDist rT]
    (hD : ProbLangDist.dist n v = (2⁻¹ : ℝ≥0∞) • (dirac x₀ + dirac x₁)) :
    IsProbabilityMeasure (ProbLangDist.dist n v) := by
  rw [hD]
  constructor
  simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top]

/-- The fiber of observing `1` holds `x₁` and not `x₀`. -/
theorem fiber_one [ProbLangObs rT] (h₀ : obs k (a, x₀) = 0) (h₁ : obs k (a, x₁) = 1) :
    ((2⁻¹ : ℝ≥0∞) • (dirac x₀ + dirac x₁) : Measure (Val rT))
      ((fun x => obs k (a, x)) ⁻¹' {1}) = 2⁻¹ := by
  have hs := measurableSet_obs_fiber k a 1
  simp [dirac_apply' _ hs, h₀, h₁]

variable [ProbLangDist rT] [ProbLangObs rT]
  (hD : ProbLangDist.dist n v = (2⁻¹ : ℝ≥0∞) • (dirac x₀ + dirac x₁))
  (h₀ : obs k (a, x₀) = 0) (h₁ : obs k (a, x₁) = 1)
include hD h₀ h₁

/-- After observing `1`, the posterior is the point mass at `x₁`. -/
theorem post_observe_one :
    ((fresh n v).observe k a 1).post ProbLangDist.dist = dirac x₁ := by
  classical
  have := isProbabilityMeasure_prior hD
  have hs := measurableSet_obs_fiber k a 1
  rw [post_observe rfl, post_fresh, ProbabilityTheory.cond, hD, fiber_one h₀ h₁,
    Measure.restrict_smul, Measure.restrict_add, restrict_dirac' hs, restrict_dirac' hs]
  simp [h₀, h₁, smul_smul, ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top]

/-- After observing `1`, testing again returns `1` surely. -/
theorem test_after_one (hσ : σ.rvs[l]? = some ((fresh n v).observe k a 1)) :
    test k a l σ = dirac (testOutcome k a l σ ((fresh n v).observe k a 1) 1) := by
  rw [test_eq_map hσ, post_observe_one hD h₀ h₁, map_dirac' measurable_testOutcome, h₁]

variable [LawfulProbLangℝ rT]

/-- The first test observes `1` with the prior probability of `x₁`. -/
theorem test_fresh_one (hσ : σ.rvs[l]? = some (fresh n v)) :
    test k a l σ {testOutcome k a l σ (fresh n v) 1} = 2⁻¹ := by
  have := isProbabilityMeasure_prior hD
  rw [test_apply_testOutcome hσ, post_fresh, hD]
  exact fiber_one h₀ h₁

end ProbLang.Test.Rv
