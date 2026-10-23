module

public import Metrology.Couplings.Divergences.GaussianRenyi

/-! # Gaussian composition

`k` Gaussian queries composed in the zCDP lifting are `(ε, δ)`-DP with `ε` of order `√k`
(`DP_gaussianMechPow_sqrt`). -/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory GradedLifting GradedDivergence Real Set ENNReal
open scoped ENNReal NNReal

namespace Mechanism

/-! ## Composition in the zCDP lifting and DP bounds -/

variable {σ : ℝ≥0} (r : ℝ) {δ : ℝ}

/-- `k` Gaussian queries of inputs at distance at most `r` lift equality in the zCDP lifting at
`k` times the budget `r² / (2 σ²)` of one query. -/
theorem zcdpLifting_rel_gaussianMechPow (hσ : σ ≠ 0) {a a' : ℝ} (h : |a - a'| ≤ r) (k : ℕ) :
    zcdpLifting.Rel (0, k * ENNReal.ofReal (r ^ 2 / (2 * (σ : ℝ) ^ 2))) (· = ·)
      (gaussianMechPow σ k a) (gaussianMechPow σ k a') := by
  set ρ := ENNReal.ofReal (r ^ 2 / (2 * (σ : ℝ) ^ 2))
  induction k with
  | zero =>
    rw [gaussianMechPow_zero_apply, gaussianMechPow_zero_apply, Nat.cast_zero, zero_mul]
    exact IsReflexive.refl _
  | succ k ih =>
    have hb : ((0 : ℝ≥0∞), ((k + 1 : ℕ) : ℝ≥0∞) * ρ) = (0, ρ) + (0, k * ρ) := by
      rw [Prod.mk_add_mk, add_zero, Nat.cast_succ, add_one_mul, add_comm]
    rw [gaussianMechPow_succ_apply, gaussianMechPow_succ_apply, hb]
    exact ((concentratedLifting_complete (zCDP_gaussianMech hσ r h)).prod_of_isTopAbsorbing
      ih).map fun p q h ↦ by rw [Prod.ext h.1 h.2]

/-- `k` Gaussian queries with standard deviation `σ` are `(ε, δ)`-DP for inputs at distance at
most `r`, with `ε` the best Rényi conversion of the composed zCDP budget `k r² / (2 σ²)`. -/
theorem DP_gaussianMechPow (hσ : σ ≠ 0) (hδ : 0 < δ) (k : ℕ) :
    (gaussianMechPow σ k).DP (fun a a' ↦ |a - a'| ≤ r)
      (⨅ α ∈ Ioi (1 : ℝ), ENNReal.ofReal α * (k * ENNReal.ofReal (r ^ 2 / (2 * (σ : ℝ) ^ 2))) +
        ENNReal.ofReal (Real.log (1 / δ) / (α - 1)))
      (ENNReal.ofReal δ) := fun a a' h ↦ by
  simpa using codensity_sound
    ((LiftingRelHom.zcdpToDp hδ).map_rel (zcdpLifting_rel_gaussianMechPow r hσ h k))

/-- `k` Gaussian queries with standard deviation `σ` are `(ρₖ + 2 √(ρₖ log (1 / δ)), δ)`-DP for
inputs at distance at most `r`, where `ρₖ = k r² / (2 σ²)`: the privacy loss grows as `√k`. -/
theorem DP_gaussianMechPow_sqrt (hσ : σ ≠ 0) (hδ : 0 < δ) (hδ₁ : δ < 1) (k : ℕ) :
    (gaussianMechPow σ k).DP (fun a a' ↦ |a - a'| ≤ r)
      (ENNReal.ofReal
        (k * (r ^ 2 / (2 * σ ^ 2)) + 2 * √(k * (r ^ 2 / (2 * σ ^ 2)) * Real.log (1 / δ))))
      (ENNReal.ofReal δ) := fun a a' h ↦ by
  have hρ : 0 ≤ k * (r ^ 2 / (2 * (σ : ℝ) ^ 2)) := by positivity
  have hk : (k : ℝ≥0∞) * ENNReal.ofReal (r ^ 2 / (2 * (σ : ℝ) ^ 2)) =
      ENNReal.ofReal (k * (r ^ 2 / (2 * (σ : ℝ) ^ 2))) := by
    rw [ofReal_mul (Nat.cast_nonneg k), ofReal_natCast]
  -- `codensity_dp_rel_of_zcdp` is stated for the codensity lifting of `zcdpDivergence`.
  have hz := ((LiftingHom.concentratedToCodensity _).toLiftingRelHom rfl).map_rel
    (zcdpLifting_rel_gaussianMechPow r hσ h k)
  have := codensity_sound (codensity_dp_rel_of_zcdp hδ hδ₁ hz)
  rwa [zero_add, hk, toReal_ofReal hρ, ← ofReal_add hρ (by positivity)] at this

end Mechanism
