module

public import Metrology.Couplings.Divergences.GaussianRenyi

/-! # Gaussian composition

`k` Gaussian queries composed in the zCDP lifting are `(ε, δ)`-DP with `ε` of order `√k`
(`DP_gaussianMechPow_sqrt`; Approximate Span Liftings, §§4–5). -/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory GradedLifting GradedDivergence Real Set
open scoped ENNReal NNReal

namespace Mechanism

/-! ## `k` independent Gaussian queries -/

/-- Splitting off the first coordinate of a tuple of reals. -/
noncomputable abbrev consEquiv (k : ℕ) : (Fin (k + 1) → ℝ) ≃ᵐ ℝ × (Fin k → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0

/-- `k` independent queries of the Gaussian mechanism with standard deviation `σ` on the same
input. -/
noncomputable def gaussianMechPow (σ : ℝ≥0) : (k : ℕ) → Mechanism ℝ (Fin k → ℝ)
  | 0 => Kernel.const ℝ (dirac isEmptyElim)
  | k + 1 => (gaussianMech σ ×ₖ gaussianMechPow σ k).map (consEquiv k).symm

/-- Each of the `k` queries is a probability measure, so their product is one. -/
instance isMarkovKernel_gaussianMechPow (σ : ℝ≥0) : ∀ k, IsMarkovKernel (gaussianMechPow σ k)
  | 0 => by
    rw [gaussianMechPow]
    infer_instance
  | k + 1 => by
    have := isMarkovKernel_gaussianMechPow σ k
    rw [gaussianMechPow]
    exact Kernel.IsMarkovKernel.map _ (consEquiv k).symm.measurable

/-- No queries give the point mass at the empty tuple. -/
theorem gaussianMechPow_zero_apply (σ : ℝ≥0) (a : ℝ) :
    gaussianMechPow σ 0 a = dirac isEmptyElim := by
  rw [gaussianMechPow, Kernel.const_apply]

/-- One more query draws a fresh first coordinate. -/
theorem gaussianMechPow_succ_apply (σ : ℝ≥0) (k : ℕ) (a : ℝ) :
    gaussianMechPow σ (k + 1) a =
      ((gaussianReal a (σ ^ 2)).prod (gaussianMechPow σ k a)).map (consEquiv k).symm := by
  rw [gaussianMechPow, Kernel.map_apply _ (consEquiv k).symm.measurable, Kernel.prod_apply]
  rfl

/-- The `k` Gaussian queries are independent draws from `N(a, σ²)`. -/
theorem gaussianMechPow_apply (σ : ℝ≥0) (k : ℕ) (a : ℝ) :
    gaussianMechPow σ k a = Measure.pi fun _ ↦ gaussianReal a (σ ^ 2) := by
  induction k with
  | zero => exact (gaussianMechPow_zero_apply σ a).trans (Measure.pi_of_empty _ _).symm
  | succ k ih =>
    rw [gaussianMechPow_succ_apply, ih]
    exact ((measurePreserving_piFinSuccAbove (fun _ ↦ gaussianReal a (σ ^ 2)) 0).symm _).map_eq

/-! ## Composition in the zCDP lifting and DP bounds -/

variable {σ : ℝ≥0} {r δ : ℝ}

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
theorem DP_gaussianMechPow (hσ : σ ≠ 0) (r : ℝ) (hδ : 0 < δ) (k : ℕ) :
    (gaussianMechPow σ k).DP (fun a a' ↦ |a - a'| ≤ r)
      (⨅ α ∈ Ioi (1 : ℝ), ENNReal.ofReal α * (k * ENNReal.ofReal (r ^ 2 / (2 * (σ : ℝ) ^ 2))) +
        ENNReal.ofReal (log (1 / δ) / (α - 1)))
      (ENNReal.ofReal δ) := fun a a' h ↦ by
  simpa using codensity_sound
    ((LiftingRelHom.zcdpToDp hδ).map_rel (zcdpLifting_rel_gaussianMechPow hσ h k))

/-- `k` Gaussian queries with standard deviation `σ` are `(ρₖ + 2 √(ρₖ log (1 / δ)), δ)`-DP for
inputs at distance at most `r`, where `ρₖ = k r² / (2 σ²)`: the privacy loss grows as `√k`. -/
theorem DP_gaussianMechPow_sqrt (hσ : σ ≠ 0) (r : ℝ) (hδ : 0 < δ) (hδ₁ : δ < 1) (k : ℕ) :
    (gaussianMechPow σ k).DP (fun a a' ↦ |a - a'| ≤ r)
      (ENNReal.ofReal (k * (r ^ 2 / (2 * σ ^ 2)) +
        2 * √(k * (r ^ 2 / (2 * σ ^ 2)) * log (1 / δ))))
      (ENNReal.ofReal δ) := fun a a' h ↦ by
  have hρ : 0 ≤ k * (r ^ 2 / (2 * (σ : ℝ) ^ 2)) := by positivity
  have hk : (k : ℝ≥0∞) * ENNReal.ofReal (r ^ 2 / (2 * (σ : ℝ) ^ 2)) =
      ENNReal.ofReal (k * (r ^ 2 / (2 * (σ : ℝ) ^ 2))) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
  -- `codensity_dp_rel_of_zcdp` is stated for the codensity lifting of `zcdpDivergence`.
  have hz := ((LiftingHom.concentratedToCodensity _).toLiftingRelHom rfl).map_rel
    (zcdpLifting_rel_gaussianMechPow hσ h k)
  have := codensity_sound (codensity_dp_rel_of_zcdp hδ hδ₁ hz)
  rwa [zero_add, hk, ENNReal.toReal_ofReal hρ, ← ENNReal.ofReal_add hρ (by positivity)] at this

end Mechanism
