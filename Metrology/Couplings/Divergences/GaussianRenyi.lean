module

public import Metrology.Couplings.Divergences.Gaussian

/-! The Rényi divergence between Gaussians of equal variance, and the Gaussian mechanism is zCDP
(Mironov 2017, Prop. 7; Bun–Steinke 2016, Prop. 1.6). -/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {a a' : ℝ} {v : ℝ≥0}

/-- The ratio of two Gaussian densities of equal variance is the exponential of an affine map. -/
theorem gaussianPDFReal_div_gaussianPDFReal (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal a v x / gaussianPDFReal a' v x =
      exp ((a - a') / v * x - (a - a') * (a + a') / (2 * v)) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  rw [gaussianPDFReal, gaussianPDFReal, mul_div_mul_left _ _ (by positivity), ← exp_sub]
  congr 1
  field_simp
  ring

/-- The density of `N(a, v)` against `N(a', v)` is the ratio of their Lebesgue densities. -/
theorem toReal_rnDeriv_gaussianReal (hv : v ≠ 0) :
    (fun x ↦ ((gaussianReal a v).rnDeriv (gaussianReal a' v) x).toReal)
      =ᵐ[gaussianReal a' v] fun x ↦ exp ((a - a') / v * x - (a - a') * (a + a') / (2 * v)) := by
  have hac := gaussianReal_absolutelyContinuous a' hv
  filter_upwards [Measure.rnDeriv_eq_div (gaussianReal_absolutelyContinuous a hv) hac,
    hac (rnDeriv_gaussianReal a v), hac (rnDeriv_gaussianReal a' v)] with x hx ha ha'
  rw [hx, ha, ha', ENNReal.toReal_div, toReal_gaussianPDF, toReal_gaussianPDF,
    gaussianPDFReal_div_gaussianPDFReal hv]

/-- The `α`-th moment of the density ratio of two Gaussians of equal variance `v` is
`exp ((α - 1) α (a - a')² / (2 v))` (Mironov 2017, Prop. 7). -/
theorem fDiv_rpow_gaussianReal (hv : v ≠ 0) (α : ℝ) :
    fDiv (· ^ α) (gaussianReal a v) (gaussianReal a' v) =
      ((exp ((α - 1) * (α * (a - a') ^ 2 / (2 * v))) : ℝ) : EReal) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  set t := α * (a - a') / v
  have hpow : (fun x ↦ ((gaussianReal a v).rnDeriv (gaussianReal a' v) x).toReal ^ α)
      =ᵐ[gaussianReal a' v] fun x ↦ exp (-(α * (a - a') * (a + a') / (2 * v))) * exp (t * x) := by
    filter_upwards [toReal_rnDeriv_gaussianReal hv] with x hx
    rw [hx, ← exp_mul, ← exp_add]
    congr 1
    ring
  have hint : Integrable (fun x ↦ ((gaussianReal a v).rnDeriv (gaussianReal a' v) x).toReal ^ α)
      (gaussianReal a' v) :=
    ((integrable_exp_mul_gaussianReal t).const_mul _).congr hpow.symm
  have hmgf : ∫ x, exp (t * x) ∂gaussianReal a' v = exp (a' * t + v * t ^ 2 / 2) :=
    congrFun mgf_fun_id_gaussianReal t
  have hac : gaussianReal a v ≪ gaussianReal a' v :=
    (gaussianReal_absolutelyContinuous a hv).trans (gaussianReal_absolutelyContinuous' a' hv)
  rw [fDiv_of_integrable hint, singularPart_eq_zero_of_ac hac, integral_congr_ae hpow,
    integral_const_mul, hmgf, ← exp_add]
  simp only [Measure.coe_zero, Pi.zero_apply, EReal.coe_ennreal_zero, mul_zero, add_zero,
    EReal.coe_eq_coe_iff, exp_eq_exp, t]
  field_simp
  ring

end ProbabilityTheory

namespace GradedDivergence

variable {a a' α : ℝ} {v : ℝ≥0}

/-- Two Gaussians of equal variance `v` are within Rényi budget `α (a - a')² / (2 v)` at order
`α` (Mironov 2017, Prop. 7). -/
theorem renyiDivergence_gaussianReal (hα : 1 ≤ α) (hv : v ≠ 0) :
    renyiDivergence α (ENNReal.ofReal (α * (a - a') ^ 2 / (2 * v))) (gaussianReal a v)
      (gaussianReal a' v) := by
  have hρ : 0 ≤ α * (a - a') ^ 2 / (2 * v) :=
    div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)
  rw [renyiDivergence_iff_of_ne_top hα ENNReal.ofReal_ne_top, fDiv_rpow_gaussianReal hv,
    ENNReal.toReal_ofReal hρ]

/-- The Rényi divergence of order `α > 1` between two Gaussians of equal variance `v` is
`α (a - a')² / (2 v)` (Mironov 2017, Prop. 7). -/
theorem renyiDiv_gaussianReal (hα : 1 < α) (hv : v ≠ 0) :
    renyiDiv α (gaussianReal a v) (gaussianReal a' v) =
      ((α * (a - a') ^ 2 / (2 * v) : ℝ) : EReal) := by
  rw [renyiDiv, fDiv_rpow_gaussianReal hv, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _),
    EReal.toReal_coe, ENNReal.log_ofReal_of_pos (exp_pos _), log_exp, ← EReal.coe_mul,
    inv_mul_cancel_left₀ (sub_pos.2 hα).ne']

/-- Two Gaussians of equal variance `v` are `(0, (a - a')² / (2 v))`-zCDP close (Bun–Steinke 2016,
Prop. 1.6). -/
theorem zcdpDivergence_gaussianReal (hv : v ≠ 0) :
    zcdpDivergence (0, ENNReal.ofReal ((a - a') ^ 2 / (2 * v))) (gaussianReal a v)
      (gaussianReal a' v) :=
  zcdpDivergence_iff.2 fun α hα ↦ by
    rw [zero_add, ← ENNReal.ofReal_mul (by linarith), ← mul_div_assoc]
    exact renyiDivergence_gaussianReal hα.le hv

end GradedDivergence

namespace Mechanism

/-- The Gaussian mechanism with standard deviation `σ` is `(0, r² / (2 σ²))`-zCDP for inputs at
distance at most `r` (Bun–Steinke 2016, Prop. 1.6). -/
theorem zCDP_gaussianMech {σ : ℝ≥0} (hσ : σ ≠ 0) (r : ℝ) :
    (gaussianMech σ).zCDP (fun a a' ↦ |a - a'| ≤ r) 0
      (ENNReal.ofReal (r ^ 2 / (2 * (σ : ℝ) ^ 2))) := by
  intro a a' h
  refine GradedDivergence.IsGraded.mono (Prod.mk_le_mk.2 ⟨le_rfl, ENNReal.ofReal_le_ofReal ?_⟩)
    (GradedDivergence.zcdpDivergence_gaussianReal (a := a) (a' := a') (pow_ne_zero 2 hσ))
  push_cast
  gcongr ?_ / _
  exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2

end Mechanism
