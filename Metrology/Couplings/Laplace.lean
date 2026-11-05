module

public import Mathlib.Probability.Distributions.Exponential

/-! # The Laplace distribution

`laplace a b` has density `exp (-|x - a| / b) / (2 b)`; it is a probability measure for `0 < b`
and jointly measurable in its parameters. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ENNReal

namespace ProbabilityTheory

variable (a : ℝ) (b : ℝ≥0)

/-- The density `exp (-|x - a| / b) / (2 b)` of the Laplace distribution. -/
noncomputable def laplacePDF (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-|x - a| / b) / (2 * b))

/-- The Laplace distribution with location `a` and scale `b`, a probability measure for `0 < b`. -/
noncomputable def laplace : Measure ℝ :=
  volume.withDensity (laplacePDF a b)

/-- The Laplace density is measurable. -/
@[fun_prop]
theorem measurable_laplacePDF : Measurable (laplacePDF a b) := by
  unfold laplacePDF
  fun_prop

/-- The exponential density `exponentialPDF r` is measurable. -/
@[fun_prop]
theorem measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) := by
  unfold exponentialPDF
  fun_prop

variable {b}

/-- Off the location, the Laplace density is an even mixture of two exponential densities. -/
theorem laplacePDF_eq (hb : 0 < b) {x : ℝ} (hx : x ≠ a) :
    laplacePDF a b x = 2⁻¹ * (exponentialPDF b⁻¹ (x - a) + exponentialPDF b⁻¹ (a - x)) := by
  have hb' : (0 : ℝ) < b := hb
  have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
    rw [ofReal_inv_of_pos two_pos, ofReal_ofNat]
  rw [exponentialPDF_eq, exponentialPDF_eq, h2, laplacePDF]
  rcases hx.lt_or_gt with h | h
  · simp only [show ¬0 ≤ x - a by linarith, show 0 ≤ a - x by linarith, ↓reduceIte,
      ofReal_zero, zero_add]
    rw [← ofReal_mul (by norm_num), abs_of_neg (sub_neg.2 h)]
    congr 1
    field_simp
    ring_nf
  · simp only [show 0 ≤ x - a by linarith, show ¬0 ≤ a - x by linarith, ↓reduceIte,
      ofReal_zero, add_zero]
    rw [← ofReal_mul (by norm_num), abs_of_pos (sub_pos.2 h)]
    congr 1
    field_simp

/-- The Laplace distribution is a probability measure. -/
instance isProbabilityMeasure_laplace [hb : Fact (0 < b)] :
    IsProbabilityMeasure (laplace a b) where
  measure_univ := by
    have hr : (0 : ℝ) < (b : ℝ)⁻¹ := inv_pos.2 hb.out
    have hae : laplacePDF a b =ᵐ[volume]
        fun x ↦ 2⁻¹ * (exponentialPDF (b : ℝ)⁻¹ (x - a) + exponentialPDF (b : ℝ)⁻¹ (a - x)) := by
      have : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by simp [ae_iff, measure_singleton]
      filter_upwards [this] with x hx using laplacePDF_eq a hb.out hx
    rw [laplace, withDensity_apply _ .univ, Measure.restrict_univ, lintegral_congr_ae hae,
      lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop),
      lintegral_sub_right_eq_self (exponentialPDF (b : ℝ)⁻¹) a,
      lintegral_sub_left_eq_self (exponentialPDF (b : ℝ)⁻¹) a,
      lintegral_exponentialPDF_eq_one hr, one_add_one_eq_two,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

variable (b)

/-- The Laplace distribution with scale `b` is measurable in its location parameter. -/
@[fun_prop]
theorem measurable_laplace : Measurable fun a ↦ laplace a b := by
  refine Measure.measurable_of_measurable_coe _ fun S hS ↦ ?_
  simp_rw [laplace, withDensity_apply _ hS]
  exact Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ ↦ laplacePDF p.1 b p.2)
    (by unfold laplacePDF; fun_prop)

/-- The Laplace distribution is jointly measurable in its location and scale. -/
@[fun_prop]
theorem measurable_uncurry_laplace : Measurable fun p : ℝ × ℝ≥0 ↦ laplace p.1 p.2 := by
  refine Measure.measurable_of_measurable_coe _ fun S hS ↦ ?_
  simp_rw [laplace, withDensity_apply _ hS]
  exact Measurable.lintegral_prod_right' (f := fun q : (ℝ × ℝ≥0) × ℝ ↦ laplacePDF q.1.1 q.1.2 q.2)
    (by unfold laplacePDF; fun_prop)

end ProbabilityTheory
