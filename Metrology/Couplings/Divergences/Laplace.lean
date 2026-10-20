module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Exponential
public import Metrology.Couplings.Divergences.Mechanism

/-! The Bernoulli and Laplace mechanisms (Approximate Span Liftings, Fig. 2). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped ENNReal NNReal

/-! ## The Laplace distribution -/

namespace ProbabilityTheory
open ENNReal

/-- The density `exp (-|x - a| / b) / (2 b)` of the Laplace distribution. -/
noncomputable def laplacePDF (a : ℝ) (b : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-|x - a| / b) / (2 * b))

/-- The Laplace distribution with location `a` and scale `b`. -/
noncomputable def laplace (a : ℝ) (b : ℝ≥0) : Measure ℝ :=
  volume.withDensity (laplacePDF a b)

/-- The Laplace density is measurable. -/
@[fun_prop]
theorem measurable_laplacePDF (a : ℝ) (b : ℝ≥0) : Measurable (laplacePDF a b) := by
  unfold laplacePDF
  fun_prop

/-- The exponential density `exponentialPDF r` is measurable. -/
@[fun_prop]
theorem measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) := by
  unfold exponentialPDF
  fun_prop

/-- Off the location, the Laplace density is an even mixture of two exponential densities. -/
theorem laplacePDF_eq (a : ℝ) {b : ℝ≥0} (hb : 0 < b) {x : ℝ} (hx : x ≠ a) :
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

instance isProbabilityMeasure_laplace (a : ℝ) {b : ℝ≥0} [hb : Fact (0 < b)] :
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

/-- The Laplace distribution with scale `b` is measurable in its location parameter. -/
@[fun_prop]
theorem measurable_laplace (b : ℝ≥0) : Measurable fun a ↦ laplace a b := by
  refine Measure.measurable_of_measurable_coe _ fun S hS ↦ ?_
  simp_rw [laplace, withDensity_apply _ hS]
  exact Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ ↦ laplacePDF p.1 b p.2)
    (by unfold laplacePDF; fun_prop)

end ProbabilityTheory

namespace GradedDivergence
open ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ## Bernoulli -/

/-- Equal Bernoulli parameters are at DP budget `(0, 0)` ([DP-Bern-Eq]). -/
theorem dp_bernoulli_self (x y : X) (p : I) :
    dp 0 (bernoulliMeasure x y p) (bernoulliMeasure x y p) :=
  IsReflexive.refl _

/-- Scaling `b ≥ m` by the ratio `M / m` dominates any `a ≤ M`, in `ℝ≥0∞`. -/
theorem ofReal_le_ofReal_div_mul {a b m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) (ha : a ≤ M)
    (hb : m ≤ b) : ENNReal.ofReal a ≤ ENNReal.ofReal (M / m) * ENNReal.ofReal b := by
  rw [← ofReal_mul (div_pos (hm.trans_le hmM) hm).le]
  refine ofReal_le_ofReal (ha.trans ?_)
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  exact mul_le_mul_of_nonneg_left hb (hm.le.trans hmM)

/-- Complementary Bernoulli parameters are at DP budget `log (max p (1-p) / min p (1-p))`
([DP-Bern]). -/
theorem dp_bernoulli_symm (x y : X) {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1) :
    dp (ENNReal.ofReal (Real.log (max (p : ℝ) (σ p) / min (p : ℝ) (σ p))), 0)
      (bernoulliMeasure x y p) (bernoulliMeasure x y (σ p)) := by
  classical
  have hq₀ : 0 < ((σ p : I) : ℝ) := by simpa [coe_symm_eq] using hp₁
  have hmin : 0 < min (p : ℝ) (σ p) := lt_min hp₀ hq₀
  have hratio : 0 < max (p : ℝ) (σ p) / min (p : ℝ) (σ p) :=
    div_pos (hmin.trans_le min_le_max) hmin
  refine dp_of_forall_le fun S hS ↦ ?_
  rw [expBudget_ofReal (Real.log_nonneg ((one_le_div hmin).2 min_le_max)),
    Real.exp_log hratio, bernoulliMeasure_apply _ hS, bernoulliMeasure_apply _ hS, symm_symm]
  have hp : ((toNNReal p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal p := (ofReal_eq_coe_nnreal p.2.1).symm
  have hq : ((toNNReal (σ p) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (σ p) :=
    (ofReal_eq_coe_nnreal (σ p).2.1).symm
  split_ifs
  · rw [mul_one, ← ofReal_one]
    exact ofReal_le_ofReal ((one_le_div hmin).2 min_le_max)
  · rw [hp, hq]
    exact ofReal_le_ofReal_div_mul hmin min_le_max (le_max_left _ _) (min_le_right _ _)
  · rw [hp, hq]
    exact ofReal_le_ofReal_div_mul hmin min_le_max (le_max_right _ _) (min_le_left _ _)
  · simp

/-! ## Laplace -/

/-- Laplace distributions with nearby locations are at DP budget `r / b` ([DP-Lap]). -/
theorem dp_laplace {a a' r : ℝ} (h : |a - a'| ≤ r) (b : ℝ≥0) :
    dp (ENNReal.ofReal (r / b), 0) (laplace a b) (laplace a' b) := by
  refine dp_of_forall_le fun S hS ↦ ?_
  rw [expBudget_ofReal (div_nonneg ((abs_nonneg _).trans h) b.coe_nonneg), laplace, laplace,
    withDensity_apply _ hS, withDensity_apply _ hS,
    ← lintegral_const_mul _ (measurable_laplacePDF _ _)]
  refine setLIntegral_mono (by fun_prop) fun x _ ↦ ?_
  rw [laplacePDF, laplacePDF, ← ofReal_mul (Real.exp_pos _).le]
  refine ofReal_le_ofReal ?_
  rw [← mul_div_assoc, ← Real.exp_add, ← add_div]
  gcongr
  linarith [abs_sub_le x a a']

end GradedDivergence

namespace Mechanism

/-- The Laplace mechanism with scale `b`. -/
noncomputable def laplaceMech (b : ℝ≥0) : Mechanism ℝ ℝ :=
  ⟨fun a ↦ laplace a b, measurable_laplace b⟩

instance isMarkovKernel_laplaceMech (b : ℝ≥0) [Fact (0 < b)] : IsMarkovKernel (laplaceMech b) :=
  ⟨fun a ↦ isProbabilityMeasure_laplace a⟩

/-- The Laplace mechanism is `(r / b, 0)`-DP for inputs at distance at most `r` ([DP-Lap]). -/
theorem DP_laplaceMech (r : ℝ) (b : ℝ≥0) :
    (laplaceMech b).DP (fun a a' ↦ |a - a'| ≤ r) (ENNReal.ofReal (r / b)) 0 :=
  fun _ _ h ↦ GradedDivergence.dp_laplace h b

end Mechanism
