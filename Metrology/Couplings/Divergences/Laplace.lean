module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Exponential
public import Metrology.Couplings.Divergences.Mechanism

/-! The basic DP mechanisms: Bernoulli and Laplace (Approximate Span Liftings, Fig. 2, [DP-Bern],
[DP-Bern-Eq], [DP-Lap]). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped ENNReal NNReal

/-! ## The Laplace distribution -/

namespace ProbabilityTheory

/-- The density `exp (-|x - a| / b) / (2 b)` of the Laplace distribution. -/
noncomputable def laplacePDF (a : ℝ) (b : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-|x - a| / b) / (2 * b))

/-- The Laplace distribution with location `a` and scale `b`. -/
noncomputable def laplace (a : ℝ) (b : ℝ≥0) : Measure ℝ :=
  volume.withDensity (laplacePDF a b)

@[fun_prop]
theorem measurable_laplacePDF (a : ℝ) (b : ℝ≥0) : Measurable (laplacePDF a b) := by
  unfold laplacePDF
  fun_prop

/-- The exponential density is measurable. -/
@[fun_prop]
theorem measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) := by
  unfold exponentialPDF
  fun_prop

/-- Off the location, the Laplace density is an even mixture of two exponential densities. -/
theorem laplacePDF_eq (a : ℝ) {b : ℝ≥0} (hb : 0 < b) {x : ℝ} (hx : x ≠ a) :
    laplacePDF a b x = 2⁻¹ * (exponentialPDF b⁻¹ (x - a) + exponentialPDF b⁻¹ (a - x)) := by
  have hb' : (0 : ℝ) < b := hb
  have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [exponentialPDF_eq, exponentialPDF_eq, h2, laplacePDF]
  rcases hx.lt_or_gt with h | h
  · simp only [show ¬0 ≤ x - a by linarith, show 0 ≤ a - x by linarith, ↓reduceIte,
      ENNReal.ofReal_zero, zero_add]
    rw [← ENNReal.ofReal_mul (by norm_num), abs_of_neg (sub_neg.2 h)]
    congr 1
    field_simp
    ring_nf
  · simp only [show 0 ≤ x - a by linarith, show ¬0 ≤ a - x by linarith, ↓reduceIte,
      ENNReal.ofReal_zero, add_zero]
    rw [← ENNReal.ofReal_mul (by norm_num), abs_of_pos (sub_pos.2 h)]
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

@[fun_prop]
theorem measurable_laplace (b : ℝ≥0) : Measurable fun a ↦ laplace a b := by
  refine Measure.measurable_of_measurable_coe _ fun S hS ↦ ?_
  simp_rw [laplace, withDensity_apply _ hS]
  exact Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ ↦ laplacePDF p.1 b p.2)
    (by unfold laplacePDF; fun_prop)

end ProbabilityTheory

namespace GradedDivergence

variable {X : Type*} [MeasurableSpace X] {ε : ℝ≥0∞}

/-! ## Bernoulli -/

/-- Equal Bernoulli parameters are at DP budget `(0, 0)` ([DP-Bern-Eq]). -/
theorem dp_bernoulli_self (x y : X) (p : I) :
    dp 0 (bernoulliMeasure x y p) (bernoulliMeasure x y p) :=
  IsReflexive.refl _

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
  have key {a b : ℝ} (ha : a ≤ max (p : ℝ) (σ p)) (hb : min (p : ℝ) (σ p) ≤ b) (hb0 : 0 ≤ b) :
      ENNReal.ofReal a ≤ ENNReal.ofReal (max (p : ℝ) (σ p) / min (p : ℝ) (σ p)) *
        ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_mul hratio.le]
    refine ENNReal.ofReal_le_ofReal (ha.trans ?_)
    rw [div_mul_eq_mul_div, le_div_iff₀ hmin]
    exact mul_le_mul_of_nonneg_left hb ((le_max_left _ _).trans' p.2.1)
  refine dp_of_forall_le fun S hS ↦ ?_
  rw [expBudget_ofReal (Real.log_nonneg ((one_le_div hmin).2 min_le_max)),
    Real.exp_log hratio, bernoulliMeasure_apply _ hS, bernoulliMeasure_apply _ hS, symm_symm]
  have hp : ((toNNReal p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal p :=
    (ENNReal.ofReal_eq_coe_nnreal p.2.1).symm
  have hq : ((toNNReal (σ p) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (σ p) :=
    (ENNReal.ofReal_eq_coe_nnreal (σ p).2.1).symm
  split_ifs
  · rw [mul_one, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((one_le_div hmin).2 min_le_max)
  · rw [hp, hq]
    exact key (le_max_left _ _) (min_le_right _ _) (σ p).2.1
  · rw [hp, hq]
    exact key (le_max_right _ _) (min_le_left _ _) p.2.1
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
  rw [laplacePDF, laplacePDF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_div_assoc, ← Real.exp_add]
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by linarith [abs_sub_le x a a']) b.2

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
