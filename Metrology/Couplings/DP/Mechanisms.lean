module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Exponential
public import Metrology.Couplings.DP.Lifting

/-! The basic DP mechanisms: Bernoulli and Laplace (Approximate Span Liftings, Fig. 2,
[DP-Bern], [DP-Bern-Eq], [DP-Lap]). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Span unitInterval
open scoped ENNReal NNReal

namespace DPDiv

universe u

variable {X : Type*} [MeasurableSpace X] {Z : Type u} [MeasurableSpace Z]

/-- A measurable family of subprobability measures that satisfies a DP bound on related inputs
gives a span morphism into the DP lifting of equality (the pattern of App. B.5). -/
noncomputable def homOfBound {R : Set (X × X)} {k : X → Measure Z} (hk : Measurable k)
    [∀ x, IsSubProbabilityMeasure (k x)] {ε : ℝ≥0} {δ : ℝ≥0∞}
    (h : ∀ p ∈ R, Bound (ENNReal.ofReal (Real.exp ε)) δ (k p.1) (k p.2)) :
    ofRel R →ₛ dpLift (diag Z) ε δ where
  leftMap := k
  rightMap := k
  witnessMap p := ⟨(k p.1.1, k p.1.2), inferInstance, inferInstance, dp_le_iff.2 (h p.1 p.2)⟩
  comm_left _ := Measure.map_id.symm
  comm_right _ := Measure.map_id.symm

/-! ### Bernoulli -/

theorem bound_of_le {c : ℝ≥0∞} {μ ν : Measure X} (h : ∀ S, MeasurableSet S → μ S ≤ c * ν S) :
    Bound c 0 μ ν :=
  fun S hS ↦ (h S hS).trans le_self_add

/-- Equal Bernoulli parameters are at DP budget `(0, 0)` ([DP-Bern-Eq]). -/
theorem bound_bernoulli_self (x y : X) (p : I) :
    Bound (ENNReal.ofReal (Real.exp (0 : ℝ≥0))) 0 (bernoulliMeasure x y p)
      (bernoulliMeasure x y p) :=
  bound_of_le fun S _ ↦ by simp

/-- Complementary Bernoulli parameters are at DP budget `log (max p (1-p) / min p (1-p))`
([DP-Bern]). -/
theorem bound_bernoulli_symm (x y : X) {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1) :
    Bound (ENNReal.ofReal (max (p : ℝ) (σ p) / min (p : ℝ) (σ p))) 0
      (bernoulliMeasure x y p) (bernoulliMeasure x y (σ p)) := by
  classical
  have hq₀ : 0 < ((σ p : I) : ℝ) := by simpa [coe_symm_eq] using hp₁
  have hmin : 0 < min (p : ℝ) (σ p) := lt_min hp₀ hq₀
  have key {a b : ℝ} (ha : a ≤ max (p : ℝ) (σ p)) (hb : min (p : ℝ) (σ p) ≤ b) (hb0 : 0 ≤ b) :
      ENNReal.ofReal a ≤ ENNReal.ofReal (max (p : ℝ) (σ p) / min (p : ℝ) (σ p)) *
        ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_mul (div_nonneg ((le_max_left _ _).trans' p.2.1) hmin.le)]
    refine ENNReal.ofReal_le_ofReal (ha.trans ?_)
    rw [div_mul_eq_mul_div, le_div_iff₀ hmin]
    exact mul_le_mul_of_nonneg_left hb ((le_max_left _ _).trans' p.2.1)
  refine bound_of_le fun S hS ↦ ?_
  rw [bernoulliMeasure_apply _ hS, bernoulliMeasure_apply _ hS, symm_symm]
  have hp : ((toNNReal p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal p := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg p.2.1]; rfl
  have hq : ((toNNReal (σ p) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (σ p) := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (σ p).2.1]; rfl
  split_ifs
  · rw [mul_one, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((one_le_div hmin).2 (min_le_max))
  · rw [hp, hq]; exact key (le_max_left _ _) (min_le_right _ _) (σ p).2.1
  · rw [hp, hq]; exact key (le_max_right _ _) (min_le_left _ _) p.2.1
  · simp

/-! ### Laplace -/

/-- The density `exp (-|x - a| / b) / (2 b)` of the Laplace distribution. -/
noncomputable def laplacePDF (a : ℝ) (b : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-|x - a| / b) / (2 * b))

/-- The Laplace distribution with location `a` and scale `b`. -/
noncomputable def laplace (a : ℝ) (b : ℝ≥0) : Measure ℝ :=
  volume.withDensity (laplacePDF a b)

@[fun_prop]
theorem measurable_laplacePDF (a : ℝ) (b : ℝ≥0) : Measurable (laplacePDF a b) := by
  unfold laplacePDF; fun_prop

theorem measurable_exponentialPDF' (r : ℝ) : Measurable (exponentialPDF r) := by
  unfold exponentialPDF; fun_prop

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
    have hm := measurable_exponentialPDF' (b : ℝ)⁻¹
    rw [laplace, withDensity_apply _ .univ, Measure.restrict_univ, lintegral_congr_ae hae,
      lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop),
      lintegral_sub_right_eq_self (exponentialPDF (b : ℝ)⁻¹) a,
      lintegral_sub_left_eq_self (exponentialPDF (b : ℝ)⁻¹) a,
      lintegral_exponentialPDF_eq_one hr, one_add_one_eq_two,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- Laplace mechanisms with nearby locations are at DP budget `r / b` ([DP-Lap]). -/
theorem bound_laplace {a a' r : ℝ} (h : |a - a'| ≤ r) (b : ℝ≥0) :
    Bound (ENNReal.ofReal (Real.exp (r / b))) 0 (laplace a b) (laplace a' b) := by
  refine bound_of_le fun S hS ↦ ?_
  rw [laplace, laplace, withDensity_apply _ hS, withDensity_apply _ hS,
    ← lintegral_const_mul _ (measurable_laplacePDF _ _)]
  refine setLIntegral_mono (by fun_prop) fun x _ ↦ ?_
  rw [laplacePDF, laplacePDF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_div_assoc, ← Real.exp_add]
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by linarith [abs_sub_le x a a']) b.2

@[fun_prop]
theorem measurable_laplace (b : ℝ≥0) : Measurable fun a ↦ laplace a b := by
  refine Measure.measurable_of_measurable_coe _ fun S hS ↦ ?_
  simp_rw [laplace, withDensity_apply _ hS]
  exact Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ ↦ laplacePDF p.1 b p.2)
    (by unfold laplacePDF; fun_prop)

/-- The Laplace mechanism as a span morphism from `|a - a'| ≤ r` into the DP lifting of
equality ([DP-Lap]). -/
noncomputable def laplaceHom (r b : ℝ≥0) [Fact (0 < b)] :
    ofRel {p : ℝ × ℝ | |p.1 - p.2| ≤ r} →ₛ dpLift (diag ℝ) (r / b) (0 : ℝ≥0∞) :=
  homOfBound (measurable_laplace b) fun p hp ↦ by
    simpa only [NNReal.coe_div] using bound_laplace hp b

end DPDiv
