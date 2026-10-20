module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Metrology.Couplings.Divergences.Mechanism

/-! The Gaussian mechanism is differentially private (Approximate Span Liftings, Fig. 2). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- The Gaussian mass beyond `H > a` is at most `v · pdf(H) / (H - a)`. -/
theorem gaussianReal_Ioi_le {a H : ℝ} (hH : a < H) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal a v (Ioi H) ≤ ENNReal.ofReal (v * gaussianPDFReal a v H / (H - a)) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  set F : ℝ → ℝ := fun x ↦ -(v * gaussianPDFReal a v x)
  have hF (x : ℝ) : HasDerivAt F ((x - a) * gaussianPDFReal a v x) x := by
    have h : HasDerivAt (fun x ↦ -(x - a) ^ 2 / (2 * (v : ℝ))) (-(x - a) / v) x := by
      convert (((hasDerivAt_id' x).sub_const a).pow 2).neg.div_const (2 * (v : ℝ)) using 1
      field_simp
      ring
    convert ((h.exp.const_mul (√(2 * π * v))⁻¹).const_mul (v : ℝ)).neg using 1
    · rfl
    · simp only [gaussianPDFReal]
      field_simp
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h : Tendsto (fun x ↦ -(x - a) ^ 2 / (2 * (v : ℝ))) atTop atBot := by
      refine Tendsto.atBot_div_const (by positivity) (tendsto_neg_atTop_atBot.comp ?_)
      exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    have := ((tendsto_exp_atBot.comp h).const_mul ((v : ℝ) * (√(2 * π * v))⁻¹)).neg
    rw [mul_zero, neg_zero] at this
    exact this.congr fun x ↦ by simp only [F, gaussianPDFReal, Function.comp, mul_assoc]
  have hnn (x : ℝ) (hx : x ∈ Ioi H) : 0 ≤ (x - a) * gaussianPDFReal a v x :=
    mul_nonneg (by linarith [hx.out]) (gaussianPDFReal_nonneg _ _ _)
  have hint : IntegrableOn (fun x ↦ (x - a) * gaussianPDFReal a v x) (Ioi H) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ ↦ hF x) hnn hlim
  have hval : ∫ x in Ioi H, (x - a) * gaussianPDFReal a v x = v * gaussianPDFReal a v H := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ ↦ hF x) hint hlim]
    simp [F]
  rw [gaussianReal_of_var_ne_zero _ hv, withDensity_apply _ measurableSet_Ioi, ← hval,
    div_eq_mul_inv, ← integral_mul_const,
    ofReal_integral_eq_lintegral_ofReal (hint.mul_const _)
      ((ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun x hx ↦
        mul_nonneg (hnn x hx) (inv_nonneg.2 (sub_pos.2 hH).le)))]
  refine setLIntegral_mono' measurableSet_Ioi fun x hx ↦ ENNReal.ofReal_le_ofReal ?_
  rw [mul_comm (x - a), mul_assoc, ← div_eq_mul_inv]
  exact le_mul_of_one_le_right (gaussianPDFReal_nonneg _ _ _)
    ((one_le_div (sub_pos.2 hH)).2 (by linarith [hx.out]))

/-- On the window `x ≤ (a + a') / 2 + v ε / r`, the Gaussian density ratio is at most `e^ε`. -/
theorem gaussianPDFReal_le_exp_mul {a a' r ε x : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (haa : a' ≤ a)
    (har : a - a' ≤ r) {v : ℝ≥0} (hv : (0 : ℝ) < v) (hx : x ≤ (a + a') / 2 + v * ε / r) :
    gaussianPDFReal a v x ≤ exp ε * gaussianPDFReal a' v x := by
  simp only [gaussianPDFReal]
  rw [mul_left_comm, ← exp_add]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
  have key : (a - a') * (2 * x - a - a') ≤ 2 * v * ε := by
    rcases le_total (2 * x - a - a') 0 with h | h
    · nlinarith [mul_nonneg (sub_nonneg.2 haa) (neg_nonneg.2 h), mul_nonneg hv.le hε]
    · have h1 : (2 * x - a - a') * r ≤ 2 * v * ε := by
        rw [← le_div_iff₀ hr, mul_assoc, mul_div_assoc]
        linarith
      nlinarith [mul_le_mul_of_nonneg_left har h]
  have key2 : ((x - a') ^ 2 - (x - a) ^ 2) / (2 * v) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [key]
  calc -(x - a) ^ 2 / (2 * v)
        = ((x - a') ^ 2 - (x - a) ^ 2) / (2 * v) + -(x - a') ^ 2 / (2 * v) := by ring
    _ ≤ ε + -(x - a') ^ 2 / (2 * v) := by linarith

end ProbabilityTheory

namespace Real

/-- The constant `0.66` exceeds `√(e / (2π))`, the slack in the Gaussian tail bound. -/
theorem sqrt_exp_one_div_two_pi_le : √(exp 1 / (2 * π)) ≤ 0.66 := by
  rw [sqrt_le_left (by norm_num), div_le_iff₀ (by positivity)]
  nlinarith [exp_one_lt_d9, pi_gt_d2]

theorem one_lt_sub_one_div_two_mul {c : ℝ} (hc : (1 + √3) / 2 < c) : 1 < c - 1 / (2 * c) := by
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ (by positivity)]
  nlinarith [sqrt_nonneg 3]

/-- The Gaussian tail value `exp (-h²/2) / (√(2π) h)` is at most `δ` once
`h ≥ c - 1 / (2c)`, `c > (1 + √3) / 2` and `c² ≥ 2 log (0.66 / δ)`. -/
theorem gaussian_tail_le {h c δ : ℝ} (hh : c - 1 / (2 * c) ≤ h) (hc : (1 + √3) / 2 < c)
    (hδ : 0 < δ) (hcδ : 2 * log (0.66 / δ) ≤ c ^ 2) : exp (-h ^ 2 / 2) / (√(2 * π) * h) ≤ δ := by
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  have hm := one_lt_sub_one_div_two_mul hc
  have h1 : 1 < h := hm.trans_le hh
  have hsq : c ^ 2 - 1 ≤ h ^ 2 := by
    have : c ^ 2 - 1 ≤ (c - 1 / (2 * c)) ^ 2 := by
      have e : (c - 1 / (2 * c)) ^ 2 = c ^ 2 - 1 + (1 / (2 * c)) ^ 2 := by
        field_simp
        ring
      nlinarith [sq_nonneg (1 / (2 * c))]
    nlinarith [this, mul_le_mul hh hh (by linarith) (by linarith)]
  have hpi : 0 < √(2 * π) := sqrt_pos.2 (by positivity)
  have hexp : exp (-c ^ 2 / 2) ≤ δ / 0.66 := by
    rw [← exp_log (by positivity : 0 < δ / 0.66), exp_le_exp, log_div hδ.ne' (by norm_num),
      ← neg_sub, ← log_div (by norm_num) hδ.ne']
    linarith
  calc exp (-h ^ 2 / 2) / (√(2 * π) * h)
      ≤ exp (-h ^ 2 / 2) / √(2 * π) :=
        div_le_div_of_nonneg_left (exp_pos _).le hpi (le_mul_of_one_le_right hpi.le h1.le)
    _ ≤ exp (-(c ^ 2 - 1) / 2) / √(2 * π) := by gcongr
    _ = √(exp 1 / (2 * π)) * exp (-c ^ 2 / 2) := by
        rw [sqrt_div (exp_pos _).le, ← exp_half, div_mul_eq_mul_div, ← exp_add]
        ring_nf
    _ ≤ 0.66 * (δ / 0.66) := mul_le_mul sqrt_exp_one_div_two_pi_le hexp (exp_pos _).le (by norm_num)
    _ = δ := by field_simp

end Real

namespace GradedDivergence

/-- The Gaussian mechanism with nearby means is `(ε, δ)`-DP, case `a' ≤ a` ([DP-G];
Sato 2016, Lemma A.11). -/
theorem dp_gaussian_of_le {σ : ℝ≥0} {ε δ r c a a' : ℝ} (hε : 0 < ε)
    (hε₁ : ε ≤ 1) (hr : 0 < r) (hδ : 0 < δ) (hc : (1 + √3) / 2 < c)
    (hcδ : 2 * log (0.66 / δ) ≤ c ^ 2) (hcσ : c * r / ε ≤ σ) (haa : a' ≤ a) (har : a - a' ≤ r) :
    dp (ENNReal.ofReal ε, ENNReal.ofReal δ) (gaussianReal a (σ ^ 2)) (gaussianReal a' (σ ^ 2)) := by
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  have hσ' : (0 : ℝ) < σ := (div_pos (mul_pos hc0 hr) hε).trans_le hcσ
  have hσ : 0 < σ := NNReal.coe_pos.1 hσ'
  have hv : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
  have hv' : (0 : ℝ) < ((σ ^ 2 : ℝ≥0) : ℝ) := by push_cast; positivity
  set H := (a + a') / 2 + ((σ ^ 2 : ℝ≥0) : ℝ) * ε / r
  -- the tail point `(H - a) / σ` is at least `c - 1 / (2c)`
  have hc' : c ≤ σ * ε / r := by
    rw [le_div_iff₀ hr]
    exact (div_le_iff₀ hε).1 hcσ
  have hh : c - 1 / (2 * c) ≤ (H - a) / σ := by
    have hmono : c - 1 / (2 * c) ≤ σ * ε / r - 1 / (2 * (σ * ε / r)) := by
      have := one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hc' zero_le_two)
      linarith
    have hval : (H - a) / σ = (a' - a) / (2 * σ) + σ * ε / r := by
      simp only [H, NNReal.coe_pow]
      field_simp
      ring
    have hlow : -(ε / (2 * (σ * ε / r))) ≤ (a' - a) / (2 * σ) := by
      rw [show ε / (2 * (σ * ε / r)) = r / (2 * σ) by field_simp, neg_div',
        div_le_div_iff_of_pos_right (by positivity)]
      linarith
    have hε' : ε / (2 * (σ * ε / r)) ≤ 1 / (2 * (σ * ε / r)) :=
      div_le_div_of_nonneg_right hε₁ (by positivity)
    rw [hval]
    linarith
  have hHa : a < H := by
    have := (one_lt_sub_one_div_two_mul hc).trans_le hh
    rw [one_lt_div hσ'] at this
    linarith
  -- the tail `(H, ∞)` has mass at most `δ`
  have htail : gaussianReal a (σ ^ 2) (Ioi H) ≤ ENNReal.ofReal δ := by
    refine (gaussianReal_Ioi_le hHa hv).trans (ENNReal.ofReal_le_ofReal ?_)
    refine le_of_eq_of_le ?_ (gaussian_tail_le hh hc hδ hcδ)
    simp only [gaussianPDFReal, NNReal.coe_pow]
    rw [sqrt_mul' _ (by positivity), sqrt_sq hσ'.le]
    field_simp
  intro _ S hS
  rw [expBudget_ofReal hε.le]
  calc gaussianReal a (σ ^ 2) S
      ≤ gaussianReal a (σ ^ 2) (S ∩ Iic H) + gaussianReal a (σ ^ 2) (Ioi H) := by
        refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
        exact (le_or_gt x H).imp (⟨hx, ·⟩) id
    _ ≤ ENNReal.ofReal (exp ε) * gaussianReal a' (σ ^ 2) S + ENNReal.ofReal δ := by
        gcongr
        rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
          withDensity_apply _ (hS.inter measurableSet_Iic)]
        calc ∫⁻ x in S ∩ Iic H, gaussianPDF a (σ ^ 2) x
            ≤ ∫⁻ x in S ∩ Iic H, ENNReal.ofReal (exp ε) * gaussianPDF a' (σ ^ 2) x := by
              refine setLIntegral_mono' (hS.inter measurableSet_Iic) fun x hx ↦ ?_
              rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (exp_pos _).le]
              exact ENNReal.ofReal_le_ofReal
                (gaussianPDFReal_le_exp_mul hr hε.le haa har hv' hx.2)
          _ = ENNReal.ofReal (exp ε) *
                volume.withDensity (gaussianPDF a' (σ ^ 2)) (S ∩ Iic H) := by
              rw [lintegral_const_mul _ (by fun_prop),
                withDensity_apply _ (hS.inter measurableSet_Iic)]
          _ ≤ _ := by grw [inter_subset_left]

/-- The Gaussian mechanism with means at distance at most `r` is `(ε, δ)`-DP when `ε ≤ 1`,
`c > (1 + √3) / 2`, `c² ≥ 2 log (0.66 / δ)` and `σ ≥ c r / ε` ([DP-G]). -/
theorem dp_gaussian {σ : ℝ≥0} {ε δ r c a a' : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hr : 0 < r) (hδ : 0 < δ) (hc : (1 + √3) / 2 < c) (hcδ : 2 * log (0.66 / δ) ≤ c ^ 2)
    (hcσ : c * r / ε ≤ σ) (h : |a - a'| ≤ r) :
    dp (ENNReal.ofReal ε, ENNReal.ofReal δ) (gaussianReal a (σ ^ 2)) (gaussianReal a' (σ ^ 2)) := by
  rcases le_total a' a with haa | haa
  · exact dp_gaussian_of_le hε hε₁ hr hδ hc hcδ hcσ haa (le_of_abs_le h)
  · simpa only [gaussianReal_map_neg, neg_neg] using
      dp_map (dp_gaussian_of_le hε hε₁ hr hδ hc hcδ hcσ (neg_le_neg haa)
        (by linarith [(abs_le.1 h).1])) measurable_neg

end GradedDivergence

namespace Mechanism

/-- The Gaussian mechanism with standard deviation `σ`. -/
noncomputable def gaussianMech (σ : ℝ≥0) : Mechanism ℝ ℝ :=
  ⟨fun a ↦ gaussianReal a (σ ^ 2), measurable_gaussianReal.comp (measurable_id.prodMk
    measurable_const)⟩

/-- The Gaussian mechanism is a Markov kernel. -/
instance isMarkovKernel_gaussianMech (σ : ℝ≥0) : IsMarkovKernel (gaussianMech σ) :=
  ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (gaussianReal _ _))⟩

/-- The Gaussian mechanism is `(ε, δ)`-DP for inputs at distance at most `r`, under the side
conditions of [DP-G]. -/
theorem DP_gaussianMech {σ : ℝ≥0} {ε δ r c : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hr : 0 < r) (hδ : 0 < δ) (hc : (1 + √3) / 2 < c) (hcδ : 2 * log (0.66 / δ) ≤ c ^ 2)
    (hcσ : c * r / ε ≤ σ) :
    (gaussianMech σ).DP (fun a a' ↦ |a - a'| ≤ r) (ENNReal.ofReal ε) (ENNReal.ofReal δ) :=
  fun _ _ h ↦ GradedDivergence.dp_gaussian hε hε₁ hr hδ hc hcδ hcσ h

end Mechanism
