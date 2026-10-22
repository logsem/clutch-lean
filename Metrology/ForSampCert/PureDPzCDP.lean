/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
-- Adapted from SampCert (https://github.com/leanprover/SampCert):
-- `SampCert/DifferentialPrivacy/ZeroConcentrated/DP.lean` (section `ofDP_bound`, the sinh
-- inequality and `ofDP_bound`), `SampCert/DifferentialPrivacy/RenyiDivergence.lean` and
-- `SampCert/Util/Log.lean` (`mul_mul_inv_eq_mul_cancel`).
module

public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Pure DP gives zCDP

SampCert's proof that a two-sided pure `ε`-DP bound between PMFs gives the Rényi bound
`D_α(p ‖ q) ≤ α ε² / 2` (Bun–Steinke 2016, Prop. 3.3), stated on the Rényi series
`∑ p^α q^(1-α) ≤ exp ((α - 1) (ε² α / 2))`.
-/

@[expose] public section

open Classical

noncomputable section

namespace ForSampCert

variable {T U : Type*}

/-! ## Rényi series (from `SampCert/DifferentialPrivacy/RenyiDivergence.lean`) -/

/--
Simplified consequence of absolute continuity between PMF's.
-/
def AbsCts (p q : T → ENNReal) : Prop := ∀ x : T, q x = 0 → p x = 0

lemma mul_mul_inv_eq_mul_cancel {x y : ENNReal} (H : y = 0 -> x = 0) (H2 : ¬(x ≠ 0 ∧ y = ⊤)) : (x * y⁻¹) * y = x := by
  cases x
  · simp_all
  rename_i x'
  cases (Classical.em (x' = 0))
  · simp_all
  rename_i Hx'
  cases y
  · simp_all
  rename_i y'
  cases (Classical.em (y' = 0))
  · simp_all
  rename_i Hy'
  rw [← ENNReal.coe_inv Hy']
  rw [← ENNReal.coe_mul]
  rw [← ENNReal.coe_mul]
  rw [mul_right_comm]
  rw [mul_inv_cancel_right₀ Hy' x']

lemma PMF_mul_mul_inv_eq_mul_cancel (p q : PMF T) (HA : AbsCts p q) (a : T) :
    (p a / q a) * q a = p a := by
  apply mul_mul_inv_eq_mul_cancel
  · exact fun h => HA a h
  · exact fun ⟨_, h⟩ => PMF.apply_ne_top q a h

lemma RenyiDivergenceExpectation_pointwise (a b : ENNReal) {α : ℝ} (h : 1 < α)
    (Hac : b = 0 → a = 0) : a ^ α * b ^ (1 - α) = (a / b) ^ α * b := by
  rcases eq_or_ne b 0 with hb0 | hb0
  · -- b = 0: a = 0 by AbsCts, so both sides vanish.
    subst hb0
    rw [Hac rfl, ENNReal.zero_rpow_of_pos (by linarith : 0 < α)]
    simp
  rcases eq_or_ne b ⊤ with hbt | hbt
  · -- b = ⊤: LHS has `⊤^(1-α) = 0`, RHS has `(a/⊤)^α = 0^α = 0`.
    subst hbt
    rw [ENNReal.top_rpow_of_neg (by linarith : (1 - α) < 0)]
    rw [ENNReal.div_top, ENNReal.zero_rpow_of_pos (by linarith : 0 < α)]
    simp
  rcases eq_or_ne a 0 with ha0 | ha0
  · -- a = 0: both sides are 0^α = 0.
    subst ha0
    rw [ENNReal.zero_rpow_of_pos (by linarith : 0 < α), ENNReal.zero_div,
        ENNReal.zero_rpow_of_pos (by linarith : 0 < α)]
    simp
  rcases eq_or_ne a ⊤ with hat | hat
  · -- a = ⊤ with b ∈ (0, ⊤): both sides equal ⊤.
    subst hat
    rw [ENNReal.top_rpow_of_pos (by linarith : 0 < α)]
    rw [ENNReal.top_div_of_ne_top hbt]
    rw [ENNReal.top_rpow_of_pos (by linarith : 0 < α)]
    have hb_pow_ne : b ^ (1 - α) ≠ 0 := by
      intro hc
      rcases ENNReal.rpow_eq_zero_iff.mp hc with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hb0 h1
      · exact hbt h1
    rw [ENNReal.top_mul hb_pow_ne, ENNReal.top_mul hb0]
  -- Generic case: a, b ∈ (0, ⊤). Apply `rpow_sub` and rearrange.
  rw [ENNReal.rpow_sub _ _ hb0 hbt, ← ENNReal.mul_comm_div,
      ← ENNReal.div_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ α), ENNReal.rpow_one]

/--
Renyi Divergence series written as a conditional expectation, conditioned on q.
-/
theorem RenyiDivergenceExpectation (p q : T → ENNReal) {α : ℝ} (h : 1 < α) (H : AbsCts p q) :
    (∑' x : T, (p x)^α * (q x)^(1 - α)) = ∑' x : T, (p x / q x)^α * (q x) := by
  refine tsum_congr (fun x => ?_)
  exact RenyiDivergenceExpectation_pointwise (p x) (q x) h (H x)

lemma ENNReal_rpow_sub_one_mul (a : ENNReal) {α : ℝ}
    (ha_ne_zero : a ≠ 0) (ha_ne_top : a ≠ ⊤) :
    a ^ (α - 1) * a = a ^ α := by
  conv_rhs => rw [show α = (α - 1) + 1 from by ring]
  rw [ENNReal.rpow_add _ _ ha_ne_zero ha_ne_top, ENNReal.rpow_one]

lemma RenyiDivergenceExpectation'_pointwise (a b : ENNReal) {α : ℝ} (h : 1 < α)
    (Ha_ne_zero : a ≠ 0) (Ha_ne_top : a ≠ ⊤) :
    a ^ α * b ^ (1 - α) = (a / b) ^ (α - 1) * a := by
  rcases eq_or_ne b 0 with hb0 | hb0
  · -- b = 0: both sides equal `⊤ * a`.
    subst hb0
    rw [ENNReal.zero_rpow_of_neg (by linarith : (1 - α) < 0)]
    rw [ENNReal.div_zero Ha_ne_zero]
    rw [ENNReal.top_rpow_of_pos (by linarith : 0 < α - 1)]
    rw [ENNReal.top_mul Ha_ne_zero]
    rw [ENNReal.mul_top (by
      intro hc
      exact Ha_ne_zero (ENNReal.rpow_eq_zero_iff_of_pos (by linarith : 0 < α) |>.mp hc))]
  rcases eq_or_ne b ⊤ with hbt | hbt
  · -- b = ⊤: both sides are 0.
    subst hbt
    rw [ENNReal.top_rpow_of_neg (by linarith : (1 - α) < 0)]
    rw [ENNReal.div_top, ENNReal.zero_rpow_of_pos (by linarith : 0 < α - 1)]
    simp
  -- Generic case: expand `(a/b)^(α-1) = a^(α-1) * b^(-(α-1))`, split `a^α = a^(α-1) * a`.
  rw [ENNReal.div_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ α - 1)]
  rw [ENNReal.div_eq_inv_mul, mul_assoc, mul_comm, ← ENNReal_rpow_sub_one_mul a Ha_ne_zero Ha_ne_top]
  congr 1
  rw [← ENNReal.rpow_neg]; congr 1; ring

/--
Renyi Divergence series written as a conditional expectation, conditioned on p.
-/
theorem RenyiDivergenceExpectation' (p q : PMF T) {α : ℝ} (h : 1 < α) :
    (∑' x : T, (p x)^α * (q x)^(1 - α)) = ∑' x : T, (p x / q x)^(α - 1) * (p x) := by
  have K1 : Function.support (fun x : T => (p x / q x)^(α - 1) * p x) ⊆ { t : T | p t ≠ 0 } := by
    intro a Ha hpa
    apply Ha
    show (p a / q a)^(α - 1) * p a = 0
    rw [hpa, mul_zero]
  rw [← tsum_subtype_eq_of_support_subset K1]
  have K2 : Function.support (fun x : T => (p x)^α * (q x)^(1 - α)) ⊆ { t : T | p t ≠ 0 } := by
    intro a Ha hpa
    apply Ha
    show (p a)^α * (q a)^(1 - α) = 0
    rw [hpa, ENNReal.zero_rpow_of_pos (by linarith : 0 < α)]
    simp
  rw [← tsum_subtype_eq_of_support_subset K2]
  refine tsum_congr (fun ⟨x', Hx'⟩ => ?_)
  exact RenyiDivergenceExpectation'_pointwise (p x') (q x') h Hx' (PMF.apply_ne_top p x')

/-! ## Auxiliary definitions used in the proof of the (ε^2 / 2) bound -/
section ofDP_bound
variable (ε : NNReal)
variable (p q : PMF U)

noncomputable def β (x : U) : ENNReal :=
  (ENNReal.ofReal (Real.exp ε) - (p x / q x)) / (ENNReal.ofReal (Real.exp (ε)) - ENNReal.ofReal (Real.exp (- ε)))

lemma β_le_one (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x) {x : U} : β ε p q x ≤ 1 := by
  unfold β
  apply ENNReal.div_le_of_le_mul
  simp
  rw [← tsub_le_iff_right]
  refine (ENNReal.sub_le_sub_iff_left ?h.h ?h.h').mpr ?h.a
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    simp
  · simp
  · apply Hqp

lemma β_ne_top (Hε : 0 < ε) : β ε p q x ≠ ⊤ := by
  unfold β
  intro HK
  apply ENNReal.div_eq_top.mp at HK
  rcases HK with ⟨ _ , HK' ⟩ | ⟨ HK', _ ⟩
  · rw [<- ENNReal.ofReal_sub] at HK'
    · simp at HK'
      apply not_le.mpr Hε HK'
    · apply Real.exp_nonneg
  · apply ENNReal.sub_eq_top_iff.mp at HK'
    simp at HK'

lemma one_sub_β (Hε : 0 < ε) (Hpq : ∀ x, (p x / q x ≤ ENNReal.ofReal (Real.exp ε))) (x : U) : 1 - (β ε p q x : ENNReal) =
    ((p x / q x) - ENNReal.ofReal (Real.exp (-ε)) ) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))) := by
  unfold β
  generalize HC : (p x / q x) = C
  generalize HD : (ENNReal.ofReal (Real.exp ε)) = D
  generalize HE : (ENNReal.ofReal (Real.exp (- ε))) = E
  have H1 : (D - E ≠ 0) := by
    rw [<- HD, <- HE]
    rw [<- ENNReal.ofReal_sub]
    · simp
      trivial
    · apply Real.exp_nonneg
  have H2 : (D - E ≠ ⊤) := by simp [<- HD, <- HE]
  apply (ENNReal.mul_left_inj H1 H2).mp
  rw [ENNReal.sub_mul ?G1]
  case G1 =>
    intros
    trivial
  conv =>
    congr
    · rw [ENNReal.mul_comm_div]
      rw [ENNReal.div_eq_inv_mul]
    · rw [ENNReal.mul_comm_div]
      rw [ENNReal.div_eq_inv_mul]
  simp [ENNReal.inv_mul_cancel H1 H2]
  rw [tsub_tsub]
  rw [tsub_add_eq_tsub_tsub_swap]
  rw [ENNReal.sub_sub_cancel ?G1 ?G2]
  case G1 => simp [<- HD]
  case G2 =>
    rw [<- HD, <- HC]
    apply Hpq

lemma sub_one_β_ne_top : (1 - β ε p q x) ≠ ⊤ := by
  apply ENNReal.sub_ne_top
  simp

/--
Value of the random variable A
-/
noncomputable def A_val (b : Bool) : ENNReal :=
    match b with
    | false => ENNReal.ofReal (Real.exp (-ε))
    | true => ENNReal.ofReal (Real.exp (ε))

/--
Proability space underlying the random variable A
-/
noncomputable def A_pmf (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x) (x : U) : PMF Bool :=
  ⟨ fun b =>
        match b with
        | false => β ε p q x
        | true => 1 - β ε p q x, by
       simp only [Summable.hasSum_iff ENNReal.summable, tsum_bool]
       rw [add_comm]
       exact tsub_add_cancel_of_le (β_le_one ε p q Hqp) ⟩

/--
Expectation for the random variable A at each point x
-/
lemma A_expectation (Hε : 0 < ε) (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x)
    (Hpq : ∀ x, (p x / q x ≤ ENNReal.ofReal (Real.exp ε))) (Hac : AbsCts p q) (x : U) :
    ∑'(b : Bool), A_val ε b * A_pmf ε p q Hqp x b = p x / q x := by
  rw [tsum_bool]
  unfold A_pmf
  rw [A_val, A_val, DFunLike.coe, PMF.instFunLike]
  simp only []
  conv =>
    lhs
    congr
    · unfold β
    · rw [one_sub_β _ _ _ Hε Hpq]
  generalize HC : (p x / q x) = C
  generalize HD : (ENNReal.ofReal (Real.exp ε)) = D
  generalize HE : (ENNReal.ofReal (Real.exp (- ε))) = E
  have H1 : (D - E ≠ 0) := by
    rw [<- HD, <- HE]
    rw [<- ENNReal.ofReal_sub]
    · simp
      trivial
    · apply Real.exp_nonneg
  have H2 : (D - E ≠ ⊤) := by simp [<- HD, <- HE]
  apply (ENNReal.mul_left_inj H1 H2).mp
  rw [add_mul]
  rw [division_def]
  rw [division_def]
  repeat rw [mul_assoc]
  simp [ENNReal.inv_mul_cancel H1 H2]
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    rw [<- HE]
    simp
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    rw [<- HD]
    simp
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    rw [<- HC]
    have Hac := Hac x
    intro HK
    apply ENNReal.div_eq_top.mp at HK
    rcases HK with ⟨ h1, h2 ⟩ | ⟨ h, _ ⟩
    · exact absurd (Hac h2) h1
    · exact PMF.apply_ne_top p x h
  conv =>
    enter [1, 2, 2]
    rw [mul_comm]

  -- Arithmetic: prove finiteness of all products to avoid ⊤ case analysis
  have HD_ne_top : D ≠ ⊤ := by simp [<- HD]
  have HE_ne_top : E ≠ ⊤ := by simp [<- HE]
  have HC_ne_top : C ≠ ⊤ := by
    rw [<- HC]
    intro HK
    apply ENNReal.div_eq_top.mp at HK
    rcases HK with ⟨ h1, h2 ⟩ | ⟨ h, _ ⟩
    · exact h1 (Hac x h2)
    · exact PMF.apply_ne_top p x h
  conv =>
    enter [1, 1, 2]
    rw [mul_comm]
  conv =>
    enter [1, 2, 1]
    rw [mul_comm]
  rw [add_comm]
  apply tsub_add_tsub_cancel
  · -- CD ≥ ED: need E * D ≤ C * D
    apply mul_le_mul'
    · rw [← HE, ← HC]; apply Hqp
    · rfl
  · -- ED ≥ CE: need C * E ≤ E * D
    rw [mul_comm E D]
    apply mul_le_mul'
    · rw [← HC, ← HD]; apply Hpq
    · rfl

/--
Jensen's inequality for the random variable A: real reduct
-/
lemma A_jensen_real (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x) {α : ℝ} (Hα : 1 < α) (x : U) :
    (∑'(b : Bool), (A_val ε b).toReal * (A_pmf ε p q Hqp x b).toReal) ^ α ≤ (∑'(b : Bool), ((A_val ε b).toReal)^α * (A_pmf ε p q Hqp x b).toReal) := by
  have HJensen := @ConvexOn.map_integral_le _ _ ⊤ _ _ _ _ _ (fun b => (A_val ε b).toReal) _
          (PMF.toMeasure.isProbabilityMeasure (A_pmf ε p q Hqp x))
          (@convexOn_rpow α (le_of_lt Hα))
          ?G1 ?G2 ?G3 ?G4 ?G5
  case G1 =>
    apply ContinuousOn.rpow
    · exact continuousOn_id' (Set.Ici 0)
    · exact continuousOn_const
    · intro _ _
      right
      linarith
  case G2 =>
    exact isClosed_Ici
  case G3 =>
    apply MeasureTheory.ae_of_all
    intro b
    cases b <;> simp
  case G4 => simp
  case G5 => apply MeasureTheory.Integrable.of_finite
  rw [PMF.integral_eq_tsum _ _ ?G4] at HJensen
  case G4 => simp
  rw [PMF.integral_eq_tsum _ _ ?G5] at HJensen
  case G5 => apply MeasureTheory.Integrable.of_finite
  rw [tsum_bool, tsum_bool] at HJensen
  simp only [smul_eq_mul] at HJensen
  convert HJensen using 2
  · rw [tsum_bool]; ring
  · rw [tsum_bool]; ring

/--
Jensen's inequality for the random variable A
-/
lemma A_jensen (Hε : 0 < ε) (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x)
    {α : ℝ} (Hα : 1 < α) (x : U) :
    (∑'(b : Bool), A_val ε b * A_pmf ε p q Hqp x b) ^ α ≤ (∑'(b : Bool), (A_val ε b)^α * A_pmf ε p q Hqp x b) := by
  have SC1 (b : Bool) : A_val ε b ≠ ⊤ := by cases b <;> simp [A_val]
  have SC2 (b : Bool) : (A_pmf ε p q Hqp x) b ≠ ⊤ := by
    cases b <;> simp only [A_pmf, DFunLike.coe]
    · apply β_ne_top
      apply Hε
    · apply sub_one_β_ne_top
  apply (ENNReal.toReal_le_toReal ?G1 ?G2).mp
  case G1 =>
    apply ENNReal.rpow_ne_top_of_nonneg
    · linarith
    · rw [tsum_bool]
      apply ENNReal.add_ne_top.mpr
      apply And.intro
      · apply ENNReal.mul_ne_top
        · apply (SC1 false)
        · apply (SC2 false)
      · apply ENNReal.mul_ne_top
        · apply (SC1 true)
        · apply (SC2 true)
  case G2 =>
    rw [tsum_bool]
    apply ENNReal.add_ne_top.mpr
    apply And.intro
    · apply ENNReal.mul_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · linarith
        apply (SC1 false)
      · apply (SC2 false)
    · apply ENNReal.mul_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · linarith
        apply (SC1 true)
      · apply (SC2 true)
  rw [tsum_bool, tsum_bool]
  rw [← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_add ?G1 ?G2]
  case G1 =>
    apply ENNReal.mul_ne_top
    · apply (SC1 false)
    · apply (SC2 false)
  case G2 =>
    apply ENNReal.mul_ne_top
    · apply (SC1 true)
    · apply (SC2 true)
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_add ?G1 ?G2]
  case G1 =>
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · linarith
      apply (SC1 false)
    · apply (SC2 false)
  case G2 =>
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · linarith
      apply (SC1 true)
    · apply (SC2 true)
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_mul]
  rw [← ENNReal.toReal_rpow]
  rw [← ENNReal.toReal_rpow]
  have HJR := A_jensen_real ε p q Hqp Hα x
  rw [tsum_bool, tsum_bool] at HJR
  trivial

noncomputable def B (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x) : PMF Bool := q.bind (A_pmf ε p q Hqp)

/--
Formula for B which shows up in the main derivation
-/
lemma B_eval_open (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x)
    (b : Bool) : B ε p q Hqp b = ∑'(x : U), A_pmf ε p q Hqp x b * q x := by
  unfold B
  simp
  apply tsum_congr
  intro
  rw [mul_comm]

lemma B_eval_false_closed_form (Hε : 0 < ε) (Bval : ENNReal) (HBtop : Bval ≠ ⊤) (HBle : Bval ≤ 1)
    (Hrel : ENNReal.ofReal (Real.exp (-ε)) * Bval + ENNReal.ofReal (Real.exp ε) * (1 - Bval) = 1) :
    Bval = (ENNReal.ofReal (Real.exp ε) - 1)
         / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))) := by
  conv =>
    enter [2, 1, 2]
    rw [<- Hrel]
  generalize HE1 : (Real.exp ε.toReal) = E1
  generalize HE2 : (Real.exp (-ε.toReal)) = E2
  generalize HB : Bval = B
  rw [HB] at HBtop HBle
  apply (ENNReal.toReal_eq_toReal_iff' ?G1 ?G2).mp
  case G1 => exact HBtop
  case G2 =>
    apply lt_top_iff_ne_top.mp
    apply ENNReal.div_lt_top
    · apply ENNReal.sub_ne_top
      apply ENNReal.ofReal_ne_top
    · intro HK
      rw [<- ENNReal.ofReal_sub _ ?G3] at HK
      case G3 =>
        rw [<- HE2]
        apply Real.exp_nonneg
      simp at HK
      rw [<- HE1, <- HE2] at HK
      apply Real.exp_le_exp.mp at HK
      simp at HK
      apply LE.le.not_gt at HK
      apply HK
      trivial
  rw [ENNReal.toReal_div]
  rw [<- ENNReal.ofReal_sub _ ?G1]
  case G1 =>
    rw [<- HE2]
    apply Real.exp_nonneg
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 =>
    simp
    rw [<- HE2, <- HE1]
    apply Real.exp_le_exp.mpr
    simp
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    apply ENNReal.ofReal_ne_top
  have HHB : B = ENNReal.ofReal (ENNReal.toReal B) := by
    rw [ENNReal.ofReal_toReal]
    exact HBtop
  rw [HHB]
  rw [<- ENNReal.ofReal_mul ?G1]
  case G1 =>
    rw [<- HE2]
    apply Real.exp_nonneg
  rw [<- ENNReal.ofReal_mul ?G1]
  case G1 =>
    rw [<- HE1]
    apply Real.exp_nonneg
  simp
  rw [<- ENNReal.ofReal_sub _ ?G1]
  case G1 =>
    apply mul_nonneg
    · rw [<- HE1]
      apply Real.exp_nonneg
    · apply ENNReal.toReal_nonneg
  have SC1 : 0 ≤ E1 - E1 * B.toReal := by
    simp
    conv =>
      rhs
      rw [<- mul_one E1]
    apply mul_le_mul
    · simp
    · apply ENNReal.ofReal_le_one.mp
      rw [ENNReal.ofReal_toReal HBtop]
      exact HBle
    · apply ENNReal.toReal_nonneg
    · rw [<- HE1]
      apply Real.exp_nonneg
  have SC2 : 0 ≤ E2 * B.toReal + (E1 - E1 * B.toReal) := by
    apply add_nonneg
    · apply mul_nonneg
      · rw [<- HE2]
        apply Real.exp_nonneg
      · apply ENNReal.toReal_nonneg
    · apply SC1
  have SC3 : 0 ≤ E1 - (E2 * B.toReal + (E1 - E1 * B.toReal)) := by
    rw [tsub_add_eq_tsub_tsub_swap]
    rw [sub_nonneg]
    simp
    rw [<- HE2, <- HE1]
    apply mul_le_mul
    · apply Real.exp_le_exp.mpr
      simp
    · simp
    · apply ENNReal.toReal_nonneg
    · apply Real.exp_nonneg
  rw [<- ENNReal.ofReal_add ?G1 ?G2]
  case G1 =>
    apply mul_nonneg
    · rw [<- HE2]
      apply Real.exp_nonneg
    · apply ENNReal.toReal_nonneg
  case G2 => apply SC1
  rw [<- ENNReal.ofReal_sub _ ?G1]
  case G1 => apply SC2
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply SC3
  apply eq_div_of_mul_eq
  · apply sub_ne_zero.mpr
    symm
    apply LT.lt.ne
    rw [<- HE1, <- HE2]
    apply Real.exp_lt_exp.mpr
    simp
    trivial
  ring_nf

/--
closed form for B false
-/
lemma B_eval_false (Hε : 0 < ε) (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x)
    (Hpq : ∀ x, (p x / q x ≤ ENNReal.ofReal (Real.exp ε))) (Hac : AbsCts p q) :
    B ε p q Hqp false = (ENNReal.ofReal (Real.exp ε) - 1) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))) := by
  have H1 : (1 - (B ε p q Hqp) false) = B ε p q Hqp true := by
    apply ENNReal.sub_eq_of_eq_add ?G1
    case G1 => apply PMF.apply_ne_top
    rw [<- PMF.tsum_coe (B ε p q Hqp)]
    rw [tsum_bool]
    rw [add_comm]
  suffices (ENNReal.ofReal (Real.exp (- ε)) * B ε p q Hqp false + ENNReal.ofReal (Real.exp ε) * (1 - B ε p q Hqp false) = 1) by
    exact B_eval_false_closed_form (ε := ε) Hε _ (PMF.apply_ne_top _ _) (PMF.coe_le_one _ _) this
  suffices ∑'(x : U), (∑'(b : Bool), A_val ε b * A_pmf ε p q Hqp x b) * q x = 1 by
    conv at this =>
      enter [1, 1, x]
      rw [<- ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm] at this
    rw [tsum_bool] at this
    conv at this =>
      lhs
      congr
      · enter [1, a]
        rw [mul_assoc]
      · enter [1, a]
        rw [mul_assoc]
    rw [ENNReal.tsum_mul_left] at this
    rw [ENNReal.tsum_mul_left] at this
    rw [<- B_eval_open] at this
    rw [<- B_eval_open] at this
    conv =>
      rhs
      rw [<- this]
    congr
  conv =>
    enter [1, 1, x]
    rw [A_expectation _ _ _ Hε Hqp Hpq Hac]
  suffices ∑' (x : U), p x / q x * q x = ∑'(x : U), p x by
    rw [this]
    apply PMF.tsum_coe
  apply tsum_eq_tsum_of_ne_zero_bij (fun x => x.val)
  · simp [Function.Injective]
  · intro x Hx
    simp [Function.support] at Hx
    simp_all only [Subtype.range_coe_subtype, Function.mem_support, ne_eq, Set.mem_ofPred_eq, not_false_eq_true]
  · simp [Function.support]
    intros x _
    rw [PMF_mul_mul_inv_eq_mul_cancel p q Hac x]

/--
closed form for B true
-/
lemma B_eval_true (Hε : 0 < ε) (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x)
    (Hpq : ∀ x, (p x / q x ≤ ENNReal.ofReal (Real.exp ε))) (Hac : AbsCts p q) :
    B ε p q Hqp true = (1 - ENNReal.ofReal (Real.exp (- ε))) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))):= by
  have H1 : (1 - (B ε p q Hqp) false) = B ε p q Hqp true := by
    apply ENNReal.sub_eq_of_eq_add ?G1
    case G1 => apply PMF.apply_ne_top
    rw [<- PMF.tsum_coe (B ε p q Hqp)]
    rw [tsum_bool]
    rw [add_comm]
  rw [<- H1]
  rw [B_eval_false] <;> try trivial

  -- Quality of life
  generalize HE1 : (Real.exp ε.toReal) = E1
  generalize HE2 : (Real.exp (-ε.toReal)) = E2
  have Hexp_nn : 0 ≤ E2 := by rw [<- HE2]; exact Real.exp_nonneg _
  have Hdiff_ne : ENNReal.ofReal E1 - ENNReal.ofReal E2 ≠ 0 := by
    rw [<- ENNReal.ofReal_sub _ Hexp_nn]
    simp
    rw [<- HE2, <- HE1]
    apply Real.exp_lt_exp.mpr
    simp
    trivial
  have Hdiff_ne_top : ENNReal.ofReal E1 - ENNReal.ofReal E2 ≠ ⊤ := by
    rw [<- ENNReal.ofReal_sub _ Hexp_nn]; simp
  apply (ENNReal.eq_div_iff Hdiff_ne Hdiff_ne_top).mpr
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    exact ENNReal.ofReal_ne_top
  simp
  rw [division_def, <- mul_assoc]
  conv =>
    enter [1, 2, 1]
    rw [mul_comm]
  rw [mul_assoc, ENNReal.mul_inv_cancel Hdiff_ne Hdiff_ne_top]
  simp
  rw [<- ENNReal.ofReal_sub _ ?G1]
  case G1 =>
    rw [<- HE2]
    apply Real.exp_nonneg
  have X : (1 : ENNReal) = (ENNReal.ofReal (1 : ℝ)) := by simp
  conv =>
    enter [1, 2, 2]
    rw [X]
  rw [<- ENNReal.ofReal_sub _ ?G1]
  case G1 => simp
  rw [<- ENNReal.ofReal_sub _ ?G1]
  case G1 =>
    simp
    rw [<- HE1]
    apply Real.one_le_exp
    apply NNReal.zero_le_coe
  congr 1
  simp
  rw [<- HE2]
  exact Real.exp_nonneg _

end ofDP_bound

/-
## Prove trig inequality B.1
-/

section sinh_inequality

lemma lemma_cosh_add {w z : ℝ} : Real.cosh (w + z) = Real.cosh w * Real.cosh z * (1 + Real.tanh w * Real.tanh z) :=
  let L {a : ℝ} : Real.sinh a = Real.cosh a * Real.tanh a := by
    rw [Real.tanh_eq_sinh_div_cosh]
    rw [division_def, mul_comm, mul_assoc]
    rw [inv_mul_cancel₀]
    · simp
    · linarith [Real.cosh_pos a]
  calc Real.cosh (w + z)
    _ = Real.cosh w * Real.cosh z + Real.sinh w * Real.sinh z := Real.cosh_add w z
    _ = Real.cosh w * Real.cosh z + ((Real.cosh w * Real.tanh w) * (Real.cosh z * Real.tanh z)) := by rw [L, L]
    _ = Real.cosh w * Real.cosh z * (1 + Real.tanh w * Real.tanh z) := by linarith

variable (x y : ℝ)

noncomputable def C := 2 * Real.sinh ((x - y) / 2) * Real.cosh (x / 2) * Real.cosh (y / 2)

noncomputable def t := Real.tanh (x / 2) * Real.tanh (y / 2)

lemma lemma_sinh_sub : Real.sinh (x - y) = (C x y) * (1 - t x y) :=
  calc Real.sinh (x - y)
    _ = (Real.exp (x - y) - Real.exp (-(x-y))) / 2 := by
      rw [Real.sinh_eq]
    _ = ((Real.exp ((x - y) / 2) - (Real.exp (- ((x - y) / 2)))) * (Real.exp ((x - y) / 2) + (Real.exp (- ((x - y) / 2))))) / 2 := by
      congr 1
      ring_nf
      simp
      rw [← Real.exp_nsmul]
      rw [← Real.exp_nsmul]
      rw [nsmul_eq_mul]
      simp
      congr 2
      · ring_nf
      · ring_nf
    _ = 2 * Real.sinh ((x - y) / 2) * Real.cosh ((x - y) / 2) := by
      rw [Real.sinh_eq]
      rw [Real.cosh_eq]
      ring_nf
    _ = (C x y) * (1 - t x y) := by
      unfold C
      unfold t
      repeat rw [mul_assoc]
      congr 2
      have T1 : (1 - Real.tanh (x / 2) * Real.tanh (y / 2)) = (1 + Real.tanh (x / 2) * Real.tanh (-(y / 2))) := by
        rw [Real.tanh_neg (y / 2)]
        linarith
      have T2 : Real.cosh (y / 2) = Real.cosh (-(y / 2)) := by
        exact Eq.symm (Real.cosh_neg (y / 2))
      rw [T1, T2]
      clear T1 T2
      repeat rw [<- mul_assoc]
      rw [<- lemma_cosh_add]
      congr
      linarith

lemma lemma_sub_sinh : Real.sinh x - Real.sinh y = C x y * (1 + t x y) :=
  calc Real.sinh x - Real.sinh y
    _ = (Real.exp x - Real.exp (-x) - Real.exp y + Real.exp (-y)) / 2 := by
      simp [Real.sinh_eq, Real.sinh_eq]
      ring_nf
    _ = ((Real.exp ((x - y) / 2) - Real.exp (-((x - y) / 2))) * (Real.exp ((x + y) / 2) + Real.exp (-((x + y) / 2))) ) / 2:= by
      congr 1
      ring_nf
      simp [<- Real.exp_add]
      ring_nf
    _ = 2 * Real.sinh ((x - y)/2) * Real.cosh ((x+y)/2) := by
      rw [Real.sinh_eq, Real.cosh_eq]
      linarith
    _ = C x y * (1 + t x y) := by
      unfold C
      unfold t
      conv =>
        enter [1, 2, 1]
        rw [add_div]
      rw [lemma_cosh_add]
      linarith

lemma C_ne_zero (Hyx : y < x) : C x y ≠ 0 := by
  unfold C
  repeat apply mul_ne_zero
  · simp
  · apply Real.sinh_ne_zero.mpr
    linarith
  · linarith [Real.cosh_pos (x / 2)]
  · linarith [Real.cosh_pos (y / 2)]

lemma lemma_step_1 (Hyx : y < x) : (Real.sinh x - Real.sinh y) / Real.sinh (x - y) = (1 + t x y) / (1 - t x y) := by
  rw [lemma_sinh_sub]
  rw [lemma_sub_sinh]
  rw [mul_div_mul_comm]
  rw [div_self]
  · simp
  · apply C_ne_zero
    linarith

lemma t_nonneg (Hy : 0 ≤ y) (Hyx : y < x) : 0 ≤ t x y := by
  unfold t
  apply mul_nonneg
  · rw [Real.tanh_eq_sinh_div_cosh]
    apply div_nonneg
    · apply Real.sinh_nonneg_iff.mpr
      linarith
    · linarith [Real.cosh_pos (x / 2)]
  · rw [Real.tanh_eq_sinh_div_cosh]
    apply div_nonneg
    · apply Real.sinh_nonneg_iff.mpr
      linarith
    · linarith [Real.cosh_pos (y / 2)]

-- Upstream?
lemma tanh_lt_1 (w : ℝ) : Real.tanh w < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  apply (div_lt_one ?hb).mpr
  · rw [Real.sinh_eq, Real.cosh_eq]
    apply div_lt_div_of_pos_right
    · linarith [Real.exp_pos (-w)]
    · simp
  · apply Real.cosh_pos

-- Upstream?
lemma tanh_nonneg {w : ℝ} (HW : 0 ≤ w) : 0 ≤ Real.tanh w := by
  rw [Real.tanh_eq_sinh_div_cosh]
  apply div_nonneg
  · exact Real.sinh_nonneg_iff.mpr HW
  · exact (LT.lt.le (Real.cosh_pos w))

lemma t_le_one (Hy : 0 ≤ y) (Hyx : y < x) : t x y < 1 := by
  unfold t
  conv =>
    enter [2]
    rw [<- mul_one 1]
  apply (mul_lt_mul'' (tanh_lt_1 (x / 2)) (tanh_lt_1 (y / 2)))
  · apply tanh_nonneg
    linarith
  · apply tanh_nonneg
    linarith

lemma lemma_step_2 (Hy : 0 ≤ y) (Hyx : y < x) (H : t x y ≤ Real.tanh (x * y / 4)) : (1 + t x y) / (1 - t x y) ≤ Real.exp (x * y / 2) := by
  apply div_le_of_le_mul₀
  · linarith [t_le_one x y Hy Hyx]
  · apply Real.exp_nonneg
  rw [mul_sub]
  simp
  apply (add_le_add_iff_right (Real.exp (x * y / 2) * t x y)).mp
  rw [sub_add_cancel]
  apply (add_le_add_iff_left (-1)).mp
  repeat rw [<- add_assoc]
  rw [neg_add_cancel, zero_add]
  conv =>
    enter [1, 1]
    rw [<- one_mul (t x y)]
  rw [<- add_mul]
  apply (le_div_iff₀' ?G1).mp
  case G1 =>
    apply add_pos
    · simp
    · apply Real.exp_pos
  apply le_trans H
  apply Eq.le
  rw [Real.tanh_eq_sinh_div_cosh]
  rw [Real.sinh_eq, Real.cosh_eq]
  rw [div_div_div_comm]
  have R1 : (Real.exp (x * y / 4) - Real.exp (-(x * y / 4))) = (Real.exp (-(x * y / 4)) *  (Real.exp (x * y / 2) - 1)) := by
    rw [mul_sub]
    rw [<- Real.exp_add]
    simp
    linarith
  rw [R1]
  clear R1
  have R2 : (Real.exp (x * y / 4) + Real.exp (-(x * y / 4))) = (Real.exp (-(x * y / 4)) *(Real.exp (x * y / 2) + 1)) := by
    rw [mul_add]
    rw [<- Real.exp_add]
    simp
    linarith
  rw [R2]
  clear R2
  simp
  rw [mul_div_mul_comm]
  have R3 : Real.exp (-(x * y / 4)) / Real.exp (-(x * y / 4)) = 1 := by
    apply div_self
    apply Real.exp_ne_zero
  rw [R3]
  simp
  congr 1
  · linarith
  · linarith

lemma Differentiable.differentiable_tanh :  Differentiable ℝ Real.tanh := by
  conv =>
    enter [2, y]
    rw [Real.tanh_eq_sinh_div_cosh]
  apply Differentiable.div
  · apply Real.differentiable_sinh
  · apply Real.differentiable_cosh
  · intro z
    have _ := Real.cosh_pos z
    linarith

lemma Real.continuous_tanh : Continuous Real.tanh := by
  conv =>
    enter [1, y]
    rw [Real.tanh_eq_sinh_div_cosh]
  apply Continuous.div
  · apply Real.continuous_sinh
  · apply Real.continuous_cosh
  · intro z
    have _ := Real.cosh_pos z
    linarith

lemma deriv.deriv_tanh (x : ℝ) : deriv Real.tanh x = 1 / (Real.cosh x) ^ 2 := by
  have Hcne : Real.cosh x ≠ 0 := by have := Real.cosh_pos x; linarith
  have Htanh_eq : Real.tanh = Real.sinh / Real.cosh := by
    funext z; simp [Real.tanh_eq_sinh_div_cosh, Pi.div_apply]
  rw [Htanh_eq]
  rw [deriv_div (Real.differentiable_sinh x) (Real.differentiable_cosh x) Hcne]
  rw [Real.deriv_sinh, Real.deriv_cosh]
  rw [← Real.cosh_sub]
  simp

lemma tanh_lt_id_nonneg {x : ℝ} (Hx : 0 ≤ x) : Real.tanh x ≤ x := by
  let f (x : ℝ) := x - Real.tanh x
  suffices 0 * (x - 0) ≤ f x - f 0 by
    dsimp [f] at this
    simp at this
    trivial
  have Hdiff : DifferentiableOn ℝ f (interior (Set.Ici 0)) := by
    apply Differentiable.differentiableOn
    dsimp [f]
    apply Differentiable.sub
    · apply differentiable_id
    · apply Differentiable.differentiable_tanh
  have Hcts : ContinuousOn f (Set.Ici 0) := by
    apply Continuous.continuousOn
    dsimp [f]
    apply Continuous.sub
    · apply continuous_id'
    · apply Real.continuous_tanh
  apply Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ici 0)
  · trivial
  · trivial
  · simp
    intro y _
    dsimp [f]
    -- Calculate the derivative
    have Heq : (fun x : ℝ => x - Real.tanh x) = id - Real.tanh := by
      funext z; simp
    rw [Heq]
    rw [deriv_sub (differentiable_id.differentiableAt)
        (Differentiable.differentiable_tanh.differentiableAt)]
    rw [deriv.deriv_tanh]
    simp
    apply inv_le_one_of_one_le₀
    exact (one_le_sq_iff_one_le_abs _).mpr (by rw [abs_of_nonneg (Real.cosh_pos _).le]; exact Real.one_le_cosh _)
  · simp
  · simp
    trivial
  · trivial

lemma lemma_step_3_aux_differentiable (x : ℝ) :
    Differentiable ℝ (fun z : ℝ => Real.tanh (x * z / 4) - Real.tanh (x / 2) * Real.tanh (z / 2)) := by
  apply Differentiable.sub
  · have Hfunc : (fun y : ℝ => Real.tanh (x * y / 4)) =
                 ((fun (y : ℝ) => Real.tanh y) ∘ (fun (z : ℝ) => x * z / 4)) := by
      rw [Function.comp_def]
    rw [Hfunc]
    apply Differentiable.comp
    · exact Differentiable.differentiable_tanh
    · apply Differentiable.mul_const
      apply Differentiable.const_mul
      exact differentiable_id
  · apply Differentiable.const_mul
    have Hfunc : (fun y : ℝ => Real.tanh (y / 2)) =
                 ((fun (y : ℝ) => Real.tanh y) ∘ (fun (z : ℝ) => z / 2)) := by
      rw [Function.comp_def]
    rw [Hfunc]
    apply Differentiable.comp
    · exact Differentiable.differentiable_tanh
    · apply Differentiable.mul_const
      exact differentiable_id

lemma lemma_step_3_aux_continuous (x : ℝ) :
    Continuous (fun z : ℝ => Real.tanh (x * z / 4) - Real.tanh (x / 2) * Real.tanh (z / 2)) :=
  (lemma_step_3_aux_differentiable x).continuous

lemma lemma_step_3_deriv_nonneg (x z : ℝ) (Hx : x ≤ 2) (Hx' : 0 ≤ x) (Hz0 : 0 ≤ z) :
    0 ≤ deriv (fun z => Real.tanh (x * z / 4) - Real.tanh (x / 2) * Real.tanh (z / 2)) z := by
  have Hfunc_xz4 : (fun z => Real.tanh (x * z / 4)) = Real.tanh ∘ (fun z => x * z / 4) := by rw [Function.comp_def]
  have Hfunc_z2 : (fun z => Real.tanh (z / 2)) = Real.tanh ∘ (fun z => z / 2) := by rw [Function.comp_def]
  have Heq : (fun z => Real.tanh (x * z / 4) - Real.tanh (x / 2) * Real.tanh (z / 2)) =
      (fun z => Real.tanh (x * z / 4)) - (fun z => Real.tanh (x / 2) * Real.tanh (z / 2)) := by
    funext; simp
  rw [Heq]
  rw [deriv_sub ?G1 ?G2]
  case G1 =>
    apply Differentiable.differentiableAt
    rw [Hfunc_xz4]
    apply Differentiable.comp
    · apply Differentiable.differentiable_tanh
    · apply Differentiable.mul_const
      apply Differentiable.const_mul
      apply differentiable_id
  case G2 =>
    apply Differentiable.differentiableAt
    apply Differentiable.const_mul
    rw [Hfunc_z2]
    apply Differentiable.comp
    · apply Differentiable.differentiable_tanh
    · apply Differentiable.mul_const
      apply differentiable_id
  rw [sub_nonneg]
  simp
  rw [Hfunc_xz4]
  rw [Hfunc_z2]
  rw [deriv_comp _ ?G1 ?G2]
  case G1 =>
    apply Differentiable.differentiableAt
    apply Differentiable.differentiable_tanh
  case G2 =>
    apply Differentiable.differentiableAt
    apply Differentiable.mul_const
    apply differentiable_id
  simp
  rw [deriv_comp _ ?G1 ?G2]
  case G1 =>
    apply Differentiable.differentiableAt
    apply Differentiable.differentiable_tanh
  case G2 =>
    apply Differentiable.differentiableAt
    apply Differentiable.mul_const
    apply Differentiable.const_mul
    apply differentiable_id
  simp
  rw [deriv.deriv_tanh]
  rw [deriv.deriv_tanh]
  suffices ((x / 2) * (1 / Real.cosh (z / 2) ^ 2 * 2⁻¹) ≤ 1 / Real.cosh (x * z / 4) ^ 2 * (x / 4)) by
    apply (le_trans _ this)
    apply mul_le_mul
    · apply tanh_lt_id_nonneg
      linarith
    · apply Eq.le
      rfl
    · apply mul_nonneg
      · apply div_nonneg
        · simp
        · apply sq_nonneg
      · simp
    · linarith
  conv =>
    enter [1]
    rw [mul_comm]
    rw [mul_assoc]
    enter [2]
    rw [mul_comm]
    rw [<- division_def]
    rw [div_div]
  apply mul_le_mul
  · apply (div_le_div_iff_of_pos_left _ _ _).mpr
    · apply sq_le_sq'
      · apply (@le_trans _ _ _ 0)
        · apply neg_nonneg.mp
          simp
          apply (LT.lt.le (Real.cosh_pos _))
        · apply (LT.lt.le (Real.cosh_pos _))
      · apply Real.cosh_le_cosh.mpr
        apply abs_le_abs
        · apply (div_le_div_iff₀ (by simp) (by simp)).mpr
          rw [mul_assoc]
          rw [mul_comm]
          rw [mul_assoc]
          apply mul_le_mul <;> linarith
        · apply (@le_trans _ _ _ 0)
          · apply neg_nonneg.mp
            simp
            apply div_nonneg
            · apply mul_nonneg
              · linarith
              · linarith
            · simp
          · linarith
    · simp
    · apply sq_pos_of_pos
      apply Real.cosh_pos
    · apply sq_pos_of_pos
      apply Real.cosh_pos
  · apply Eq.le
    congr
    linarith
  · apply div_nonneg <;> linarith
  · apply div_nonneg
    · linarith
    apply sq_nonneg

lemma lemma_step_3 (Hy : 0 ≤ y) (Hyx : y < x) (Hx : x ≤ 2) : Real.tanh (x / 2) * Real.tanh (y / 2) ≤ Real.tanh (x * y / 4) := by
  let f (z : ℝ) :=  Real.tanh (x * z / 4) - Real.tanh (x / 2) * Real.tanh (z / 2)
  suffices 0 ≤ f y by
    dsimp [f] at this
    linarith
  suffices 0 * (y - 0) ≤ f y - f 0 by
    dsimp [f] at this
    simp at this
    dsimp [f]
    simp
    trivial
  have Hdiff : DifferentiableOn ℝ f (interior (Set.Icc 0 2)) :=
    (lemma_step_3_aux_differentiable x).differentiableOn
  have Hcts : ContinuousOn f (Set.Icc 0 2) :=
    (lemma_step_3_aux_continuous x).continuousOn
  apply Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 0 2)
  · trivial
  · trivial
  · simp
    intros z Hz0 _
    exact lemma_step_3_deriv_nonneg x z Hx (by linarith) (le_of_lt Hz0)
  · simp
  · simp
    apply And.intro <;> linarith
  · linarith

lemma sinh_inequality (Hy : 0 ≤ y) (Hyx : y < x) (Hx : x ≤ 2) :
    (Real.sinh x - Real.sinh y) / Real.sinh (x - y) ≤ Real.exp (x * y / 2) := by
  -- Temp usage of hypothesis so Lean doesn't freak out
  have _ := Hy
  have _ := Hx
  rw [lemma_step_1 _ _ Hyx]
  apply (lemma_step_2 _ _ Hy Hyx)
  unfold t
  apply lemma_step_3 _ _ Hy Hyx Hx

end sinh_inequality
lemma ofDP_bound_SC0 (ε : NNReal) (Hε : 0 < ε) :
    ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)) ≠ 0 := by
  apply ne_of_gt
  simp
  apply ENNReal.ofReal_lt_ofReal_iff'.mpr
  refine ⟨?_, Real.exp_pos _⟩
  apply Real.exp_lt_exp.mpr
  simp
  exact Hε

lemma ofDP_bound_SC1 (ε : NNReal) (Hε : 0 < ε) (α : ℝ) (Hα : 0 ≤ α) :
    ENNReal.ofReal (Real.exp (-↑ε)) ^ α *
      ((ENNReal.ofReal (Real.exp ↑ε) - 1) /
       (ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)))) ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg Hα ENNReal.ofReal_ne_top
  apply lt_top_iff_ne_top.mp
  apply ENNReal.div_lt_top
  · exact ENNReal.sub_ne_top ENNReal.ofReal_ne_top
  · exact ofDP_bound_SC0 ε Hε

lemma ofDP_bound_SC2 (ε : NNReal) (Hε : 0 < ε) (α : ℝ) (Hα : 0 ≤ α) :
    ENNReal.ofReal (Real.exp ↑ε) ^ α *
      ((1 - ENNReal.ofReal (Real.exp (-↑ε))) /
       (ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)))) ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg Hα ENNReal.ofReal_ne_top
  apply lt_top_iff_ne_top.mp
  apply ENNReal.div_lt_top
  · exact ENNReal.sub_ne_top ENNReal.one_ne_top
  · exact ofDP_bound_SC0 ε Hε

lemma ofDP_bound_ratio_inv {V : Type*} (p q : PMF V) (ε : ℝ) (x : V)
    (Hpx : p x ≠ 0)
    (H : q x / p x ≤ ENNReal.ofReal (Real.exp ε)) :
    ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x := by
  apply ENNReal.inv_le_inv.mp
  rw [<- ENNReal.ofReal_inv_of_pos ?G4]
  case G4 => apply Real.exp_pos
  rw [<- Real.exp_neg]
  simp
  apply (le_trans _ H)
  apply Eq.le
  apply (ENNReal.toReal_eq_toReal_iff' ?G4 ?G5).mp
  case G4 =>
    apply ENNReal.inv_ne_top.mpr
    apply ENNReal.div_ne_zero.mpr
    refine ⟨Hpx, PMF.apply_ne_top _ _⟩
  case G5 =>
    intro HK
    apply ENNReal.div_eq_top.mp at HK
    rcases HK with ⟨ _, h2 ⟩ | ⟨ h, _ ⟩
    · exact Hpx h2
    · exact PMF.apply_ne_top _ _ h
  rw [ENNReal.toReal_inv]
  repeat rw [ENNReal.toReal_div]
  rw [inv_div]

lemma ofDP_bound_sinh_step (ε α : ℝ) (Hε : 0 < ε) (Hα : 1 < α) (Hεα : ε * α ≤ 2) :
    Real.exp (-ε) ^ α * ((Real.exp ε - 1) / (Real.exp ε - Real.exp (-ε))) +
      Real.exp ε ^ α * ((1 - Real.exp (-ε)) / (Real.exp ε - Real.exp (-ε))) ≤
      Real.exp ((α - 1) * (1/2 * ε^2 * α)) := by
  rw [division_def]
  rw [division_def]
  repeat rw [<- mul_assoc]
  rw [<- add_mul]
  rw [mul_sub]
  rw [mul_sub]
  simp only [mul_one]
  repeat rw [<- Real.exp_mul]
  repeat rw [<- Real.exp_add]
  have X : (Real.exp (-ε * α + ε) - Real.exp (-ε * α) + (Real.exp (ε * α) - Real.exp (ε * α + -ε))) =
           (Real.exp (-ε * α + ε) - Real.exp (ε * α + -ε)) + ((Real.exp (ε * α) - Real.exp (-ε * α))) := by
    linarith
  rw [X]
  clear X
  have X : ε * α + -ε = (ε * (α - 1)) := by linarith
  rw [X]
  clear X
  have X : (-ε * α + ε) = -(ε * (α - 1)) := by linarith
  rw [X]
  clear X
  have X : (-ε * α) = -(ε * α) := by linarith
  rw [X]
  clear X
  have X : (Real.exp (-(ε * (α - OfNat.ofNat 1))) - Real.exp (ε * (α - OfNat.ofNat 1)) +
              (Real.exp (ε * α) - Real.exp (-(ε * α)))) =
           ((Real.exp (ε * α) - Real.exp (-(ε * α))) -
             (Real.exp (ε * (α - OfNat.ofNat 1)) - Real.exp (-(ε * (α - OfNat.ofNat 1))))) := by
    linarith
  rw [X]
  clear X
  have Hsinh (x : ℝ) : (Real.exp x - Real.exp (-x)) = 2 * Real.sinh x := by
    rw [Real.sinh_eq]
    linarith
  rw [Hsinh]
  rw [Hsinh]
  rw [Hsinh]
  have X : (OfNat.ofNat 2 * Real.sinh (ε * α) - OfNat.ofNat 2 * Real.sinh (ε * (α - OfNat.ofNat (OfNat.ofNat 1)))) * (OfNat.ofNat 2 * Real.sinh ε)⁻¹ =
           (Real.sinh (ε * α) - Real.sinh (ε * (α - OfNat.ofNat (OfNat.ofNat 1)))) * (Real.sinh ε)⁻¹ := by
    rw [mul_inv]
    repeat rw [<- mul_assoc]
    congr 1
    rw [mul_comm]
    rw [mul_sub]
    repeat rw [<- mul_assoc]
    rw [inv_mul_cancel₀ ?G1]
    case G1 => simp
    simp
  rw [X]
  clear X
  rw [<- division_def]
  have W : ε = (ε * α) - ((ε * (α - 1))) := by linarith
  conv =>
    enter [1, 2]
    rw [W]
  clear W
  apply (le_trans (sinh_inequality _ _ ?G1 ?G2 ?G3))
  case G1 =>
    apply mul_nonneg
    · exact le_of_lt Hε
    linarith
  case G2 =>
    apply (mul_lt_mul_of_pos_left)
    · exact sub_one_lt α
    · exact Hε
  case G3 => linarith
  apply Eq.le
  congr 1
  linarith

/-! ## The `(1/2)ε²` bound -/

/--
Renyi series is bounded above by the Max Divergence ε
(SampCert `RenyiDivergence_le_MaxDivergence`, stated on the series).
-/
lemma RenyiDivergence_le_MaxDivergence {p q : PMF T} {ε : ℝ} {α : ℝ} (Hα : 1 < α)
    (Hmax_divergence : ∀ t : T, (p t / q t) ≤ ENNReal.ofReal (Real.exp ε)) :
    ∑' x : T, (p x)^α * (q x)^(1 - α) ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε)) := by
  -- Rewrite to expectation conditioned on q
  rw [RenyiDivergenceExpectation' p q Hα]

  -- Pointwise bound
  have H : ∑' (x : T), (p x / q x) ^ (α - 1) * p x ≤
      ∑' (x : T), (ENNReal.ofReal (Real.exp ε)) ^ (α - 1) * p x := by
    apply ENNReal.tsum_le_tsum
    intro x
    apply mul_le_mul
    · apply ENNReal.rpow_le_rpow (Hmax_divergence x)
      linarith
    · rfl
    · apply _root_.zero_le
    · apply _root_.zero_le
  apply (le_trans H)
  rw [ENNReal.tsum_mul_left]
  rw [PMF.tsum_coe]
  rw [mul_one, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm]

/--
Pure DP bound implies absolute continuity
-/
lemma ACNeighbour_of_DP (ε : ℝ) (p q : PMF U)
    (H : ∀ x, p x / q x ≤ ENNReal.ofReal (Real.exp ε)) : AbsCts p q := by
  intro x Hx2
  apply Classical.by_contradiction
  intro Hx1
  have H' : p x / q x ≤ ENNReal.ofReal (Real.exp ↑ε) := H x
  rw [Hx2, ENNReal.div_zero Hx1] at H'
  simp at H'

lemma ofDP_bound_large_εα (ε : NNReal) (p q : PMF U)
    (H : ∀ x, p x / q x ≤ ENNReal.ofReal (Real.exp ε)) (α : ℝ) (Hα : 1 < α) (Hεα : ε * α > 2) :
    ∑' x, p x ^ α * q x ^ (1 - α) ≤ ENNReal.ofReal (Real.exp ((α - 1) * (1/2 * ε^2 * α))) := by
  apply (le_trans (RenyiDivergence_le_MaxDivergence Hα H))
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have : (0 : ℝ) ≤ ε := NNReal.zero_le_coe
  nlinarith

/--
Convert a two-sided ε-DP bound to the `(1/2)ε²`-zCDP bound on the Renyi series
(SampCert `ofDP_bound`, for one pair of PMFs).
-/
lemma ofDP_bound (ε : NNReal) (p₀ q₀ : PMF U)
    (H : ∀ x, p₀ x / q₀ x ≤ ENNReal.ofReal (Real.exp ε))
    (H' : ∀ x, q₀ x / p₀ x ≤ ENNReal.ofReal (Real.exp ε)) (α : ℝ) (Hα : 1 < α) :
    ∑' x, p₀ x ^ α * q₀ x ^ (1 - α) ≤ ENNReal.ofReal (Real.exp ((α - 1) * (1/2 * ε^2 * α))) := by
  obtain Hεα | Hεα := Classical.em (ε * α > 2)
  · exact ofDP_bound_large_εα ε p₀ q₀ H α Hα Hεα
  apply le_of_not_gt at Hεα

  -- Reduction to the nonzero case here
  have K1 : Function.support (fun (x : U) => DFunLike.coe p₀ x ) ⊆ { u : U | p₀ u ≠ 0 } := by
    simp [Function.support]
  have Hp_pre := PMF.tsum_coe p₀
  rw [<- tsum_subtype_eq_of_support_subset K1 ] at Hp_pre
  have K2 : Function.support (fun (x : U) => DFunLike.coe q₀ x ) ⊆ { u : U | p₀ u ≠ 0 } := by
    simp [Function.support]
    intro a Ha Hk
    apply Ha
    apply (ACNeighbour_of_DP _ _ _ H')
    apply Hk
  have Hq_pre := PMF.tsum_coe q₀
  rw [<- tsum_subtype_eq_of_support_subset K2 ] at Hq_pre
  let U' := { x // DFunLike.coe p₀ x ≠ 0 }
  let p : PMF U' :=
    ⟨ fun u => p₀ u, by
        rw [<- Hp_pre]
        apply Summable.hasSum
        exact ENNReal.summable ⟩
  let q : PMF U' :=
    ⟨ fun u => q₀ u, by
        rw [<- Hq_pre]
        apply Summable.hasSum
        exact ENNReal.summable ⟩
  clear K1 K2
  have X : ∑' x, p₀ x ^ α * q₀ x ^ (1 - α) = ∑' x, p x ^ α * q x ^ (1 - α) := by
    have K3 : Function.support (fun (x : U) =>
        DFunLike.coe p₀ x ^ α * DFunLike.coe q₀ x ^ (OfNat.ofNat 1 - α)) ⊆
        { u : U | p₀ u ≠ 0 } := by
      simp [Function.support]
      intro u H1 _ _ _ H5
      have H5 := H1 H5
      linarith
    rw [<- tsum_subtype_eq_of_support_subset K3]
    dsimp [p, q]
    rfl
  rw [X]
  clear X

  -- Derive absolute continuity facts from the pure DP bound
  have Hacpq : AbsCts p q := by
    dsimp [p, q]
    simp [DFunLike.coe]
    intro u' Hu'
    rcases u' with ⟨ u'' , _ ⟩
    simp
    apply (ACNeighbour_of_DP _ _ _ H)
    trivial
  have Hqp : ∀ (x : U'), ENNReal.ofReal (Real.exp (-↑ε)) ≤ p x / q x := by
    intro x
    apply ofDP_bound_ratio_inv p q ε x
    · rcases x with ⟨ x' , Hx' ⟩
      dsimp [p]
      simp [DFunLike.coe]
      exact Hx'
    · rcases x with ⟨ x' , _ ⟩
      apply (le_trans _ (H' x'))
      dsimp [p, q]
      simp [DFunLike.coe]
  have Hpq : ∀ (x : U'), p x / q x ≤ ENNReal.ofReal (Real.exp ↑ε) := by
    intro x
    rcases x with ⟨ x' , _ ⟩
    apply (le_trans _ (H x'))
    dsimp [p, q]
    simp [DFunLike.coe]

  -- Rewrite to conditional expectation
  rw [RenyiDivergenceExpectation _ _ Hα Hacpq]

  -- Rewrite to A
  -- Next step won't work with ε=0, must separate the case.
  obtain rfl | Hε' := Classical.em (ε = 0)
  · -- Follows from the DP bound
    simp_all
    apply (@le_trans _ _ _ (∑' (x : U'), 1 ^ α * q x))
    · apply ENNReal.tsum_le_tsum
      intro i
      apply (ENNReal.mul_le_mul_iff_left ?G1 ?G2).mpr
      case G1 =>
        intro HK
        have HK' := Hacpq _ HK
        rcases i
        trivial
      case G2 => apply PMF.apply_ne_top
      apply ENNReal.rpow_le_rpow
      · exact Hpq i
      · linarith
    · simp
  have Hε : 0 < ε := by exact pos_iff_ne_zero.mpr Hε'
  conv =>
    enter [1, 1, x]
    rw [<- A_expectation ε p q Hε Hqp Hpq Hacpq x]

  -- Apply Jensen's inequality
  apply (@le_trans _ _ _ (∑' (x : U'), (∑' (b : Bool), (A_val ε b)^α * (A_pmf ε p q Hqp x) b) * q x))
  · apply ENNReal.tsum_le_tsum
    intro a
    apply (ENNReal.mul_le_mul_iff_left ?G1 ?G2).mpr
    case G1 =>
      have HK1 : p a ≠ 0 := by
        rcases a
        dsimp [p]
        simp [DFunLike.coe]
        trivial
      intro HK
      apply HK1
      apply Hacpq
      trivial
    case G2 => apply PMF.apply_ne_top
    apply A_jensen _ _ _ Hε _ Hα

  -- Exchange the summations
  conv =>
    enter [1, 1, x]
    rw [<- ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]

  -- Pull out constant from inner series
  -- Rewrite in terms of B
  -- Evaluate A_val and B to a closed form
  conv =>
    enter [1, 1, b, 1, u]
    rw [mul_assoc]
  conv =>
    enter [1, 1, b]
    rw [ENNReal.tsum_mul_left]
    rw [<- B_eval_open]
  rw [tsum_bool]
  rw [B_eval_false] <;> try trivial
  rw [B_eval_true] <;> try trivial
  simp only [A_val]
  have SC0 := ofDP_bound_SC0 ε Hε
  have SC1 := ofDP_bound_SC1 ε Hε α (by linarith)
  have SC2 := ofDP_bound_SC2 ε Hε α (by linarith)
  apply (ENNReal.toReal_le_toReal ?G1 ?G2).mp
  case G1 =>
    apply ENNReal.add_ne_top.mpr
    apply And.intro
    · trivial
    · trivial
  case G2 => exact ENNReal.ofReal_ne_top
  simp
  rw [ENNReal.toReal_add ?G1 ?G2]
  case G1 => apply SC1
  case G2 => apply SC2
  clear SC0 SC1 SC2
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_div]
  rw [ENNReal.toReal_div]
  rw [← ENNReal.toReal_rpow]
  rw [← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply ENNReal.one_le_ofReal.mpr
    apply Real.one_le_exp
    simp only [NNReal.zero_le_coe]
  case G2 => exact ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply ENNReal.ofReal_le_ofReal_iff'.mpr
    left
    apply Real.exp_le_exp.mpr
    simp
  case G2 => exact ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply ENNReal.ofReal_le_one.mpr
    apply Real.exp_le_one_iff.mpr
    simp
  case G2 => simp
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  simp
  apply le_trans (ofDP_bound_sinh_step ε.toReal α (NNReal.coe_pos.mpr Hε) Hα Hεα)
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  apply Eq.le
  ring_nf

end ForSampCert
