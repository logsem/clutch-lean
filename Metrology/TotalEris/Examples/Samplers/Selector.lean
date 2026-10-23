module

public import Metrology.TotalEris
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Index selector -/

open Iris Iris.BI Iris.ProofMode ProbLang
  ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open MeasureTheory (lintegral_add_left lintegral_const lintegral_const_mul'
  lintegral_indicator lintegral_mul_const lintegral_piecewise lintegral_tsum
  setLIntegral_congr_fun setLIntegral_const volume measure_univ)
open MeasureTheory.Measure (restrict_apply restrict_restrict)
open scoped ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
local bi IProp GF

section distribution

def BiiFailProb (k : ℕ) (x : ℝ) : ℝ := (2 * k + x) / (2 * k + 2)

theorem BiiFailProb_nonneg (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) : 0 ≤ BiiFailProb k x :=
  div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)

theorem BiiFailProb_le_one (k : ℕ) {x : ℝ} (hx1 : x ≤ 1) : BiiFailProb k x ≤ 1 := by
  unfold BiiFailProb
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) k]

def BiiPMF (k : ℕ) (x : ℝ) : Bool → ℝ≥0∞
  | true => .ofReal (1 - BiiFailProb k x)
  | false => .ofReal (BiiFailProb k x)

def SPMF₀ (k : ℕ) (x y : ℝ) (n : ℕ) : ℝ≥0∞ :=
  .ofReal ((y ^ n / n.factorial) * BiiFailProb k x ^ n -
    (y ^ (n + 1) / (n + 1).factorial) * BiiFailProb k x ^ (n + 1))

def SPMF (k : ℕ) (x y : ℝ) (N n : ℕ) : ℝ≥0∞ :=
  if N ≤ n then SPMF₀ k x y (n - N) else 0

theorem SPMF₀_eq_RealDecrTrialPMF₀ (k : ℕ) (x y : ℝ) (n : ℕ) :
    SPMF₀ k x y n = RealDecrTrialPMF₀ (y * BiiFailProb k x) n := by
  unfold SPMF₀ RealDecrTrialPMF₀
  congr 1
  rw [mul_pow, mul_pow]; ring

theorem BiiFailProb_mul_setLIntegral_SPMF₀ (k : ℕ) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (m : ℕ) :
    ENNReal.ofReal (BiiFailProb k x) * (∫⁻ z in Set.Icc 0 y, SPMF₀ k x z m ∂volume)
      = SPMF₀ k x y (m + 1) := by
  have hqnn := BiiFailProb_nonneg k hx0
  have hq1 := BiiFailProb_le_one k hx1
  have hint : (∫ z in (0 : ℝ)..y, ((z * BiiFailProb k x) ^ m / (m.factorial : ℝ)
        - (z * BiiFailProb k x) ^ (m + 1) / ((m + 1).factorial : ℝ)))
      = BiiFailProb k x ^ m * y ^ (m + 1) / (m + 1).factorial
        - BiiFailProb k x ^ (m + 1) * y ^ (m + 2) / (m + 2).factorial := by
    have h0 : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hcm0 : (fun z : ℝ => z ^ m * BiiFailProb k x ^ m / (m.factorial : ℝ))
        = fun z => BiiFailProb k x ^ m / (m.factorial : ℝ) * z ^ m := by funext z; ring
    have hcm1 : (fun z : ℝ => z ^ (m + 1) * BiiFailProb k x ^ (m + 1) / ((m + 1).factorial : ℝ))
        = fun z => BiiFailProb k x ^ (m + 1) / ((m + 1).factorial : ℝ) * z ^ (m + 1) := by
      funext z; ring
    simp only [mul_pow]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        hcm0, hcm1, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_pow, integral_pow, zero_pow (by omega), zero_pow (by omega)]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have hbridge : (∫⁻ z in Set.Icc 0 y, SPMF₀ k x z m ∂volume)
      = ENNReal.ofReal (BiiFailProb k x ^ m * y ^ (m + 1) / (m + 1).factorial
          - BiiFailProb k x ^ (m + 1) * y ^ (m + 2) / (m + 2).factorial) := by
    rw [← hint, ← lintegral_ofReal_Icc hy0 (by fun_prop) (fun z hz =>
          RealDecrTrialPMF₀_real_nonneg (mul_nonneg hz.1 hqnn)
            ((mul_le_of_le_one_left hqnn (hz.2.trans hy1)).trans hq1) m)]
    refine setLIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
    rw [SPMF₀_eq_RealDecrTrialPMF₀]; rfl
  rw [hbridge, ← ENNReal.ofReal_mul hqnn]
  unfold SPMF₀
  congr 1
  ring

end distribution

section creditExpectation

def CCreditV (F : ℕ → ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  .ofReal (1 / ((m : ℝ) + 2)) * F 0 + .ofReal (1 / ((m : ℝ) + 2)) * F 1 +
  .ofReal ((m : ℝ) / ((m : ℝ) + 2)) * F 2

def BiiCreditV (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  BiiPMF k x false * F false + BiiPMF k x true * F true

def SCreditV (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, SPMF k x y N n * F n

def BCreditV (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  .ofReal (Real.exp (-x * (2 * k + x) / (2 * k + 2))) * F true +
  (1 - .ofReal (Real.exp (-x * (2 * k + x) / (2 * k + 2)))) * F false

theorem SCreditV_eq_RealDecrTrialCreditV (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) :
    SCreditV F k x y N = RealDecrTrialCreditV F N (y * BiiFailProb k x) := by
  unfold SCreditV RealDecrTrialCreditV
  refine tsum_congr fun n => ?_
  congr 1
  unfold SPMF RealDecrTrialPMF
  by_cases h : N ≤ n
  · rw [ite_eq_left h, ite_eq_left h, SPMF₀_eq_RealDecrTrialPMF₀]
  · rw [ite_eq_right h, ite_eq_right h]

theorem SCreditV_peel (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) :
    SCreditV F k x y N
      = ENNReal.ofReal (1 - BiiFailProb k x * y) * F N
        + ∑' m : ℕ, SPMF₀ k x y (m + 1) * F (N + 1 + m) := by
  rw [SCreditV_eq_RealDecrTrialCreditV, RealDecrTrialCreditV_reindex,
      tsum_eq_zero_add' (f := fun m => RealDecrTrialPMF₀ (y * BiiFailProb k x) m
        * F (N + m)) ENNReal.summable]
  congr 1
  · rw [Nat.add_zero]
    congr 1
    unfold RealDecrTrialPMF₀
    congr 1
    simp only [pow_zero, pow_one, zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      div_one]
    ring
  · exact tsum_congr fun m => by
      have hidx : N + (m + 1) = N + 1 + m := by omega
      rw [← SPMF₀_eq_RealDecrTrialPMF₀, hidx]

end creditExpectation

section creditKernel

def CCredit (F : ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun j => if j = 0 then F 0 else if j = 1 then F 1 else F 2

theorem CCredit_sum (F : ℕ → ℝ≥0∞) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 2), CCredit F n = F 0 + F 1 + (m : ℝ≥0∞) * F 2 := by
  induction m with
  | zero => simp [Finset.sum_range_succ, CCredit]
  | succ k ih =>
    have hk2 : CCredit F (k + 2) = F 2 := by simp [CCredit]
    rw [add_right_comm, Finset.sum_range_succ, ih, hk2]
    push_cast; ring

theorem cCredit_sum_div_le (F : ℕ → ℝ≥0∞) (m : ℕ) :
    (∑ n ∈ Finset.range ((m : ℤ) + 2).toNat, CCredit F n)
        / (((m : ℤ) + 2).toNat : ENNReal) ≤ CCreditV F m := by
  have hz : ((m : ℤ) + 2).toNat = m + 2 := by omega
  have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hd : ENNReal.ofReal ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ≥0∞) := by
    have h : (m : ℝ) + 2 = ((m + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [h, ENNReal.ofReal_natCast]
  have hinv : ENNReal.ofReal (1 / ((m : ℝ) + 2)) = ((m + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hpos, hd]
  have hmm : ENNReal.ofReal ((m : ℝ) / ((m : ℝ) + 2))
      = (m : ℝ≥0∞) * ((m + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_inv_of_pos hpos, hd]
  have hcv : CCreditV F m
      = (F 0 + F 1 + (m : ℝ≥0∞) * F 2) * ((m + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [CCreditV, hinv, hmm]; ring
  refine le_of_eq ?_
  rw [hz, CCredit_sum, hcv, div_eq_mul_inv]

def BiiCredit (F : Bool → ℝ≥0∞) (x : ℝ) (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  if n = 0 then F true else if n = 1 then (if x < r then F true else F false) else F false

def BiiCCredit (F : Bool → ℝ≥0∞) (x : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ r, BiiCredit F x n r ∂(LawfulProbLangℝ.unifUnit (T := ℝ))

theorem BiiCCredit_zero (F : Bool → ℝ≥0∞) (x : ℝ) : BiiCCredit F x 0 = F true := by
  show ∫⁻ _, F true ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) = F true
  rw [lintegral_const, measure_univ, mul_one]

theorem BiiCCredit_two (F : Bool → ℝ≥0∞) (x : ℝ) : BiiCCredit F x 2 = F false := by
  show ∫⁻ _, F false ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) = F false
  rw [lintegral_const, measure_univ, mul_one]

private theorem Ioi_inter_unit {x : ℝ} (hx0 : 0 ≤ x) : Set.Ioi x ∩ Set.Icc 0 1 = Set.Ioc x 1 := by
  ext r; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
  exact ⟨fun ⟨h2, _, h1⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h2, hx0.trans h2.le, h1⟩⟩

private theorem Iic_inter_unit {x : ℝ} (hx1 : x ≤ 1) : Set.Iic x ∩ Set.Icc 0 1 = Set.Icc 0 x := by
  ext r; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
  exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hx1⟩⟩

theorem BiiCCredit_one (F : Bool → ℝ≥0∞) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    BiiCCredit F x 1 = F true * ENNReal.ofReal (1 - x) + F false * ENNReal.ofReal x := by
  show ∫⁻ r, (if x < r then F true else F false) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  have hdecomp : (fun r => if x < r then F true else F false)
      = (fun r => (Set.Ioi x).indicator (fun _ => F true) r
          + (Set.Iic x).indicator (fun _ => F false) r) := by
    funext r; by_cases h : x < r
    · simp [h, not_le.mpr h]
    · simp [h, not_lt.mp h]
  rw [hdecomp,
    lintegral_add_left ((measurable_const.indicator measurableSet_Ioi)),
    lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Iic,
    setLIntegral_const, setLIntegral_const, restrict_apply measurableSet_Ioi,
    restrict_apply measurableSet_Iic, Ioi_inter_unit hx0, Iic_inter_unit hx1, Real.volume_Ioc, Real.volume_Icc,
    sub_zero]

def SbiiCredit (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (z : ℝ) (c : ℝ≥0∞) :
    Bool → ℝ≥0∞ :=
  fun bii => if bii then F N else SCreditV F k x z (N + 1) + c

def SCreditAmp (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun z => if y < z then F N else BiiCreditV (SbiiCredit F k x N z c) k x

def SCredit (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) : ℝ → ℝ≥0∞ :=
  SCreditAmp F k x N y 0

def BS0Credit (F : Bool → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun n => if n % 2 = 0 then F true else F false

end creditKernel

section measurability

theorem measurable_sPMF₀ (k : ℕ) (x : ℝ) (n : ℕ) :
    Measurable (fun y : ℝ => SPMF₀ k x y n) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

theorem measurable_sPMF (k : ℕ) (x : ℝ) (N n : ℕ) :
    Measurable (fun y : ℝ => SPMF k x y N n) := by
  unfold SPMF
  by_cases h : N ≤ n
  · simpa only [h, ite_true] using measurable_sPMF₀ k x (n - N)
  · simpa only [h, ite_false] using measurable_const

theorem measurable_sCreditV (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) :
    Measurable (fun y : ℝ => SCreditV F k x y N) :=
  Measurable.tsum fun n => (measurable_sPMF k x N n).mul_const (F n)

theorem measurable_sCreditAmp (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞) :
    Measurable (SCreditAmp F k x N y c) := by
  unfold SCreditAmp
  refine Measurable.ite measurableSet_Ioi measurable_const ?_
  change Measurable fun z => BiiPMF k x false * (SCreditV F k x z (N + 1) + c)
    + BiiPMF k x true * F N
  exact (((measurable_sCreditV F k x (N + 1)).add_const c).const_mul (BiiPMF k x false)).add
    measurable_const

theorem measurable_biiCredit (F : Bool → ℝ≥0∞) (x : ℝ) (n : ℕ) :
    Measurable (BiiCredit F x n) := by
  unfold BiiCredit
  split
  · exact measurable_const
  · split
    · exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
    · exact measurable_const

end measurability

section conservation

theorem BiiFailProb_mul_setLIntegral_SCreditV (F : ℕ → ℝ≥0∞) (k : ℕ) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (N : ℕ) :
    ENNReal.ofReal (BiiFailProb k x)
        * (∫⁻ z in Set.Icc 0 y, SCreditV F k x z (N + 1) ∂volume)
      = ∑' m : ℕ, SPMF₀ k x y (m + 1) * F (N + 1 + m) := by
  have hreindex : ∀ z, SCreditV F k x z (N + 1) = ∑' m : ℕ, SPMF₀ k x z m * F (N + 1 + m) := by
    intro z
    rw [SCreditV_eq_RealDecrTrialCreditV, RealDecrTrialCreditV_reindex]
    exact tsum_congr fun m => by rw [← SPMF₀_eq_RealDecrTrialPMF₀]
  have hint : (∫⁻ z in Set.Icc 0 y, SCreditV F k x z (N + 1) ∂volume)
      = ∫⁻ z in Set.Icc 0 y, ∑' m : ℕ, SPMF₀ k x z m * F (N + 1 + m) ∂volume :=
    setLIntegral_congr_fun measurableSet_Icc (fun z _ => hreindex z)
  rw [hint,
    lintegral_tsum (fun m => ((measurable_sPMF₀ k x m).mul_const (F (N + 1 + m))).aemeasurable),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [lintegral_mul_const _ (measurable_sPMF₀ k x m), ← mul_assoc,
    BiiFailProb_mul_setLIntegral_SPMF₀ k hx0 hx1 hy0 hy1]

theorem SCreditAmp_lintegral_eq (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∫⁻ z, SCreditAmp F k x N y c z ∂(LawfulProbLangℝ.unifUnit (T := ℝ))
      = SCreditV F k x y N + ENNReal.ofReal (BiiFailProb k x * y) * c := by
  have hqnn := BiiFailProb_nonneg k hx0
  show ∫⁻ z, SCreditAmp F k x N y c z ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  have hfun : (fun z => SCreditAmp F k x N y c z) = (Set.Ioi y).piecewise (fun _ => F N)
      (fun z => ENNReal.ofReal (BiiFailProb k x) * SCreditV F k x z (N + 1)
        + (ENNReal.ofReal (BiiFailProb k x) * c
          + ENNReal.ofReal (1 - BiiFailProb k x) * F N)) := by
    funext z
    simp only [SCreditAmp, Set.piecewise, Set.mem_Ioi]
    by_cases h : y < z
    · simp only [ite_eq_left h]
    · simp only [ite_eq_right h]
      unfold BiiCreditV SbiiCredit BiiPMF
      simp only [Bool.false_eq_true, ite_false, ite_true]
      ring
  rw [hfun,
    lintegral_piecewise measurableSet_Ioi, Set.compl_Ioi,
    setLIntegral_const, restrict_apply measurableSet_Ioi, Ioi_inter_unit hy0, Real.volume_Ioc,
    restrict_restrict measurableSet_Iic, Iic_inter_unit hy1,
    lintegral_add_left ((measurable_sCreditV F k x (N + 1)).const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    BiiFailProb_mul_setLIntegral_SCreditV F k hx0 hx1 hy0 hy1,
    setLIntegral_const, Real.volume_Icc, sub_zero, SCreditV_peel F k x y N]
  have hq1 := BiiFailProb_le_one k hx1
  have hc1 : ENNReal.ofReal (1 - y) + ENNReal.ofReal (1 - BiiFailProb k x) * ENNReal.ofReal y
      = ENNReal.ofReal (1 - BiiFailProb k x * y) := by
    rw [← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_add (by linarith) (mul_nonneg (by linarith) hy0)]
    congr 1; ring
  have hc2 : ENNReal.ofReal (BiiFailProb k x) * ENNReal.ofReal y
      = ENNReal.ofReal (BiiFailProb k x * y) := (ENNReal.ofReal_mul hqnn).symm
  rw [← hc1, ← hc2]
  ring

theorem SCreditAmp_lintegral_le (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (B : ℝ) (hyB : y ≤ B) :
    ∫⁻ z, SCreditAmp F k x N y c z ∂(LawfulProbLangℝ.unifUnit (T := ℝ))
      ≤ SCreditV F k x y N + ENNReal.ofReal B * c := by
  rw [SCreditAmp_lintegral_eq F k x N y c hx0 hx1 hy0 hy1]
  have hq1 := BiiFailProb_le_one k hx1
  gcongr
  nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hy0, hyB]

theorem BiiCreditV_C_eq (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    BiiCreditV F k x = CCreditV (BiiCCredit F x) (2 * k) := by
  have hcT : ENNReal.ofReal (1 / (2 * (k : ℝ) + 2))
        + ENNReal.ofReal (1 / (2 * (k : ℝ) + 2)) * ENNReal.ofReal (1 - x)
      = ENNReal.ofReal (1 - BiiFailProb k x) := by
    rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by positivity) (by linarith))]
    congr 1; unfold BiiFailProb; field_simp; ring
  have hcF : ENNReal.ofReal (1 / (2 * (k : ℝ) + 2)) * ENNReal.ofReal x
        + ENNReal.ofReal (2 * (k : ℝ) / (2 * k + 2))
      = ENNReal.ofReal (BiiFailProb k x) := by
    rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (mul_nonneg (by positivity) hx0) (by positivity)]
    congr 1; unfold BiiFailProb; field_simp; ring
  simp only [CCreditV, BiiCCredit_zero, BiiCCredit_one F hx0 hx1, BiiCCredit_two, BiiCreditV,
    BiiPMF]
  push_cast
  rw [← hcT, ← hcF]
  ring

theorem BCreditV_S0_eq (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    BCreditV F k x = SCreditV (BS0Credit F) k x x 0 := by
  have hp0 : (0 : ℝ) ≤ x * BiiFailProb k x := mul_nonneg hx0 (BiiFailProb_nonneg k hx0)
  have hp1 : x * BiiFailProb k x ≤ 1 :=
    (mul_le_of_le_one_left (BiiFailProb_nonneg k hx0) hx1).trans (BiiFailProb_le_one k hx1)
  have hSeq : SCreditV (BS0Credit F) k x x 0
      = RealDecrTrialCreditV (fun n => if n % 2 = 0 then F true else F false) 0
          (x * BiiFailProb k x) := by
    unfold SCreditV RealDecrTrialCreditV
    refine tsum_congr fun n => ?_
    have hSPMF : SPMF k x x 0 n = RealDecrTrialPMF₀ (x * BiiFailProb k x) n := by
      rw [SPMF, ite_eq_left (Nat.zero_le n), Nat.sub_zero, SPMF₀_eq_RealDecrTrialPMF₀]
    rw [hSPMF, RealDecrTrialPMF_base]
    simp only [BS0Credit]
  rw [hSeq, RealDecrTrialCreditV_parity (F true) (F false) hp0 hp1]
  have harg : Real.exp (-x * (2 * k + x) / (2 * k + 2))
      = Real.exp (-(x * BiiFailProb k x)) := by congr 1; unfold BiiFailProb; ring
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-(x * BiiFailProb k x)))
      = ENNReal.ofReal (1 - Real.exp (-(x * BiiFailProb k x))) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  unfold BCreditV
  rw [harg, hsub]

end conservation

section specification

theorem beq_int_lit {n m : Int} :
    ((BaseLit.int n : BaseLit ℝ) == BaseLit.int m) = (n == m) := rfl

theorem twp_C (E : CoPset) (F : ℕ → ℝ≥0∞) (m : ℕ) :
    ⊢ ↯ (CCreditV F m) -∗
      tglWp E pl(&C #int (m : ℤ))
        (fun v : Val ℝ => iprop(∃ n : ℕ,
          ⌜v.1 = pl(#int (Int.ofNat n))⌝ ∗ ⌜n = 0 ∨ n = 1 ∨ n = 2⌝ ∗ ↯ (F n))) := by
  iintro Hε
  twp_pure
  twp_bind pl(rand(#int (m : ℤ) + #2, #()))
  twp_pures
  twp_bind (Exp.rand (pl(#int ((m : ℤ) + 2))) pl(#()))
  iapply (twp_rand_exp (ε₂ := CCredit F) (Hz := by omega) (HSum := cCredit_sum_div_le F m)) $$ Hε
  iintro %n ⟨%hn, Hcr⟩
  iapply (ErisWpGS.tglWp_value_of_toVal (v := (.int n : Val ℝ)) rfl)
  simp only [Exp.ofVal]
  obtain ⟨hn0, hnz⟩ := hn
  twp_pures
  by_cases h0 : n = 0
  · rw [beq_int_lit, beq_iff_eq.mpr h0]
    twp_pures
    twp_value
    imodintro
    have hc : CCredit F n.toNat = F 0 := by
      simp only [CCredit]; rw [ite_eq_left (by omega : n.toNat = 0)]
    isimp only [hc] at Hcr
    iframe Hcr
    itrivial
  · rw [beq_int_lit, beq_eq_false_iff_ne.mpr h0]
    twp_pures
    by_cases h1 : n = 1
    · rw [beq_int_lit, beq_iff_eq.mpr h1]
      twp_pures
      twp_value
      imodintro
      have hc : CCredit F n.toNat = F 1 := by
        simp only [CCredit]; rw [ite_eq_right (by omega), ite_eq_left (by omega : n.toNat = 1)]
      isimp only [hc] at Hcr
      iframe Hcr
      itrivial
    · rw [beq_int_lit, beq_eq_false_iff_ne.mpr h1]
      twp_pures
      twp_value
      imodintro
      have hc : CCredit F n.toNat = F 2 := by
        simp only [CCredit]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      isimp only [hc] at Hcr
      iframe Hcr
      itrivial

theorem twp_Bii (E : CoPset) (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ⊢ ↯ (BiiCreditV F k x) -∗
      tglWp E pl(&Bii #int (k : ℤ) #x)
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hε
  twp_pure
  twp_pure
  twp_bind pl(&C (#2 * #int (k : ℤ)))
  twp_pure
  have h2k : (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) := by push_cast; ring
  rw [h2k]
  iapply tglWp_wand
  isplitl [Hε]
  · iapply (twp_C E (BiiCCredit F x) (2 * k))
    iapply (ErrorCredit.ext (BiiCreditV_C_eq F k x hx0 hx1)) $$ Hε
  iintro %⟨w, _⟩ ⟨%n, %rfl, %hmem, Hcn⟩
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp (ε₂ := BiiCredit F x n) (measurable_biiCredit F x n) ?hint) $$ Hcn
  case hint => exact le_rfl
  iintro %r ⟨%-, Hcr⟩
  twp_pure
  obtain rfl | rfl | rfl := hmem
  · twp_pures
    twp_value
    imodintro
    isimp only [BiiCredit, Nat.reduceEqDiff, reduceIte] at Hcr
    iframe Hcr
    itrivial
  · twp_pures
    rcases hb : ProbLangℝ.realLt x r with _ | _
    · twp_value
      imodintro
      isimp only [BiiCredit, of_decide_eq_false hb, Nat.reduceEqDiff, reduceIte] at Hcr
      iframe Hcr
      itrivial
    · twp_value
      imodintro
      isimp only [BiiCredit, of_decide_eq_true hb, Nat.reduceEqDiff, reduceIte] at Hcr
      iframe Hcr
      itrivial
  · twp_pures
    twp_value
    imodintro
    isimp only [BiiCredit, Nat.reduceEqDiff, reduceIte] at Hcr
    iframe Hcr
    itrivial

theorem twp_S_tail (E : CoPset) (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1) :
    ⊢ ∀ (N : ℕ) (y : ℝ), ⌜0 ≤ y⌝ -∗ ⌜y ≤ B⌝ -∗
      ↯ (SCreditV F k x y N) -∗
      tglWp E pl(&S #int (k : ℤ) #x #y #int (N : ℤ))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  have hkpos : (0 : ℝ) ≤ 1 / B := by positivity
  set kf : ℝ≥0 := ⟨1 / B, hkpos⟩
  have hk1 : 1 < kf := by
    have h : (1 : ℝ) < 1 / B := by rw [lt_div_iff₀ hB0]; linarith
    exact_mod_cast h
  iintro %N %y %hy0 %hyB Hε_spec
  iapply twp_err_pos solve_not_value
  iintro %ε_term %hε_pos Hε_term
  irevert %N %y %hy0 %hyB Hε_spec
  iapply ErrorCredit.Induction.simple (k := kf) hε_pos hk1 $$ [] Hε_term
  imodintro
  iintro ⟨IH, Hε_term⟩ %N %y %hy0 %hyB Hε_spec
  iterate 5 twp_pure
  twp_bind pl(urand)
  icombine Hε_spec Hε_term as Hε
  iapply (twp_urand_exp (ε₂ := SCreditAmp F k x N y ((kf : ℝ≥0∞) * ε_term))
    (measurable_sCreditAmp F k x N y _) ?hint) $$ Hε
  case hint =>
    have hy1 : y ≤ 1 := by linarith
    have hBkf : ENNReal.ofReal B * (↑kf * ε_term) = ε_term := by
      have hkf : (↑kf : ℝ≥0∞) = ENNReal.ofReal (1 / B) := by
        rw [← ENNReal.ofReal_coe_nnreal]; rfl
      rw [← mul_assoc, hkf,
          ← ENNReal.ofReal_mul hB0.le, mul_one_div, div_self (ne_of_gt hB0),
          ENNReal.ofReal_one, one_mul]
    calc ∫⁻ r, SCreditAmp F k x N y (↑kf * ε_term) r ∂(LawfulProbLangℝ.unifUnit (T := ℝ))
        ≤ SCreditV F k x y N + ENNReal.ofReal B * (↑kf * ε_term) :=
          SCreditAmp_lintegral_le F k x N y (↑kf * ε_term) hx0 hx1 hy0 hy1 B hyB
      _ = SCreditV F k x y N + ε_term := by rw [hBkf]
  iintro %z ⟨%hzm, Hcz⟩
  have hzr := mem_unifUnitSupport_real_le hzm
  twp_pures
  rcases hyz : ProbLangℝ.realLt y z with _ | _
  · isimp only [SCreditAmp, of_decide_eq_false hyz, reduceIte] at Hcz
    twp_pure
    twp_bind pl(&Bii #int (k : ℤ) #real x)
    iapply tglWp_wand
    isplitl [Hcz]
    · iapply (twp_Bii E (SbiiCredit F k x N z ((kf : ℝ≥0∞) * ε_term)) k x hx0 hx1) $$ Hcz
    iintro %⟨w, _⟩ ⟨%bii, %rfl, Hcbii⟩
    cases bii with
    | false =>
      isimp only [SbiiCredit, Bool.false_eq_true, reduceIte] at Hcbii
      ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split (GF := GF) $$ Hcbii
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&S #int (k : ℤ) #real x #z #int ((N + 1 : ℕ) : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      have hzB : z ≤ B := (not_lt.mp (of_decide_eq_false hyz)).trans hyB
      iapply IH $$ Hterm %(N + 1) %z %hzr.1 %hzB Hexp
    | true =>
      isimp only [SbiiCredit, Bool.false_eq_true, reduceIte] at Hcbii
      twp_pures
      twp_value
      imodintro
      iframe Hcbii
      itrivial
  · isimp only [SCreditAmp, of_decide_eq_true hyz, reduceIte] at Hcz
    twp_pures
    twp_value
    imodintro
    iframe Hcz
    itrivial

theorem twp_S (E : CoPset) (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ⊢ ↯ (SCreditV F k x y N) -∗
      tglWp E pl(&S #int (k : ℤ) #x #y #int (N : ℤ))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε_spec
  iterate 5 twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp (ε₂ := SCredit F k x N y) (measurable_sCreditAmp F k x N y 0)
    (le_of_eq (by rw [SCredit, SCreditAmp_lintegral_eq F k x N y 0 hx0 hx1 hy0 hy1, mul_zero, add_zero]))) $$ Hε_spec
  iintro %z ⟨%hzm, Hcz⟩
  have hz01 : 0 < z ∧ z < 1 := mem_unifUnitSupport_real.mp hzm
  twp_pures
  rcases hyz : ProbLangℝ.realLt y z with _ | _
  · isimp only [SCredit, SCreditAmp, of_decide_eq_false hyz, reduceIte] at Hcz
    twp_pure
    twp_bind pl(&Bii #int (k : ℤ) #real x)
    iapply tglWp_wand
    isplitl [Hcz]
    · iapply (twp_Bii E (SbiiCredit F k x N z 0) k x hx0 hx1) $$ Hcz
    iintro %⟨w, _⟩ ⟨%bii, %rfl, Hcbii⟩
    cases bii with
    | false =>
      isimp only [SbiiCredit, Bool.false_eq_true, reduceIte, add_zero] at Hcbii
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&S #int (k : ℤ) #real x #z #int ((N + 1 : ℕ) : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply twp_S_tail E F k x hx0 hx1 z hz01.1 hz01.2 $$ %(N + 1) %z %hz01.1.le %le_rfl Hcbii
    | true =>
      isimp only [SbiiCredit, Bool.false_eq_true, reduceIte] at Hcbii
      twp_pures
      twp_value
      imodintro
      iframe Hcbii
      itrivial
  · isimp only [SCredit, SCreditAmp, of_decide_eq_true hyz, reduceIte] at Hcz
    twp_pures
    twp_value
    imodintro
    iframe Hcz
    itrivial

theorem twp_S0 (E : CoPset) (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ⊢ ↯ (SCreditV F k x x 0) -∗
      tglWp E pl(&S0 #int (k : ℤ) #x)
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε
  twp_pure
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp (ε₂ := SCredit F k x 0 x) (measurable_sCreditAmp F k x 0 x 0)
    (le_of_eq (by rw [SCredit, SCreditAmp_lintegral_eq F k x 0 x 0 hx0 hx1 hx0 hx1, mul_zero, add_zero]))) $$ Hε
  iintro %z ⟨%hzm, Hcz⟩
  have hz01 : 0 < z ∧ z < 1 := mem_unifUnitSupport_real.mp hzm
  twp_pures
  rcases hyz : ProbLangℝ.realLt x z with _ | _
  · isimp only [SCredit, SCreditAmp, of_decide_eq_false hyz, reduceIte] at Hcz
    twp_pure
    twp_bind pl(&Bii #int (k : ℤ) #real x)
    iapply tglWp_wand
    isplitl [Hcz]
    · iapply (twp_Bii E (SbiiCredit F k x 0 z 0) k x hx0 hx1) $$ Hcz
    iintro %⟨w, _⟩ ⟨%bii, %rfl, Hcbii⟩
    cases bii with
    | false =>
      isimp only [SbiiCredit, Bool.false_eq_true, reduceIte, add_zero] at Hcbii
      twp_pure
      twp_bind pl(&S #int (k : ℤ) #real x #z #(1 : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply (twp_S E F k x z 1 hx0 hx1 hz01.1.le hz01.2.le) $$ Hcbii
    | true =>
      isimp only [SbiiCredit, Bool.false_eq_true, reduceIte] at Hcbii
      twp_pures
      twp_value
      imodintro
      iframe Hcbii
      itrivial
  · isimp only [SCredit, SCreditAmp, of_decide_eq_true hyz, reduceIte] at Hcz
    twp_pures
    twp_value
    imodintro
    iframe Hcz
    itrivial

theorem twp_B (E : CoPset) (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢ ↯ (BCreditV F k x) -∗
      tglWp E pl(&B #int (k : ℤ) #x)
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hε
  twp_pure
  twp_pure
  twp_bind pl(&S0 #int (k : ℤ) #real x)
  iapply tglWp_wand
  isplitl [Hε]
  · iapply (twp_S0 E (BS0Credit F) k x hx.1 hx.2)
    iapply (ErrorCredit.ext (BCreditV_S0_eq F k x hx.1 hx.2)) $$ Hε
  iintro %⟨w, _⟩ ⟨%n, %rfl, Hcn⟩
  twp_pures
  obtain hpar | hpar := Nat.mod_two_eq_zero_or_one n
  · rw [intOfNat_emod_two_eq_zero hpar]
    twp_value
    imodintro
    isimp only [BS0Credit, hpar, Nat.reduceEqDiff, reduceIte] at Hcn
    iframe Hcn
    itrivial
  · rw [intOfNat_emod_two_eq_one hpar]
    twp_value
    imodintro
    isimp only [BS0Credit, hpar, Nat.reduceEqDiff, reduceIte] at Hcn
    iframe Hcn
    itrivial

end specification

end
end Examples
end TotalEris
end ProbLang
