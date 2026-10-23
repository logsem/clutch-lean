module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Metrology.Code.Samplers
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Real decreasing trial — continuous-uniform sampler -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
local bi IProp GF

theorem intOfNat_emod_two_eq_zero {n : ℕ} (hn : n % 2 = 0) : Int.ofNat n % 2 = 0 := by
  simp only [Int.ofNat_eq_natCast]; omega

theorem intOfNat_emod_two_eq_one {n : ℕ} (hn : n % 2 = 1) : Int.ofNat n % 2 = 1 := by
  simp only [Int.ofNat_eq_natCast]; omega

theorem mem_unifUnitSupport_real_le {r : ℝ} (hr : r ∈ LawfulProbLangℝ.unifUnitSupport) :
    0 ≤ r ∧ r ≤ 1 :=
  ⟨(mem_unifUnitSupport_real.mp hr).1.le, (mem_unifUnitSupport_real.mp hr).2.le⟩

section distribution

def RealDecrTrialPMF₀ (x : ℝ) (n : ℕ) : ℝ≥0∞ :=
  .ofReal (x ^ n / n.factorial - x ^ (n + 1) / (n + 1).factorial)

def RealDecrTrialPMF (x : ℝ) (i n : ℕ) : ℝ≥0∞ :=
  if i ≤ n then RealDecrTrialPMF₀ x (n - i) else 0

theorem RealDecrTrialPMF_not_supp {x : ℝ} {i n : ℕ} (h : n < i) :
    RealDecrTrialPMF x i n = 0 := by
  simp only [RealDecrTrialPMF, ite_eq_right (Nat.not_le.mpr h)]

theorem RealDecrTrialPMF_supp {x : ℝ} {i n : ℕ} (h : i ≤ n) :
    RealDecrTrialPMF x i n = RealDecrTrialPMF₀ x (n - i) := by
  simp only [RealDecrTrialPMF, ite_eq_left h]

theorem RealDecrTrialPMF_base {x : ℝ} {n : ℕ} :
    RealDecrTrialPMF x 0 n = RealDecrTrialPMF₀ x n := by
  simp only [RealDecrTrialPMF, Nat.zero_le, ite_eq_left, Nat.sub_zero]

open MeasureTheory in
theorem RealDecrTrialPMF₀_real_integral (m : ℕ) (t : ℝ) :
    ∫ y in (0 : ℝ)..t, (y ^ m / (m.factorial : ℝ) - y ^ (m + 1) / ((m + 1).factorial : ℝ))
      = t ^ (m + 1) / ((m + 1).factorial : ℝ) - t ^ (m + 2) / ((m + 2).factorial : ℝ) := by
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_div, intervalIntegral.integral_div,
      integral_pow, integral_pow]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem RealDecrTrialPMF₀_real_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    0 ≤ x ^ n / (n.factorial : ℝ) - x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hfact : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hrw : x ^ (n + 1) / ((n + 1).factorial : ℝ)
      = (x ^ n / (n.factorial : ℝ)) * (x / ((n : ℝ) + 1)) := by
    rw [hfact, pow_succ]; field_simp
  rw [sub_nonneg, hrw]
  have hnn1 : 0 ≤ x ^ n / (n.factorial : ℝ) := by positivity
  have hyle : x / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  exact mul_le_of_le_one_right hnn1 hyle

theorem summable_pow_div_factorial_two_mul_add_two (x : ℝ) :
    Summable fun k : ℕ => x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ) :=
  (Real.summable_pow_div_factorial x).comp_injective fun i j h => by omega

theorem RealDecrTrialPMF₀_real_parity (x : ℝ) :
    (∑' k : ℕ, (x ^ (2 * k) / ((2 * k).factorial : ℝ)
        - x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) = Real.exp (-x))
    ∧ (∑' k : ℕ, (x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)
        - x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)) = 1 - Real.exp (-x)) := by
  have hCe := x.hasSum_cosh.summable
  have hCo := x.hasSum_sinh.summable
  refine ⟨?_, ?_⟩
  · rw [hCe.tsum_sub hCo, ← Real.cosh_eq_tsum, ← Real.sinh_eq_tsum, Real.cosh_sub_sinh]
  · have hC2 : (∑' k, x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)) = Real.cosh x - 1 := by
      have hsplit := hCe.tsum_eq_zero_add
      simp only [Nat.mul_zero, Nat.factorial_zero, pow_zero] at hsplit
      have hreindex : (∑' n, x ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ))
          = ∑' k, x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ) :=
        tsum_congr fun k => by rw [Nat.mul_succ]
      rw [Real.cosh_eq_tsum]
      linarith
    rw [hCo.tsum_sub (summable_pow_div_factorial_two_mul_add_two x), ← Real.sinh_eq_tsum, hC2]
    linarith [Real.cosh_sub_sinh x]

open MeasureTheory in
theorem RealDecrTrialPMF₀_setLIntegral {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (m : ℕ) :
    ∫⁻ y in Set.Icc 0 x, RealDecrTrialPMF₀ y m ∂volume = RealDecrTrialPMF₀ x (m + 1) := by
  have hcont : Continuous fun y : ℝ =>
      y ^ m / (m.factorial : ℝ) - y ^ (m + 1) / ((m + 1).factorial : ℝ) := by fun_prop
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc 0 x)]
      fun y : ℝ => y ^ m / (m.factorial : ℝ) - y ^ (m + 1) / ((m + 1).factorial : ℝ) := by
    refine ae_restrict_of_forall_mem measurableSet_Icc fun y hy => ?_
    exact RealDecrTrialPMF₀_real_nonneg hy.1 (hy.2.trans hx.2) m
  simp only [RealDecrTrialPMF₀]
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc) hnn,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.1,
      RealDecrTrialPMF₀_real_integral]

end distribution

section creditExpectation

def RealDecrTrialCreditV (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, RealDecrTrialPMF x i n * F n

theorem RealDecrTrialCreditV_reindex (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) :
    RealDecrTrialCreditV F i x = ∑' m : ℕ, RealDecrTrialPMF₀ x m * F (i + m) := by
  unfold RealDecrTrialCreditV
  rw [← (add_right_injective i).tsum_eq ?supp]
  · exact tsum_congr fun m => by
      rw [RealDecrTrialPMF_supp (Nat.le_add_right i m), Nat.add_sub_cancel_left]
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    have hin : i ≤ n := by
      by_contra h
      exact hn (by rw [RealDecrTrialPMF_not_supp (by omega), zero_mul])
    exact ⟨n - i, Nat.add_sub_cancel' hin⟩

theorem RealDecrTrialCreditV_parity (A B : ℝ≥0∞) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    RealDecrTrialCreditV (fun n => if n % 2 = 0 then A else B) 0 x
      = ENNReal.ofReal (Real.exp (-x)) * A + ENNReal.ofReal (1 - Real.exp (-x)) * B := by
  obtain ⟨hpe, hpo⟩ := RealDecrTrialPMF₀_real_parity x
  have hEven : (∑' k, RealDecrTrialPMF₀ x (2 * k)) = ENNReal.ofReal (Real.exp (-x)) := by
    rw [← hpe,
      ENNReal.ofReal_tsum_of_nonneg (fun k => RealDecrTrialPMF₀_real_nonneg hx0 hx1 (2 * k))
        (x.hasSum_cosh.summable.sub x.hasSum_sinh.summable)]
    rfl
  have hOdd : (∑' k, RealDecrTrialPMF₀ x (2 * k + 1)) = ENNReal.ofReal (1 - Real.exp (-x)) := by
    rw [← hpo,
      ENNReal.ofReal_tsum_of_nonneg (fun k => RealDecrTrialPMF₀_real_nonneg hx0 hx1 (2 * k + 1))
        (x.hasSum_sinh.summable.sub (summable_pow_div_factorial_two_mul_add_two x))]
    rfl
  unfold RealDecrTrialCreditV
  simp only [RealDecrTrialPMF_base]
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  congr 1
  · have heq : ∀ k, RealDecrTrialPMF₀ x (2 * k) * (if (2 * k) % 2 = 0 then A else B)
        = RealDecrTrialPMF₀ x (2 * k) * A := fun k => by rw [ite_eq_left (by omega : (2 * k) % 2 = 0)]
    rw [tsum_congr heq, ENNReal.tsum_mul_right, hEven]
  · have heq : ∀ k, RealDecrTrialPMF₀ x (2 * k + 1) * (if (2 * k + 1) % 2 = 0 then A else B)
        = RealDecrTrialPMF₀ x (2 * k + 1) * B := fun k => by
      rw [ite_eq_right (by omega : ¬ (2 * k + 1) % 2 = 0)]
    rw [tsum_congr heq, ENNReal.tsum_mul_right, hOdd]

end creditExpectation

section creditKernel

def RealDecrTrialCredit (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) : ℝ → ℝ≥0∞ := fun y =>
  (if y ≤ x then RealDecrTrialCreditV F (i + 1) y else 0) +
  (if x ≤ y then F i else 0)

def RealDecrTrialCreditAmp (F : ℕ → ℝ≥0∞) (N : ℕ) (x : ℝ) (c : ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun y => RealDecrTrialCredit F N x y + (if y < x then c else 0)

end creditKernel

section measurability

theorem measurable_realDecrTrialPMF₀ (n : ℕ) :
    Measurable (fun x : ℝ => RealDecrTrialPMF₀ x n) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

theorem measurable_realDecrTrialPMF (i n : ℕ) :
    Measurable (fun x : ℝ => RealDecrTrialPMF x i n) := by
  unfold RealDecrTrialPMF
  by_cases h : i ≤ n
  · simpa only [h, ite_true] using measurable_realDecrTrialPMF₀ (n - i)
  · simpa only [h, ite_false] using measurable_const

theorem measurable_realDecrTrialCreditV (F : ℕ → ℝ≥0∞) (i : ℕ) :
    Measurable (fun x : ℝ => RealDecrTrialCreditV F i x) :=
  Measurable.tsum fun n => (measurable_realDecrTrialPMF i n).mul_const (F n)

theorem measurable_realDecrTrialCredit (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) :
    Measurable (RealDecrTrialCredit F i x) := by
  unfold RealDecrTrialCredit
  refine Measurable.add ?_ ?_
  · exact Measurable.ite measurableSet_Iic (measurable_realDecrTrialCreditV F (i + 1))
      measurable_const
  · exact Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem measurable_realDecrTrialCreditAmp (F : ℕ → ℝ≥0∞) (N : ℕ) (x : ℝ) (c : ℝ≥0∞) :
    Measurable (RealDecrTrialCreditAmp F N x c) :=
  (measurable_realDecrTrialCredit F N x).add
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

end measurability

section lintegral

open MeasureTheory in
theorem lintegral_ofReal_Icc {t : ℝ} (ht : 0 ≤ t) {g : ℝ → ℝ} (hg : Continuous g)
    (hgn : ∀ r ∈ Set.Icc (0 : ℝ) t, 0 ≤ g r) :
    ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (g r) ∂volume
      = ENNReal.ofReal (∫ r in (0 : ℝ)..t, g r) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hg.integrableOn_Icc
        (ae_restrict_of_forall_mem measurableSet_Icc hgn),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]

end lintegral

section indicator

theorem indicator_Iic_eq (x : ℝ) (f : ℝ → ℝ≥0∞) :
    (Set.Iic x).indicator f = fun y => if y ≤ x then f y else 0 := by
  ext y; simp only [Set.indicator_apply, Set.mem_Iic]

theorem indicator_Ici_eq (x : ℝ) (f : ℝ → ℝ≥0∞) :
    (Set.Ici x).indicator f = fun y => if x ≤ y then f y else 0 := by
  ext y; simp only [Set.indicator_apply, Set.mem_Ici]

theorem indicator_Iio_eq (x : ℝ) (f : ℝ → ℝ≥0∞) :
    (Set.Iio x).indicator f = fun y => if y < x then f y else 0 := by
  ext y; simp only [Set.indicator_apply, Set.mem_Iio]

end indicator

section conservation

open MeasureTheory in
theorem RealDecrTrialCredit_lintegral {F : ℕ → ℝ≥0∞} {N : ℕ} {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) :
    ∫⁻ y, RealDecrTrialCredit F N x y ∂(LawfulProbLangℝ.unifUnit) =
      RealDecrTrialCreditV F N x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hset2 : Set.Ici x ∩ Set.Icc (0 : ℝ) 1 = Set.Icc x 1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hx0.trans h1, h2⟩⟩
  have hset1 : Set.Iic x ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 x := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hx1⟩⟩
  show ∫⁻ y, RealDecrTrialCredit F N x y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  simp only [RealDecrTrialCredit]
  rw [lintegral_add_left (Measurable.ite measurableSet_Iic
      (measurable_realDecrTrialCreditV F (N + 1)) measurable_const)]
  have hpart2 : (∫⁻ y, (if x ≤ y then F N else 0) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = F N * RealDecrTrialPMF₀ x 0 := by
    rw [← indicator_Ici_eq, lintegral_indicator measurableSet_Ici, setLIntegral_const,
      Measure.restrict_apply measurableSet_Ici, hset2, Real.volume_Icc]
    rw [RealDecrTrialPMF₀]; norm_num
  have hpart1 : (∫⁻ y, (if y ≤ x then RealDecrTrialCreditV F (N + 1) y else 0)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∑' m : ℕ, RealDecrTrialPMF₀ x (m + 1) * F (N + 1 + m) := by
    rw [← indicator_Iic_eq, lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, hset1]
    simp only [RealDecrTrialCreditV_reindex]
    rw [lintegral_tsum fun m =>
        ((measurable_realDecrTrialPMF₀ m).mul_const (F (N + 1 + m))).aemeasurable]
    exact tsum_congr fun m => by
      rw [lintegral_mul_const _ (measurable_realDecrTrialPMF₀ m),
        RealDecrTrialPMF₀_setLIntegral ⟨hx0, hx1⟩ m]
  rw [hpart1, hpart2, RealDecrTrialCreditV_reindex]
  have hsplit : (∑' m, RealDecrTrialPMF₀ x m * F (N + m))
      = RealDecrTrialPMF₀ x 0 * F N + ∑' m, RealDecrTrialPMF₀ x (m + 1) * F (N + (m + 1)) := by
    rw [tsum_eq_zero_add' ENNReal.summable, Nat.add_zero]
  rw [hsplit]
  have hkey : (∑' m, RealDecrTrialPMF₀ x (m + 1) * F (N + 1 + m))
      = ∑' m, RealDecrTrialPMF₀ x (m + 1) * F (N + (m + 1)) :=
    tsum_congr fun m => by rw [← Nat.add_assoc, Nat.add_right_comm]
  rw [hkey]
  ring

open MeasureTheory in
theorem RealDecrTrialCreditAmp_lintegral {F : ℕ → ℝ≥0∞} {N : ℕ} {x : ℝ} {c : ℝ≥0∞}
    (hx : 0 ≤ x ∧ x ≤ 1) :
    ∫⁻ y, RealDecrTrialCreditAmp F N x c y ∂(LawfulProbLangℝ.unifUnit) =
      RealDecrTrialCreditV F N x + c * ENNReal.ofReal x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hset : Set.Iio x ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 x := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.le.trans hx1⟩⟩
  show ∫⁻ y, RealDecrTrialCreditAmp F N x c y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  simp only [RealDecrTrialCreditAmp]
  rw [lintegral_add_left (measurable_realDecrTrialCredit F N x)]
  congr 1
  · exact RealDecrTrialCredit_lintegral ⟨hx0, hx1⟩
  · rw [← indicator_Iio_eq, lintegral_indicator measurableSet_Iio, setLIntegral_const,
        Measure.restrict_apply measurableSet_Iio, hset, Real.volume_Ico, sub_zero]

end conservation

section specification

theorem twp_DecrTrial_tail (E : CoPset) (F : ℕ → ℝ≥0∞) (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1) :
    ⊢ ∀ (N : ℕ) (x : ℝ), ⌜0 ≤ x⌝ -∗ ⌜x ≤ B⌝ -∗
      ↯ (RealDecrTrialCreditV F N x) -∗
      tglWp E pl(&DecrTrial #int (N : ℤ) #real x)
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  set k : ℝ≥0 := ⟨1 / B, by positivity⟩
  have hk1 : 1 < k := by
    have h : (1 : ℝ) < 1 / B := by rw [lt_div_iff₀ hB0]; linarith
    exact_mod_cast h
  iintro %N %x %hx0 %hxB Hε_spec
  iapply twp_err_pos solve_not_value
  iintro %ε_term %hε_pos Hε_term
  irevert %N %x %hx0 %hxB Hε_spec
  iapply ErrorCredit.Induction.simple hε_pos hk1 $$ [] Hε_term
  iintro !> ⟨IH, Hε_term⟩ %N %x %hx0 %hxB Hε_spec
  iterate 3 twp_pure
  twp_bind pl(urand)
  icombine Hε_spec Hε_term as Hε
  iapply (twp_urand_exp
    (ε₂ := RealDecrTrialCreditAmp F N x ((k : ℝ≥0∞) * ε_term)) ?hmeas ?hint) $$ Hε
  case hmeas => exact measurable_realDecrTrialCreditAmp F N x _
  case hint =>
    rw [RealDecrTrialCreditAmp_lintegral ⟨hx0, hxB.trans hB1.le⟩]
    have hkx : (↑k : ℝ≥0∞) * ENNReal.ofReal x ≤ 1 := by
      have hkcast : (↑k : ℝ≥0∞) = ENNReal.ofReal (1 / B) := by
        rw [← ENNReal.ofReal_coe_nnreal]; rfl
      rw [hkcast, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_one,
        div_mul_eq_mul_div, one_mul, div_le_one hB0]
      exact hxB
    gcongr
    calc (↑k * ε_term) * ENNReal.ofReal x = ε_term * ((↑k : ℝ≥0∞) * ENNReal.ofReal x) := by ring
      _ ≤ ε_term := by simpa using mul_le_mul_right hkx ε_term
  iintro %y ⟨%hym, Hcy⟩
  have hy := mem_unifUnitSupport_real_le hym
  twp_pures
  rcases hb : ProbLangℝ.realLt y x with _ | _
  · twp_pures
    twp_value
    imodintro
    iexists N
    have hle : F N ≤ RealDecrTrialCreditAmp F N x ((k : ℝ≥0∞) * ε_term) y := by
      have hnlt : ¬ y < x := of_decide_eq_false hb
      have hxy : x ≤ y := not_lt.mp hnlt
      unfold RealDecrTrialCreditAmp RealDecrTrialCredit
      rw [ite_eq_left hxy, ite_eq_right hnlt, add_zero]
      exact le_add_self
    isplitr [Hcy]
    · itrivial
    · iapply (ErrorCredit.weaken hle) $$ Hcy
  · have hlt : y < x := of_decide_eq_true hb
    twp_pure
    have heq : RealDecrTrialCreditV F (N + 1) y + (k : ℝ≥0∞) * ε_term
        = RealDecrTrialCreditAmp F N x ((k : ℝ≥0∞) * ε_term) y := by
      unfold RealDecrTrialCreditAmp RealDecrTrialCredit
      rw [ite_eq_left hlt.le, ite_eq_right (not_le.mpr hlt), ite_eq_left hlt, add_zero]
    ihave Hcy' := ErrorCredit.ext heq.symm $$ Hcy
    ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split $$ Hcy'
    twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&DecrTrial #int ((N + 1 : ℕ) : ℤ) #real y)
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm
    · ipureintro; exact hy.1
    · ipureintro; linarith [hlt.le, hxB]
    · iexact Hexp

theorem twp_DecrTrial (E : CoPset) (F : ℕ → ℝ≥0∞) (N : ℕ) (x : ℝ) (Hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢ ↯ (RealDecrTrialCreditV F N x) -∗
      tglWp E pl(&DecrTrial #int (N : ℤ) #real x)
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε_spec
  iterate 3 twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp ?hmeas ?hint) $$ Hε_spec
  case hmeas => exact measurable_realDecrTrialCredit F N x
  case hint => exact le_of_eq (RealDecrTrialCredit_lintegral Hx)
  iintro %y ⟨%hym, Hcy⟩
  have hy : 0 < y ∧ y < 1 := mem_unifUnitSupport_real.mp hym
  twp_pures
  rcases hb : ProbLangℝ.realLt y x with _ | _
  · twp_pures
    twp_value
    imodintro
    iexists N
    have hle : F N ≤ RealDecrTrialCredit F N x y := by
      have hxy : x ≤ y := not_lt.mp (of_decide_eq_false hb)
      unfold RealDecrTrialCredit
      rw [ite_eq_left hxy]
      exact le_add_self
    isplitr [Hcy]
    · itrivial
    · iapply (ErrorCredit.weaken hle) $$ Hcy
  · have hlt : y < x := of_decide_eq_true hb
    twp_pure
    have heq : RealDecrTrialCreditV F (N + 1) y = RealDecrTrialCredit F N x y := by
      unfold RealDecrTrialCredit
      rw [ite_eq_left hlt.le, ite_eq_right (not_le.mpr hlt), add_zero]
    ihave Hcy' := ErrorCredit.ext heq.symm $$ Hcy
    twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&DecrTrial #int ((N + 1 : ℕ) : ℤ) #real y)
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (twp_DecrTrial_tail E F y hy.1 (hlt.trans_le Hx.2))
    · ipureintro; exact hy.1.le
    · ipureintro; exact le_rfl
    · iexact Hcy'

end specification

end
end Examples
end TotalEris
end ProbLang
