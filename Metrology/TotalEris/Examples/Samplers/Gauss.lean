module

public import Metrology.TotalEris
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.HalfBernNegExp
public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric
public import Metrology.TotalEris.Examples.Samplers.BernIter
public import Metrology.TotalEris.Examples.Samplers.Selector

@[expose] public section

/-! # Discrete/continuous Gaussian sampler -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]

section program

def IterN (k : ℕ) : ℕ := k * (k - 1)

end program

section distribution

open MeasureTheory

def Norm1 : ℝ := ∑' k : ℕ, Real.exp (-(k : ℝ) ^ 2 / 2)

def G1PMF (k : ℕ) : ℝ≥0∞ := .ofReal (Real.exp (-(k : ℝ) ^ 2 / 2) / Norm1)

def Norm2 : ℝ := ∫ x in (0 : ℝ)..1, ∑' k : ℕ, Real.exp (-((x + k) ^ 2) / 2)

def G2pdf (k : ℕ) (x : ℝ) : ℝ≥0∞ := .ofReal (Real.exp (-((x + k) ^ 2) / 2) / Norm2)

end distribution

section creditExpectation

open MeasureTheory

def G1CreditV (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∑' k : ℕ, G1PMF k * F k

def G2CreditV (F : ℕ → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' k : ℕ, ∫⁻ x, G2pdf k x * F k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))

end creditExpectation

section creditKernel

open MeasureTheory

abbrev BNEHalfVal : Val ℝ := ⟨BNEHalf, IsVal.lam (by is_lc), by is_lc⟩

noncomputable def γBNE : ↑unitInterval :=
  ⟨Real.exp (-1 / 2), (Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by norm_num)⟩

theorem γBNE_coe : (γBNE : ℝ) = Real.exp (-1 / 2) := rfl

theorem γBNE_pos : (0 : ℝ) < (γBNE : ℝ) := Real.exp_pos _

theorem γBNE_nonneg : (0 : ℝ) ≤ (γBNE : ℝ) := γBNE_pos.le

theorem γBNE_lt_one : (γBNE : ℝ) < 1 := by
  rw [γBNE_coe]; exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem γBNE_credit_eq (F : Bool → ℝ≥0∞) :
    ENNReal.ofReal (γBNE : ℝ) * F true + (1 - ENNReal.ofReal (γBNE : ℝ)) * F false
      = BNEHalfCreditV F := by
  have ht : BNEHalfPMF true = ENNReal.ofReal (Real.exp (-1 / 2)) := rfl
  have hf : BNEHalfPMF false = ENNReal.ofReal (1 - Real.exp (-1 / 2)) := rfl
  simp only [BNEHalfCreditV, ht, hf, γBNE_coe, ENNReal.one_sub_ofReal (Real.exp_pos (-1 / 2)).le]
  ring

theorem abstractBernoulli_BNEHalf : AbstractBernoulli (GF := GF) BNEHalfVal γBNE where
  spec := by
    intro E
    iintro %F Hε
    iapply twp_BNEHalf E F
    iapply ErrorCredit.ext (γBNE_credit_eq F) $$ Hε

theorem abstractBernoulliI_BNEHalf (I : IProp GF) :
    AbstractBernoulliI (hlc := hlc) (GF := GF) BNEHalfVal γBNE I :=
  abstractBernoulli_BNEHalf.toAbstractBernoulliI I

def G1IterContAmp (F : ℕ → ℝ≥0∞) (c : ℝ≥0∞) (k : ℕ) : Bool → ℝ≥0∞ :=
  fun b => if b then F k else G1CreditV F + c

def G1GeometricCredit (F : ℕ → ℝ≥0∞) (c : ℝ≥0∞) : ℤ → ℝ≥0∞ :=
  fun z => IterCreditV (G1IterContAmp F c z.toNat) γBNE (IterN z.toNat)

noncomputable def γBkx (k : ℕ) (x : ℝ) : ↑unitInterval :=
  ⟨Real.exp (min 0 (-x * (2 * k + x) / (2 * k + 2))), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (min_le_left _ _)⟩

abbrev BkxVal (k : ℕ) (x : ℝ) : Val ℝ :=
  ⟨pl% (fun _u, &B #(.int (k : ℤ)) #(.real x)), IsVal.lam (by is_lc), by is_lc⟩

theorem γBkx_coe (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (γBkx k x : ℝ) = Real.exp (-x * (2 * k + x) / (2 * k + 2)) := by
  have harg : -x * (2 * (k : ℝ) + x) / (2 * k + 2) ≤ 0 := by
    rw [neg_mul, neg_div]
    exact neg_nonpos.mpr
      (div_nonneg (mul_nonneg hx (by linarith [Nat.cast_nonneg (α := ℝ) k])) (by positivity))
  show Real.exp (min 0 (-x * (2 * (k : ℝ) + x) / (2 * k + 2)))
      = Real.exp (-x * (2 * k + x) / (2 * k + 2))
  rw [min_eq_right harg]

theorem γBkx_credit_eq (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal (γBkx k x : ℝ) * F true + (1 - ENNReal.ofReal (γBkx k x : ℝ)) * F false
      = BCreditV F k x := by
  rw [γBkx_coe k hx]; rfl

theorem abstractBernoulli_Bkx (k : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    AbstractBernoulli (GF := GF) (BkxVal k x) (γBkx k x) where
  spec := by
    intro E
    iintro %F Hε
    twp_pure
    have hβ :
        (Exp.openRec 0 pl(#(.unit)) (Exp.closeRec 0 (Var.internal 0) B) : Exp ℝ) = B := rfl
    rw [hβ]
    iapply twp_B E F k x hx
    iapply ErrorCredit.ext (γBkx_credit_eq F k x hx.1) $$ Hε

theorem abstractBernoulliI_Bkx (k : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (I : IProp GF) :
    AbstractBernoulliI (hlc := hlc) (GF := GF) (BkxVal k x) (γBkx k x) I :=
  (abstractBernoulli_Bkx k x hx).toAbstractBernoulliI I

def G2IterContAmp (F : ℕ → ℝ → ℝ≥0∞) (c : ℝ≥0∞) (k : ℕ) (x : ℝ) : Bool → ℝ≥0∞ :=
  fun b => if b then F k x else G2CreditV F + c

def G2CreditAmp (F : ℕ → ℝ → ℝ≥0∞) (c : ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  IterCreditV (G2IterContAmp F c k x) (γBkx k x) (k + 1)

def G2G1Credit (F : ℕ → ℝ → ℝ≥0∞) (c : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, G2CreditAmp F c k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))

def G2p (k : ℕ) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((γBkx k x : ℝ) ^ (k + 1))

end creditKernel

section measurability

open MeasureTheory

theorem measurable_g2p (k : ℕ) : Measurable (G2p k) :=
  ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (by fun_prop)).pow_const (k + 1))

theorem measurable_g2CreditAmp (F : ℕ → ℝ → ℝ≥0∞) (hF : ∀ a, Measurable (F a))
    (c : ℝ≥0∞) (k : ℕ) :
    Measurable (G2CreditAmp F c k) := by
  show Measurable (fun x : ℝ => ENNReal.ofReal ((γBkx k x : ℝ) ^ (k + 1)) * F k x
      + (1 - ENNReal.ofReal ((γBkx k x : ℝ) ^ (k + 1))) * (G2CreditV F + c))
  exact ((measurable_g2p k).mul (hF k)).add (((measurable_g2p k).const_sub 1).mul measurable_const)

end measurability

section unifUnit

open MeasureTheory

theorem unifUnit_univ : (LawfulProbLangℝ.unifUnit (T := ℝ)) Set.univ = 1 := by
  show (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1
  rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num

theorem unifUnit_lintegral_one :
    ∫⁻ _x : ℝ, (1 : ℝ≥0∞) ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) = 1 := by
  rw [lintegral_one, unifUnit_univ]

end unifUnit

section bounds

open MeasureTheory

theorem G2p_le_one (k : ℕ) (x : ℝ) : G2p k x ≤ 1 := by
  rw [G2p, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (pow_le_one₀ (γBkx k x).2.1 (γBkx k x).2.2)

theorem G2G1Credit_le (F : ℕ → ℝ → ℝ≥0∞) {M : ℝ≥0∞}
    (Hbd : ∀ x k, 0 ≤ x → x ≤ 1 → F k x ≤ M) (c : ℝ≥0∞) (n : ℕ) :
    G2G1Credit F c n ≤ M + G2CreditV F + c := by
  rw [G2G1Credit]
  calc ∫⁻ x, G2CreditAmp F c n x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))
      ≤ ∫⁻ _x, (M + (G2CreditV F + c)) ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have ht : G2IterContAmp F c n x true = F n x := by simp [G2IterContAmp]
        have hf : G2IterContAmp F c n x false = G2CreditV F + c := by simp [G2IterContAmp]
        rw [G2CreditAmp, IterCreditV, ht, hf]
        refine add_le_add ?_ ?_
        · exact (mul_le_mul' (G2p_le_one n x) (Hbd x n hx.1 hx.2)).trans (one_mul M).le
        · exact (mul_le_mul' tsub_le_self le_rfl).trans (one_mul _).le
    _ = M + (G2CreditV F + c) := by rw [lintegral_const, unifUnit_univ, mul_one]
    _ = M + G2CreditV F + c := (add_assoc _ _ _).symm

end bounds

section conservation

open MeasureTheory

theorem normTerm_le_geometric (k : ℕ) :
    Real.exp (-(k : ℝ) ^ 2 / 2) ≤ Real.exp (-1 / 2) ^ k := by
  rw [← Real.exp_nat_mul]
  have hnat : (k : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) k
  exact Real.exp_le_exp.mpr (by linarith)

theorem exp_neg_half_lt_one : Real.exp (-1 / 2) < 1 := γBNE_lt_one

theorem summable_geometric_exp_neg_half : Summable fun k : ℕ => Real.exp (-1 / 2) ^ k :=
  summable_geometric_of_lt_one (Real.exp_pos _).le exp_neg_half_lt_one

theorem summable_normTerm : Summable (fun k : ℕ => Real.exp (-(k : ℝ) ^ 2 / 2)) :=
  Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) normTerm_le_geometric
    summable_geometric_exp_neg_half

theorem Norm1_pos : 0 < Norm1 :=
  (Real.exp_pos (-((0 : ℕ) : ℝ) ^ 2 / 2)).trans_le
    (summable_normTerm.le_tsum 0 fun _ _ => (Real.exp_pos _).le)

theorem Norm1_bound : Norm1 < (1 - Real.exp (-1 / 2))⁻¹ := by
  rw [Norm1, ← tsum_geometric_of_lt_one (Real.exp_pos _).le exp_neg_half_lt_one]
  refine Summable.tsum_lt_tsum_of_nonneg (i := 2) (fun _ => (Real.exp_pos _).le)
    normTerm_le_geometric ?_ summable_geometric_exp_neg_half
  show Real.exp (-((2 : ℕ) : ℝ) ^ 2 / 2) < Real.exp (-1 / 2) ^ 2
  rw [← Real.exp_nat_mul]
  exact Real.exp_lt_exp.mpr (by norm_num)

theorem Norm1_reject_lt_one : (1 - (γBNE : ℝ)) * Norm1 < 1 := by
  rw [γBNE_coe]
  have h1γ : (0 : ℝ) < 1 - Real.exp (-1 / 2) := by linarith [exp_neg_half_lt_one]
  calc (1 - Real.exp (-1 / 2)) * Norm1
      < (1 - Real.exp (-1 / 2)) * (1 - Real.exp (-1 / 2))⁻¹ :=
        mul_lt_mul_of_pos_left Norm1_bound h1γ
    _ = 1 := mul_inv_cancel₀ h1γ.ne'

theorem one_lt_one_div_one_sub {r : ℝ} (h0 : 0 < r) (h1 : r < 1) : 1 < 1 / (1 - r) := by
  rw [one_lt_div (by linarith)]
  linarith

noncomputable def G1Factor : ℝ≥0 :=
  ⟨1 / (1 - (1 - (γBNE : ℝ)) * Norm1),
    div_nonneg zero_le_one (by linarith [Norm1_reject_lt_one])⟩

theorem one_lt_G1Factor : 1 < G1Factor := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_one]
  show (1 : ℝ) < 1 / (1 - (1 - (γBNE : ℝ)) * Norm1)
  exact one_lt_one_div_one_sub (mul_pos (by linarith [γBNE_lt_one]) Norm1_pos)
    Norm1_reject_lt_one

theorem geometricPMF_γBNE (k : ℕ) :
    GeometricPMF γBNE k = ENNReal.ofReal ((γBNE : ℝ) ^ k * (1 - γBNE)) := rfl

theorem IterN_add_self (k : ℕ) : IterN k + k = k ^ 2 := by
  unfold IterN
  cases k with
  | zero => rfl
  | succ n => rw [Nat.succ_sub_one]; ring

theorem IterN_toNat_cast {z : ℤ} (hz : 0 ≤ z) : z * (z - 1) = ((IterN z.toNat : ℕ) : ℤ) := by
  rw [IterN]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = (k : ℤ) := ⟨z.toNat, (Int.toNat_of_nonneg hz).symm⟩
  simp only [Int.toNat_natCast]
  cases k with
  | zero => simp
  | succ k => push_cast; ring

theorem γBNE_pow_sq (k : ℕ) : (γBNE : ℝ) ^ k ^ 2 = Real.exp (-(k : ℝ) ^ 2 / 2) := by
  rw [γBNE_coe, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem geometricPMF_tsum : ∑' k : ℕ, GeometricPMF γBNE k = 1 := by
  have hγ1 : (γBNE : ℝ) < 1 := γBNE_lt_one
  rw [tsum_congr geometricPMF_γBNE,
      ← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (pow_nonneg γBNE_nonneg k) (by linarith))
        ((summable_geometric_of_lt_one γBNE_nonneg hγ1).mul_right _),
      tsum_mul_right, tsum_geometric_of_lt_one γBNE_nonneg hγ1,
      inv_mul_cancel₀ (sub_pos.mpr hγ1).ne', ENNReal.ofReal_one]

theorem geom_iterN_tsum :
    ∑' k : ℕ, GeometricPMF γBNE k * ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)
      = ENNReal.ofReal ((1 - (γBNE : ℝ)) * Norm1) := by
  have hγ1 : (γBNE : ℝ) < 1 := γBNE_lt_one
  have hterm : ∀ k : ℕ, GeometricPMF γBNE k * ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)
      = ENNReal.ofReal ((1 - (γBNE : ℝ)) * Real.exp (-(k : ℝ) ^ 2 / 2)) := fun k => by
    rw [geometricPMF_γBNE, ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg γBNE.2.1 k) (by linarith))]
    congr 1
    have hregroup : (γBNE : ℝ) ^ k * (1 - (γBNE : ℝ)) * (γBNE : ℝ) ^ IterN k
        = (1 - (γBNE : ℝ)) * (γBNE : ℝ) ^ (IterN k + k) := by rw [pow_add]; ring
    rw [hregroup, IterN_add_self, γBNE_pow_sq]
  rw [tsum_congr hterm,
      ← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by linarith) (Real.exp_pos _).le)
        (summable_normTerm.mul_left _),
      tsum_mul_left]
  rfl

theorem Norm2_eq_tsum :
    Norm2 = ∑' k : ℕ, ∫ x in (0 : ℝ)..1, Real.exp (-((x + (k : ℝ)) ^ 2) / 2) := by
  have hpk : ∀ k : ℕ, (∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖Real.exp (-((x + (k : ℝ)) ^ 2) / 2)‖ₑ ∂volume)
      ≤ ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / 2)) := by
    intro k
    calc ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖Real.exp (-((x + (k : ℝ)) ^ 2) / 2)‖ₑ ∂volume
        ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / 2)) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          have hkx : (0 : ℝ) ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx.1.le
          rw [← ofReal_norm, Real.norm_of_nonneg (Real.exp_pos _).le]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [hx.1, hkx]))
      _ = ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / 2)) := by
          rw [setLIntegral_const, Real.volume_Ioc]; norm_num
  have hbound : (∑' k : ℕ, ∫⁻ x in Set.Ioc (0 : ℝ) 1,
      ‖Real.exp (-((x + (k : ℝ)) ^ 2) / 2)‖ₑ ∂volume) ≠ (⊤ : ℝ≥0∞) := by
    rw [← lt_top_iff_ne_top]
    calc (∑' k : ℕ, ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖Real.exp (-((x + (k : ℝ)) ^ 2) / 2)‖ₑ ∂volume)
        ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / 2)) := ENNReal.tsum_le_tsum hpk
      _ = ENNReal.ofReal Norm1 := by
          rw [Norm1, ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) summable_normTerm]
      _ < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top
  rw [Norm2, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    MeasureTheory.integral_tsum (fun k => (Continuous.aestronglyMeasurable (by fun_prop))) hbound]
  exact tsum_congr fun k => (intervalIntegral.integral_of_le (by norm_num)).symm

theorem Norm2_summand_le (k : ℕ) :
    (∫ x in (0 : ℝ)..1, Real.exp (-((x + (k : ℝ)) ^ 2) / 2)) ≤ Real.exp (-(k : ℝ) ^ 2 / 2) := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun x => Real.exp (-((x + (k : ℝ)) ^ 2) / 2))
    (g := fun _ => Real.exp (-(k : ℝ) ^ 2 / 2))
    (Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1)
    (intervalIntegrable_const)
    (fun x hx => Real.exp_le_exp.mpr (by
      have hkx : (0 : ℝ) ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx.1
      nlinarith [hx.1, hkx]))
  rwa [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h

theorem Norm2_summand_summable :
    Summable (fun k : ℕ => ∫ x in (0 : ℝ)..1, Real.exp (-((x + (k : ℝ)) ^ 2) / 2)) :=
  Summable.of_nonneg_of_le (fun k => intervalIntegral.integral_nonneg (by norm_num)
    (fun x _ => (Real.exp_pos _).le)) Norm2_summand_le summable_normTerm

theorem Norm2_pos : 0 < Norm2 := by
  rw [Norm2_eq_tsum]
  refine lt_of_lt_of_le ?_ (Norm2_summand_summable.le_tsum 0
    (fun b _ => intervalIntegral.integral_nonneg (by norm_num) (fun x _ => (Real.exp_pos _).le)))
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (Continuous.intervalIntegrable (by fun_prop) _ _) (fun x _ => Real.exp_pos _) (by norm_num)

theorem Norm2_lt_Norm1 : Norm2 < Norm1 := by
  rw [Norm2_eq_tsum, Norm1]
  refine Norm2_summand_summable.tsum_lt_tsum (i := 0) Norm2_summand_le ?_ summable_normTerm
  simp only [Nat.cast_zero, add_zero]
  have key : (0 : ℝ) < ∫ x in (0 : ℝ)..1,
      (Real.exp (-(0 : ℝ) ^ 2 / 2) - Real.exp (-x ^ 2 / 2)) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (Continuous.intervalIntegrable (by fun_prop) 0 1) ?_ (by norm_num)
    intro x hx
    have : Real.exp (-x ^ 2 / 2) < Real.exp (-(0 : ℝ) ^ 2 / 2) :=
      Real.exp_lt_exp.mpr (by nlinarith [mul_pos hx.1 hx.1])
    linarith
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) 0 1), intervalIntegral.integral_const,
      sub_zero, smul_eq_mul, one_mul] at key
  linarith

theorem Norm2_div_Norm1_lt_one : Norm2 / Norm1 < 1 := (div_lt_one Norm1_pos).mpr Norm2_lt_Norm1

noncomputable def G2Factor : ℝ≥0 :=
  ⟨1 / (1 - Norm2 / Norm1),
    div_nonneg zero_le_one (by linarith [Norm2_div_Norm1_lt_one])⟩

theorem one_lt_G2Factor : 1 < G2Factor := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_one]
  show (1 : ℝ) < 1 / (1 - Norm2 / Norm1)
  exact one_lt_one_div_one_sub (div_pos Norm2_pos Norm1_pos) Norm2_div_Norm1_lt_one

theorem G1Factor_coe :
    (G1Factor : ℝ≥0∞) = ENNReal.ofReal (1 / (1 - (1 - (γBNE : ℝ)) * Norm1)) := by
  rw [← ENNReal.ofReal_coe_nnreal]; rfl

theorem G1Factor_mul_reject :
    (G1Factor : ℝ≥0∞) * ENNReal.ofReal (1 - (1 - (γBNE : ℝ)) * Norm1) = 1 := by
  have hrej : (0 : ℝ) < 1 - (1 - (γBNE : ℝ)) * Norm1 := by linarith [Norm1_reject_lt_one]
  rw [G1Factor_coe, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hrej.ne',
    ENNReal.ofReal_one]

theorem G2Factor_coe : (G2Factor : ℝ≥0∞) = ENNReal.ofReal (1 / (1 - Norm2 / Norm1)) := by
  rw [← ENNReal.ofReal_coe_nnreal]; rfl

theorem G2Factor_mul_reject :
    (G2Factor : ℝ≥0∞) * ENNReal.ofReal (1 - Norm2 / Norm1) = 1 := by
  have hrej : (0 : ℝ) < 1 - Norm2 / Norm1 := by linarith [Norm2_div_Norm1_lt_one]
  rw [G2Factor_coe, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hrej.ne',
    ENNReal.ofReal_one]

theorem G1PMF_tsum : ∑' k : ℕ, G1PMF k = 1 := by
  simp only [G1PMF]
  rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun k => div_nonneg (Real.exp_pos _).le Norm1_pos.le)
        (summable_normTerm.div_const _),
      tsum_div_const, ← Norm1, div_self Norm1_pos.ne', ENNReal.ofReal_one]

theorem G2pdf_setLIntegral (k : ℕ) :
    ∫⁻ x, G2pdf k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))
      = ENNReal.ofReal (∫ x in (0 : ℝ)..1, Real.exp (-((x + k) ^ 2) / 2) / Norm2) := by
  show ∫⁻ x in Set.Icc (0 : ℝ) 1, G2pdf k x ∂volume = _
  simp only [G2pdf]
  exact lintegral_ofReal_Icc (by norm_num) (by fun_prop)
    (fun r _ => div_nonneg (Real.exp_pos _).le Norm2_pos.le)

theorem G2pdf_total : ∑' k : ℕ, ∫⁻ x, G2pdf k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) = 1 := by
  simp_rw [G2pdf_setLIntegral, intervalIntegral.integral_div]
  rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun k => div_nonneg (intervalIntegral.integral_nonneg (by norm_num)
          (fun x _ => (Real.exp_pos _).le)) Norm2_pos.le)
        (Norm2_summand_summable.div_const _),
      tsum_div_const, ← Norm2_eq_tsum, div_self (ne_of_gt Norm2_pos), ENNReal.ofReal_one]

theorem G1PMF_mul_accept (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    G1PMF k * G2p k x = ENNReal.ofReal (Norm2 / Norm1) * G2pdf k x := by
  have hpow : (γBkx k x : ℝ) ^ (k + 1) = Real.exp (-x * (2 * k + x) / 2) := by
    rw [γBkx_coe k hx, ← Real.exp_nat_mul]
    congr 1
    have h2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    push_cast; field_simp
  simp only [G1PMF, G2pdf, G2p]
  rw [hpow, ← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le Norm1_pos.le),
      ← ENNReal.ofReal_mul (div_nonneg Norm2_pos.le Norm1_pos.le)]
  congr 1
  have hrr : Real.exp (-(k : ℝ) ^ 2 / 2) / Norm1 * Real.exp (-x * (2 * k + x) / 2)
      = Real.exp (-(k : ℝ) ^ 2 / 2) * Real.exp (-x * (2 * k + x) / 2) / Norm1 := by ring
  have hadd : -(k : ℝ) ^ 2 / 2 + -x * (2 * k + x) / 2 = -((x + k) ^ 2) / 2 := by ring
  rw [hrr, ← Real.exp_add, hadd]
  field_simp [ne_of_gt Norm1_pos, ne_of_gt Norm2_pos]

theorem G2_accept_lintegral (F : ℕ → ℝ → ℝ≥0∞) (k : ℕ) :
    G1PMF k * ∫⁻ x, G2p k x * F k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))
      = ENNReal.ofReal (Norm2 / Norm1)
          * ∫⁻ x, G2pdf k x * F k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) := by
  rw [← lintegral_const_mul' (G1PMF k) _ (by rw [G1PMF]; exact ENNReal.ofReal_ne_top),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  show ∫⁻ x in Set.Icc (0 : ℝ) 1, _ ∂volume = ∫⁻ x in Set.Icc (0 : ℝ) 1, _ ∂volume
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [← mul_assoc, G1PMF_mul_accept k hx.1, mul_assoc]

theorem G2_accept_mass (k : ℕ) :
    G1PMF k * ∫⁻ x, G2p k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))
      = ENNReal.ofReal (Norm2 / Norm1) * ∫⁻ x, G2pdf k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) := by
  simpa only [mul_one] using G2_accept_lintegral (fun _ _ => 1) k

theorem G1Geometric_collapse (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    shiftGeometricPMFCreditV γBNE 0 (G1GeometricCredit F ((G1Factor : ℝ≥0∞) * ε))
      = G1CreditV F + ε := by
  have hγ1 : (γBNE : ℝ) < 1 := γBNE_lt_one
  set c := (G1Factor : ℝ≥0∞) * ε with hc
  set R := ENNReal.ofReal ((1 - (γBNE : ℝ)) * Norm1) with hR
  have hR1 : R ≤ 1 := by
    rw [hR, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [Norm1_reject_lt_one])
  have hak1 : ∀ k, ENNReal.ofReal ((γBNE : ℝ) ^ IterN k) ≤ 1 := fun k => by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (pow_le_one₀ γBNE.2.1 hγ1.le)
  have hpterm : ∀ k, ENNReal.ofReal ((γBNE : ℝ) ^ IterN k) * GeometricPMF γBNE k
      = R * G1PMF k := fun k => by
    rw [hR, G1PMF, geometricPMF_γBNE,
        ← ENNReal.ofReal_mul (pow_nonneg γBNE.2.1 _),
        ← ENNReal.ofReal_mul (mul_nonneg (by linarith) Norm1_pos.le)]
    congr 1
    have hregroup : (γBNE : ℝ) ^ IterN k * ((γBNE : ℝ) ^ k * (1 - (γBNE : ℝ)))
        = (1 - (γBNE : ℝ)) * (γBNE : ℝ) ^ (IterN k + k) := by rw [pow_add]; ring
    rw [hregroup, IterN_add_self, γBNE_pow_sq]
    field_simp [Norm1_pos.ne']
  have hRfin : (∑' k : ℕ, ENNReal.ofReal ((γBNE : ℝ) ^ IterN k) * GeometricPMF γBNE k) = R := by
    rw [tsum_congr fun k => mul_comm _ _]; exact geom_iterN_tsum
  have hrejsum : (∑' k : ℕ, (1 - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)) * GeometricPMF γBNE k)
      = 1 - R := by
    have hfun :
        (fun k : ℕ => (1 - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)) * GeometricPMF γBNE k)
          = fun k => GeometricPMF γBNE k
              - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k) * GeometricPMF γBNE k := by
      funext k
      rw [ENNReal.sub_mul (fun _ _ => by simp [GeometricPMF]), one_mul]
    rw [hfun,
      ENNReal.tsum_sub (by rw [hRfin, hR]; exact ENNReal.ofReal_ne_top)
        (fun k => by
          nth_rewrite 2 [← one_mul (GeometricPMF γBNE k)]
          exact mul_le_mul_left (hak1 k) _),
      geometricPMF_tsum, hRfin]
  have hgeo : ∀ k : ℕ, G1GeometricCredit F c (0 + (k : ℤ)) * GeometricPMF γBNE k
      = R * G1PMF k * F k
        + (1 - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)) * GeometricPMF γBNE k
          * (G1CreditV F + c) := by
    intro k
    have hgc : G1GeometricCredit F c (k : ℤ)
        = ENNReal.ofReal ((γBNE : ℝ) ^ IterN k) * F k
            + (1 - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)) * (G1CreditV F + c) := rfl
    rw [zero_add, hgc, add_mul, ← hpterm k]
    ring
  unfold shiftGeometricPMFCreditV
  have hacc : (∑' k : ℕ, R * G1PMF k * F k) = R * G1CreditV F := by
    rw [G1CreditV, ← ENNReal.tsum_mul_left]; exact tsum_congr fun k => by rw [mul_assoc]
  have hrej' : (∑' k : ℕ, (1 - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)) * GeometricPMF γBNE k
        * (G1CreditV F + c))
      = (G1CreditV F + c) * (1 - R) := by
    rw [ENNReal.tsum_mul_right, hrejsum, mul_comm]
  rw [tsum_congr hgeo, ENNReal.tsum_add, hacc, hrej']
  have halg : R * G1CreditV F + (G1CreditV F + c) * (1 - R)
      = G1CreditV F * (R + (1 - R)) + c * (1 - R) := by ring
  rw [halg, add_tsub_cancel_of_le hR1, mul_one]
  congr 1
  have h1R : (1 : ℝ≥0∞) - R = ENNReal.ofReal (1 - (1 - (γBNE : ℝ)) * Norm1) := by
    rw [hR, ENNReal.one_sub_ofReal (mul_nonneg (by linarith) Norm1_pos.le)]
  rw [hc, h1R, mul_right_comm, G1Factor_mul_reject, one_mul]

theorem G2G1_collapse (F : ℕ → ℝ → ℝ≥0∞) (hFm : ∀ a, Measurable (F a)) (ε : ℝ≥0∞) :
    G1CreditV (G2G1Credit F ((G2Factor : ℝ≥0∞) * ε)) = G2CreditV F + ε := by
  set c : ℝ≥0∞ := (G2Factor : ℝ≥0∞) * ε with hc
  have hρ_le : ENNReal.ofReal (Norm2 / Norm1) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal Norm2_div_Norm1_lt_one.le
  have hq1 : ∀ k, (∫⁻ x, G2p k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))) ≤ 1 := fun k =>
    (lintegral_mono (fun x => G2p_le_one k x)).trans unifUnit_lintegral_one.le
  have hgm_mul : ∀ k, ENNReal.ofReal (Norm2 / Norm1)
      * ∫⁻ x, G2pdf k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) ≤ G1PMF k := fun k => by
    rw [← G2_accept_mass k]
    exact (mul_le_mul_right (hq1 k) (G1PMF k)).trans (le_of_eq (mul_one _))
  have h1mp : ∀ k, (∫⁻ x, (1 - G2p k x) ∂(LawfulProbLangℝ.unifUnit (T := ℝ)))
      = 1 - ∫⁻ x, G2p k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) := fun k => by
    rw [MeasureTheory.lintegral_sub (measurable_g2p k)
          (ne_top_of_le_ne_top ENNReal.one_ne_top (hq1 k))
          (Filter.Eventually.of_forall (fun x => G2p_le_one k x)), unifUnit_lintegral_one]
  have hfun :
      (fun k : ℕ => (1 - ∫⁻ x, G2p k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))) * G1PMF k)
        = fun k => G1PMF k
            - ENNReal.ofReal (Norm2 / Norm1)
              * ∫⁻ x, G2pdf k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) := by
    funext k
    rw [ENNReal.sub_mul (fun _ _ => by rw [G1PMF]; exact ENNReal.ofReal_ne_top), one_mul,
        mul_comm (∫⁻ x, G2p k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))) (G1PMF k), G2_accept_mass k]
  have hrejsum : (∑' k : ℕ, (1 - ∫⁻ x, G2p k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))) * G1PMF k)
      = 1 - ENNReal.ofReal (Norm2 / Norm1) := by
    rw [hfun,
      ENNReal.tsum_sub
        (by rw [ENNReal.tsum_mul_left, G2pdf_total, mul_one]
            exact ne_top_of_le_ne_top ENNReal.one_ne_top hρ_le) hgm_mul,
      G1PMF_tsum, ENNReal.tsum_mul_left, G2pdf_total, mul_one]
  have haccsum : (∑' k : ℕ, ENNReal.ofReal (Norm2 / Norm1)
      * ∫⁻ x, G2pdf k x * F k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)))
      = ENNReal.ofReal (Norm2 / Norm1) * G2CreditV F := by
    rw [ENNReal.tsum_mul_left]; rfl
  have hsplit : ∀ k : ℕ, G1PMF k * G2G1Credit F c k
      = ENNReal.ofReal (Norm2 / Norm1) * (∫⁻ x, G2pdf k x * F k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)))
        + (1 - ∫⁻ x, G2p k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))) * G1PMF k * (G2CreditV F + c) := by
    intro k
    have hamp : (fun x => G2CreditAmp F c k x)
        = fun x => G2p k x * F k x + (1 - G2p k x) * (G2CreditV F + c) := by
      funext x; rw [G2CreditAmp, IterCreditV]; rfl
    rw [G2G1Credit, hamp,
        lintegral_add_left (f := fun x => G2p k x * F k x) ((measurable_g2p k).mul (hFm k)),
        lintegral_mul_const _ ((measurable_g2p k).const_sub 1),
        mul_add, G2_accept_lintegral F k, h1mp k]
    ring
  rw [G1CreditV, tsum_congr hsplit, ENNReal.tsum_add, haccsum, ENNReal.tsum_mul_right, hrejsum]
  have halg : ENNReal.ofReal (Norm2 / Norm1) * G2CreditV F
        + (1 - ENNReal.ofReal (Norm2 / Norm1)) * (G2CreditV F + c)
      = G2CreditV F * (ENNReal.ofReal (Norm2 / Norm1) + (1 - ENNReal.ofReal (Norm2 / Norm1)))
        + c * (1 - ENNReal.ofReal (Norm2 / Norm1)) := by ring
  rw [halg, add_tsub_cancel_of_le hρ_le, mul_one]
  congr 1
  rw [hc, ENNReal.one_sub_ofReal (div_nonneg Norm2_pos.le Norm1_pos.le), mul_right_comm,
    G2Factor_mul_reject, one_mul]

end conservation

section specification

theorem twp_G1 (E : CoPset) (F : ℕ → ℝ≥0∞) :
    ⊢@{IProp GF} ↯ (G1CreditV F) -∗
      tglWp E pl(&G1 #.unit)
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε_spec
  iapply twp_err_pos solve_not_value
  iintro %ε_term %Hε_pos Hε_term
  irevert Hε_spec
  iapply ErrorCredit.Induction.simple (k := G1Factor) Hε_pos one_lt_G1Factor $$ [] Hε_term
  iintro !> ⟨IH, Hε_term⟩ Hε_spec
  set c : ℝ≥0∞ := (G1Factor : ℝ≥0∞) * ε_term
  twp_pure
  twp_pure
  twp_bind pl(&GeometricTrial &BNEHalfVal.1 #(.int (0 : ℤ)))
  icombine Hε_spec Hε_term as Hε
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ z : ℤ,
    ⌜v.1 = pl(#(.int z))⌝ ∗ ⌜(0 : ℤ) ≤ z⌝ ∗ ↯ (G1GeometricCredit F c z))))
  isplitl [Hε]
  · iapply (twp_GeometricTrial E 0 BNEHalfVal γBNE_pos γBNE_lt_one
      abstractBernoulli_BNEHalf) $$ %(G1GeometricCredit F c)
    iapply (ErrorCredit.ext (G1Geometric_collapse F ε_term).symm)
    iexact Hε
  iintro %vk ⟨%z, %hz, %hz0, Hck⟩
  obtain ⟨wk, _⟩ := vk
  obtain rfl : wk = _ := hz
  twp_pure
  have hck : G1GeometricCredit F c z
      = IterCreditV (G1IterContAmp F c z.toNat) γBNE (IterN z.toNat) := rfl
  twp_bind pl(&IterTrial &BNEHalf (#(.int z) * (#(.int z) - #1)))
  twp_pure
  twp_pure
  rw [IterN_toNat_cast hz0]
  iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
    ⌜w.1 = pl(#(.bool b))⌝ ∗ ↯ (G1IterContAmp F c z.toNat b) ∗ ⌜True⌝)))
  isplitl [Hck]
  · iapply (twp_IterTrial E BNEHalfVal γBNE (iprop(⌜True⌝))
      (abstractBernoulliI_BNEHalf (iprop(⌜True⌝)))
      (G1IterContAmp F c z.toNat) (IterN z.toNat))
    rw [← hck]
    iframe Hck
  iintro %vb ⟨%b, %hb, Hcb, -⟩
  obtain ⟨wb, _⟩ := vb
  obtain rfl : wb = _ := hb
  cases b with
  | true =>
    have hcb : G1IterContAmp F c z.toNat true = F z.toNat := by simp [G1IterContAmp]
    twp_pures
    twp_value
    imodintro
    iexists z.toNat
    rw [← hcb, show Int.ofNat z.toNat = z from Int.toNat_of_nonneg hz0]
    iframe Hcb
    itrivial
  | false =>
    have hcb : G1IterContAmp F c z.toNat false = G1CreditV F + c := by simp [G1IterContAmp]
    isimp only [hcb] at Hcb
    ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split $$ Hcb
    twp_pure
    twp_bind pl(&G1 #.unit)
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hexp

theorem twp_G2 (E : CoPset) (F : ℕ → ℝ → ℝ≥0∞) (hFm : ∀ a, Measurable (F a)) :
    ⊢@{IProp GF} ↯ (G2CreditV F) -∗
      tglWp E pl(&G2 #.unit)
        (fun p : Val ℝ => iprop(∃ (k : ℕ) (r : ℝ),
          ⌜0 ≤ r ∧ r < 1⌝ ∗
          ⌜p.1 = .pair pl(#(.real r)) (pl(#(.int (Int.ofNat k))))⌝ ∗ ↯ (F k r))) := by
  iintro Hε_spec
  iapply twp_err_pos solve_not_value
  iintro %ε_term %Hε_pos Hε_term
  irevert Hε_spec
  iapply ErrorCredit.Induction.simple (k := G2Factor) Hε_pos one_lt_G2Factor $$ [] Hε_term
  iintro !> ⟨IH, Hε_term⟩ Hε_spec
  set c : ℝ≥0∞ := (G2Factor : ℝ≥0∞) * ε_term
  twp_pure
  twp_pure
  twp_bind pl(&G1 #.unit)
  icombine Hε_spec Hε_term as Hε
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
    ⌜v.1 = pl(#(.int (Int.ofNat n)))⌝ ∗ ↯ (G2G1Credit F c n))))
  isplitl [Hε]
  · iapply (twp_G1 E (G2G1Credit F c))
    iapply (ErrorCredit.ext (G2G1_collapse F hFm ε_term).symm)
    iexact Hε
  iintro %vk ⟨%k, %hk, Hck⟩
  obtain ⟨wk, _⟩ := vk
  obtain rfl : wk = _ := hk
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp' (ε₂ := G2CreditAmp F c k)
    (measurable_g2CreditAmp F hFm c k) ?hint) $$ Hck
  case hint => exact le_rfl
  iintro %x ⟨%hxm, Hcx⟩
  have hx01 : 0 < x ∧ x < 1 := mem_unifUnitSupport_real.mp hxm
  have hxr : 0 ≤ x ∧ x ≤ 1 := ⟨hx01.1.le, hx01.2.le⟩
  twp_pure
  twp_bind pl(&IterTrial &(BkxVal k x).1 (#(.int (k : ℤ)) + #1))
  twp_pure
  rw [← Nat.cast_add_one]
  have hck : G2CreditAmp F c k x
      = IterCreditV (G2IterContAmp F c k x) (γBkx k x) (k + 1) := rfl
  iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
    ⌜w.1 = pl(#(.bool b))⌝ ∗ ↯ (G2IterContAmp F c k x b) ∗ ⌜True⌝)))
  isplitl [Hcx]
  · iapply (twp_IterTrial E (BkxVal k x) (γBkx k x) (iprop(⌜True⌝))
      (abstractBernoulliI_Bkx k x hxr (iprop(⌜True⌝)))
      (G2IterContAmp F c k x) (k + 1))
    rw [← hck]
    iframe Hcx
  iintro %vb ⟨%b, %hb, Hcb, -⟩
  obtain ⟨wb, _⟩ := vb
  obtain rfl : wb = _ := hb
  cases b with
  | true =>
    have hcb : G2IterContAmp F c k x true = F k x := by simp [G2IterContAmp]
    have hx1 : 0 ≤ x ∧ x < 1 := ⟨hx01.1.le, hx01.2⟩
    twp_pures
    twp_value
    imodintro
    iexists k, x
    rw [← hcb]
    iframe %hx1 Hcb
    itrivial
  | false =>
    have hcb : G2IterContAmp F c k x false = G2CreditV F + c := by simp [G2IterContAmp]
    isimp only [hcb] at Hcb
    ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split $$ Hcb
    twp_pure
    twp_bind pl(&G2 #.unit)
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hexp

end specification

end
end Examples
end TotalEris
end ProbLang
