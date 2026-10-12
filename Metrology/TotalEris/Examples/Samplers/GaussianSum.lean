module

public import Metrology.TotalEris.Examples.Samplers.GaussianConcentration
public import Metrology.Code.GaussSum
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.Examples
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

theorem Gauss_lc : (Gauss : Exp ℝ).IsLocallyClosed := by is_lc

theorem Gauss_fv : (Gauss : Exp ℝ).fv = ∅ := by
  simp [Gauss, G2, G1, B, Bii, BNEHalf, DecrTrial, FairCoin, GeometricTrial, IterTrial, LeHalf,
    S, S0, C, Exp.fv]

@[simp] theorem Gauss_openRec (k : ℕ) (t : Exp ℝ) : Exp.openRec k t Gauss = Gauss :=
  (Exp.open_lc k t Gauss Gauss_lc).symm

@[simp] theorem Gauss_closeRec (k : ℕ) (x : Var) : Exp.closeRec k x (Gauss : Exp ℝ) = Gauss :=
  Exp.closeRec_fresh x Gauss k (by simp [Gauss_fv])

def gaussSumCost (s a : ℝ) (k : ℕ) (b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (k * s ^ 2 / 2 + s * (b - a)))

abbrev gaussSumPost (a b : ℝ) : Val ℝ → IProp GF :=
  fun v => iprop(∃ y : ℝ, ⌜v = .real y ∧ b + y < a⌝)

open MeasureTheory ProbabilityTheory in
theorem gaussCreditV_exp_le (c s : ℝ) :
    GaussCreditV (fun y => ENNReal.ofReal (Real.exp (c + s * y))) ≤
      ENNReal.ofReal (Real.exp (c + s ^ 2 / 2)) := by
  rw [← gauss_credit_eq_gaussianReal _ (by fun_prop),
    ← ofReal_integral_eq_lintegral_ofReal
      (by simpa [Real.exp_add] using
        (hasSubgaussianMGF_id_gaussianReal.integrable_exp_mul s).const_mul (Real.exp c))
      (ae_of_all _ fun y => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ y, Real.exp (c + s * y) ∂gaussianReal 0 1
      = Real.exp c * mgf id (gaussianReal 0 1) s := by
        simp only [Real.exp_add, mgf, id]
        exact integral_const_mul _ _
    _ ≤ Real.exp c * Real.exp (1 * s ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (by simpa using hasSubgaussianMGF_id_gaussianReal.mgf_le s)
          (Real.exp_pos c).le
    _ = Real.exp (c + s ^ 2 / 2) := by rw [← Real.exp_add, one_mul]

theorem twp_gaussSum_exp (E : CoPset) {s : ℝ} (hs : 0 ≤ s) (a : ℝ) (k : ℕ) (b : ℝ) :
    iprop(↯(gaussSumCost s a k b)) ⊢@{IProp GF}
      tglWp E pl(&gaussSum #(.int (k : ℤ))) (gaussSumPost a b) := by
  induction k generalizing b with
  | zero =>
    iintro Herr
    twp_pures
    by_cases hab : b < a
    · twp_value
      iexists ((0 : ℤ) : ℝ)
      ipureintro
      exact ⟨rfl, by simpa using hab⟩
    · iexfalso
      iapply ErrorCredit.contradict ?_ $$ Herr
      simp only [gaussSumCost, Nat.cast_zero, zero_mul, zero_div, zero_add]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hs (by linarith)))
  | succ k IH =>
    iintro Herr
    twp_pure; twp_pure; twp_pure
    isimp only [Gauss_openRec, Gauss_closeRec]
    twp_pure
    twp_bind pl(&Gauss #.unit)
    iapply tglWp_wand
    isplitl [Herr]
    · iapply twp_Gauss E (fun y => gaussSumCost s a k (b + y)) (by unfold gaussSumCost; fun_prop)
      iapply ErrorCredit.weaken ?_ $$ Herr
      convert gaussCreditV_exp_le (k * s ^ 2 / 2 + s * (b - a)) s using 3
      · unfold gaussSumCost
        ring_nf
      · unfold gaussSumCost
        push_cast
        ring_nf
    iintro %v ⟨%y, %hy, Hcr⟩
    obtain rfl : v = Val.real y := Val.ext hy
    simp only [Exp.ofVal]
    twp_pure
    twp_pure
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega]
    twp_bind pl(&gaussSum #(.int (k : ℤ)))
    iapply tglWp_wand (Φ := gaussSumPost a (b + y))
    isplitl [Hcr]
    · iapply IH $$ Hcr
    iintro %w ⟨%m, %⟨rfl, Hm⟩⟩
    twp_pures
    twp_value
    iexists (y + m)
    ipureintro
    exact ⟨rfl, by linarith⟩

theorem twp_gaussSum_chernoff (E : CoPset) (a : ℝ) (n : ℕ) :
    iprop(↯(⨅ s ∈ Set.Ici (0 : ℝ), gaussSumCost s a n 0)) ⊢@{IProp GF}
      tglWp E pl(&gaussSum #(.int (n : ℤ))) (gaussSumPost a 0) := by
  iintro Herr
  iapply twp_err_biInf solve_not_value
  iframe Herr
  iintro %s %hs Hs
  iapply twp_gaussSum_exp E hs a n 0 $$ Hs

theorem gaussSumCost_tail {n : ℕ} (hn : 0 < n) (a : ℝ) :
    gaussSumCost (a / n) a n 0 = ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * n))) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold gaussSumCost
  congr 2
  field_simp
  ring

theorem twp_gaussSum_tail (E : CoPset) {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 ≤ a) :
    iprop(↯(ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * n))))) ⊢@{IProp GF}
      tglWp E pl(&gaussSum #(.int (n : ℤ))) (gaussSumPost a 0) := by
  iintro Herr
  iapply twp_gaussSum_chernoff E
  iapply ErrorCredit.weaken ((biInf_le (fun s => gaussSumCost s a n 0)
    (Set.mem_Ici.mpr (by positivity))).trans (gaussSumCost_tail hn a).le) $$ Herr

end
end Examples
end TotalEris
end ProbLang
