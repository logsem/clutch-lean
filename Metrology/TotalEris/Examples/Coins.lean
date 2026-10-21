module

public import Metrology.TotalEris
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Code.Coins
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Metrology.Iris.LocalBI

@[expose] public section

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi IProp GF

def headsCost (s a : ℝ) (k : ℕ) (b : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + Real.exp s) / 2) ^ k * Real.exp (s * (b - a)))

abbrev headsPost (a : ℝ) (b : ℤ) : Val rT → IProp GF :=
  fun v => iprop(∃ m : ℤ, ⌜v = .int m ∧ (b : ℝ) + m < a⌝)

theorem twp_heads_exp (E : CoPset) {s : ℝ} (hs : 0 ≤ s) (a : ℝ) (k : ℕ) (b : ℤ) :
    iprop(↯(headsCost s a k b)) ⊢
      tglWp E pl(&heads #int (k : ℤ)) (headsPost (rT := rT) a b) := by
  induction k generalizing b with
  | zero =>
    iintro Herr
    twp_pures
    by_cases hab : (b : ℝ) < a
    · twp_value
      iexists 0
      ipureintro
      exact ⟨rfl, by simpa using hab⟩
    · iexfalso
      iapply ErrorCredit.contradict ?_ $$ Herr
      simp only [headsCost, pow_zero, one_mul]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hs (by linarith)))
  | succ k IH =>
    iintro Herr
    twp_pures
    twp_bind pl(rand(#2, #()))
    let F : ℕ → ℝ≥0∞ := fun x => headsCost s a k (b + x)
    have HSum : (∑ n ∈ Finset.range (2 : Int).toNat, F n) / ((2 : Int).toNat : ℝ≥0∞) ≤
        headsCost s a (k + 1) b := by
      rw [show (2 : Int).toNat = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [F, headsCost]
      rw [show ((2 : ℕ) : ℝ≥0∞) = 2 from Nat.cast_ofNat,
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_div_of_pos (by norm_num)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      push_cast
      rw [show s * ((b : ℝ) + 1 - a) = s * (b - a) + s by ring, Real.exp_add]
      ring_nf
    iapply (twp_rand_exp' (z := 2) (ε₂ := F) (Hz := by decide) (HSum := HSum)) $$ Herr
    iintro %n ⟨%⟨Hn₁, Hn₂⟩, Hcr⟩
    simp only [Exp.ofVal]
    twp_pure
    twp_pure
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega]
    twp_bind pl(&heads #int (k : ℤ))
    iapply (tglWp_wand (Φ := headsPost a (b + n)))
    isplitl [Hcr]
    · iapply IH
      iapply ErrorCredit.ext (by simp [F, Int.toNat_of_nonneg Hn₁]) $$ Hcr
    iintro %w ⟨%m, %⟨rfl, Hm⟩⟩
    twp_pures
    twp_value
    iexists (n + m)
    ipureintro
    refine ⟨rfl, ?_⟩
    push_cast at Hm ⊢
    linarith

theorem twp_heads_chernoff (E : CoPset) (a : ℝ) (n : ℕ) :
    iprop(↯(⨅ s ∈ Set.Ici (0 : ℝ), headsCost s a n 0)) ⊢
      tglWp E pl(&heads #int (n : ℤ)) (headsPost (rT := rT) a 0) := by
  iintro Herr
  iapply twp_err_biInf solve_not_value
  iframe Herr
  iintro %s %hs Hs
  iapply twp_heads_exp E hs a n 0 $$ Hs

theorem headsCost_hoeffding {n : ℕ} (hn : 0 < n) (t : ℝ) :
    headsCost (4 * t / n) (n / 2 + t) n 0 ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / n)) := by
  refine ENNReal.ofReal_le_ofReal ?_
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hcosh (s : ℝ) : (1 + Real.exp s) / 2 ≤ Real.exp (s / 2 + s ^ 2 / 8) := by
    have h : Real.exp (s / 2) * Real.cosh (s / 2) = (1 + Real.exp s) / 2 := by
      rw [Real.cosh_eq, mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add,
        show s / 2 + s / 2 = s by ring, show s / 2 + -(s / 2) = 0 by ring, Real.exp_zero]
      ring
    rw [← h, Real.exp_add]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    convert Real.cosh_le_exp_half_sq (s / 2) using 2
    ring
  calc ((1 + Real.exp (4 * t / n)) / 2) ^ n *
        Real.exp (4 * t / n * (((0 : ℤ) : ℝ) - (n / 2 + t)))
      ≤ Real.exp (4 * t / n / 2 + (4 * t / n) ^ 2 / 8) ^ n *
          Real.exp (4 * t / n * (((0 : ℤ) : ℝ) - (n / 2 + t))) := by
        gcongr
        exact hcosh _
    _ = Real.exp (-2 * t ^ 2 / n) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        field_simp
        ring

theorem twp_heads_hoeffding (E : CoPset) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    iprop(↯(ENNReal.ofReal (Real.exp (-2 * t ^ 2 / n)))) ⊢
      tglWp E pl(&heads #int (n : ℤ)) (headsPost (rT := rT) (n / 2 + t) 0) := by
  iintro Herr
  iapply twp_heads_chernoff E
  iapply ErrorCredit.weaken ((biInf_le (fun s => headsCost s (n / 2 + t) n 0)
    (Set.mem_Ici.mpr (by positivity))).trans (headsCost_hoeffding hn t)) $$ Herr

end
end Examples
end TotalEris
end ProbLang
