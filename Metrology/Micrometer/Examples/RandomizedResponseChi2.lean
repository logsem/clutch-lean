module

public import Metrology.Micrometer.Examples.RandomizedResponseRenyi
public import Metrology.Couplings.Divergences.Power

@[expose] public section

/-! # Randomized response has bounded χ² divergence

At order `2` one round has moment `7/3` (`fDiv_rrOut`), so it is within χ² budget `4/3`. χ²
budgets compose as `c₁ + c₂ + c₁ c₂` (Barthe–Olmedo), and the loop refinement runs in the χ²
lifting: `k` rounds have `∫ (dμ/dν)² dν ≤ (7/3)^k`. -/

open MeasureTheory ProbabilityTheory GradedLifting GradedDivergence GradedDivergence.PowerBudget
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

theorem one_add_four_thirds : (1 + 4 / 3 : ℝ≥0∞) = 7 / 3 := by
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num), mul_add,
    ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  norm_num

/-- One round on any two bits is within χ² budget `4/3`. -/
theorem chi2Divergence_rrOut (b b' : Bool) :
    chi2Divergence (ofENNReal (4 / 3)) ((unifInt 4 (by norm_num)).map (rrOut b))
      ((unifInt 4 (by norm_num)).map (rrOut b')) := by
  obtain rfl | rfl : b' = b ∨ b' = !b := by cases b <;> cases b' <;> simp
  · exact IsGraded.mono (by simp) (IsReflexive.refl _)
  rw [chi2Divergence_iff, fDiv_rrOut one_lt_two, toENNReal_ofENNReal,
    one_add_four_thirds, show (7 / 3 : ℝ≥0∞) = ENNReal.ofReal (7 / 3) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num,
    EReal.coe_ennreal_ofReal, max_eq_left (by norm_num), EReal.coe_le_coe_iff]
  norm_num [Real.rpow_two, Real.rpow_neg_one]

/-- The two draws couple along equal reports in the χ² lifting at `4/3`. -/
theorem rr_chi2_coupling (b b' : Bool) :
    chi2Lifting.Rel (ofENNReal (4 / 3)) (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) :=
  chi2Lifting_rel_iff.2 (codensity_renyi_rel_of_map .of_discrete .of_discrete
    (chi2Divergence_iff_renyi.1 (chi2Divergence_rrOut b b')))

section Logic

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- The loop refines itself at equal counts in the χ² lifting, spending `4/3` per round. -/
theorem rrCount_refines_chi2 {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS PowerBudget GF] (b b' : Bool) (k : ℕ) :
    ⊢@{IProp GF} ↯b (k • ofENNReal (4 / 3)) -∗
      REL[chi2Lifting] (rrCount (rT := rT) b k) << (rrCount b' k) : lrel_int :=
  rrCount_refines_of _ (rr_refines_of _ (isAddLeftRegular_of_ne_top (by simp [ENNReal.div_eq_top]))
    rr_chi2_coupling) b b' k

/-- Randomized response in a loop of `k` rounds has second moment at most `(7/3)^k`, that is
χ² divergence at most `(7/3)^k - 1`, for any two bits. -/
theorem rrCount_fDiv_sq_le (b b' : Bool) (k : ℕ) (σ σ' : State rT) :
    fDiv (· ^ (2 : ℝ)) (limExecV ⟨rrCount b k, σ⟩) (limExecV ⟨rrCount b' k, σ'⟩) ≤
      (((7 / 3 : ℝ≥0∞) ^ k : ℝ≥0∞) : EReal) := by
  have h := approximates_div (GF := MicrometerFunctor rT PowerBudget) (D := chi2Divergence)
    (fun _ _ ↦ lrel_int) _ _ σ σ' _ (fun _ _ ↦ lrel_int_car_eq) fun _ _ ↦ rrCount_refines_chi2 b b' k
  rwa [chi2Divergence_iff, one_add_toENNReal_nsmul, toENNReal_ofENNReal,
    one_add_four_thirds] at h

end Logic

end RandomizedResponse
end ProbLang
