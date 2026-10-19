module

public import Metrology.Micrometer.Examples.RandomizedResponse.Basic
public import Metrology.Couplings.Divergences.Power
public import Metrology.Couplings.Divergences.RenyiFiber

@[expose] public section

/-! # Randomized response has bounded χ² divergence

One round has second moment `(3² + 3⁻¹) / 4 = 7/3`, so χ² budget `4/3`; χ² budgets compose as
`c₁ + c₂ + c₁ c₂`, so `k` rounds have second moment at most `(7/3)^k`. -/

open ProbabilityTheory GradedLifting GradedDivergence GradedDivergence.PowerBudget
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

theorem one_add_four_thirds : (1 + 4 / 3 : ℝ≥0∞) = 7 / 3 := by
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num), mul_add,
    ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  norm_num

/-- The two draws couple along equal reports in the χ² lifting at `4/3`. -/
theorem rr_chi2_coupling (b b' : Bool) :
    chi2Lifting.Rel (ofENNReal (4 / 3)) (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) := by
  refine chi2Lifting_rel_iff.2 (codensity_renyi_rel_of_map .of_discrete .of_discrete
    (chi2Divergence_iff_renyi.1 ?_))
  obtain rfl | rfl : b' = b ∨ b' = !b := by cases b <;> cases b' <;> simp
  · exact IsGraded.mono (by simp) (IsReflexive.refl _)
  rw [chi2Divergence_iff, fDiv_rrOut one_lt_two, toENNReal_ofENNReal,
    one_add_four_thirds, show (7 / 3 : ℝ≥0∞) = ENNReal.ofReal (7 / 3) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num,
    EReal.coe_ennreal_ofReal, max_eq_left (by norm_num), EReal.coe_le_coe_iff]
  norm_num [Real.rpow_two, Real.rpow_neg_one]

/-- `k` rounds have second moment at most `(7/3)^k`, so χ² at most `(7/3)^k - 1`. -/
theorem rrCount_fDiv_sq_le {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (b b' : Bool) (k : ℕ) (σ σ' : State rT) :
    fDiv (· ^ (2 : ℝ)) (limExecV ⟨rrCount b k, σ⟩) (limExecV ⟨rrCount b' k, σ'⟩) ≤
      (((7 / 3 : ℝ≥0∞) ^ k : ℝ≥0∞) : EReal) := by
  have h := rrCount_div (D := chi2Divergence) _
    (isAddLeftRegular_of_ne_top (by simp [ENNReal.div_eq_top])) rr_chi2_coupling b b' k σ σ'
  rwa [chi2Divergence_iff, one_add_toENNReal_nsmul, toENNReal_ofENNReal, one_add_four_thirds] at h

end RandomizedResponse
end ProbLang
