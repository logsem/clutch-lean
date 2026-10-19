module

public import Metrology.Micrometer.Examples.RandomizedResponse.Basic
public import Metrology.Couplings.Divergences.RenyiFiber

@[expose] public section

/-! # Randomized response is Rényi private at each order

One round costs `ρ_α = log ((3^α + 3^{1-α}) / 4) / (α - 1)` at order `α`, so `k` rounds are
`(α, k ρ_α)`-RDP. -/

open GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

/-- The Rényi divergence of order `α` between rounds on different bits. -/
noncomputable def rrRenyi (α : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.log ((3 ^ α + 3 ^ (1 - α)) / 4) / (α - 1))

/-- The `α`-th moment `(3^α + 3^{1-α}) / 4` is at least `1`: with `t = 3^α ≥ 3`, it is
`1 + (t - 1)(t - 3) / (4 t)`. -/
theorem one_le_rrMoment {α : ℝ} (hα : 1 ≤ α) : 1 ≤ ((3 : ℝ) ^ α + 3 ^ (1 - α)) / 4 := by
  have ht : (3 : ℝ) ≤ 3 ^ α := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hα
  have hpos : (0 : ℝ) < 3 ^ α := by positivity
  rw [Real.rpow_sub (by norm_num), Real.rpow_one, le_div_iff₀ (by norm_num), ← sub_nonneg,
    show 3 ^ α + 3 / 3 ^ α - 1 * 4 = ((3 : ℝ) ^ α - 1) * (3 ^ α - 3) / 3 ^ α by
      field_simp; ring]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hpos.le

variable (α : ℝ) [hα : Fact (1 < α)]

/-- The two draws couple along equal reports at `ρ_α`: condition on the reports. -/
theorem rr_renyi_coupling (b b' : Bool) :
    (codensity (renyiDivergence α)).Rel (rrRenyi α) (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) := by
  refine codensity_renyi_rel_of_map .of_discrete .of_discrete ?_
  obtain rfl | rfl : b' = b ∨ b' = !b := by cases b <;> cases b' <;> simp
  · exact IsGraded.mono (by simp) (IsReflexive.refl _)
  have hX := one_le_rrMoment hα.out.le
  rw [rrRenyi, renyiDivergence_iff_of_ne_top hα.out.le ENNReal.ofReal_ne_top, fDiv_rrOut hα.out,
    ENNReal.toReal_ofReal (div_nonneg (Real.log_nonneg hX) (by linarith [hα.out])),
    mul_div_cancel₀ _ (by linarith [hα.out]), Real.exp_log (by linarith)]

/-- `k` rounds are `(α, k ρ_α)`-RDP (Def. 2.3). -/
theorem rrCount_RDP {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] (k : ℕ)
    (σ : State rT) : (rrCountMech k σ).RDP ⊤ α (k * rrRenyi α) := by
  simpa [nsmul_eq_mul] using rrCount_isPrivate (L := codensity (renyiDivergence α)) (rrRenyi α)
    (IsAddRegular.of_ne_top ENNReal.ofReal_ne_top).1 (rr_renyi_coupling α) k σ

end RandomizedResponse
end ProbLang
