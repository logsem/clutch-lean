module

public import Metrology.Micrometer.Examples.RandomizedResponse.Basic
public import Metrology.Couplings.Divergences.RenyiFiber

@[expose] public section

/-! # Randomized response is Rényi private at each order

One round couples at the exact order-`α` cost `ρ_α = log ((3^α + 3^{1-α}) / 4) / (α - 1)`
(`rrCoupling_renyi`), so `k` rounds are `(α, k ρ_α)`-RDP (`rrCount_RDP`). -/

open GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang.RandomizedResponse

open ENNReal (ofReal ofReal_ne_top toReal_ofReal isAddLeftRegular_ofReal)
open Real (log rpow_le_rpow_of_exponent_le rpow_sub rpow_one log_nonneg exp_log)

/-- The exact order-`α` Rényi cost `ρ_α` of one round, between the reports on different bits. -/
noncomputable def rrRenyi (α : ℝ) : ℝ≥0∞ :=
  ofReal (log ((3 ^ α + 3 ^ (1 - α)) / 4) / (α - 1))

/-- The `α`-th moment `(3^α + 3^{1-α}) / 4` of one round is at least `1`: with `t = 3^α ≥ 3`, it is
`1 + (t - 1)(t - 3) / (4 t)`. -/
theorem one_le_rrMoment {α : ℝ} (hα : 1 ≤ α) : 1 ≤ ((3 : ℝ) ^ α + 3 ^ (1 - α)) / 4 := by
  have ht : (3 : ℝ) ≤ 3 ^ α := by
    simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hα
  rw [rpow_sub (by norm_num), rpow_one, le_div_iff₀ (by norm_num), ← sub_nonneg,
    show 3 ^ α + 3 / 3 ^ α - 1 * 4 = ((3 : ℝ) ^ α - 1) * (3 ^ α - 3) / 3 ^ α by
      field_simp; ring]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)

variable {α : ℝ} [hα : Fact (1 < α)]

/-- A Rényi bound between the reports on different bits couples the draws: condition on the
report. -/
theorem rrCoupling_of_renyi {ρ : ℝ≥0∞}
    (h : ∀ b, renyiDivergence α ρ (draw.map (rrOut b)) (draw.map (rrOut !b))) :
    RRCoupling (codensity (renyiDivergence α)) ρ := fun b b' ↦
  codensity_renyi_rel_of_map .of_discrete .of_discrete <| by
    rcases Bool.eq_or_eq_not b' b with rfl | rfl
    exacts [IsGraded.mono zero_le (IsReflexive.refl _), h b]

/-- One round couples at `ρ_α`. -/
theorem rrCoupling_renyi : RRCoupling (codensity (renyiDivergence α)) (rrRenyi α) :=
  rrCoupling_of_renyi fun b ↦ by
    have := one_le_rrMoment hα.out.le
    -- unfold to `M ≤ exp ((α-1) · log M / (α-1))`; `1 ≤ M` makes `toReal ∘ ofReal` the identity,
    -- leaving `M ≤ M`
    rw [rrRenyi, renyiDivergence_iff_of_ne_top hα.out.le ofReal_ne_top, fDiv_rrOut hα.out,
      toReal_ofReal (div_nonneg (log_nonneg this) (by linarith [hα.out])),
      mul_div_cancel₀ _ (by linarith [hα.out]), exp_log (by linarith)]

variable {rT : Type} [LawfulProbLangℝ rT]

/-- `k` rounds are `(α, k ρ_α)`-RDP (Def. 2.3). -/
theorem rrCount_RDP (k : ℕ) (σ : State rT) : (rrCountMech k σ).RDP ⊤ α (k * rrRenyi α) :=
  nsmul_eq_mul k (rrRenyi α) ▸ rrCount_isPrivate _ (isAddLeftRegular_ofReal _) rrCoupling_renyi k σ

end ProbLang.RandomizedResponse
