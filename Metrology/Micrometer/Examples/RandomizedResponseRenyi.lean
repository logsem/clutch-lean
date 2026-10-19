module

public import Metrology.Micrometer.Examples.RandomizedResponseLoop
public import Metrology.Couplings.Divergences.RenyiFiber

@[expose] public section

/-! # Randomized response is Rényi private at each order

At order `α` one round costs `ρ_α = log ((3^α + 3^{1-α}) / 4) / (α - 1)`, and the loop
refinement runs unchanged in the Rényi lifting: `k` rounds are `(α, k ρ_α)`-RDP. -/

open MeasureTheory ProbabilityTheory GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

/-! ## The Rényi profile of one round -/

/-- One round reports its bit with probability `3/4`. -/
theorem map_rrOut_singleton (b c : Bool) :
    (unifInt 4 (by norm_num)).map (rrOut b) {c} = if b = c then 3 / 4 else 1 / 4 := by
  rw [Measure.map_apply .of_discrete (measurableSet_singleton c), unifInt_apply,
    show Finset.Ico (0 : Int) 4 = {0, 1, 2, 3} by decide]
  cases b <;> cases c <;> norm_num [rrOut, Set.indicator, Finset.filter_insert,
    Finset.filter_singleton, ENNReal.div_eq_inv_mul, mul_comm]

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

/-- The `α`-th moment between rounds on different bits is `(3^α + 3^{1-α}) / 4`. -/
theorem fDiv_rrOut {α : ℝ} (hα : 1 < α) (b : Bool) :
    fDiv (· ^ α) ((unifInt 4 (by norm_num)).map (rrOut b))
      ((unifInt 4 (by norm_num)).map (rrOut !b)) = (((3 ^ α + 3 ^ (1 - α)) / 4 : ℝ) : EReal) := by
  rw [fDiv_eq_sum (convexOn_rpow hα.le) (continuousWithinAt_rpow_zero (by linarith)),
    Fintype.sum_bool, map_rrOut_singleton, map_rrOut_singleton, map_rrOut_singleton,
    map_rrOut_singleton, Real.rpow_sub (by norm_num), Real.rpow_one]
  cases b
  all_goals
    norm_num [persp_rpow_of_pos, Real.div_rpow]
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    field_simp
  ring

/-- One round on any two bits is within `rrRenyi α` at order `α`. -/
theorem renyiDivergence_rrOut {α : ℝ} [hα : Fact (1 < α)] (b b' : Bool) :
    renyiDivergence α (rrRenyi α) ((unifInt 4 (by norm_num)).map (rrOut b))
      ((unifInt 4 (by norm_num)).map (rrOut b')) := by
  obtain rfl | rfl : b' = b ∨ b' = !b := by cases b <;> cases b' <;> simp
  · exact IsGraded.mono (by simp) (IsReflexive.refl _)
  have hX := one_le_rrMoment hα.out.le
  rw [rrRenyi, renyiDivergence_iff_of_ne_top hα.out.le ENNReal.ofReal_ne_top, fDiv_rrOut hα.out,
    ENNReal.toReal_ofReal (div_nonneg (Real.log_nonneg hX) (by linarith [hα.out])),
    mul_div_cancel₀ _ (by linarith [hα.out]), Real.exp_log (by linarith)]

/-- The two draws couple along equal reports at `rrRenyi α`: condition on the reports. -/
theorem rr_renyi_coupling (α : ℝ) [Fact (1 < α)] (b b' : Bool) :
    (codensity (renyiDivergence α)).Rel (rrRenyi α) (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) :=
  codensity_renyi_rel_of_map .of_discrete .of_discrete (renyiDivergence_rrOut b b')

/-! ## `k` rounds in the logic -/

section Logic

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] (α : ℝ) [Fact (1 < α)]

/-- The loop refines itself at equal counts in the Rényi lifting, spending `rrRenyi α` per
round. -/
theorem rrCount_refines_renyi {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS ℝ≥0∞ GF] (b b' : Bool) (k : ℕ) :
    ⊢@{IProp GF} ↯b (k • rrRenyi α) -∗
      REL[codensity (renyiDivergence α)] (rrCount (rT := rT) b k) << (rrCount b' k) : lrel_int :=
  rrCount_refines_of _ (rr_refines_of _ (IsAddRegular.of_ne_top ENNReal.ofReal_ne_top).1
    (rr_renyi_coupling α)) b b' k

/-- Randomized response in a loop of `k` rounds is `(α, k ρ_α)`-RDP for any two bits
(Def. 2.3). -/
theorem rrCount_RDP (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).RDP ⊤ α (k * rrRenyi α) := fun b b' _ ↦ by
  rw [← nsmul_eq_mul]
  exact approximates_div (GF := MicrometerFunctor rT ℝ≥0∞) (fun _ _ ↦ lrel_int) _ _ σ σ _
    (fun _ _ ↦ lrel_int_car_eq) fun _ _ ↦ rrCount_refines_renyi α b b' k

end Logic

end RandomizedResponse
end ProbLang
