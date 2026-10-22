module

public import Metrology.Micrometer.Examples.RandomizedResponse.Adaptive
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Adaptive randomized response in χ², with the regraded escort law

`rrAdaptive_chi2`: adaptive randomized response is within χ² budget `7/12`, below the
non-adaptive `(3/2)(3/2) - 1 = 5/4` (`chi2_adaptive_lt`). χ² is Rényi-2 read along
`c ↦ log (1 + c)`, so the escort law regrades (`escortPower`) and the Rényi proof of
`RR.Adaptive` carries over. -/

open MeasureTheory ProbabilityTheory GradedLifting GradedDivergence PowerBudget AdaptiveRenyi
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

open BindLaw (escortPower head_escortPower)
open Cfg (drawCost)

/-! ## Budgets -/

section Costs

variable (b : Bool) (n m : Int)

/-- The χ² cost of the second stage after each first report: `1/2` after `true`. -/
noncomputable def stageTwoCostChi2 : PowerBudget :=
  cond b (ofReal (1 / 2)) 0

/-- Read as Rényi-2, the χ² stage cost is the Rényi stage cost. -/
theorem toRenyi_stageTwoCostChi2 : toRenyi 2 (stageTwoCostChi2 b) = stageTwoCost b := by
  cases b
  · simp [stageTwoCostChi2, stageTwoCost]
  · rw [stageTwoCostChi2, stageTwoCost, Bool.cond_true, Bool.cond_true, toRenyi_two,
      log_ofReal (by norm_num)]
    norm_num

/-- The χ² budget handed to the continuation after first draws `n`, `m`. -/
noncomputable def adaptiveCostChi2 : PowerBudget :=
  if rr3Out false n = rr3Out true m then stageTwoCostChi2 (rr3Out false n) else ⊤

theorem toRenyi_adaptiveCostChi2 : toRenyi 2 (adaptiveCostChi2 n m) = adaptiveCost n m := by
  unfold adaptiveCostChi2 adaptiveCost
  split_ifs <;> simp [toRenyi_stageTwoCostChi2]

end Costs

/-- The second round couples along equal reports at χ² `1/2`, Rényi-2 `log (3/2)`. -/
theorem rr3_coupling_chi2 :
    chi2Lifting.Rel (ofReal (1 / 2)) (fun r r' ↦ rr3Out false r = rr3Out true r')
      (unifInt 3 (by norm_num)) (unifInt 3 (by norm_num)) :=
  chi2Lifting_rel_iff.2 <| by
    rw [log_ofReal (by norm_num), show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
    exact rr3_coupling

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- The first draws form a regraded escort head at χ² `7/12`: read along `toRenyi 2` it is the
Rényi escort head `escortHead_rr3` at `log (19/12)`. -/
theorem escortHead_rr3_chi2 (K : Ectx rT) (σ σ' : State rT) :
    (escortPower 2).head ((unifInt 3 (by norm_num)).map fun n ↦ (⟨pl(#int n), σ⟩ : Cfg rT))
      ((unifInt 3 (by norm_num)).map fun m ↦ (⟨K.fill pl(#int m), σ'⟩ : Cfg rT))
      (drawCost σ σ' K adaptiveCostChi2) (ofReal (7 / 12)) := by
  have hR : (fun ρ ρ' ↦ toRenyi 2 (drawCost σ σ' K adaptiveCostChi2 ρ ρ')) =
      drawCost σ σ' K adaptiveCost := by
    ext ρ ρ'
    unfold drawCost
    split_ifs <;> simp [toRenyi_adaptiveCostChi2]
  rw [head_escortPower, hR, toRenyi_two, log_ofReal (by norm_num),
    show (1 : ℝ) + 7 / 12 = 19 / 12 by norm_num]
  exact escortHead_rr3 K σ σ'

/-! ## The relational proof -/

section Logic

open Iris Iris.BI Iris.ProofMode

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS PowerBudget GF]
local bi IProp GF

/-- The adaptive program on `false` refines it on `true` at equal pairs of reports, spending χ²
`7/12`: the regraded escort law at the first draw, the canonical law at the second. -/
theorem rrAdaptive_refines_chi2 :
    ⊢ ↯b (ofReal (7 / 12)) -∗
      REL[chi2Lifting] (rrAdaptive (rT := rT) false) << (rrAdaptive true) :
        lrel_prod lrel_bool lrel_bool := by
  iintro Hb
  rel_couple_UU_law (escortPower 2) adaptiveCostChi2 (ofReal (7 / 12))
    (isAddLeftRegular_ofReal _) escortHead_rr3_chi2
  iframe Hb
  iintro %n %m %hR Hb
  rel_pures
  by_cases hn : n < 2 <;> by_cases hm : m < 2 <;>
    simp only [adaptiveCostChi2, rr3Out, hn, hm, ↓reduceIte, decide_true, decide_false,
      Bool.not_false, Bool.not_true, stageTwoCostChi2, Bool.cond_true, Bool.cond_false] at hR ⊢ <;>
    (try simp at hR) <;> rel_pures
  -- mismatched reports close by `hR`; first goal: report `false`, no second round; second goal:
  -- report `true`, spend the remaining `1/2` on the second draw
  · rel_values
  · rel_couple_UU_spend (fun r r' ↦ rr3Out false r = rr3Out true r') _
      (isAddLeftRegular_ofReal _) rr3_coupling_chi2
    iframe Hb
    iintro %r %r' %hr
    rel_pures
    by_cases hd : r < 2 <;> by_cases hd' : r' < 2 <;>
      simp only [rr3Out, hd, hd', ↓reduceIte, decide_true, decide_false, Bool.not_false,
        Bool.not_true] at hr ⊢ <;> (try simp at hr) <;> rel_pures <;> rel_values

end Logic

/-! ## Adequacy -/

/-- The adaptive program on `false` and on `true` is within χ² budget `7/12`. -/
theorem rrAdaptive_chi2 (σ σ' : State rT) :
    chi2Divergence (ofReal (7 / 12))
      (limExecV ⟨rrAdaptive false, σ⟩) (limExecV ⟨rrAdaptive true, σ'⟩) :=
  approximates_div (GF := MicrometerFunctor rT PowerBudget)
    (fun _ _ ↦ lrel_prod lrel_bool lrel_bool) _ _ σ σ' _
    (fun _ _ ↦ lrel_prod_car_eq lrel_bool_car_eq lrel_bool_car_eq)
    fun _ _ ↦ rrAdaptive_refines_chi2

/-! ## Adaptivity helps -/

/-- Two rounds at χ² `1/2` compose, non-adaptively, to `(3/2)(3/2) - 1 = 5/4`. -/
theorem ofReal_half_add_half :
    (ofReal (1 / 2) : PowerBudget) + ofReal (1 / 2) = ofReal (5 / 4) := by
  rw [← two_nsmul, nsmul_ofReal (by norm_num)]
  norm_num

/-- The adaptive χ² budget `7/12` is below the non-adaptive `5/4`. -/
theorem chi2_adaptive_lt : (ofReal (7 / 12) : PowerBudget) < ofReal (1 / 2) + ofReal (1 / 2) := by
  rw [ofReal_half_add_half]
  refine toENNReal.lt_iff_lt.1 ?_
  simp only [toENNReal_ofReal]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

end RandomizedResponse
end ProbLang
