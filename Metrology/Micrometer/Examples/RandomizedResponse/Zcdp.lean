module

public import Metrology.Micrometer.Examples.RandomizedResponse.Basic
public import Metrology.Couplings.Divergences.RenyiFiber

@[expose] public section

/-! # Randomized response is zCDP

One round couples in the zCDP lifting at `(ln 3, 0)`, so `k` rounds are `(k ln 3, 0)`-zCDP. -/

open GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

/-- The two draws couple along equal reports in the zCDP lifting at `(ln 3, 0)`. -/
theorem rr_zcdp_coupling (b b' : Bool) :
    zcdpLifting.Rel budget (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) :=
  zcdpLifting_rel_of_fiber .of_discrete .of_discrete fun c ↦
    expBudget_log_three ▸ rrOut_fiber_le_three b b' c

/-- `k` rounds are `(k ln 3, 0)`-zCDP (Def. 2.4). -/
theorem rrCount_zCDP {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] (k : ℕ)
    (σ : State rT) : (rrCountMech k σ).zCDP ⊤ (k * ENNReal.ofReal (Real.log 3)) 0 := by
  simpa [nsmul_eq_mul] using
    rrCount_isPrivate (L := zcdpLifting) budget isAddLeftRegular_budget rr_zcdp_coupling k σ

end RandomizedResponse
end ProbLang
