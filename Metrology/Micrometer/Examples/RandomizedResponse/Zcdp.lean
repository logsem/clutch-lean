module

public import Metrology.Micrometer.Examples.RandomizedResponse.Basic
public import Metrology.Couplings.Divergences.RenyiFiber

@[expose] public section

/-! # Randomized response is zCDP

One round couples in `zcdpLifting` at `(ln 3, 0)` (`rrCoupling_zcdp`), so `k` rounds are
`(k ln 3, 0)`-zCDP (`rrCount_zCDP`). -/

open GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang.RandomizedResponse

/-- One round couples at `(ln 3, 0)`: each report is at most three times likelier under one bit. -/
theorem rrCoupling_zcdp : RRCoupling zcdpLifting budget := fun b b' ↦
  zcdpLifting_rel_of_fiber .of_discrete .of_discrete fun c ↦
    expBudget_log_three ▸ rrOut_fiber_le_three b b' c

/-- `k` rounds are `(k ln 3, 0)`-zCDP (Def. 2.4). -/
theorem rrCount_zCDP {rT : Type} [LawfulProbLangℝ rT] (k : ℕ)
    (σ : State rT) : (rrCountMech k σ).zCDP ⊤ (k * ENNReal.ofReal (Real.log 3)) 0 := by
  simpa [nsmul_eq_mul] using rrCount_isPrivate budget isAddLeftRegular_budget rrCoupling_zcdp k σ

end ProbLang.RandomizedResponse
