module

public import Metrology.Micrometer.Examples.RandomizedResponse.Renyi

@[expose] public section

/-! # Randomized response at the whole Rényi curve

One round couples at the curve `α ↦ ρ_α` order by order, so `k` rounds are private for `α ↦ k ρ_α`
(`rrCount_curve`); as `ρ_α ≤ ln 3`, this lies below the zCDP line, giving `(k ln 3, 0)`-zCDP. -/

open ProbabilityTheory GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang.RandomizedResponse

open ENNReal (ofReal ofReal_ne_top)
open Real (log)

/-! ## One round at every order -/

/-- The Rényi profile `α ↦ ρ_α` of one round, as a budget curve. -/
noncomputable def rrCurve : RenyiBudget := fun α ↦ rrRenyi α

/-- The curve is finite at every order. -/
theorem isAddLeftRegular_rrCurve : IsAddLeftRegular rrCurve := fun _ _ h ↦
  funext fun α ↦ (IsAddRegular.of_ne_top ofReal_ne_top).1 (congrFun h α)

/-- One round couples at the curve: the coupling holds at each order `α` separately. -/
theorem rrCoupling_curve : RRCoupling (codensity renyiCurve) rrCurve := fun b b' ↦
  codensity_renyiCurve_iff.2 fun α ↦ by
    simp only [relCost_renyiBudget_apply]
    exact rrCoupling_renyi b b'

/-! ## `k` rounds -/

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT] (k : ℕ) (σ : State rT)

/-- `k` rounds are private for the Rényi curve `α ↦ k ρ_α`. -/
theorem rrCount_curve : (rrCountMech k σ).IsPrivate renyiCurve ⊤ fun α ↦ k * rrRenyi α := by
  convert rrCount_isPrivate (D := renyiCurve) rrCurve
    isAddLeftRegular_rrCurve rrCoupling_curve k σ using 1
  ext α
  simp [rrCurve]

/-! ## Below the zCDP line -/

/-- One round couples at `(ln 3, 0)` in the zCDP lifting. -/
theorem rrCoupling_zcdp_of_curve : RRCoupling zcdpLifting rrBudget := fun b b' ↦
  concentratedLifting_rel_of_renyiCurve_le (rrCoupling_curve b b') fun α _ ↦ by
    simpa [rrCurve] using rrRenyi_le_log_three α.2

/-- `k` rounds are `(k ln 3, 0)`-zCDP (Def. 2.4). -/
theorem rrCount_zCDP_of_curve : (rrCountMech k σ).zCDP ⊤ (k * ofReal (log 3)) 0 :=
  Kernel.zCDP_of_renyiCurve_le (rrCount_curve k σ) fun α ↦ by
    simpa using mul_le_mul' le_rfl (rrRenyi_le_log_three α.2)

end ProbLang.RandomizedResponse
