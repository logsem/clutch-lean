module

public import Metrology.Micrometer.Examples.RandomizedResponse.Renyi

@[expose] public section

/-! # The whole Rényi profile of randomized response

One round couples at the curve `α ↦ ρ_α`, order by order, so `k` rounds are private for
`α ↦ k ρ_α`; every `ρ_α ≤ ln 3`, so this lies below the zCDP line `(k ln 3, 0)`. -/

open MeasureTheory GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

/-- The Rényi profile of one round, as a curve. -/
noncomputable def rrCurve : RenyiBudget :=
  fun α ↦ rrRenyi α

/-- The curve is finite at every order, so it can be spent. -/
theorem isAddLeftRegular_rrCurve : IsAddLeftRegular rrCurve := fun _ _ h ↦
  funext fun α ↦ (IsAddRegular.of_ne_top ENNReal.ofReal_ne_top).1 (congrFun h α)

/-- The two draws couple along equal reports at the curve: couple at each order. -/
theorem rr_curve_coupling (b b' : Bool) :
    (codensity renyiCurve).Rel rrCurve (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) :=
  codensity_renyiCurve_iff.2 fun α ↦ by
    have hcost : (fun r r' ↦ (relCost (fun r r' ↦ rrOut b r = rrOut b' r') r r' : RenyiBudget) α) =
        relCost fun r r' ↦ rrOut b r = rrOut b' r' := by
      ext r r'
      by_cases h : rrOut b r = rrOut b' r' <;> simp [h]
    rw [hcost]
    exact rr_renyi_coupling α b b'

/-- The Rényi profile of one round is at most `ln 3` at every order: `(3^α + 3^{1-α}) / 4` is at
most `3^{α-1}`. -/
theorem rrRenyi_le_log_three {α : ℝ} (hα : 1 < α) :
    rrRenyi α ≤ ENNReal.ofReal (Real.log 3) := by
  have hpos : (0 : ℝ) < 3 ^ α := by positivity
  have ht : (3 : ℝ) ≤ 3 ^ α := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hα.le
  refine ENNReal.ofReal_le_ofReal ((div_le_iff₀ (by linarith)).2 ?_)
  rw [mul_comm, ← Real.log_rpow (by norm_num)]
  refine Real.log_le_log (by positivity) ?_
  rw [Real.rpow_sub (by norm_num), Real.rpow_sub_one (by norm_num), Real.rpow_one,
    div_le_div_iff₀ (by norm_num) (by norm_num)]
  have : (3 : ℝ) / 3 ^ α ≤ 3 ^ α / 3 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    nlinarith
  linarith

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- `k` rounds are private for the Rényi curve `α ↦ k ρ_α`. -/
theorem rrCount_curve (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).IsPrivate renyiCurve ⊤ fun α ↦ k * rrRenyi α := by
  convert rrCount_isPrivate (L := codensity renyiCurve) (D := renyiCurve) rrCurve
    isAddLeftRegular_rrCurve rr_curve_coupling k σ using 1
  ext α
  simp [rrCurve]

/-- The curve lies below the zCDP line `(k ln 3, 0)`, so `k` rounds are `(k ln 3, 0)`-zCDP
(Def. 2.4). -/
theorem rrCount_zCDP_of_curve (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).zCDP ⊤ (k * ENNReal.ofReal (Real.log 3)) 0 := fun b b' h ↦ by
  have hle : (fun α ↦ k * rrRenyi α : RenyiBudget) ≤
      concentratedLine (Set.Ioi 1) (k * ENNReal.ofReal (Real.log 3), 0) := fun α ↦ by
    simpa [concentratedLine, α.2] using mul_le_mul' le_rfl (rrRenyi_le_log_three α.2)
  exact IsGraded.mono (D := renyiCurve) (μ := limExecV ⟨rrCount b k, σ⟩)
    (ν := limExecV ⟨rrCount b' k, σ⟩) hle (rrCount_curve k σ h)

end RandomizedResponse
end ProbLang
