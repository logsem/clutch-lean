module

public import Metrology.Micrometer.Examples.RandomizedResponse.Basic
public import Metrology.Couplings.Divergences.FillKl
public import Metrology.Couplings.Divergences.RenyiFiber

@[expose] public section

/-! # Randomized response in filled KL

One round is within KL `(log 3) / 2` (`klDivergence_rrOut`), so it couples at that budget in
`codensity (fill klDivergence)`, and `k` rounds are `k (log 3) / 2`-private in filled KL. -/

open MeasureTheory ProbabilityTheory GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang.RandomizedResponse

/-- The reports on different bits are `(3/4, 1/4)` and `(1/4, 3/4)`, at KL `(log 3) / 2`. -/
theorem klDivergence_rrOut (b : Bool) :
    klDivergence (ENNReal.ofReal (Real.log 3 / 2)) (draw.map (rrOut b)) (draw.map (rrOut !b)) := by
  have hl : Real.log (1 / 3) = - Real.log 3 := by rw [one_div, Real.log_inv]
  rw [klDivergence_iff_fDiv, fDiv_klFun_eq_sum _ _ fun c ↦ by
      rw [map_rrOut_singleton, map_rrOut_singleton]; split_ifs <;> norm_num,
    EReal.coe_ennreal_ofReal, max_eq_left (by positivity), EReal.coe_le_coe_iff,
    Fintype.sum_bool, map_rrOut_singleton, map_rrOut_singleton, map_rrOut_singleton,
    map_rrOut_singleton]
  cases b <;> norm_num [klTerm, div_div_div_cancel_right₀, hl] <;> linarith

/-- One round couples the draws at `(log 3) / 2` in the filled-KL codensity lifting: lift equal
reports from the KL bound by binding the fibers. -/
theorem rrCoupling_fillKl :
    RRCoupling (codensity klDivergence.fill) (ENNReal.ofReal (Real.log 3 / 2)) := fun b b' ↦ by
  refine codensity_rel_of_map .of_discrete .of_discrete
    (fun c h ↦ absurd h (ne_of_gt (lt_of_lt_of_le (by norm_num) (rrOut_fiber_ge b' c)))) ?_
  rw [fill_kl_iff_of_isProbabilityMeasure]
  rcases Bool.eq_or_eq_not b' b with rfl | rfl
  exacts [IsGraded.mono zero_le (IsReflexive.refl _), klDivergence_rrOut b]

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- `k` rounds are `k (log 3) / 2`-private in filled KL. -/
theorem rrCount_fillKl (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).IsPrivate klDivergence.fill ⊤ (k • ENNReal.ofReal (Real.log 3 / 2)) :=
  rrCount_isPrivate _ (ENNReal.isAddLeftRegular_ofReal _) rrCoupling_fillKl k σ

end ProbLang.RandomizedResponse
