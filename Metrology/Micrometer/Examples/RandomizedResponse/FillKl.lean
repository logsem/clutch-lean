module

public import Metrology.Micrometer.Examples.RandomizedResponse.Renyi
public import Metrology.Micrometer.Examples.RandomizedResponse.Zcdp
public import Metrology.Couplings.Divergences.RenyiFillKl

@[expose] public section

/-! # Randomized response in filled KL

One round is within KL `(log 3) / 2` (`klDivergence_rrOut`), so it couples at that budget in
`codensity (fill klDivergence)`, and `k` rounds are `k (log 3) / 2`-private in filled KL.

The same coupling can be read off the Rényi and zCDP ones, since the draw is a probability measure:
`k ρ_α` for every order `α > 1` (`rrCount_fillKl_of_renyi`) and `k ln 3` (`rrCount_fillKl_of_zcdp`).
Both are weaker than `rrCount_fillKl`: `ρ_α` decreases to the KL cost `(log 3) / 2` as `α → 1`, and
the zCDP line pays the DP cost `ln 3`, twice the KL cost. -/

open MeasureTheory ProbabilityTheory GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang.RandomizedResponse

open ENNReal (ofReal ofReal_le_ofReal isAddLeftRegular_ofReal)
open Real (log log_inv log_nonneg)
open EReal (coe_ennreal_ofReal coe_le_coe_iff)

/-- The reports on different bits are `(3/4, 1/4)` and `(1/4, 3/4)`, at KL `(log 3) / 2`. -/
theorem klDivergence_rrOut (b : Bool) :
    klDivergence (ofReal (log 3 / 2)) (draw.map (rrOut b)) (draw.map (rrOut !b)) := by
  have hl : log (1 / 3) = - log 3 := by rw [one_div, log_inv]
  rw [klDivergence_iff_fDiv, fDiv_klFun_eq_sum _ _ fun c ↦ by
      rw [map_rrOut_singleton, map_rrOut_singleton]; split_ifs <;> norm_num,
    coe_ennreal_ofReal, max_eq_left (by positivity), coe_le_coe_iff,
    Fintype.sum_bool, map_rrOut_singleton, map_rrOut_singleton, map_rrOut_singleton,
    map_rrOut_singleton]
  cases b <;> norm_num [klTerm, div_div_div_cancel_right₀, hl] <;> linarith

/-- One round couples the draws at `(log 3) / 2` in the filled-KL codensity lifting: lift equal
reports from the KL bound by binding the fibers. -/
theorem rrCoupling_fillKl :
    RRCoupling (codensity klDivergence.fill) (ofReal (log 3 / 2)) := fun b b' ↦ by
  refine codensity_rel_of_map .of_discrete .of_discrete
    (fun c h ↦ absurd h (ne_of_gt (lt_of_lt_of_le (by norm_num) (rrOut_fiber_ge b' c)))) ?_
  rw [fill_kl_iff_of_isProbabilityMeasure]
  rcases Bool.eq_or_eq_not b' b with rfl | rfl
  exacts [IsGraded.mono zero_le (IsReflexive.refl _), klDivergence_rrOut b]

variable {rT : Type} [LawfulProbLangℝ rT] (α : ℝ) [Fact (1 < α)]
  (k : ℕ) (σ : State rT)

/-- `k` rounds are `k (log 3) / 2`-private in filled KL. -/
theorem rrCount_fillKl : (rrCountMech k σ).IsPrivate klDivergence.fill ⊤ (k • ofReal (log 3 / 2)) :=
  rrCount_isPrivate _ (isAddLeftRegular_ofReal _) rrCoupling_fillKl k σ

/-! ## Read off the Rényi and zCDP couplings -/

/-- One round couples at `ρ_α` in filled KL, read off the Rényi coupling. -/
theorem rrCoupling_fillKl_of_renyi :
    RRCoupling (codensity klDivergence.fill) (rrRenyi α) := fun b b' ↦
  codensity_fill_kl_rel_of_renyi_of_isProbabilityMeasure (rrCoupling_renyi b b')

/-- One round couples at `ln 3` in filled KL, read off the zCDP coupling at `(ln 3, 0)`. -/
theorem rrCoupling_fillKl_of_zcdp :
    RRCoupling (codensity klDivergence.fill) (ofReal (log 3)) := fun b b' ↦ by
  simpa using codensity_fill_kl_rel_of_zcdp_of_isProbabilityMeasure (rrCoupling_zcdp b b')

/-- `k` rounds are `k ρ_α`-private in filled KL, for every order `α > 1`. -/
theorem rrCount_fillKl_of_renyi : (rrCountMech k σ).IsPrivate klDivergence.fill ⊤ (k • rrRenyi α) :=
  rrCount_isPrivate _ (isAddLeftRegular_ofReal _) (rrCoupling_fillKl_of_renyi α) k σ

/-- `k` rounds are `k ln 3`-private in filled KL, through zCDP. -/
theorem rrCount_fillKl_of_zcdp :
    (rrCountMech k σ).IsPrivate klDivergence.fill ⊤ (k • ofReal (log 3)) :=
  rrCount_isPrivate _ (isAddLeftRegular_ofReal _) rrCoupling_fillKl_of_zcdp k σ

/-- The direct filled-KL budget `(log 3) / 2` is half the one read off zCDP. -/
theorem rrFillKl_le_zcdp : ofReal (log 3 / 2) ≤ ofReal (log 3) :=
  ofReal_le_ofReal (half_le_self (log_nonneg (by norm_num)))

end ProbLang.RandomizedResponse
