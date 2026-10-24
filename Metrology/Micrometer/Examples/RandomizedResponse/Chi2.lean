module

public import Metrology.Micrometer.Examples.RandomizedResponse.Renyi
public import Metrology.Couplings.Divergences.Power

@[expose] public section

/-! # Randomized response has χ² divergence at most `(7/3)^k - 1`

χ² is Rényi-2 read through `c ↦ log (1 + c)`, so the generic loop theorem applies with the
budget type `PowerBudget`, where `k` rounds cost `(1 + c)^k - 1`; one round has χ² `4/3`. -/

open GradedLifting GradedDivergence PowerBudget

namespace ProbLang.RandomizedResponse

open Real (rpow_two rpow_neg_one)

/-- One round has second moment `(3² + 3⁻¹) / 4 = 7/3`, and χ² `4/3`. -/
theorem chi2Divergence_rrOut (b : Bool) :
    chi2Divergence (.ofReal (4 / 3)) (draw.map (rrOut b)) (draw.map (rrOut !b)) :=
  (powerDivergence_ofReal_iff one_lt_two (by norm_num)).2 <| by
    rw [fDiv_rrOut one_lt_two]
    norm_num [rpow_two, rpow_neg_one]

/-- One round couples at χ² `4/3`, which is Rényi-2 at `log (1 + 4/3)`. -/
theorem rrCoupling_chi2 : RRCoupling chi2Lifting (.ofReal (4 / 3)) := fun b b' ↦
  chi2Lifting_rel_iff.2 <|
    rrCoupling_of_renyi (fun b ↦ chi2Divergence_iff_renyi.1 (chi2Divergence_rrOut b)) b b'

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- `k` rounds have χ² divergence at most `(7/3)^k - 1`. -/
theorem rrCount_chi2 (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).IsPrivate chi2Divergence ⊤ (.ofReal ((7 / 3) ^ k - 1)) := by
  -- generic loop bound costs `k • (4/3)` in `PowerBudget`, which is `(7/3)^k - 1`
  convert rrCount_isPrivate (D := chi2Divergence) _ (isAddLeftRegular_ofReal _)
    rrCoupling_chi2 k σ using 1
  norm_num [nsmul_ofReal]

end ProbLang.RandomizedResponse
