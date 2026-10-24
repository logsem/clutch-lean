module

public import Metrology.Code.SumPerm
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.Fundamental
public import Metrology.Couplings.Divergences.FillKl
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # The sum of two random permutations is a good PRF (skeleton)

Dai, Hoang and Tessaro's chi-squared method (ePrint 2017/537, Lemma 3 and Thm. 4): the
query-bounded `sumPerm` refines the query-bounded random function within filled KL `2 Q³ / N³`
(`bounded_refines`, `sorry`), so does every typed adversary's game (`game_refines`), and by Pinsker
(`le_add_sqrt_of_fill_kl`, `sorry`) every event moves by at most `(Q / N)^{3/2}` (`sumPerm_prf`). -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open MeasureTheory (Measure)
open scoped ENNReal

namespace ProbLang
namespace SumPerm

open Switching

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-! ## Pinsker -/

/-- Pinsker's inequality for filled KL, read on events: within filled KL `c`, an event's
probability moves by at most `√(c / 2)`. -/
theorem le_add_sqrt_of_fill_kl {X : Type} [MeasurableSpace X] {μ ν : Measure X} {c : ℝ≥0∞}
    (hc : c ≠ ∞) (h : klDivergence.fill c μ ν) {S : Set X} (hS : MeasurableSet S) :
    μ S ≤ ν S + ENNReal.ofReal √(c.toReal / 2) := by
  sorry

/-! ## The coupled games -/

/-- The filled-KL budget `2 Q³ / N³`: Lemma 3 with `E[χ²] ≤ 2 (i - 1)² / N³` at query `i`. -/
noncomputable def budget (N Q : Int) : ℝ≥0∞ := 2 * (Q.toNat : ℝ≥0∞) ^ 3 / (N.toNat : ℝ≥0∞) ^ 3

/-- The adversary's type: a query-bounded oracle `int → unit + int` to a boolean guess. -/
def advTy : Ty := .arrow (.arrow .int (.sum .unit .int)) .bool

section Games

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS ℝ≥0∞ GF]
  (N Q : Int)
local bi IProp GF

/-- The query-bounded `sumPerm` refines the query-bounded random function within filled KL
`budget N Q`, for `16 Q ≤ N`. -/
theorem bounded_refines (hQ : 0 ≤ Q) (hQN : 16 * Q ≤ N) :
    ⊢ ↯b (budget N Q) -∗
      REL[codensity klDivergence.fill] pl(&bounded #Q {sumPerm (rT := rT) N}) <<
        pl(&bounded #Q {randomFunction N}) :
          lrel_arr (codensity klDivergence.fill) lrel_int (lrel_sum lrel_unit lrel_int) := by
  sorry

/-- Every typed adversary's real game refines its ideal game within filled KL `budget N Q`. -/
theorem game_refines (hQ : 0 ≤ Q) (hQN : 16 * Q ≤ N) {A : Exp rT} (hA : Typed .empty A advTy) :
    ⊢ ↯b (budget N Q) -∗
      REL[codensity klDivergence.fill] realGame N Q A << idealGame N Q A : lrel_bool := by
  have HA := refines_typed (L := codensity klDivergence.fill) (default : TyEnv rT GF) hA
  simp only [advTy, interp_arrow, interp_sum, interp_int, interp_unit, interp_bool] at HA
  unfold realGame idealGame
  iintro Hb
  ihave HA' := HA
  iapply refines_app $$ HA'
  iapply bounded_refines N Q hQ hQN $$ Hb

end Games

/-! ## Adequacy -/

section AdequacyCor

variable (N Q : Int) {A : Exp rT} (σ σ' : State rT)

/-- Adequacy of `game_refines`: the two games are within filled KL `budget N Q`. -/
theorem game_fillKl (hQ : 0 ≤ Q) (hQN : 16 * Q ≤ N) (hA : Typed .empty A advTy) :
    klDivergence.fill (budget N Q) (limExecV ⟨realGame N Q A, σ⟩)
      (limExecV ⟨idealGame N Q A, σ'⟩) :=
  approximates_div (GF := MicrometerFunctor rT ℝ≥0∞) (fun _ _ ↦ lrel_bool) _ _ σ σ' _
    (fun _ _ ↦ lrel_bool_car_eq) fun _ _ ↦ game_refines N Q hQ hQN hA

/-- The sum of two random permutations is a PRF: against any typed adversary making at most `Q`
queries, any event's probability moves by at most `√(budget N Q / 2) = (Q / N)^{3/2}`. -/
theorem sumPerm_prf (hN : 0 < N) (hQ : 0 ≤ Q) (hQN : 16 * Q ≤ N) (hA : Typed .empty A advTy)
    {S : Set (Exp rT)} (hS : MeasurableSet S) :
    limExecV ⟨realGame N Q A, σ⟩ S ≤
      limExecV ⟨idealGame N Q A, σ'⟩ S + ENNReal.ofReal √((budget N Q).toReal / 2) :=
  le_add_sqrt_of_fill_kl
    (by simp [budget, ENNReal.div_eq_top, ENNReal.mul_eq_top, Int.pos_iff_toNat_pos.1 hN |>.ne'])
    (game_fillKl N Q σ σ' hQ hQN hA) hS

end AdequacyCor

end SumPerm
end ProbLang
