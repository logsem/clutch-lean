module

public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.RelTactics
public import Metrology.Micrometer.CappedCredits
import Metrology.Iris.LocalBI
import Metrology.ProbLang.Syntax.Notation

/-! # The absorbing exit: an exhausted budget proves anything

`refines_of_absorbing` proves even the false refinement `0 << 1` from an absorbing budget `↯b`. -/

@[expose] public section

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace AbsorbingExit

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT] {GF : BundledGFunctors}
  [MicrometerRGS rT .hasNoLC GF]
local bi IProp GF

/-- With `↯b (ε, δ)` for `δ ≥ 1`, `0` refines `1` at equal integers. -/
theorem zero_refines_one_dp [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] {ε δ : ℝ≥0∞} (hδ : 1 ≤ δ) :
    ↯b (ε, δ) ⊢ REL[codensity dp] (pl(#0) : Exp rT) << pl(#1) : lrel_int :=
  refines_of_absorbing (absorbing_codensity_dp_iff.2 (.inr hδ))

/-- With `↯b 1`, `0` refines `1` at equal integers in the total variation lifting. -/
theorem zero_refines_one_tv [BudgetCreditGS ℝ≥0∞ GF] :
    ↯b (1 : ℝ≥0∞) ⊢ REL[codensity tv] (pl(#0) : Exp rT) << pl(#1) : lrel_int :=
  refines_of_absorbing absorbing_codensity_tv_one

open CappedCredit

variable [CappedCreditGS (ℝ≥0∞ × ℝ≥0∞) {b | (codensity dp.{0}).Absorbing b} GF]

/-- In the capped view, a DP credit with `δ ≥ 1` is contradictory, so it proves anything. -/
theorem capped_dp_exit {ε δ : ℝ≥0∞} (hδ : 1 ≤ δ) (P : _) : ↯c (ε, δ) ⊢ P :=
  (dp_contradict_of_one_le hδ).trans false_elim

/-- A capped credit entails that its budget is not absorbing. -/
theorem capped_valid (b : ℝ≥0∞ × ℝ≥0∞) : ↯c b ⊢ ⌜¬(codensity dp.{0}).Absorbing b⌝ :=
  valid

end AbsorbingExit
end ProbLang
