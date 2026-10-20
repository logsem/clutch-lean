module

public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.RelTactics
public import Metrology.Micrometer.CappedCredits
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # The absorbing exit: an exhausted budget proves anything

`refines_of_absorbing` proves even the false refinement `0 << 1` from `↯b` at an absorbing budget
(`δ ≥ 1` for DP, `1` for tv); with capped credits `↯c` such a budget is contradictory. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace AbsorbingExit

variable {rT : Type} [LawfulProbLangℝ rT] {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]

/-- With `↯b (ε, δ)` for `δ ≥ 1`, `0` refines `1` at equal integers. -/
theorem zero_refines_one_dp [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] {ε δ : ℝ≥0∞} (hδ : 1 ≤ δ) :
    ↯b (ε, δ) ⊢@{IProp GF} REL[codensity dp] (pl(#0) : Exp rT) << pl(#1) : lrel_int :=
  refines_of_absorbing (absorbing_codensity_dp_iff.2 (.inr hδ))

/-- With `↯b 1`, `0` refines `1` at equal integers in the total variation lifting. -/
theorem zero_refines_one_tv [BudgetCreditGS ℝ≥0∞ GF] :
    ↯b (1 : ℝ≥0∞) ⊢@{IProp GF} REL[codensity tv] (pl(#0) : Exp rT) << pl(#1) : lrel_int :=
  refines_of_absorbing absorbing_codensity_tv_one

/-- In the capped view, a DP credit with `δ ≥ 1` is contradictory, so it proves anything. -/
theorem capped_dp_exit {GF : BundledGFunctors}
    [CappedCreditGS (ℝ≥0∞ × ℝ≥0∞) {b | (codensity dp.{0}).Absorbing b} GF] {ε δ : ℝ≥0∞}
    (hδ : 1 ≤ δ) (P : IProp GF) : ↯c (ε, δ) ⊢ P :=
  (CappedCredit.dp_contradict_of_one_le hδ).trans false_elim

/-- A capped credit is valid exactly when its budget is not absorbing. -/
theorem capped_valid {GF : BundledGFunctors}
    [CappedCreditGS (ℝ≥0∞ × ℝ≥0∞) {b | (codensity dp.{0}).Absorbing b} GF]
    (b : ℝ≥0∞ × ℝ≥0∞) : ↯c b ⊢@{IProp GF} ⌜¬(codensity dp.{0}).Absorbing b⌝ :=
  CappedCredit.valid (bad := {b | (codensity dp.{0}).Absorbing b})

end AbsorbingExit
end ProbLang
