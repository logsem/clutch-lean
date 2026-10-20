module

public import Metrology.Code.SkipZero
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.RelTactics
public import Metrology.Couplings.Divergences.Tv
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Total variation with credits: a sampler that skips `0` is at most `1/N` below uniform

The two draws are coupled along the identity; the one outcome where the programs disagree is
paid for with a credit `↯b (1/N)` in the `codensity tv` lifting. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace SkipZero

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- A uniform draw refines `skipZero`, spending `↯b (1/N)` to avoid the draw `0`. -/
theorem unif_refines_skipZero {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS ℝ≥0∞ GF] (N : Int) (hN : 0 < N) :
    ⊢@{IProp GF} ↯b (N.toNat : ℝ≥0∞)⁻¹ -∗
      REL[codensity tv] (unif (rT := rT) N) << skipZero N : lrel_int := by
  iintro Hε
  rel_apply (refines_couple_rands_lr_avoid (s := .id ℝ≥0∞) 0 hN absorbing_codensity_tv_one
    (IsAddRegular.of_ne_top (by simp [hN])).1)
  simp only [OrderAddMonoidHom.coe_id, id_eq]
  iframe Hε
  iintro %n ⟨%hn, %h0⟩
  rel_pures
  rel_values

/-- On every event, `unif N` is at most `1/N` more likely than `skipZero N`. -/
theorem unif_le_skipZero (N : Int) (hN : 0 < N) (σ σ' : State rT) {S : Set (Exp rT)}
    (hS : MeasurableSet S) :
    limExecV ⟨unif N, σ⟩ S ≤ limExecV ⟨skipZero N, σ'⟩ S + (N.toNat : ℝ≥0∞)⁻¹ :=
  tv_iff.1 (approximates_div (GF := MicrometerFunctor rT ℝ≥0∞) (L := codensity tv)
    (fun _ _ ↦ lrel_int) _ _ σ σ' _ (fun _ _ ↦ lrel_int_car_eq)
    fun _ _ ↦ unif_refines_skipZero N hN) S hS

end SkipZero
end ProbLang
