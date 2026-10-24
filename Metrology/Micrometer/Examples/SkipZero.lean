module

public import Metrology.Code.SkipZero
public import Metrology.Micrometer.AdequacyTV
public import Metrology.Micrometer.RelTactics
public import Metrology.Couplings.Divergences.Tv
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Skip-zero sampler within `1/N` of uniform in total variation

`skipZero N` (uniform with `0` reported as `1`) is within `1/N` tv of `unif N`
(`unif_refines_skipZero`). -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace SkipZero

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS ℝ≥0∞ GF]
local bi IProp GF

/-- A uniform draw refines `skipZero` in `codensity tv`, spending `↯b (1/N)` to avoid `0`. -/
theorem unif_refines_skipZero (N : Int) (hN : 0 < N) :
    ⊢ ↯b (N.toNat : ℝ≥0∞)⁻¹ -∗
      REL[codensity tv] (unif (rT := rT) N) << skipZero N : lrel_int := by
  iintro Hε
  -- couple the two draws along the identity, using the credit to rule out `0` on the left
  rel_apply (refines_couple_rands_lr_avoid (s := .id ℝ≥0∞) 0 hN absorbing_codensity_tv_one
    (IsAddRegular.of_ne_top (by simp [hN])).1)
  simp only [OrderAddMonoidHom.coe_id, id_eq]
  iframe Hε
  iintro %n ⟨%hn, %h0⟩
  -- `n ≠ 0`, so `skipZero`'s branch returns `n` too
  rel_pures
  rel_values

/-- On every event, `unif N` is at most `1/N` more likely than `skipZero N`: the tv bound,
read off `unif_refines_skipZero` by adequacy. -/
theorem unif_le_skipZero (N : Int) (hN : 0 < N) (σ σ' : State rT) {S : Set (Exp rT)}
    (hS : MeasurableSet S) :
    limExecV ⟨unif N, σ⟩ S ≤ limExecV ⟨skipZero N, σ'⟩ S + (N.toNat : ℝ≥0∞)⁻¹ :=
  limExecV_le_add_of_refines_tv (GF := MicrometerFunctor rT ℝ≥0∞)
    (fun _ _ ↦ lrel_int) _ _ σ σ' _ (fun _ _ ↦ lrel_int_car_eq)
    (fun _ _ ↦ unif_refines_skipZero N hN) hS

end SkipZero
end ProbLang
