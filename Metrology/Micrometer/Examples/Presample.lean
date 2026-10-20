module

public import Metrology.Code.Presample
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.RelTactics
public import Metrology.Couplings.Divergences.Tv
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Presampling with tapes: the order of two labelled draws does not matter

Main result: `drawAB_refines_drawBA` (drawing from tape `α` then `β` refines the reverse order), and
by adequacy at `codensity tv`, `drawAB_le_drawBA`. The reverse direction is the same proof. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace Presample

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

section Rel

variable {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
  [BudgetCreditGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]
  [L.HasBind]

/-- A draw from a fresh tape refines a plain draw. -/
theorem drawTape_refines_draw (N : Int) (hN : 0 < N) :
    ⊢@{IProp GF} REL[L] (drawTape (rT := rT) N) << draw N : lrel_int := by
  rel_alloctape_l α as Hα
  rel_pures
  rel_couple_TU α
  iframe Hα
  iintro %n Hα %_
  rel_values

/-- Drawing from `α` then `β` refines drawing from `β` then `α`, at budget `0`.
Both tapes are presampled, each left tape coupled with its right twin along `id`, before either
program draws; afterwards every draw only reads its tape. -/
theorem drawAB_refines_drawBA (N : Int) (hN : 0 < N) :
    ⊢@{IProp GF} REL[L] (drawAB (rT := rT) N) << drawBA N : lrel_prod lrel_int lrel_int := by
  rel_alloctape_l α as Hα
  rel_alloctape_r α' as Hα'
  rel_alloctape_l β as Hβ
  rel_alloctape_r β' as Hβ'
  iapply refines_couple_tapes_bij id id_dom_range id_bij_range hN
  iframe Hα Hα'
  iintro %x %_ Hα Hα'
  iapply refines_couple_tapes_bij id id_dom_range id_bij_range hN
  iframe Hβ Hβ'
  iintro %y %_ Hβ Hβ'
  simp only [List.nil_append, id_eq]
  rel_rand_l
  iintro %_
  rel_rand_l
  iintro %_
  rel_rand_r
  iintro %_
  rel_rand_r
  iintro %_
  rel_pures
  rel_values

end Rel

/-! ## Adequacy: from the refinement to a bound on executions -/

/-- On every event, drawing in the order `α, β` is at most as likely as in the order `β, α`. -/
theorem drawAB_le_drawBA (N : Int) (hN : 0 < N) (σ σ' : State rT) {S : Set (Exp rT)}
    (hS : MeasurableSet S) :
    limExecV ⟨drawAB N, σ⟩ S ≤ limExecV ⟨drawBA N, σ'⟩ S := by
  simpa using tv_iff.1 (approximates_div (GF := MicrometerFunctor rT ℝ≥0∞) (L := codensity tv)
    (fun _ _ ↦ lrel_prod lrel_int lrel_int) _ _ σ σ' 0
    (fun _ _ ↦ lrel_prod_car_eq lrel_int_car_eq lrel_int_car_eq)
    fun _ _ ↦ by iintro -; iapply drawAB_refines_drawBA N hN) S hS

end Presample
end ProbLang
