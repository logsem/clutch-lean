import MetrologyAsm.Examples.Callback.Boundary
import Metrology.Micrometer.Asm
import Metrology.Iris.LocalBI

/-! # The actual Sail import toy under the shared weakest precondition

The evaluator premises describe the `rv` machine's initial call and resumed return. -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm
open Exp (lcb_imp_lc decomp_unfold isValM_some open' openRec asValM toVal?
  asm_toVal?_eq_none asmResume_toVal?_eq_none lam app asmResume)
open Ectx (fill fillCfg fillCfg_empty fill_asmResume)
open List (map_nil mapM_nil)
open Finset (sort_empty)
open BoundaryValue (ofVal toVal)
open IsVal (lit check?)
open MeasureTheory.Measure

variable {rT : Type}

/-- The ordinary ProbLang callback returns the signed integer seven. -/
def importToyCallback : Val rT :=
  let hc : (lam (.lit (.int 7))).IsLocallyClosed := lcb_imp_lc (by rfl)
  ⟨.lam (.lit (.int 7)), .lam hc, hc⟩

/-- The explicit environment uses actual Sail and the ordinary integer callback. -/
noncomputable def importToyEnv : FfiEnv rT := ⟨rv, fun _ => importToyCallback⟩

/-- The initial replay archive records the toy's empty argument tuple and footprint. -/
def importToyArchive : Replay := ⟨importToyCode, [], [], []⟩

/-- The initial foreign expression invokes the actual assembled import toy. -/
abbrev importToyExpression : Exp rT :=
  .asm (.lit (.code importToyCode)) (.lit .unit)

/-- The paused foreign expression evaluates the ordinary callback under its resumption frame. -/
abbrev importToyPaused : Exp rT :=
  .asmResume importToyArchive (.app importToyCallback.fst (.lit .unit))

private theorem overwrite_empty {V : Type} (heap fragment : LocHeap V) :
    overwrite ∅ heap fragment = heap := by
  apply Std.ExtTreeMap.ext_getElem?
  intro l
  simp

private theorem snapshot_empty : snapshot ∅ = some [] := rfl

private theorem restore_empty : HeapSnapshot.restore [] = ∅ := rfl

/-- Returning seven with the empty footprint satisfies the toy's import response contract. -/
theorem importToy_response_ok :
    rv.ResponseOK importToyCode [] ∅ "cb" (.int 7) ∅ := by
  exact (importToy_response_iff _ _).mpr ⟨7, rfl, rfl, by decide +kernel⟩

variable (σ : State rT)

/-- The empty-footprint overwrite preserves the entire ProbLang state. -/
private theorem importToy_state_unchanged :
    σ.update_heap (fun h => overwrite ∅ h (valueHeap ∅)) = σ := by
  simp [overwrite_empty, State.update_heap]

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- The ordinary callback's actual primitive step returns seven. -/
theorem importToy_callback_step :
    primStepWith importToyEnv ⟨.app importToyCallback.fst (.lit .unit), σ⟩ =
      dirac ⟨.lit (.int 7), σ⟩ := by
  have hd : (app importToyCallback.fst (.lit .unit) : Exp rT).decomp =
      ([], .app importToyCallback.fst (.lit .unit)) := by
    rw [decomp_unfold]
    rfl
  rw [primStepWith, hd]
  change (headStep ⟨.app (.lam (.lit (.int 7))) (.lit .unit), σ⟩).map (fillCfg []) = _
  simp only [headStep, isValM_some (lit.toIsValue), open', openRec,
    fillCfg_empty, map_id]

/-- The callback reduces under the actual assembly resumption frame. -/
theorem importToy_paused_step :
    primStepWith importToyEnv ⟨importToyPaused, σ⟩ =
      dirac ⟨.asmResume importToyArchive (.lit (.int 7)), σ⟩ := by
  change primStepWith importToyEnv
    ⟨fill [.asmResume importToyArchive] (.app importToyCallback.fst (.lit .unit)), σ⟩ = _
  rw [primStepWith_fill importToyEnv _ σ (fun ⟨w⟩ => nomatch w), importToy_callback_step]
  simp [map_dirac, fillCfg, fill_asmResume]

variable {next : BoundaryValue → LocHeap BoundaryValue → Interaction BoundaryValue}
  (heval : rv.eval importToyCode [] ∅ ∅ = some (.call "cb" [] ∅ next))

include heval

/-- The actual Sail evaluator's initial call determines the foreign dispatch action. -/
theorem importToy_start_action :
    start rv importToyCode [] ∅ = .call "cb" [] ∅ importToyArchive := by
  classical
  have hc : validFragment importToyCode [] ∅ ∧ ∃ sig, ("cb", sig) ∈ importToyCode.sig.imports ∧
        check sig (boundaryArgs []) (valueHeap ∅) = true := by
    exact ⟨importToy_valid_empty, ⟨[], .int 64⟩, by simp [importToyCode], by decide +kernel⟩
  simp only [start, importToy_footprint, restrict_empty_heap]
  have hcheck : (importToyCode.sig.valid &&
      check importToyCode.sig.toCallSig (boundaryArgs []) (valueHeap ∅)) = true :=
    by decide +kernel
  simp only [hcheck, ite_true, snapshot_empty, heval,
    rootAction, ite_eq_left hc]
  rfl

/-- Starting the actual foreign expression invokes its ordinary callback without heap exchange. -/
theorem importToy_start_step :
    primStepWith importToyEnv ⟨importToyExpression, σ⟩ = dirac ⟨importToyPaused, σ⟩ := by
  change primStepWith importToyEnv ⟨.asm (.lit (.code importToyCode)) (argumentTuple []), σ⟩ = _
  rw [primStepWith_asm]
  simp only [callStep, show importToyCode.sig.args.length = ([] : List BoundaryValue).length
    from rfl, readTuple_argumentTuple, importToy_footprint, capture, footprintLocations,
    sort_empty, mapM_nil]
  change actionStep importToyEnv ∅ σ (start rv importToyCode [] ∅) = _
  rw [importToy_start_action heval]
  simp only [actionStep, importToyEnv, importToyPaused, argumentTuple,
    importToy_state_unchanged]

variable (hnext : next (.int 7) ∅ = .ret (.int 7) ∅)

include hnext

/-- Actual replay selects the evaluator's return subtree after the callback replies seven. -/
theorem importToy_resume_action : resume rv importToyArchive (.int 7) ∅ = .ret (.int 7) ∅ := by
  classical
  have ho : validFragment importToyCode [] ∅ ∧
      checkResult importToyCode.sig.toCallSig (boundaryArgs []) importToyCode.sig.result
        (BoundaryValue.int 7).toVal = true :=
    ⟨importToy_valid_empty, by decide +kernel⟩
  simp only [resume, importToyArchive, importToy_footprint, restrict_empty_heap,
    restore_empty, heval, map_nil, Interaction.replay, importToy_response_ok, ite_true,
    snapshot_empty, hnext, rootAction]
  exact ite_eq_left ho

/-- Actual assembly resumption returns seven and preserves the entire ProbLang state. -/
theorem importToy_resume_step :
    primStepWith importToyEnv ⟨.asmResume importToyArchive (.lit (.int 7)), σ⟩ =
      dirac ⟨.lit (.int 7), σ⟩ := by
  have hd : (asmResume importToyArchive (.lit (.int 7)) : Exp rT).decomp =
      ([], .asmResume importToyArchive (.lit (.int 7))) := by
    rw [decomp_unfold]
    rfl
  simp only [primStepWith, hd, headStepWith, asValM, toVal?, check?]
  simp only [resumeStep, ofVal, importToyArchive, importToy_footprint,
    capture, footprintLocations, sort_empty, mapM_nil]
  change (actionStep importToyEnv ∅ σ (resume rv importToyArchive (.int 7) ∅)).map (fillCfg []) = _
  rw [importToy_resume_action heval hnext]
  simp only [actionStep, toVal, importToy_state_unchanged,
    fillCfg_empty, map_id]

open Iris Iris.BI Iris.ProofMode MicrometerWpGS

variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsTopAbsorbing]
  {E : CoPset} {Φ : Val rT → IProp GF}

local bi IProp GF

/-- The actual Sail import toy, given its evaluator premises, satisfies the shared `wp`. -/
theorem wp_importToy_of_eval : iprop%
    ▷ ▷ ▷ Φ (.int 7) ⊢ wpFor (primStepWith importToyEnv) L E importToyExpression Φ := by
  iintro HΦ
  iapply wpFor_pure_step asm_toVal?_eq_none (fun σ => importToy_start_step σ heval)
  iintro !>
  iapply wpFor_pure_step asmResume_toVal?_eq_none (fun σ => importToy_paused_step σ)
  iintro !>
  iapply wpFor_pure_step asmResume_toVal?_eq_none (fun σ => importToy_resume_step σ heval hnext)
  iintro !>
  iapply wpFor_value_of_toVal (by rfl)
  iexact HΦ

end MetrologyAsm
