module

public import Metrology.Micrometer.Asm
import Metrology.Iris.LocalBI

/-! # A one-import assembly call through the shared weakest precondition -/

@[expose] public section

namespace ProbLang.AsmImports

open Iris Iris.Std Iris.ProofMode MicrometerWpGS BIFUpdate Asm
open LawfulSet (empty_subset)
open AsmSemantics (canonicalize eval_eq_some)
open HeapSnapshot (restore)
open Interaction (replay)
open Exp (lcb_imp_lc decomp_unfold isValM_some open' openRec asValM toVal?
  asm_toVal?_eq_none asmResume_toVal?_eq_none)
open Ectx (fillCfg_empty fill_asmResume)
open MeasureTheory.Measure

/-- A one-cell assembly contract with one integer-valued import. -/
def code : Code :=
  { prog := ⟨[], "toy"⟩
    sig := { args := [.array 8 (.const 1)], result := .int 64
             imports := [("echo", ⟨[], .int 64⟩)] } }

/-- The pointer argument identifying the toy call's owned cell. -/
def args : List BoundaryValue := [.loc 1]

/-- The integer fragment at the toy call's unique owned location. -/
def heap (z : Int) : LocHeap BoundaryValue := integerHeap {1} (fun _ => z)

/-- The observable stop of the toy's initial or resumed machine state. -/
def stop : Option (BoundaryValue × LocHeap BoundaryValue) → Stop BoundaryValue
  | none => .call "echo" [] (heap 22)
  | some (r, h) => .ret r h

/-- A two-phase machine that updates its cell before one callback and returns the reply. -/
def machine : AsmSemantics Code BoundaryValue where
  Mach := Option (BoundaryValue × LocHeap BoundaryValue)
  runs := fun _ _ t Q => Q t
  Compat := fun _ _ _ _ t => t = none
  ExitCompat := fun _ _ _ _ _ t' s => s = stop t'
  Resume := fun _ _ _ _ t r h t' => t = none ∧ t' = some (r, h)
  ResponseOK := boundaryResponseOK
  invalidResult := .unit

/-- The toy machine has deterministic stops and accepts every representable resumption. -/
theorem machine_lawful : LawfulAsmSemantics machine where
  runs_agree _ _ t _ _ hQ hR := ⟨t, hQ, hR⟩
  exit_det _ _ _ _ _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  resume_nonempty := by
    intro ι c entryArgs F t t' name vs h r h' hs hr
    cases t' with
    | none => exact ⟨some (r, h'), rfl, rfl⟩
    | some p => cases hs

/-- The canonical interaction returns the callback's actual value and current heap. -/
noncomputable def tree : Interaction BoundaryValue :=
  machine.canonicalize code args {1} (.call "echo" [] (heap 22) fun r h => .ret r h)

/-- The toy signature owns exactly its one argument cell. -/
@[simp] theorem footprint_eq : callFootprint code args = {1} := rfl

/-- The toy machine follows the canonical call and its checked resumption branches. -/
theorem machine_follows (ι : Placement) : machine.Follows code args {1} ι none tree := by
  change (Stop.call "echo" [] (heap 22) = stop none) ∧ _
  refine ⟨rfl, ?_⟩
  intro r h hr t ht
  obtain ⟨_, rfl⟩ := ht
  dsimp [tree, canonicalize]
  rw [ite_eq_left hr]
  rfl

/-- Every entry fragment has the toy's same nonvacuous canonical interaction. -/
theorem machine_eval (entry : LocHeap BoundaryValue) :
    machine.eval code args {1} entry = some tree := by
  apply eval_eq_some machine_lawful
  refine ⟨⟨⟨fun _ => 0, 0, fun _ => 0, 0⟩, none, rfl⟩, ?_, ?_⟩
  · exact machine.canonicalize_canonical code args {1} _
  · intro ι t ht
    cases ht
    exact machine_follows ι

/-- Both boundary checks preserve the toy's integer fragment. -/
theorem valid_heap (z : Int) (hz : 0 ≤ z ∧ z < 256) : validFragment code args (heap z) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [heap]
  · simp [check, code, args, boundaryArgs, BoundaryValue.toVal, ArgKind.validResult,
      ArgKind.check, ArgKind.region, locValue, Len.resolve, Region.check, intFits,
      intValue, inRange, regions, Region.compatible, heap, hz]
    left
    rfl

/-- The toy fragment has the canonical singleton archive. -/
theorem snapshot_heap (z : Int) : snapshot (heap z) = some [(1, z)] := by
  have hp := LawfulFiniteMap.toList_ofList
    (M := LocHeap) (l := [(1, BoundaryValue.int z)]) (by simp [NoDupKeys])
  have hlist : (PartialMap.ofList [(1, BoundaryValue.int z)] : LocHeap BoundaryValue).toList =
      [(1, BoundaryValue.int z)] := List.perm_singleton.mp hp
  simp [heap, integerHeap, integerSnapshot, footprintLocations, restore,
    snapshot, hlist]

/-- Restriction retains exactly the toy's one-cell fragment. -/
@[simp] theorem restrict_heap (z : Int) : restrict {1} (heap z) = heap z := by simp [heap]

/-- The archive remembers the entry value before the machine updates its cell. -/
def archive : Replay := ⟨code, args, [(1, 11)], []⟩

/-- Starting the call exposes its updated cell and records the original entry fragment. -/
theorem start_eq :
    start machine code args (heap 11) = .call "echo" [] (heap 22) archive := by
  have hi := valid_heap 11 (by omega)
  have hc : validFragment code args (heap 22) ∧ ∃ sig, ("echo", sig) ∈ code.sig.imports ∧
        check sig (boundaryArgs []) (valueHeap (rT := Empty) (heap 22)) = true := by
    refine ⟨valid_heap 22 (by omega), ⟨[], .int 64⟩, by simp [code], rfl⟩
  have hcheck : (code.sig.valid && check code.sig.toCallSig (boundaryArgs args)
      (valueHeap (rT := Empty) (heap 11))) = true := by
    simpa only [Bool.and_eq_true] using And.intro hi.1 hi.2.2
  simp only [start, footprint_eq, restrict_heap, hcheck, ite_true, snapshot_heap, machine_eval,
    tree, canonicalize, rootAction, ite_eq_left hc]
  rfl

/-- The callback's integer reply and current fragment pass the import signature. -/
theorem response_ok : machine.ResponseOK code args {1} "echo" (.int 7) (heap 22) := by
  have hv := valid_heap 22 (by omega)
  refine ⟨hv.1, footprint_eq.symm, ?_, hv.2.2, ⟨[], .int 64⟩, by simp [code], ?_, ?_⟩
  · apply Std.ExtTreeMap.ext_getElem?
    intro l
    by_cases hl : l ∈ ({1} : Finset Loc) <;> simp [restrict_get, heap, hl]
  · rfl
  · rfl

/-- Replaying the recorded response selects its exact return subtree. -/
theorem replay_response : tree.replay [(.int 7, heap 22)] = some (.ret (.int 7) (heap 22)) := by
  simp only [tree, canonicalize, replay, response_ok, ite_true]

/-- Resumption replays the archived call and returns the callback's current heap. -/
theorem resume_eq : resume machine archive (.int 7) (heap 22) = .ret (.int 7) (heap 22) := by
  have ho : validFragment code args (heap 22) ∧
      checkResult code.sig.toCallSig (boundaryArgs args) code.sig.result
        (BoundaryValue.int 7).toVal = true := ⟨valid_heap 22 (by omega), rfl⟩
  simp only [resume, archive, footprint_eq, restrict_heap, machine_eval, List.map_nil,
    replay, tree, canonicalize, response_ok, ite_true,
    snapshot_heap, rootAction]
  exact ite_eq_left ho

variable {rT : Type}

/-- The ordinary ProbLang callback returns the integer seven. -/
def callback : Val rT :=
  let hc : (Exp.lam (.lit (.int 7)) : Exp rT).IsLocallyClosed := lcb_imp_lc (by rfl)
  ⟨.lam (.lit (.int 7)), .lam hc, hc⟩

/-- The explicit environment connects the toy machine to its ProbLang callback. -/
def env : FfiEnv rT := ⟨machine, fun _ => callback⟩

/-- The initial foreign expression has its checked pointer argument already evaluated. -/
abbrev expression : Exp rT := .asm (.lit (.code code)) (argumentTuple args)

/-- The dispatcher evaluates the callback inside its actual resumption context. -/
abbrev paused : Exp rT := .asmResume archive (.app callback.fst (.lit .unit))

section Steps

variable (σ : State rT)

/-- The updated one-cell footprint is the write performed at both foreign boundaries. -/
abbrev updated : State rT := σ.writeFragment [(1, .int 22)]

/-- Capturing the toy cell records its known integer value. -/
theorem capture_cell (z : Int) (h : σ.heap[(1 : Loc)]? = some (.int z)) :
    capture {1} σ.heap = some [(1, z)] := by
  simpa [footprintLocations] using capture_eq_snapshot {1} (fun _ => z) σ.heap (by simpa using h)

/-- Writing the toy cell is exactly the boundary's footprint replacement. -/
theorem updated_eq :
    updated σ = σ.update_heap (fun h => overwrite {1} h (valueHeap (heap 22))) := by
  simpa [updated, integerValues, footprintLocations, heap] using
    write_integerValues σ {1} (fun _ => 22)

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- The assembly call updates its cell and invokes the actual import implementation. -/
theorem start_step (h : σ.heap[(1 : Loc)]? = some (.int 11)) :
    primStepWith env ⟨expression, σ⟩ = dirac ⟨paused, updated σ⟩ := by
  rw [expression, primStepWith_asm]
  simp only [callStep, show code.sig.args.length = args.length from rfl,
    readTuple_argumentTuple, footprint_eq, capture_cell σ 11 h]
  change actionStep env {1} σ (start machine code args (restore [(1, 11)])) = _
  rw [show restore [(1, 11)] = heap 11 from restore_snapshot (snapshot_heap 11), start_eq]
  simp only [actionStep, env, paused, callback, argumentTuple, updated_eq]

/-- The callback's ordinary beta reduction returns seven under the explicit environment. -/
theorem callback_step :
    primStepWith env ⟨.app callback.fst (.lit .unit), σ⟩ = dirac ⟨.lit (.int 7), σ⟩ := by
  have hd : (Exp.app callback.fst (.lit .unit) : Exp rT).decomp =
      ([], .app callback.fst (.lit .unit)) := by
    rw [decomp_unfold]
    rfl
  rw [primStepWith, hd]
  change (headStep ⟨.app (.lam (.lit (.int 7))) (.lit .unit), σ⟩).map (Ectx.fillCfg []) = _
  simp only [headStep, isValM_some (IsVal.lit.toIsValue), open', openRec,
    fillCfg_empty, map_id]

/-- The actual resumption captures the updated cell and returns the import's reply. -/
theorem resume_step (h : σ.heap[(1 : Loc)]? = some (.int 22)) :
    primStepWith env ⟨.asmResume archive (.lit (.int 7)), σ⟩ =
      dirac ⟨.lit (.int 7), updated σ⟩ := by
  have hd : (Exp.asmResume archive (.lit (.int 7)) : Exp rT).decomp =
      ([], .asmResume archive (.lit (.int 7))) := by
    rw [decomp_unfold]
    rfl
  simp only [primStepWith, hd, headStepWith, asValM, toVal?, IsVal.check?]
  simp only [resumeStep, BoundaryValue.ofVal, archive, footprint_eq, capture_cell σ 22 h]
  change (actionStep env {1} σ
    (resume machine archive (.int 7) (restore [(1, 22)]))).map (Ectx.fillCfg []) = _
  rw [show restore [(1, 22)] = heap 22 from restore_snapshot (snapshot_heap 22), resume_eq]
  simp only [actionStep, updated_eq, BoundaryValue.toVal, fillCfg_empty, map_id]

end Steps

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsTopAbsorbing]
  {E : CoPset} {Φ : Val rT → IProp GF}

local bi IProp GF

/-- The shared weakest precondition evaluates a reply inside its assembly resumption frame. -/
theorem wp_resume_bind (environment : FfiEnv rT) (saved : Replay) (reply : Exp rT) : iprop%
    wpFor (primStepWith environment) L E reply
      (fun v => wpFor (primStepWith environment) L E (.asmResume saved v.fst) Φ) ⊢
      wpFor (primStepWith environment) L E (.asmResume saved reply) Φ := by
  have hbind := wpFor_bind (L := L) (E := E) (Φ := Φ) (e := reply) (K := [.asmResume saved])
    (fun K e σ hv => primStepWith_fill environment K (e := e) σ hv)
  simpa only [fill_asmResume, Exp.ofVal] using hbind

/-- The toy foreign call exchanges its cell, runs ProbLang, and resumes through replay. -/
theorem wp_one_import : iprop%
    appHeapFragment [(1, .int 11)] ∗
      ▷ ▷ ▷ (appHeapFragment [(1, .int 22)] -∗ Φ (.int 7)) ⊢
      wpFor (primStepWith env) L E expression Φ := by
  unfold expression
  iintro ⟨Hcell, HΦ⟩
  iapply wpFor_lift_det_step asm_toVal?_eq_none
  iintro %σ Hσ
  ihave %hlook := app_state_lookup_fragment _ $$ Hσ Hcell
  have hdet := start_step σ (hlook (1, .int 11) (by simp))
  imod subset empty_subset with Hclose
  imod app_state_update_fragment [(1, .int 11)] [(1, .int 22)] rfl (by simp)
    $$ Hσ Hcell with ⟨Hσ', Hcell⟩
  imodintro
  iexists ⟨paused, updated σ⟩
  iframe %hdet
  iintro !>
  imod Hclose
  imodintro
  iframe Hσ'
  iapply wp_resume_bind env archive (.app callback.fst (.lit .unit))
  iapply wpFor_pure_step (by rfl) (fun σ => callback_step σ)
  iintro !>
  iapply wpFor_value_of_toVal (v := .int 7) (by rfl)
  iapply wpFor_lift_atomic_step asmResume_toVal?_eq_none
  iintro %τ Hτ
  ihave %hlook := app_state_lookup_fragment _ $$ Hτ Hcell
  have hdet : primStepWith env ⟨.asmResume archive (.lit (.int 7)), τ⟩ =
      dirac ⟨.ofVal (.int 7), updated τ⟩ := by
    simpa only [Exp.ofVal] using resume_step τ (hlook (1, .int 22) (by simp))
  imod subset empty_subset with Hclose
  imod app_state_update_fragment [(1, .int 22)] [(1, .int 22)] rfl (by simp)
    $$ Hτ Hcell with ⟨Hτ', Hcell⟩
  imodintro
  iexists (.int 7 : Val rT), updated τ
  iframe %hdet
  iintro !>
  imod Hclose
  imodintro
  iframe Hτ'
  iapply HΦ $$ Hcell

end ProbLang.AsmImports
