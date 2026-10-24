module

public import Metrology.ProbLang.Asm.Step
public import Metrology.ProbLang.Asm.Fragments
public import Metrology.ProbLang.Syntax.HeapFragment

/-! # Machine specifications and concrete foreign-call steps -/

@[expose] public section

namespace ProbLang.Asm

open MeasureTheory.Measure

variable {rT : Type}

/-- The ProbLang values owned by an integer footprint. -/
def integerValues (F : Finset Loc) (values : Loc → Int) : List (Loc × Val rT) :=
  (footprintLocations F).map (fun l => (l, .int (values l)))

/-- Integer footprint ownership lists have exactly the footprint's keys. -/
@[simp] theorem integerValues_keys (F : Finset Loc) (values : Loc → Int) :
    (integerValues (rT := rT) F values).map Prod.fst = footprintLocations F := by
  simp [integerValues, List.map_map, Function.comp_def]

/-- Integer footprint ownership lists contain no duplicate locations. -/
theorem integerValues_nodup (F : Finset Loc) (values : Loc → Int) :
    ((integerValues (rT := rT) F values).map Prod.fst).Nodup := by simp

/-- Writing the owned integer cells equals replacing exactly their footprint. -/
theorem write_integerValues (σ : State rT) (F : Finset Loc) (values : Loc → Int) :
    σ.writeFragment (integerValues F values) =
      σ.update_heap (fun heap => overwrite F heap (valueHeap (integerHeap F values))) := by
  change State.mk (σ.heap.writeFragment (integerValues F values)) σ.tapes =
    State.mk (overwrite F σ.heap (valueHeap (integerHeap F values))) σ.tapes
  apply congrArg (fun heap => State.mk heap σ.tapes)
  apply Std.ExtTreeMap.ext_getElem?
  intro l
  rw [overwrite_get]
  by_cases hl : l ∈ F
  · rw [ite_eq_left hl, valueHeap_integerHeap_get, ite_eq_left hl]
    apply LocHeap.writeFragment_lookup_of_mem _ _ (integerValues_nodup F values)
    exact List.mem_map.mpr ⟨l, (mem_footprintLocations F l).mpr hl, rfl⟩
  · rw [ite_eq_right hl]
    apply LocHeap.writeFragment_lookup_of_not_mem
    simpa only [integerValues_keys, mem_footprintLocations] using hl

/-- The output fragment of a call is valid and its returned value passes the result check. -/
def ValidReturn (code : Code) (args : List BoundaryValue) (heap : LocHeap BoundaryValue)
    (value : BoundaryValue) : Prop :=
  validFragment code args heap ∧
    checkResult code.sig.toCallSig (boundaryArgs args) code.sig.result value.toVal = true

section

variable {M : AsmSemantics Code BoundaryValue} (code : Code) (args : List BoundaryValue)

/-- The dispatcher `start` returns the evaluator's return value on an integer footprint. -/
theorem start_integer_ret_of_eval (old new : Loc → Int) (value : BoundaryValue)
    (hinput : validFragment code args (integerHeap (callFootprint code args) old))
    (heval : M.eval code args (callFootprint code args)
      (integerHeap (callFootprint code args) old) =
      some (.ret value (integerHeap (callFootprint code args) new)))
    (houtput : ValidReturn code args (integerHeap (callFootprint code args) new) value) :
    start M code args (integerHeap (callFootprint code args) old) =
      .ret value (integerHeap (callFootprint code args) new) := by
  obtain ⟨saved, hsaved⟩ := snapshot_integerHeap (callFootprint code args) old
  apply start_ret_of_eval (saved := saved)
  · simp only [restrict_integerHeap, Bool.and_eq_true]
    exact ⟨hinput.1, hinput.2.2⟩
  · simpa only [restrict_integerHeap] using hsaved
  · simpa only [restrict_integerHeap] using heval
  · exact houtput

/-- A proved canonical return makes the dispatcher return it on an integer footprint. -/
theorem start_integer_ret (law : LawfulAsmSemantics M) (old new : Loc → Int)
    (value : BoundaryValue)
    (hinput : validFragment code args (integerHeap (callFootprint code args) old))
    (hspec : M.Evaluates code args (callFootprint code args)
      (integerHeap (callFootprint code args) old)
      (.ret value (integerHeap (callFootprint code args) new)))
    (houtput : ValidReturn code args (integerHeap (callFootprint code args) new) value) :
    start M code args (integerHeap (callFootprint code args) old) =
      .ret value (integerHeap (callFootprint code args) new) := by
  apply start_integer_ret_of_eval code args old new value hinput _ houtput
  exact M.eval_eq_some law hspec

end

section

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- A return-valued evaluator result yields the actual assembly primitive transition. -/
theorem primStepWith_asm_ret_of_eval (env : FfiEnv rT)
    (code : Code) (args : List BoundaryValue) (old new : Loc → Int) (value : BoundaryValue)
    (hlen : args.length = code.sig.args.length)
    (hinput : validFragment code args (integerHeap (callFootprint code args) old))
    (heval : env.machine.eval code args (callFootprint code args)
      (integerHeap (callFootprint code args) old) =
      some (.ret value (integerHeap (callFootprint code args) new)))
    (houtput : ValidReturn code args (integerHeap (callFootprint code args) new) value)
    (σ : State rT)
    (hlookup : ∀ l ∈ callFootprint code args, σ.heap[l]? = some (.int (old l))) :
    primStepWith env ⟨.asm (.lit (.code code)) (argumentTuple args), σ⟩ =
      dirac ⟨value.toVal.fst, σ.writeFragment (integerValues (callFootprint code args) new)⟩ := by
  rw [primStepWith_asm]
  simp only [callStep, ← hlen, readTuple_argumentTuple, capture_eq_snapshot _ _ _ hlookup]
  change actionStep env (callFootprint code args) σ
    (start env.machine code args (integerHeap (callFootprint code args) old)) = _
  rw [start_integer_ret_of_eval code args old new value hinput heval houtput]
  simp only [actionStep, write_integerValues]

/-- A nonvacuous plain machine spec yields the actual assembly primitive transition. -/
theorem primStepWith_asm_ret (env : FfiEnv rT) (law : LawfulAsmSemantics env.machine)
    (code : Code) (args : List BoundaryValue) (old new : Loc → Int) (value : BoundaryValue)
    (hlen : args.length = code.sig.args.length)
    (hinput : validFragment code args (integerHeap (callFootprint code args) old))
    (hentry : ∃ ι t, env.machine.Compat ι code args (integerHeap (callFootprint code args) old) t)
    (hspec : env.machine.Spec code args (callFootprint code args)
      (integerHeap (callFootprint code args) old)
      (.ret value (integerHeap (callFootprint code args) new)))
    (houtput : ValidReturn code args (integerHeap (callFootprint code args) new) value)
    (σ : State rT)
    (hlookup : ∀ l ∈ callFootprint code args, σ.heap[l]? = some (.int (old l))) :
    primStepWith env ⟨.asm (.lit (.code code)) (argumentTuple args), σ⟩ =
      dirac ⟨value.toVal.fst, σ.writeFragment (integerValues (callFootprint code args) new)⟩ := by
  apply primStepWith_asm_ret_of_eval env code args old new value hlen hinput _ houtput σ hlookup
  exact env.machine.eval_eq_some law ⟨hentry, True.intro, hspec⟩

end

end ProbLang.Asm
