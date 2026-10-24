import MetrologyAsm.Examples.OTP.Evaluation
import MetrologyAsm.Examples.OTP.Callback
import Metrology.ProbLang.Asm.Specification

/-! # Actual foreign dispatch and replay of the compiled OTP interaction -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm ProbLang.RandomBytes MeasureTheory.Measure

/-- The replay archive records the original message, private pad location and initialized byte. -/
def otpArchive (message : Int) (pad : Loc) (initial : Int) : Replay :=
  ⟨otpCode, otpArgs message pad, [(pad, initial)], []⟩

/-- The actual language expression invokes the compiled Sail-backed OTP with two arguments. -/
abbrev otpExpression {rT : Type} (message : Int) (pad : Loc) : Exp rT :=
  .asm (.lit (.code otpCode)) (argumentTuple (otpArgs message pad))

/-- The paused language expression invokes the real randombytes lambda inside its replay frame. -/
abbrev otpPaused {rT : Type} (message : Int) (pad : Loc) (initial : Int) : Exp rT :=
  .asmResume (otpArchive message pad initial)
    (.app randombytesValue.fst (argumentTuple [.loc pad, .int 1]))

/-- The imported tuple is exactly the actual randombytes lambda's ordinary ProbLang call. -/
theorem otp_callback_expression {rT : Type} (pad : Loc) :
    (.app randombytesValue.fst (argumentTuple [.loc pad, .int 1]) : Exp rT) =
      (pl% &randombytes (#loc pad, (#int 1, #()))) := rfl

/-- The actual callback argument tuple and its owned byte pass the randombytes signature check. -/
theorem randombytes_boundary_check (pad : Loc) (byte : Int) (hb : inRange false 8 byte = true) :
    check ⟨[.array 8 (.arg 1), .uint 64], .unit⟩ (boundaryArgs [.loc pad, .int 1])
      (valueHeap (padHeap pad byte)) = true := by
  have hbounds := inRange_eight_iff.mp hb
  simp [check, boundaryArgs, BoundaryValue.toVal, ArgKind.validResult, ArgKind.check,
    ArgKind.region, locValue, Len.resolve, intValue, intFits, Region.check, inRange, regions,
    Region.compatible, Region.cells, padHeap, hbounds, BEq.beq, instBEqRegion.beq]

/-- Actual evaluator selection dispatches to randombytes and archives the original owned byte. -/
theorem otp_start_action (message : Int) (pad : Loc) (initial : Int)
    (hm : 0 ≤ message ∧ message < 256) (hi : inRange false 8 initial = true) :
    start rv otpCode (otpArgs message pad) (padHeap pad initial) =
      .call "randombytes" [.loc pad, .int 1] (padHeap pad initial)
        (otpArchive message pad initial) := by
  have hvalid := otp_validFragment message pad initial (inRange_word_of_byte hm) hi
  have hcall : validFragment otpCode (otpArgs message pad) (padHeap pad initial) ∧
      ∃ sig, ("randombytes", sig) ∈ otpCode.sig.imports ∧
        check sig (boundaryArgs [.loc pad, .int 1]) (valueHeap (padHeap pad initial)) = true :=
    ⟨hvalid, ⟨[.array 8 (.arg 1), .uint 64], .unit⟩, by simp [otpCode, otpSig],
      randombytes_boundary_check pad initial hi⟩
  have hcheck : (otpCode.sig.valid && check otpCode.sig.toCallSig
      (boundaryArgs (otpArgs message pad))
      (valueHeap (padHeap pad initial))) = true := by
    simpa only [Bool.and_eq_true] using And.intro hvalid.1 hvalid.2.2
  simp only [start, otp_footprint, restrict_padHeap, hcheck, ite_true, snapshot_padHeap,
    otp_eval message pad initial hm hi, otpTree_eq, rootAction, ite_eq_left hcall]
  rfl

/-- An unsigned doubleword result is checked solely by its representability bound. -/
private theorem check_uint64 (sig : CallSig) (args : List (Val Empty)) (value : Int)
    (h : inRange false 64 value = true) :
    checkResult sig args (.uint 64) (BoundaryValue.int value).toVal = true := h

/-- The OTP heap fragment and ciphertext pass the validity and return checks. -/
theorem otp_output_check (message : Int) (pad : Loc) (byte : Int)
    (hm : 0 ≤ message ∧ message < 256) (hb : inRange false 8 byte = true) :
    validFragment otpCode (otpArgs message pad) (padHeap pad byte) ∧
      checkResult otpCode.sig.toCallSig (boundaryArgs (otpArgs message pad)) otpCode.sig.result
        (BoundaryValue.int (byteXor message byte)).toVal = true := by
  exact ⟨otp_validFragment message pad byte (inRange_word_of_byte hm) hb,
    check_uint64 _ _ _ (inRange_word_of_byte (byteXor_range message byte))⟩

/-- Actual replay returns the ciphertext computed from the callback's new byte. -/
theorem otp_resume_action (message : Int) (pad : Loc) (initial byte : Int)
    (hm : 0 ≤ message ∧ message < 256)
    (hi : inRange false 8 initial = true) (hb : inRange false 8 byte = true) :
    resume rv (otpArchive message pad initial) .unit (padHeap pad byte) =
      .ret (.int (byteXor message byte)) (padHeap pad byte) := by
  have hr : rv.ResponseOK otpCode (otpArgs message pad) {pad} "randombytes" .unit
      (padHeap pad byte) := (otp_response_iff message pad .unit (padHeap pad byte)).mpr
    ⟨rfl, byte, rfl, inRange_word_of_byte hm, hb⟩
  simp only [resume, otpArchive, otp_footprint, restrict_padHeap, restore_padSnapshot,
    otp_eval message pad initial hm hi, List.map_nil, Interaction.replay, otpTree_eq,
    hr, ite_true, snapshot_padHeap, otpNext_valid message pad .unit _ hr, padValue_padHeap,
    rootAction]
  exact ite_eq_left (otp_output_check message pad byte hm hb)

variable {rT : Type}

/-- Capturing the actual owned pad cell archives precisely its current byte. -/
theorem capture_pad (heap : LocHeap (Val rT)) (pad : Loc) (byte : Int)
    (h : heap[pad]? = some (.int byte)) : capture {pad} heap = some [(pad, byte)] := by
  simp [capture, footprintLocations, h, intValue]

/-- Exchanging a fragment with its current byte preserves the complete framed language state. -/
theorem exchange_pad_unchanged (σ : State rT) (pad : Loc) (byte : Int)
    (h : σ.heap[pad]? = some (.int byte)) :
    σ.update_heap (fun heap => overwrite {pad} heap (valueHeap (padHeap pad byte))) = σ := by
  change State.mk _ σ.tapes = State.mk σ.heap σ.tapes
  congr 1
  apply Std.ExtTreeMap.ext_getElem?
  intro l
  rw [overwrite_get]
  by_cases hl : l = pad <;> simp [hl, valueHeap, BoundaryValue.toVal, h]

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- Starting the actual compiled call invokes randombytes and preserves all language-state cells. -/
theorem otp_start_step (σ : State rT) (message : Int) (pad : Loc) (initial : Int)
    (hm : 0 ≤ message ∧ message < 256) (hi : inRange false 8 initial = true)
    (hlookup : σ.heap[pad]? = some (.int initial)) :
    primStepWith otpEnv ⟨otpExpression message pad, σ⟩ =
      dirac ⟨otpPaused message pad initial, σ⟩ := by
  rw [primStepWith_asm]
  simp only [callStep, show otpCode.sig.args.length = (otpArgs message pad).length from rfl,
    readTuple_argumentTuple, otp_footprint, capture_pad _ _ _ hlookup, restore_padSnapshot]
  change actionStep otpEnv {pad} σ
    (start rv otpCode (otpArgs message pad) (padHeap pad initial)) = _
  rw [otp_start_action message pad initial hm hi]
  simp only [actionStep, otpEnv, exchange_pad_unchanged σ pad initial hlookup]

/-- Actual assembly resumption returns the ciphertext and preserves every language-state cell. -/
theorem otp_resume_step (σ : State rT) (message : Int) (pad : Loc) (initial byte : Int)
    (hm : 0 ≤ message ∧ message < 256)
    (hi : inRange false 8 initial = true) (hb : inRange false 8 byte = true)
    (hlookup : σ.heap[pad]? = some (.int byte)) :
    primStepWith otpEnv ⟨.asmResume (otpArchive message pad initial) (.lit .unit), σ⟩ =
      dirac ⟨.lit (.int (byteXor message byte)), σ⟩ := by
  have hd : (Exp.asmResume (otpArchive message pad initial) (.lit .unit) : Exp rT).decomp =
      ([], .asmResume (otpArchive message pad initial) (.lit .unit)) := by
    rw [Exp.decomp_unfold]
    rfl
  simp only [primStepWith, hd, headStepWith, Exp.asValM, Exp.toVal?, IsVal.check?]
  simp only [resumeStep, BoundaryValue.ofVal, otpArchive, otp_footprint,
    capture_pad _ _ _ hlookup, restore_padSnapshot]
  change (actionStep otpEnv {pad} σ (resume rv (otpArchive message pad initial) .unit
    (padHeap pad byte))).map (Ectx.fillCfg []) = _
  rw [otp_resume_action message pad initial byte hm hi hb]
  simp only [actionStep, BoundaryValue.toVal, exchange_pad_unchanged σ pad byte hlookup,
    Ectx.fillCfg_empty, map_id]

end MetrologyAsm.OTP
