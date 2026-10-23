import MetrologyAsm.Examples.OTP.Evaluation
import MetrologyAsm.Examples.OTP.Callback
import Metrology.ProbLang.Asm.Specification

/-! # Actual foreign dispatch and replay of the compiled OTP interaction -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm

/-- Restriction retains the OTP's singleton integer fragment. -/
@[simp] theorem restrict_padHeap (pad : Loc) (byte : Int) :
    restrict {pad} (padHeap pad byte) = padHeap pad byte := by simp [padHeap]

/-- The one-cell snapshot restores exactly the corresponding logical byte heap. -/
@[simp] theorem restore_padSnapshot (pad : Loc) (byte : Int) :
    HeapSnapshot.restore [(pad, byte)] = padHeap pad byte := by
  simp [padHeap, integerHeap, integerSnapshot, footprintLocations, HeapSnapshot.restore]

/-- Archiving the owned logical byte produces its sole location/value pair. -/
theorem snapshot_padHeap (pad : Loc) (byte : Int) :
    snapshot (padHeap pad byte) = some [(pad, byte)] := by
  have hp := Iris.Std.LawfulFiniteMap.toList_ofList
    (M := LocHeap) (l := [(pad, BoundaryValue.int byte)]) (by simp [Iris.Std.NoDupKeys])
  have hlist : Iris.Std.FiniteMap.toList
      (Iris.Std.PartialMap.ofList [(pad, BoundaryValue.int byte)] : LocHeap BoundaryValue) =
        [(pad, BoundaryValue.int byte)] := List.perm_singleton.mp hp
  change (Iris.Std.PartialMap.ofList [(pad, BoundaryValue.int byte)] :
    LocHeap BoundaryValue).toList = [(pad, BoundaryValue.int byte)] at hlist
  simp [padHeap, integerHeap, integerSnapshot, footprintLocations, HeapSnapshot.restore,
    snapshot, hlist]

/-- The replay archive records the original message, private pad location and initialized byte. -/
def otpArchive (message : Int) (pad : Loc) (initial : Int) : Replay :=
  ⟨otpCode, otpArgs message pad, [(pad, initial)], []⟩

/-- The actual language expression invokes the compiled Sail-backed OTP with two arguments. -/
abbrev otpExpression {rT : Type} (message : Int) (pad : Loc) : Exp rT :=
  .asm (.lit (.code otpCode)) (argumentTuple (otpArgs message pad))

/-- The paused language expression invokes the real randombytes lambda inside its replay frame. -/
abbrev otpPaused {rT : Type} (message : Int) (pad : Loc) (initial : Int) : Exp rT :=
  .asmResume (otpArchive message pad initial)
    (.app RandomBytes.randombytesValue.fst (argumentTuple [.loc pad, .int 1]))

/-- The imported tuple is exactly the actual randombytes lambda's ordinary ProbLang call. -/
theorem otp_callback_expression {rT : Type} (pad : Loc) :
    (.app RandomBytes.randombytesValue.fst (argumentTuple [.loc pad, .int 1]) : Exp rT) =
      (pl% &RandomBytes.randombytes (#loc pad, (#int 1, #()))) := rfl

/-- The actual callback argument tuple and its owned byte pass the randombytes signature check. -/
theorem randombytes_boundary_check (pad : Loc) (byte : Int) (hb : inRange false 8 byte = true) :
    check ⟨[.array 8 (.arg 1), .uint 64], .unit⟩ (boundaryArgs [.loc pad, .int 1])
      (valueHeap (rT := Empty) (padHeap pad byte)) = true := by
  have hbounds : 0 ≤ byte ∧ byte < 256 := by simpa [inRange] using hb
  simp [check, boundaryArgs, BoundaryValue.toVal, ArgKind.validResult, ArgKind.check,
    ArgKind.region, locValue, Len.resolve, intValue, intFits, Region.check, inRange, regions,
    Region.compatible, Region.cells, padHeap, hbounds, BEq.beq, instBEqRegion.beq]

/-- Actual evaluator selection dispatches to randombytes and archives the original owned byte. -/
theorem otp_start_action (message : Int) (pad : Loc) (initial : Int)
    (hm : 0 ≤ message ∧ message < 256) (hi : inRange false 8 initial = true) :
    start rv otpCode (otpArgs message pad) (padHeap pad initial) =
      .call "randombytes" [.loc pad, .int 1] (padHeap pad initial)
        (otpArchive message pad initial) := by
  classical
  have hm64 : inRange false 64 message = true := by simp [inRange]; omega
  have hvalid := otp_validFragment message pad initial hm64 hi
  have hcall : validFragment otpCode (otpArgs message pad) (padHeap pad initial) ∧
      ∃ sig, ("randombytes", sig) ∈ otpCode.sig.imports ∧
        check sig (boundaryArgs [.loc pad, .int 1])
          (valueHeap (rT := Empty) (padHeap pad initial)) = true :=
    ⟨hvalid, ⟨[.array 8 (.arg 1), .uint 64], .unit⟩, by simp [otpCode, otpSig],
      randombytes_boundary_check pad initial hi⟩
  have hcheck : (otpCode.sig.valid && check otpCode.sig.toCallSig
      (boundaryArgs (otpArgs message pad))
      (valueHeap (rT := Empty) (padHeap pad initial))) = true := by
    simpa only [Bool.and_eq_true] using And.intro hvalid.1 hvalid.2.2
  simp only [start, otp_footprint, restrict_padHeap, hcheck, ite_true, snapshot_padHeap,
    otp_eval message pad initial hm hi, otpTree_eq, rootAction, ite_eq_left hcall]
  rfl

/-- An unsigned doubleword result is checked solely by its representability bound. -/
private theorem check_uint64 (sig : CallSig) (args : List (Val Empty)) (value : Int)
    (h : inRange false 64 value = true) :
    checkResult sig args (.uint 64) (BoundaryValue.int value).toVal = true := h

/-- The final ciphertext and sampled byte satisfy the actual return signature checks. -/
theorem otp_output_check (message : Int) (pad : Loc) (byte : Int)
    (hm : 0 ≤ message ∧ message < 256) (hb : inRange false 8 byte = true) :
    validFragment otpCode (otpArgs message pad) (padHeap pad byte) ∧
      checkResult otpCode.sig.toCallSig (boundaryArgs (otpArgs message pad)) otpCode.sig.result
        (BoundaryValue.int (byteXor message byte)).toVal = true := by
  have hm64 : inRange false 64 message = true := by simp [inRange]; omega
  refine ⟨otp_validFragment message pad byte hm64 hb, ?_⟩
  have hc := byteXor_range message byte
  apply check_uint64
  simp [inRange]
  omega

/-- Actual replay returns the ciphertext computed from the callback's new byte. -/
theorem otp_resume_action (message : Int) (pad : Loc) (initial byte : Int)
    (hm : 0 ≤ message ∧ message < 256)
    (hi : inRange false 8 initial = true) (hb : inRange false 8 byte = true) :
    resume rv (otpArchive message pad initial) .unit (padHeap pad byte) =
      .ret (.int (byteXor message byte)) (padHeap pad byte) := by
  classical
  have hm64 : inRange false 64 message = true := by simp [inRange]; omega
  have hr : rv.ResponseOK otpCode (otpArgs message pad) {pad} "randombytes" .unit
      (padHeap pad byte) := (otp_response_iff message pad .unit (padHeap pad byte)).mpr
    ⟨rfl, byte, rfl, hm64, hb⟩
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
      MeasureTheory.Measure.dirac ⟨otpPaused message pad initial, σ⟩ := by
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
      MeasureTheory.Measure.dirac ⟨.lit (.int (byteXor message byte)), σ⟩ := by
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
    Ectx.fillCfg_empty, MeasureTheory.Measure.map_id]

end MetrologyAsm.OTP
