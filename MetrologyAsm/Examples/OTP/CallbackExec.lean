import MetrologyAsm.Examples.OTP.Dispatch
import Metrology.ProbLang.Asm.Exec

/-! # Finite actual execution of the one-byte randombytes callback -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm MeasureTheory MeasureTheory.Measure

/-- A symbolic uniform integer bound gives its interval as an almost-sure support. -/
private theorem uniform_ae_bounds (z : Int) (hz : 0 < z) :
    ∀ᵐ byte ∂unifInt z hz, 0 ≤ byte ∧ byte < z := by
  rw [ae_iff]
  exact unifInt_compl_Ico hz

variable {rT : Type}

/-- The callback's zero-length recursive tail after its sole byte store. -/
def callbackTail (pad : Loc) : Exp rT :=
  pl% &RandomBytes.fill (#loc pad +ₗ #1) (#1 - #1)

/-- The continuation of the callback's sole random draw, under its sampled-byte binder. -/
def callbackDrawBody (pad : Loc) : Exp rT :=
  .app (.lam (callbackTail pad)) (.store (.lit (.loc pad)) (.bvar 0))

/-- The actual random draw and its callback continuation. -/
def callbackDraw (pad : Loc) : Exp rT :=
  .app (.lam (callbackDrawBody pad)) (.rand (.lit (.int 256)) (.lit .unit))

/-- The callback immediately after drawing its concrete byte. -/
def callbackSampled (pad : Loc) (byte : Int) : Exp rT :=
  .app (.lam (callbackDrawBody pad)) (.lit (.int byte))

/-- The callback immediately before its concrete byte store. -/
def callbackStore (pad : Loc) (byte : Int) : Exp rT :=
  .app (.lam (callbackTail pad)) (.store (.lit (.loc pad)) (.lit (.int byte)))

/-- The remaining callback computation after the actual store has returned unit. -/
def callbackStored (pad : Loc) : Exp rT := .app (.lam (callbackTail pad)) (.lit .unit)

/-- The callback's real store changes exactly the owned language-level pad cell. -/
def storedState (σ : State rT) (pad : Loc) (byte : Int) : State rT :=
  σ.update_heap (·.insert pad (.int byte))

/-- The stored state exposes the sampled byte independently of the original pad value. -/
@[simp] theorem storedState_lookup (σ : State rT) (pad : Loc) (byte : Int) :
    (storedState σ pad byte).heap[pad]? = some (.int byte) := by
  simp [storedState, State.update_heap]
  simp [← Std.ExtTreeMap.insert_eq_PartialMap_insert]

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- The real tuple-argument lambda reaches its sole byte draw by pure execution. -/
theorem callback_prefix (pad : Loc) :
    PureSteps (rT := rT) (pl% &RandomBytes.randombytes (#loc pad, (#int 1, #())))
      (callbackDraw pad) := by
  apply (RandomBytes.randombytes_steps pad 1).trans
  unfold callbackDraw callbackDrawBody callbackTail
  pure_steps

/-- Substituting the sampled byte exposes its actual owned-cell store. -/
theorem callback_sampled_beta (pad : Loc) (byte : Int) :
    PureStep (rT := rT) (callbackSampled pad byte) (callbackStore pad byte) := by
  have htail : (callbackTail (rT := rT) pad).IsLocallyClosed := by unfold callbackTail; is_lc
  have hopen := (Exp.open_lc 1 (.lit (.int byte)) (callbackTail pad) htail).symm
  have h := (PureHeadStep.app_lam
    (body := callbackDrawBody (rT := rT) pad) (v := .lit (.int byte))
    (by unfold callbackDrawBody callbackTail; is_lc) (.lit)).toPureStep
  simpa only [callbackDrawBody, callbackSampled, callbackStore, Exp.open', Exp.openRec,
    ite_true, hopen] using h

/-- The actual recursive tail returns unit by pure execution after the sole byte store. -/
theorem callback_tail (pad : Loc) : PureSteps (rT := rT) (callbackStored pad) (.lit .unit) := by
  unfold callbackStored callbackTail
  pure_steps

/-- The sole draw inside the callback and assembly frames has the actual uniform byte law. -/
theorem callback_draw_step (σ : State rT) (archive : Replay) (pad : Loc) :
    primStepWith otpEnv ⟨.asmResume archive (callbackDraw pad), σ⟩ =
      (unifInt 256 (by norm_num)).map
        (fun byte => (⟨.asmResume archive (callbackSampled pad byte), σ⟩ : Cfg rT)) := by
  let K : Ectx rT := [.appR (.lam (callbackDrawBody pad)), .asmResume archive]
  change primStepWith otpEnv ⟨K.fill (pl% rand(#256, #())), σ⟩ = _
  rw [primStepWith_fill otpEnv K σ (by rintro ⟨h⟩; cases h)]
  have hbase : primStep ⟨pl(rand(#256, #())), σ⟩ ≠ 0 := by
    rw [RandomBytes.byte_draw σ]
    exact (Measure.map_ne_zero_iff (by measurability)).mpr
      (IsProbabilityMeasure.ne_zero (unifInt 256 (by norm_num)))
  rw [primStepWith_eq_primStep_of_nonzero otpEnv _ hbase, RandomBytes.byte_draw σ,
    map_map (by measurability) (by measurability)]
  rfl

/-- The store inside both frames has its actual allocated-cell transition and memory update. -/
theorem callback_store_step (σ : State rT) (archive : Replay) (pad : Loc) (old byte : Int)
    (hlookup : σ.heap[pad]? = some (.int old)) :
    primStepWith otpEnv ⟨.asmResume archive (callbackStore (rT := rT) pad byte), σ⟩ =
      dirac ⟨.asmResume archive (callbackStored pad), storedState σ pad byte⟩ := by
  let K : Ectx rT := [.appR (.lam (callbackTail pad)), .asmResume archive]
  change primStepWith otpEnv ⟨K.fill (.store (.lit (.loc pad)) (.lit (.int byte))), σ⟩ = _
  rw [primStepWith_fill otpEnv K σ (by rintro ⟨h⟩; cases h)]
  have hstore := store_step_with otpEnv σ pad (.int old) (.int byte) hlookup
  rw [show primStepWith otpEnv ⟨.store (.lit (.loc pad)) (.lit (.int byte)), σ⟩ =
    dirac ⟨.lit .unit, storedState σ pad byte⟩ from hstore]
  rw [map_dirac' (by measurability)]
  rfl

/-- After drawing a byte, finite actual execution stores it and returns its ciphertext. -/
theorem callback_sampled_exec (pad : Loc) {k : Nat}
    (htail : nsteps PureStep k (callbackStored (rT := rT) pad) (.lit .unit))
    (σ : State rT) (message initial byte : Int)
    (hm : 0 ≤ message ∧ message < 256)
    (hi : inRange false 8 initial = true) (hb : inRange false 8 byte = true)
    (hlookup : σ.heap[pad]? = some (.int initial)) :
    execNWith otpEnv (k + 4)
      ⟨.asmResume (otpArchive message pad initial) (callbackSampled pad byte), σ⟩ =
      dirac ⟨.lit (.int (byteXor message byte)), storedState σ pad byte⟩ := by
  let archive := otpArchive message pad initial
  have hbeta := pureStep_with otpEnv
    ((callback_sampled_beta pad byte).fill [.asmResume archive]) σ
  have hbeta' : primStepWith otpEnv ⟨.asmResume archive (callbackSampled pad byte), σ⟩ =
      dirac ⟨.asmResume archive (callbackStore (rT := rT) pad byte), σ⟩ := by
    simpa only [Ectx.fill_asmResume] using hbeta
  calc
    execNWith otpEnv (k + 4) ⟨.asmResume archive (callbackSampled pad byte), σ⟩ =
        execNWith otpEnv (k + 3) ⟨.asmResume archive (callbackStore (rT := rT) pad byte), σ⟩ :=
      execNWith_succ_of_step otpEnv (by rintro ⟨h⟩; cases h) hbeta' _
    _ = execNWith otpEnv (k + 2)
        ⟨.asmResume archive (callbackStored pad), storedState σ pad byte⟩ :=
      execNWith_succ_of_step otpEnv (by rintro ⟨h⟩; cases h)
        (callback_store_step σ archive pad initial byte hlookup) _
    _ = execNWith otpEnv 2 ⟨.asmResume archive (.lit .unit), storedState σ pad byte⟩ := by
      simpa only [Ectx.fill_asmResume] using
        execNWith_pure_steps otpEnv (PureStep.fill_nsteps [.asmResume archive] htail) 2
          (storedState σ pad byte)
    _ = execNWith otpEnv 1
        ⟨.lit (.int (byteXor message byte)), storedState σ pad byte⟩ :=
      execNWith_succ_of_step otpEnv (by rintro ⟨h⟩; cases h)
        (otp_resume_step _ message pad initial byte hm hi hb (storedState_lookup σ pad byte)) 1
    _ = dirac _ := execNFor_succ_isValue IsVal.lit.toIsValue 0

/-- Finite execution from the actual draw is the uniform measure on final ciphertext states. -/
theorem callback_draw_exec (pad : Loc) {k : Nat}
    (htail : nsteps PureStep k (callbackStored (rT := rT) pad) (.lit .unit))
    (σ : State rT) (message initial : Int) (hm : 0 ≤ message ∧ message < 256)
    (hi : inRange false 8 initial = true) (hlookup : σ.heap[pad]? = some (.int initial)) :
    execNWith otpEnv (k + 5)
      ⟨.asmResume (otpArchive message pad initial) (callbackDraw pad), σ⟩ =
      (unifInt 256 (by norm_num)).map
        (fun byte => (⟨.lit (.int (byteXor message byte)), storedState σ pad byte⟩ : Cfg rT)) := by
  have hnv : ¬(Exp.asmResume (otpArchive message pad initial)
      (callbackDraw (rT := rT) pad)).isValue := by rintro ⟨h⟩; cases h
  change execNFor (primStepWith otpEnv) ((k + 4) + 1) _ = _
  rw [execNFor, ite_eq_right hnv, callback_draw_step]
  rw [Measure.bind_map (by measurability) (by fun_prop)]
  have hbytes := uniform_ae_bounds 256 (by norm_num)
  calc
    _ = (unifInt 256 (by norm_num)).bind
        (fun byte => dirac
          (⟨.lit (.int (byteXor message byte)), storedState σ pad byte⟩ : Cfg rT)) := by
      apply bind_congr_right
      filter_upwards [hbytes] with byte hb
      exact callback_sampled_exec pad htail σ message initial byte hm hi
        (by simpa [inRange] using hb) hlookup
    _ = _ := bind_dirac_eq_map _ (by measurability)

/-- A common finite fuel bound completes the actual assembly call and its real callback. -/
theorem otp_call_finite (pad : Loc) : ∃ fuel : Nat,
    ∀ (σ : State rT) (message initial : Int), 0 ≤ message ∧ message < 256 →
      inRange false 8 initial = true → σ.heap[pad]? = some (.int initial) →
      execNWith otpEnv fuel ⟨otpExpression message pad, σ⟩ =
        (unifInt 256 (by norm_num)).map
          (fun byte =>
            (⟨.lit (.int (byteXor message byte)), storedState σ pad byte⟩ : Cfg rT)) := by
  obtain ⟨prefixFuel, hprefix⟩ := callback_prefix (rT := rT) pad
  obtain ⟨tailFuel, htail⟩ := callback_tail (rT := rT) pad
  refine ⟨(prefixFuel + (tailFuel + 5)) + 1, ?_⟩
  intro σ message initial hm hi hlookup
  have hprefix' : nsteps PureStep prefixFuel (otpPaused (rT := rT) message pad initial)
      (.asmResume (otpArchive message pad initial) (callbackDraw pad)) := by
    simpa only [Ectx.fill_asmResume, otpPaused, otp_callback_expression] using
      PureStep.fill_nsteps [.asmResume (otpArchive message pad initial)] hprefix
  calc
    execNWith otpEnv ((prefixFuel + (tailFuel + 5)) + 1) ⟨otpExpression message pad, σ⟩ =
        execNWith otpEnv (prefixFuel + (tailFuel + 5)) ⟨otpPaused message pad initial, σ⟩ :=
      execNWith_succ_of_step otpEnv (by rintro ⟨h⟩; cases h)
        (otp_start_step σ message pad initial hm hi hlookup) _
    _ = execNWith otpEnv (tailFuel + 5)
        ⟨.asmResume (otpArchive message pad initial) (callbackDraw pad), σ⟩ :=
      execNWith_pure_steps otpEnv hprefix' _ σ
    _ = _ := callback_draw_exec pad htail σ message initial hm hi hlookup

end MetrologyAsm.OTP
