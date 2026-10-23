import MetrologyAsm.Examples.OTP.Dispatch
import Metrology.Micrometer.Asm

/-! # The compiled OTP and real callback under the shared guarded weakest precondition -/

namespace MetrologyAsm.OTP

open Iris Iris.Std Iris.BI Iris.ProofMode GradedLifting ProbLang ProbLang.Asm MicrometerWpGS
  BIFUpdate
open LawfulSet (empty_subset)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsTopAbsorbing]
  {E : CoPset} {Φ : Val rT → IProp GF}

local bi IProp GF

/-- Starting the actual compiled OTP preserves pad ownership and enters the real callback. -/
theorem wp_otp_start (message : Int) (pad : Loc) (initial : Int)
    (hm : 0 ≤ message ∧ message < 256) (hi : inRange false 8 initial = true) : iprop%
    appHeapFrag pad (.int initial) ∗
      ▷ (appHeapFrag pad (.int initial) -∗
        wpFor (primStepWith otpEnv) L E (otpPaused message pad initial) Φ) ⊢
      wpFor (primStepWith otpEnv) L E (otpExpression message pad) Φ := by
  iintro ⟨Hpad, HΦ⟩
  iapply wpFor_lift_det_step Exp.asm_toVal?_eq_none
  iintro %σ Hσ
  ihave %hlookup := app_state_lookup_heap $$ Hσ Hpad
  have hdet := otp_start_step σ message pad initial hm hi hlookup
  imod subset empty_subset with Hclose
  imodintro
  iexists (⟨otpPaused message pad initial, σ⟩ : Cfg rT)
  iframe %hdet
  iintro !>
  imod Hclose
  imodintro
  iframe Hσ
  iapply HΦ $$ Hpad

/-- Returning through the actual replay frame preserves ownership of the callback's sampled byte. -/
theorem wp_otp_resume (message : Int) (pad : Loc) (initial byte : Int)
    (hm : 0 ≤ message ∧ message < 256)
    (hi : inRange false 8 initial = true) (hb : inRange false 8 byte = true) : iprop%
    appHeapFrag pad (.int byte) ∗
      ▷ (appHeapFrag pad (.int byte) -∗ Φ (.int (byteXor message byte))) ⊢
      wpFor (primStepWith otpEnv) L E
        (.asmResume (otpArchive message pad initial) (.lit .unit)) Φ := by
  iintro ⟨Hpad, HΦ⟩
  iapply wpFor_lift_atomic_step Exp.asmResume_toVal?_eq_none
  iintro %σ Hσ
  ihave %hlookup := app_state_lookup_heap $$ Hσ Hpad
  have hdet : primStepWith otpEnv
      ⟨.asmResume (otpArchive message pad initial) (.lit .unit), σ⟩ =
      MeasureTheory.Measure.dirac ⟨Exp.ofVal (.int (byteXor message byte)), σ⟩ := by
    simpa only [Exp.ofVal] using otp_resume_step σ message pad initial byte hm hi hb hlookup
  imod subset empty_subset with Hclose
  imodintro
  iexists (.int (byteXor message byte) : Val rT), σ
  iframe %hdet
  iintro !>
  imod Hclose
  imodintro
  iframe Hσ
  iapply HΦ $$ Hpad

/-- The guarded context rule runs the callback inside the actual assembly resumption frame. -/
theorem wp_otp_callback_bind (message : Int) (pad : Loc) (initial : Int) : iprop%
    wpFor (primStepWith otpEnv) L E
      (.app RandomBytes.randombytesValue.fst (argumentTuple [.loc pad, .int 1]))
      (fun v => wpFor (primStepWith otpEnv) L E
        (.asmResume (otpArchive message pad initial) v.fst) Φ) ⊢
      wpFor (primStepWith otpEnv) L E (otpPaused message pad initial) Φ := by
  have hbind := wpFor_bind (L := L) (E := E) (Φ := Φ)
    (e := .app RandomBytes.randombytesValue.fst (argumentTuple [.loc pad, .int 1]))
    (K := [.asmResume (otpArchive message pad initial)])
    (fun K e σ hv => primStepWith_fill otpEnv K (e := e) σ hv)
  simpa only [Ectx.fill_asmResume, Exp.ofVal] using hbind

variable [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind]

/-- The actual assembled Sail OTP runs randombytes and returns XOR of its sampled pad byte. -/
theorem wp_otp (message : Int) (pad : Loc) (initial : Int)
    (hm : 0 ≤ message ∧ message < 256) (hi : inRange false 8 initial = true) : iprop%
    appHeapFrag pad (.int initial) ∗
      (∀ byte : Int, ⌜0 ≤ byte ∧ byte < 256⌝ -∗
        appHeapFrag pad (.int byte) -∗ Φ (.int (byteXor message byte))) ⊢
      wpFor (primStepWith otpEnv) L E (otpExpression message pad) Φ := by
  iintro ⟨Hpad, HΦ⟩
  iapply wp_otp_start message pad initial hm hi
  iframe Hpad
  iintro !> Hpad
  iapply wp_otp_callback_bind message pad initial
  rw [otp_callback_expression]
  iapply otp_randombytes_wp pad (.int initial)
  isimp only [appArrayFrag]
  iframe Hpad
  iintro Hbytes
  isimp only [RandomBytes.byteArray] at Hbytes
  icases Hbytes with ⟨%byte, %hb, Hpad, Htail⟩
  have hbyte : inRange false 8 byte = true := by simpa [inRange] using hb
  iapply wp_otp_resume message pad initial byte hm hi hbyte
  iframe Hpad
  iintro !> Hpad
  iapply HΦ
  · ipureintro
    exact hb
  · iexact Hpad

end MetrologyAsm.OTP
