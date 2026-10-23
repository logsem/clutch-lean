import MetrologyAsm.Examples.OTP.Micrometer
import Metrology.Micrometer.CouplingRules

/-! # A zero-cost uniform-ciphertext coupling through the actual randombytes callback -/

namespace MetrologyAsm.OTP

open Iris Iris.BI Iris.ProofMode GradedLifting ProbLang ProbLang.Asm MicrometerWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsReflexive]
  [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] {E : CoPset} {Φ : Val rT → IProp GF}

local bi IProp GF

/-- The real one-byte callback couples its pad draw to a uniform ciphertext at zero cost. -/
theorem wp_randombytes_masked (message : Int) (pad : Loc) (initial : Int) : iprop%
    appHeapFrag pad (.int initial) ∗ ⤇ (pl% rand(#256, #())) ∗
      (∀ byte : Int, ⌜0 ≤ byte ∧ byte < 256⌝ -∗ ⤇ (pl% #int (byteXor message byte)) -∗
        appHeapFrag pad (.int byte) -∗ Φ .unit) ⊢
      wp L E (pl% &RandomBytes.randombytes (#loc pad, (#int 1, #()))) Φ := by
  iintro ⟨Hpad, Hj, HΦ⟩
  wp_steps RandomBytes.randombytes_steps pad 1
  wp_pures
  wp_bind (pl% rand(#256, #()))
  iapply wp_couple_rand_rand 256 (byteXor message)
    (fun _ _ _ => byteXor_range _ _) (byteXor_bij message) (by norm_num) [] E
  isimp only [Ectx.fill_nil]
  iframe Hj
  iintro %byte %hb Hj
  wp_pures
  wp_bind (pl% #loc pad ← #int byte)
  rw [show (pl(#loc pad ← #int byte) : Exp rT) =
    .store (pl% #loc pad) (Exp.ofVal (.int byte)) from rfl]
  iapply wp_store
  iframe Hpad
  iintro Hpad
  wp_pure 3
  wp_show (pl% &RandomBytes.fill #loc (pad + 1) #0)
  wp_steps RandomBytes.fill_nonpos_steps (pad + 1) (by omega)
  wp_value
  iapply HΦ $$ %byte %hb Hj Hpad

/-- The coupled callback proof holds under the same explicit FFI kernel as the real assembly. -/
theorem wp_randombytes_masked_ffi (message : Int) (pad : Loc) (initial : Int) : iprop%
    appHeapFrag pad (.int initial) ∗ ⤇ (pl% rand(#256, #())) ∗
      (∀ byte : Int, ⌜0 ≤ byte ∧ byte < 256⌝ -∗ ⤇ (pl% #int (byteXor message byte)) -∗
        appHeapFrag pad (.int byte) -∗ Φ .unit) ⊢
      wpFor (primStepWith otpEnv) L E
        (pl% &RandomBytes.randombytes (#loc pad, (#int 1, #()))) Φ :=
  (wp_randombytes_masked message pad initial).trans (wp_ffi_of_wp otpEnv)

/-- The actual Sail OTP and heap-changing callback couple to a uniform ciphertext at zero cost. -/
theorem wp_otp_coupled (message : Int) (pad : Loc) (initial : Int)
    (hm : 0 ≤ message ∧ message < 256) (hi : inRange false 8 initial = true) : iprop%
    appHeapFrag pad (.int initial) ∗ ⤇ (pl% rand(#256, #())) ∗
      (∀ byte : Int, ⌜0 ≤ byte ∧ byte < 256⌝ -∗ ⤇ (pl% #int (byteXor message byte)) -∗
        appHeapFrag pad (.int byte) -∗ Φ (.int (byteXor message byte))) ⊢
      wpFor (primStepWith otpEnv) L E (otpExpression message pad) Φ := by
  iintro ⟨Hpad, Hj, HΦ⟩
  iapply wp_otp_start message pad initial hm hi
  iframe Hpad
  iintro !> Hpad
  iapply wp_otp_callback_bind message pad initial
  rw [otp_callback_expression]
  iapply wp_randombytes_masked_ffi message pad initial
  iframe Hpad Hj
  iintro %byte %hb Hj Hpad
  have hbyte : inRange false 8 byte = true := by simpa [inRange] using hb
  iapply wp_otp_resume message pad initial byte hm hi hbyte
  iframe Hpad
  iintro !> Hpad
  iapply HΦ $$ %byte %hb Hj Hpad

end MetrologyAsm.OTP
