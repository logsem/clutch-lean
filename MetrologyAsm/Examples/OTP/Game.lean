import MetrologyAsm.Examples.OTP.Coupling

/-! # A closed game allocating its private pad and invoking the actual compiled OTP -/

namespace MetrologyAsm.OTP

open Iris Iris.BI Iris.ProofMode GradedLifting ProbLang ProbLang.Asm MicrometerWpGS

/-- The assembly-call body under the game's private-pad binder. -/
def otpGameBody {rT : Type} (message : Int) : Exp rT :=
  .asm (.lit (.code otpCode)) (.pair (.lit (.int message)) (.pair (.bvar 0) (.lit .unit)))

/-- Allocate a fresh private one-byte pad initialized to zero and return only the ciphertext. -/
def otpGame {rT : Type} (message : Int) : Exp rT :=
  .app (.lam (otpGameBody message)) (.alloc (.lit (.int 0)))

/-- The closed game has the expected ordinary allocation followed by the actual foreign call. -/
theorem otpGame_source {rT : Type} (message : Int) : otpGame (rT := rT) message =
    (pl% let pad := alloc(#0); asm(#(.code otpCode), (#int message, (pad, #())))) := rfl

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- Substituting the fresh private pointer exposes exactly the assembled OTP invocation. -/
theorem otpGame_beta (message : Int) (pad : Loc) :
    PureStep (rT := rT) (.app (.lam (otpGameBody message)) (.lit (.loc pad)))
      (otpExpression message pad) := by
  have h := (PureHeadStep.app_lam (body := otpGameBody (rT := rT) message) (v := .lit (.loc pad))
    (by unfold otpGameBody; is_lc) (.lit)).toPureStep
  simpa only [otpGameBody, otpExpression, Exp.open', Exp.openRec, ite_true, argumentTuple, otpArgs,
    BoundaryValue.toVal] using h

variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsReflexive]
  [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] {E : CoPset} {Φ : Val rT → IProp GF}

local bi IProp GF

/-- The actual FFI-kernel game allocates its owned pad and then runs the compiled call. -/
theorem wp_otpGame_from_call (message : Int) : iprop%
    (∀ pad : Loc, appHeapFrag pad (.int 0) -∗
      wpFor (primStepWith otpEnv) L E (otpExpression message pad) Φ) ⊢
      wpFor (primStepWith otpEnv) L E (otpGame message) Φ := by
  iintro HΦ
  have hbind := wpFor_bind (L := L) (E := E) (Φ := Φ) (e := .alloc (.lit (.int 0)))
    (K := [.appR (.lam (otpGameBody message))])
    (fun K e σ hv => primStepWith_fill otpEnv K (e := e) σ hv)
  iapply (show wpFor (primStepWith otpEnv) L E (.alloc (.lit (.int 0)))
      (fun v => wpFor (primStepWith otpEnv) L E (.app (.lam (otpGameBody message)) v.fst) Φ) ⊢
      wpFor (primStepWith otpEnv) L E (otpGame message) Φ from by
    simpa only [Ectx.fill_appR, Exp.ofVal, otpGame] using hbind)
  iapply wp_ffi_of_wp otpEnv
  rw [show (.alloc (.lit (.int 0)) : Exp rT) = .alloc (Exp.ofVal (.int 0)) from rfl]
  iapply wp_alloc (L := L) (E := E)
  iintro %pad Hpad
  iapply wpFor_pure_step (by rfl) (pureStep_with otpEnv (otpGame_beta message pad))
  iintro !>
  iapply HΦ $$ %pad Hpad

/-- The actual private-pad, assembly-calling game couples to an ideal uniform byte at zero cost. -/
theorem wp_otpGame_coupled (message : Int) (hm : 0 ≤ message ∧ message < 256) : iprop%
    ⤇ (pl% rand(#256, #())) ⊢
      wpFor (primStepWith otpEnv) L E (otpGame message) (fun v => iprop(⤇ v.fst)) := by
  iintro Hj
  iapply wp_otpGame_from_call message
  iintro %pad Hpad
  iapply wp_otp_coupled message pad 0 hm (by decide +kernel)
  iframe Hpad Hj
  iintro %byte %hb Hj Hpad
  iexact Hj

end MetrologyAsm.OTP
