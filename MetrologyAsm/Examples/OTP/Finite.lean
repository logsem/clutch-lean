import MetrologyAsm.Examples.OTP.CallbackExec
import MetrologyAsm.Examples.OTP.Game

/-! # Finite and total actual execution of the private-pad assembly OTP game -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm MeasureTheory MeasureTheory.Measure

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- The actual game's first transition allocates a fresh pad initialized to zero. -/
theorem otp_game_alloc_step (σ : State rT) (message : Int) :
    primStepWith otpEnv ⟨otpGame message, σ⟩ =
      dirac ⟨.app (.lam (otpGameBody message)) (.lit (.loc σ.heap.fresh)),
        storedState σ σ.heap.fresh 0⟩ := by
  let K : Ectx rT := [.appR (.lam (otpGameBody message))]
  change primStepWith otpEnv ⟨K.fill (.alloc (.lit (.int 0))), σ⟩ = _
  rw [primStepWith_fill otpEnv K σ (by rintro ⟨h⟩; cases h)]
  rw [show primStepWith otpEnv ⟨.alloc (.lit (.int 0)), σ⟩ =
    dirac ⟨.lit (.loc σ.heap.fresh), storedState σ σ.heap.fresh 0⟩ from
      alloc_step_with otpEnv σ (.int 0)]
  rw [map_dirac' (by measurability)]
  rfl

/-- Finite actual game execution is exactly a uniform draw mapped to final states. -/
theorem otp_game_finite (σ : State rT) (message : Int) (hm : 0 ≤ message ∧ message < 256) :
    ∃ fuel : Nat, execNWith otpEnv fuel ⟨otpGame message, σ⟩ =
      (unifInt 256 (by norm_num)).map (fun byte =>
        (⟨.lit (.int (byteXor message byte)),
          storedState (storedState σ σ.heap.fresh 0) σ.heap.fresh byte⟩ : Cfg rT)) := by
  obtain ⟨fuel, hcall⟩ := otp_call_finite (rT := rT) σ.heap.fresh
  refine ⟨fuel + 2, ?_⟩
  calc
    execNWith otpEnv (fuel + 2) ⟨otpGame message, σ⟩ =
        execNWith otpEnv (fuel + 1)
          ⟨.app (.lam (otpGameBody message)) (.lit (.loc σ.heap.fresh)),
            storedState σ σ.heap.fresh 0⟩ :=
      execNWith_succ_of_step otpEnv (by rintro ⟨h⟩; cases h) (otp_game_alloc_step σ message) _
    _ = execNWith otpEnv fuel
        ⟨otpExpression message σ.heap.fresh, storedState σ σ.heap.fresh 0⟩ :=
      execNWith_succ_of_step otpEnv
        (val_stuck ((otpGame_beta message σ.heap.fresh).safe (storedState σ σ.heap.fresh 0)))
        (pureStep_with otpEnv (otpGame_beta message σ.heap.fresh) (storedState σ σ.heap.fresh 0)) _
    _ = _ := hcall (storedState σ σ.heap.fresh 0) message 0 hm (by decide +kernel)
      (storedState_lookup σ σ.heap.fresh 0)

/-- The actual game has a finite execution bound with total termination probability one. -/
theorem otp_game_finite_terminates (σ : State rT) (message : Int)
    (hm : 0 ≤ message ∧ message < 256) :
    ∃ fuel : Nat, execNWith otpEnv fuel ⟨otpGame message, σ⟩ Set.univ = 1 := by
  obtain ⟨fuel, hfinite⟩ := otp_game_finite σ message hm
  refine ⟨fuel, ?_⟩
  rw [hfinite]
  simp

/-- The complete actual game distribution is already attained by its finite execution law. -/
theorem otp_game_limExec (σ : State rT) (message : Int) (hm : 0 ≤ message ∧ message < 256) :
    limExecWith otpEnv ⟨otpGame message, σ⟩ =
      (unifInt 256 (by norm_num)).map (fun byte =>
        (⟨.lit (.int (byteXor message byte)),
          storedState (storedState σ σ.heap.fresh 0) σ.heap.fresh byte⟩ : Cfg rT)) := by
  obtain ⟨fuel, hfinite⟩ := otp_game_finite σ message hm
  have hterm : execNWith otpEnv fuel ⟨otpGame message, σ⟩ Set.univ = 1 := by rw [hfinite]; simp
  exact (limExecWith_term otpEnv hterm).trans hfinite

end MetrologyAsm.OTP
