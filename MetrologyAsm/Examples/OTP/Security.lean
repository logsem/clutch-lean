import MetrologyAsm.Examples.OTP.Finite

/-! # Termination, ciphertext law and perfect secrecy of the actual assembly OTP game

Only the returned ciphertext is observed, so the law is of the value marginal; the joint
ciphertext/pad distribution is not the claim. The private pad in the final heap is erased. -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm MeasureTheory MeasureTheory.Measure

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- The uniform law on byte values. -/
private noncomputable abbrev byteUnif : Measure Int := unifInt 256 (by norm_num)

/-- The ideal output law is a uniformly sampled byte represented as an integer literal. -/
noncomputable def idealByteLaw : Measure (Exp rT) :=
  byteUnif.map (fun byte => .lit (.int byte))

/-- The actual allocated Sail-backed game terminates with total probability one. -/
theorem otp_game_terminates (σ : State rT) (message : Int) (hm : 0 ≤ message ∧ message < 256) :
    limExecWith otpEnv ⟨otpGame message, σ⟩ Set.univ = 1 := by
  rw [otp_game_limExec σ message hm]
  simp

/-- Forgetting the private final heap gives exactly the ideal uniform ciphertext distribution. -/
theorem otp_game_uniform (σ : State rT) (message : Int) (hm : 0 ≤ message ∧ message < 256) :
    limExecVWith otpEnv ⟨otpGame message, σ⟩ = idealByteLaw := by
  change asExpr (limExecWith otpEnv ⟨otpGame message, σ⟩) = _
  rw [otp_game_limExec σ message hm]
  unfold asExpr
  rw [map_map Cfg.measurable_expr (by measurability)]
  change byteUnif.map (fun byte => Exp.lit (.int (byteXor message byte))) = idealByteLaw
  calc
    _ = (byteUnif.map (byteXor message)).map (fun byte => (Exp.lit (.int byte) : Exp rT)) :=
      (map_map (by measurability) (by measurability)).symm
    _ = _ := congrArg (fun μ : Measure Int => μ.map (fun byte => (Exp.lit (.int byte) : Exp rT)))
      (byteXor_uniform message)

/-- Each valid ciphertext byte has exact probability one over 256 under actual game execution. -/
theorem otp_ciphertext_probability (σ : State rT) (message ciphertext : Int)
    (hm : 0 ≤ message ∧ message < 256) (hc : 0 ≤ ciphertext ∧ ciphertext < 256) :
    limExecVWith otpEnv ⟨otpGame message, σ⟩ {Exp.lit (.int ciphertext)} = (256 : ENNReal)⁻¹ := by
  rw [otp_game_uniform σ message hm]
  unfold idealByteLaw
  rw [map_apply_of_aemeasurable (by measurability) (measurableSet_singleton _)]
  have hpre : (fun byte : Int => (Exp.lit (.int byte) : Exp rT)) ⁻¹'
      {Exp.lit (.int ciphertext)} = {ciphertext} := by ext byte; simp
  rw [hpre]
  exact RandomBytes.byte_draw_singleton hc

/-- Any two valid byte messages have identical returned-ciphertext distributions. -/
theorem otp_game_perfect_secrecy (σ₀ σ₁ : State rT) (message₀ message₁ : Int)
    (hm₀ : 0 ≤ message₀ ∧ message₀ < 256) (hm₁ : 0 ≤ message₁ ∧ message₁ < 256) :
    limExecVWith otpEnv ⟨otpGame message₀, σ₀⟩ = limExecVWith otpEnv ⟨otpGame message₁, σ₁⟩ :=
  (otp_game_uniform σ₀ message₀ hm₀).trans (otp_game_uniform σ₁ message₁ hm₁).symm

end MetrologyAsm.OTP
