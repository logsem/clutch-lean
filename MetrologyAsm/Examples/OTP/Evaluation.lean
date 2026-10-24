import MetrologyAsm.Examples.OTP.EvaluationRules
import MetrologyAsm.Examples.OTP.Specification
import MetrologyAsm.Examples.OTP.Witness

/-! # The unique evaluation of the actual compiled Sail-backed OTP on in-range inputs -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm

/-- The compiled OTP evaluates to its unique tree under a genuine entry and byte resumptions. -/
theorem otp_eval (message : Int) (pad : Loc) (initial : Int)
    (hm : 0 ≤ message ∧ message < 256) (hi : inRange false 8 initial = true) :
    rv.eval otpCode (otpArgs message pad) {pad} (padHeap pad initial) =
      some (otpTree message pad initial) := by
  have hm64 : inRange false 64 message = true := by
    simp only [inRange, show ¬(64 = 0 ∨ 64 < 64) by decide, ite_false, Bool.false_eq_true,
      decide_eq_true_eq]
    omega
  rw [otpTree_eq]
  refine rv.eval_one_call_eq_some otpCode (otpArgs message pad) {pad} (padHeap pad initial)
    "randombytes" [.loc pad, .int 1] (padHeap pad initial) (otpNext message pad)
    (fun ι t P Q => rv_runs_agree ι otpCode t P Q)
    (fun ι origin paused s u => rv_exit_det ι otpCode (otpArgs message pad) {pad} origin paused s u)
    (otp_compat_exists message pad initial hm64 hi) ?_ ?_ ?_ ?_
  · exact otpTree_canonical message pad initial
  · simpa only [RVSpec, otp_footprint, otpTree_eq] using otp_rvspec message pad initial hm hi
  · intro r heap hr
    exact ⟨.int (byteXor message (padValue pad heap)), heap, otpNext_valid message pad r heap hr⟩
  · intro ι origin paused _ hexit r heap hr
    exact otp_resume_nonempty ι origin paused message pad initial hexit r heap hr

end MetrologyAsm.OTP
