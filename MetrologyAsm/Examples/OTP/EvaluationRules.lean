import MetrologyAsm.Examples.OTP.Responses
import MetrologyAsm.Examples.OTP.Observation

/-! # Local heap-changing resumption witnesses used to select the unique OTP evaluation -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm

/-- An observed randombytes call identifies the actual imported function's program counter. -/
theorem observe_call_pc (ι : Placement) (paused : Mach) (message : Int) (pad : Loc)
    (initial : Int)
    (h : observe ι otpCode (otpArgs message pad) {pad} paused =
      some (.call "randombytes" [.loc pad, .int 1] (padHeap pad initial))) :
    pc paused = some (ι.importAddr "randombytes") := by
  exact observe_call_pc_of_single_import ι otpCode (otpArgs message pad) {pad} paused
    "randombytes" ⟨[.array 8 (.arg 1), .uint 64], .unit⟩ [.loc pad, .int 1]
    (padHeap pad initial) rfl h

/-- Every valid reply at an actual observed OTP callback has a concrete heap-changing resumption. -/
theorem otp_resume_nonempty (ι : Placement) (origin paused : Mach)
    (message : Int) (pad : Loc) (initial : Int)
    (h : rv.ExitCompat ι otpCode (otpArgs message pad) {pad} origin paused
      (.call "randombytes" [.loc pad, .int 1] (padHeap pad initial)))
    (r : BoundaryValue) (heap : LocHeap BoundaryValue)
    (hr : rv.ResponseOK otpCode (otpArgs message pad) {pad} "randombytes" r heap) :
    ∃ current, rv.Resume ι otpCode (otpArgs message pad) {pad} paused r heap current := by
  have hpc := observe_call_pc ι paused message pad initial h.1
  obtain ⟨rfl, byte, rfl, hm, hb⟩ := (otp_response_iff message pad r heap).mp hr
  obtain ⟨_, _, _, hconfig, _, hF, ra, hra, hcode⟩ := h
  refine ⟨write8State (resumeIntState paused ra 0) (ι.addr pad) (BitVec.ofInt 8 byte), ?_⟩
  exact rv_resume_unit_byte ι otpCode (otpArgs message pad) {pad} paused "randombytes"
    ⟨[.array 8 (.arg 1), .uint 64], .unit⟩ ra pad (padHeap pad byte) byte rfl
    (otp_validFragment message pad byte hm hb) (by simp) hb hconfig.1
    (by simp [otpCode, otpSig]) hpc hra hcode hF

end MetrologyAsm.OTP
