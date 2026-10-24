import MetrologyAsm.Examples.OTP.Image
import MetrologyAsm.Examples.OTP.State

/-! # The complete actual Sail continuation after the randombytes callback -/

namespace MetrologyAsm.OTP

open Sail Std.ExtDHashMap RiscvZkvm.Sail.Functions

/-- Load the callback's byte without relying on any resumed caller-scratch value. -/
def resumeLoad (s : Mach) (base : BitVec 64) (byte : BitVec 8) : Mach :=
  registerState s base 10 .x10 (byte.setWidth 64)

/-- XOR the loaded byte with the message retained in s1. -/
def resumeXor (s : Mach) (base message : BitVec 64) (byte : BitVec 8) : Mach :=
  registerState (resumeLoad s base byte) base 11 .x10 (byte.setWidth 64 ^^^ message)

/-- Restore the original caller return address from the scratch frame. -/
def resumeRA (s : Mach) (base message ret : BitVec 64) (byte : BitVec 8) : Mach :=
  registerState (resumeXor s base message byte) base 12 .x1 ret

/-- Restore the caller's original s0, after its saved pointer has been consumed. -/
def resumeS0 (s : Mach) (base message ret savedS0 : BitVec 64) (byte : BitVec 8) : Mach :=
  registerState (resumeRA s base message ret byte) base 13 .x8 savedS0

/-- Restore the caller's original s1, after its saved message has been consumed. -/
def resumeS1 (s : Mach) (base message ret savedS0 savedS1 : BitVec 64) (byte : BitVec 8) : Mach :=
  registerState (resumeS0 s base message ret savedS0 byte) base 14 .x9 savedS1

/-- Recover the original stack pointer. -/
def resumeRelease (s : Mach) (base sp message ret savedS0 savedS1 : BitVec 64)
    (byte : BitVec 8) : Mach :=
  registerState (resumeS1 s base message ret savedS0 savedS1 byte) base 15 .x2 sp

section Return

variable (s : Mach) (base sp message ret savedS0 savedS1 : BitVec 64) (byte : BitVec 8)

/-- The exact final machine of the compiled OTP continuation. -/
def returnState : Mach :=
  commitState (jumpBodyState (resumeRelease s base sp message ret savedS0 savedS1 byte)
    (codePC base 16) ret) ret

/-- The continuation reads memory but never writes it. -/
theorem returnState_mem : (returnState s base sp message ret savedS0 savedS1 byte).mem = s.mem :=
  rfl

/-- The actual committed return target is the original caller's address. -/
theorem returnState_pc :
    (returnState s base sp message ret savedS0 savedS1 byte).regs.get? .PC = some ret := by
  simp [returnState, commitState]

/-- The returned value and restored registers have their ABI values. -/
theorem returnState_registers :
    let t := returnState s base sp message ret savedS0 savedS1 byte
    t.regs.get? .x2 = some sp ∧ t.regs.get? .x1 = some ret ∧
      t.regs.get? .x8 = some savedS0 ∧ t.regs.get? .x9 = some savedS1 ∧
      t.regs.get? .x10 = some (byte.setWidth 64 ^^^ message) := by
  simp [returnState, resumeRelease, resumeS1, resumeS0, resumeRA, resumeXor, registerState,
    registerBodyState, jumpBodyState, commitState, sequentialState, counterState, get?_insert]

/-- Every register outside the continuation's explicit writes and bookkeeping is unchanged. -/
theorem returnState_reg_other (r : Register)
    (hout : r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x2, .x8, .x9, .x10]) :
    (returnState s base sp message ret savedS0 savedS1 byte).regs.get? r = s.regs.get? r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
  obtain ⟨hpc, hn, hc, h1, h2, h8, h9, h10⟩ := hout
  simp [returnState, resumeRelease, resumeS1, resumeS0, resumeRA, resumeXor, resumeLoad,
    registerState, registerBodyState, jumpBodyState, commitState, sequentialState, counterState,
    get?_insert, Ne.symm hpc, Ne.symm hn, Ne.symm hc, Ne.symm h1, Ne.symm h2, Ne.symm h8,
    Ne.symm h9, Ne.symm h10]

/-- The platform state outside registers and memory is preserved by the continuation. -/
theorem returnState_fields :
    let t := returnState s base sp message ret savedS0 savedS1 byte
    t.choiceState = s.choiceState ∧ t.tags = s.tags ∧ t.cycleCount = s.cycleCount ∧
      t.sailOutput = s.sailOutput := ⟨rfl, rfl, rfl, rfl⟩

end Return

/-- A register write and sequential commit sets the program counter to the next instruction. -/
theorem registerState_pc (s : Mach) (base : BitVec 64) (index : Nat) (destination : Register)
    (value : RegisterType destination) :
    (registerState s base index destination value).regs.get? .PC = some (codePC base (index + 1)) :=
  by simp [registerState, commitState]

/-- A register write and sequential commit leaves every other register unchanged. -/
theorem registerState_get_ne (s : Mach) (base : BitVec 64) (index : Nat) (destination r : Register)
    (value : RegisterType destination)
    (hr : r ∉ [destination, Register.PC, .nextPC, .minstret_increment]) :
    (registerState s base index destination value).regs.get? r = s.regs.get? r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨hd, hpc, hn, hc⟩ := hr
  simp [registerState, registerBodyState, commitState, sequentialState, counterState, get?_insert,
    Ne.symm hd, Ne.symm hpc, Ne.symm hn, Ne.symm hc]

/-- Each register-writing step of the continuation retains the configured user profile. -/
theorem _root_.MetrologyAsm.UserConfig.otp_resume {s : Mach} (h : UserConfig s)
    (base sp message ret savedS0 savedS1 : BitVec 64) (byte : BitVec 8) :
    UserConfig (resumeLoad s base byte) ∧ UserConfig (resumeXor s base message byte) ∧
      UserConfig (resumeRA s base message ret byte) ∧
      UserConfig (resumeS0 s base message ret savedS0 byte) ∧
      UserConfig (resumeS1 s base message ret savedS0 savedS1 byte) ∧
      UserConfig (resumeRelease s base sp message ret savedS0 savedS1 byte) := by
  have h1 := h.otpRegisterState base 10 .x10 (byte.setWidth 64) trivial
  have h2 := h1.otpRegisterState base 11 .x10 (byte.setWidth 64 ^^^ message) trivial
  have h3 := h2.otpRegisterState base 12 .x1 ret trivial
  have h4 := h3.otpRegisterState base 13 .x8 savedS0 trivial
  have h5 := h4.otpRegisterState base 14 .x9 savedS1 trivial
  exact ⟨h1, h2, h3, h4, h5, h5.otpRegisterState base 15 .x2 sp trivial⟩

/-- The compiled continuation preserves the user execution profile. -/
theorem _root_.MetrologyAsm.UserConfig.otpReturnState {s : Mach} (h : UserConfig s)
    (base sp message ret savedS0 savedS1 : BitVec 64) (byte : BitVec 8) :
    UserConfig (returnState s base sp message ret savedS0 savedS1 byte) := by
  have h6 := (h.otp_resume base sp message ret savedS0 savedS1 byte).2.2.2.2.2
  exact ((h6.counterState.sequentialState _).insert .nextPC ret trivial).insert .PC ret trivial

/-- Seven actual Sail steps load the sampled byte, encrypt, restore the ABI and return. -/
theorem runsTo_return {s : Mach} (h : UserConfig s)
    (base sp pad callback message ret savedS0 savedS1 : BitVec 64) (byte : BitVec 8)
    (layout : RawLayout base sp pad callback ret) (image : ContinuationAt s base)
    (hpc : s.regs.get? .PC = some (codePC base 10))
    (hsp : s.regs.get? .x2 = some (reservedSP sp))
    (hpad : s.regs.get? .x8 = some pad) (hmessage : s.regs.get? .x9 = some message)
    (hbyte : s.mem.get? pad.toNat = some byte)
    (hsavedRA : Word64At s (stackAddress sp 24) ret)
    (hsavedS0 : Word64At s (stackAddress sp 16) savedS0)
    (hsavedS1 : Word64At s (stackAddress sp 8) savedS1)
    (code : BitVec 64 → Prop) (hcode : ∀ i < 20, code (codePC base i)) (hout : ¬code ret) :
    RunsTo code (fun t => t = returnState s base sp message ret savedS0 savedS1 byte) s := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := h.otp_resume base sp message ret savedS0 savedS1 byte
  have hp1 := registerState_pc s base 10 .x10 (byte.setWidth 64)
  have hp2 := registerState_pc (resumeLoad s base byte) base 11 .x10 (byte.setWidth 64 ^^^ message)
  have hp3 := registerState_pc (resumeXor s base message byte) base 12 .x1 ret
  have hp4 := registerState_pc (resumeRA s base message ret byte) base 13 .x8 savedS0
  have hp5 := registerState_pc (resumeS0 s base message ret savedS0 byte) base 14 .x9 savedS1
  have hp6 := registerState_pc (resumeS1 s base message ret savedS0 savedS1 byte) base 15 .x2 sp
  have hstep1 : rvStep s = some (resumeLoad s base byte) := by
    simpa only [resumeLoad, registerState, codePC_next] using
      step_load_pad h (codePC base 10) pad byte hpc hpad
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        image.loadPad layout.padRam hbyte
  have ha1 : (resumeLoad s base byte).regs.get? .x10 = some (byte.setWidth 64) := by
    simp [resumeLoad, registerState, registerBodyState, commitState, get?_insert]
  have hm1 : (resumeLoad s base byte).regs.get? .x9 = some message :=
    (registerState_get_ne s base 10 .x10 .x9 _ (by decide)).trans hmessage
  have hstep2 : rvStep (resumeLoad s base byte) = some (resumeXor s base message byte) := by
    simpa only [resumeXor, registerState, codePC_next] using
      step_xor hc1 (codePC base 11) (byte.setWidth 64) message hp1 ha1 hm1
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        (image.xor.of_mem_eq rfl)
  have hs1 : (resumeLoad s base byte).regs.get? .x2 = some (reservedSP sp) :=
    (registerState_get_ne s base 10 .x10 .x2 _ (by decide)).trans hsp
  have hs2 : (resumeXor s base message byte).regs.get? .x2 = some (reservedSP sp) :=
    (registerState_get_ne _ base 11 .x10 .x2 _ (by decide)).trans hs1
  have h24 : reservedSP sp + sign_extend 24#12 = stackAddress sp 24 := rfl
  have h16 : reservedSP sp + sign_extend 16#12 = stackAddress sp 16 := rfl
  have h8 : reservedSP sp + sign_extend 8#12 = stackAddress sp 8 := rfl
  have hstep3 : rvStep (resumeXor s base message byte) =
      some (resumeRA s base message ret byte) := by
    simpa only [resumeRA, registerState, codePC_next] using
      step_restore_ra hc2 (codePC base 12) (reservedSP sp) ret hp2 hs2
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        (image.restoreRA.of_mem_eq rfl)
        (by rw [h24]; exact layout.stack_inUserRam (by decide))
        (by rw [h24]; exact layout.stack_aligned (by decide) (by decide))
        (by rw [h24]; exact hsavedRA.of_mem_eq rfl)
  have hs3 : (resumeRA s base message ret byte).regs.get? .x2 = some (reservedSP sp) :=
    (registerState_get_ne _ base 12 .x1 .x2 _ (by decide)).trans hs2
  have hstep4 : rvStep (resumeRA s base message ret byte) =
      some (resumeS0 s base message ret savedS0 byte) := by
    simpa only [resumeS0, registerState, codePC_next] using
      step_restore_s0 hc3 (codePC base 13) (reservedSP sp) savedS0 hp3 hs3
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        (image.restoreS0.of_mem_eq rfl)
        (by rw [h16]; exact layout.stack_inUserRam (by decide))
        (by rw [h16]; exact layout.stack_aligned (by decide) (by decide))
        (by rw [h16]; exact hsavedS0.of_mem_eq rfl)
  have hs4 : (resumeS0 s base message ret savedS0 byte).regs.get? .x2 = some (reservedSP sp) :=
    (registerState_get_ne _ base 13 .x8 .x2 _ (by decide)).trans hs3
  have hstep5 : rvStep (resumeS0 s base message ret savedS0 byte) =
      some (resumeS1 s base message ret savedS0 savedS1 byte) := by
    simpa only [resumeS1, registerState, codePC_next] using
      step_restore_s1 hc4 (codePC base 14) (reservedSP sp) savedS1 hp4 hs4
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        (image.restoreS1.of_mem_eq rfl)
        (by rw [h8]; exact layout.stack_inUserRam (by decide))
        (by rw [h8]; exact layout.stack_aligned (by decide) (by decide))
        (by rw [h8]; exact hsavedS1.of_mem_eq rfl)
  have hs5 : (resumeS1 s base message ret savedS0 savedS1 byte).regs.get? .x2 =
      some (reservedSP sp) :=
    (registerState_get_ne _ base 14 .x9 .x2 _ (by decide)).trans hs4
  have hrelease : reservedSP sp + sign_extend 32#12 = sp := reservedSP_cancel sp
  have hstep6 : rvStep (resumeS1 s base message ret savedS0 savedS1 byte) =
      some (resumeRelease s base sp message ret savedS0 savedS1 byte) := by
    simpa only [resumeRelease, registerState, codePC_next, hrelease] using
      step_release hc5 (codePC base 15) (reservedSP sp) hp5 hs5
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        (image.release.of_mem_eq rfl)
  have hr6 : (resumeRelease s base sp message ret savedS0 savedS1 byte).regs.get? .x1 =
      some ret := by
    simp [resumeRelease, resumeS1, resumeS0, resumeRA, registerState, registerBodyState,
      commitState, sequentialState, counterState, get?_insert]
  have hstep7 : rvStep (resumeRelease s base sp message ret savedS0 savedS1 byte) =
      some (returnState s base sp message ret savedS0 savedS1 byte) :=
    step_return hc6 (codePC base 16) ret hp6 hr6 (codePC_inUserRam layout.codeRam (by decide))
      (codePC_aligned layout.codeRam layout.codeAlign (by decide)) layout.returnAlign
      (image.ret.of_mem_eq rfl)
  refine .step hpc (hcode 10 (by decide)) hstep1 ?_
  refine .step hp1 (hcode 11 (by decide)) hstep2 ?_
  refine .step hp2 (hcode 12 (by decide)) hstep3 ?_
  refine .step hp3 (hcode 13 (by decide)) hstep4 ?_
  refine .step hp4 (hcode 14 (by decide)) hstep5 ?_
  refine .step hp5 (hcode 15 (by decide)) hstep6 ?_
  refine .step hp6 (hcode 16 (by decide)) hstep7 ?_
  exact .leave (returnState_pc ..) hout rfl

end MetrologyAsm.OTP
