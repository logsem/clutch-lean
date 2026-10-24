import MetrologyAsm.Examples.OTP.Image
import MetrologyAsm.Examples.OTP.State

/-! # Actual Sail execution from the OTP entry to its randombytes import -/

namespace MetrologyAsm.OTP

open Sail Std.ExtDHashMap RiscvZkvm.Sail.Functions

/-- The physical addresses and entry register values for one OTP invocation. -/
structure CallInputs where
  /-- Base of the compiled code and import slot. -/
  base : BitVec 64
  /-- Original stack pointer. -/
  sp : BitVec 64
  /-- Owned private pad byte's address. -/
  pad : BitVec 64
  /-- Message argument. -/
  message : BitVec 64
  /-- Original caller return address. -/
  ret : BitVec 64
  /-- Original callee-saved s0 value. -/
  savedS0 : BitVec 64
  /-- Original callee-saved s1 value. -/
  savedS1 : BitVec 64
  /-- Relocated randombytes entry address. -/
  callback : BitVec 64

namespace CallInputs

section Steps

variable (a : CallInputs) (s : Mach)

/-- Reserve the compiler's scratch frame. -/
def reserve : Mach :=
  registerState s a.base 0 .x2 (reservedSP a.sp)

/-- Save the original caller return address. -/
def saveRA : Mach :=
  storeState (a.reserve s) a.base 1 (stackAddress a.sp 24) a.ret

/-- Save the original s0. -/
def saveS0 : Mach :=
  storeState (a.saveRA s) a.base 2 (stackAddress a.sp 16) a.savedS0

/-- Save the original s1. -/
def saveS1 : Mach :=
  storeState (a.saveS0 s) a.base 3 (stackAddress a.sp 8) a.savedS1

/-- Capture the pad pointer before setting up the callback arguments. -/
def capturePad : Mach :=
  registerState (a.saveS1 s) a.base 4 .x8 a.pad

/-- Capture the message in s1 across the callback. -/
def captureMessage : Mach :=
  registerState (a.capturePad s) a.base 5 .x9 a.message

/-- Set the callback length argument to one. -/
def setLength : Mach :=
  registerState (a.captureMessage s) a.base 6 .x11 1#64

/-- Copy the saved pad pointer into the callback's first argument. -/
def setArgument : Mach :=
  registerState (a.setLength s) a.base 7 .x10 a.pad

/-- Form the code-relative upper part of the trampoline address. -/
def callUpper : Mach :=
  registerState (a.setArgument s) a.base 8 .x1 (codePC a.base 8)

/-- Jump into the import trampoline and save the continuation address. -/
def callLink : Mach :=
  commitState (linkBodyState (a.callUpper s) (codePC a.base 9) (codePC a.base 17))
    (codePC a.base 17)

/-- Form the code-relative upper part of the import slot address. -/
def stubUpper : Mach :=
  registerState (a.callLink s) a.base 17 .x28 (codePC a.base 17)

/-- Load the actual relocated randombytes entry. -/
def stubLoad : Mach :=
  registerState (a.stubUpper s) a.base 18 .x28 a.callback

/-- The exact paused machine entering the external randombytes callback. -/
def paused : Mach :=
  commitState (jumpBodyState (a.stubLoad s) (codePC a.base 19) a.callback) a.callback

end Steps

section Config

variable (a : CallInputs) {s : Mach} (h : UserConfig s)

include h

/-- The reserve state retains the configured user profile. -/
theorem config_reserve : UserConfig (a.reserve s) :=
  h.otpRegisterState a.base 0 .x2 (reservedSP a.sp) trivial

/-- The saveRA state retains the configured user profile. -/
theorem config_saveRA : UserConfig (a.saveRA s) :=
  (a.config_reserve h).otpStoreState a.base 1 (stackAddress a.sp 24) a.ret

/-- The saveS0 state retains the configured user profile. -/
theorem config_saveS0 : UserConfig (a.saveS0 s) :=
  (a.config_saveRA h).otpStoreState a.base 2 (stackAddress a.sp 16) a.savedS0

/-- The saveS1 state retains the configured user profile. -/
theorem config_saveS1 : UserConfig (a.saveS1 s) :=
  (a.config_saveS0 h).otpStoreState a.base 3 (stackAddress a.sp 8) a.savedS1

/-- The capturePad state retains the configured user profile. -/
theorem config_capturePad : UserConfig (a.capturePad s) :=
  (a.config_saveS1 h).otpRegisterState a.base 4 .x8 a.pad trivial

/-- The captureMessage state retains the configured user profile. -/
theorem config_captureMessage : UserConfig (a.captureMessage s) :=
  (a.config_capturePad h).otpRegisterState a.base 5 .x9 a.message trivial

/-- The setLength state retains the configured user profile. -/
theorem config_setLength : UserConfig (a.setLength s) :=
  (a.config_captureMessage h).otpRegisterState a.base 6 .x11 1#64 trivial

/-- The setArgument state retains the configured user profile. -/
theorem config_setArgument : UserConfig (a.setArgument s) :=
  (a.config_setLength h).otpRegisterState a.base 7 .x10 a.pad trivial

/-- The callUpper state retains the configured user profile. -/
theorem config_callUpper : UserConfig (a.callUpper s) :=
  (a.config_setArgument h).otpRegisterState a.base 8 .x1 (codePC a.base 8) trivial

/-- The callLink state retains the configured user profile. -/
theorem config_callLink : UserConfig (a.callLink s) :=
  (((a.config_callUpper h).counterState.sequentialState _).insert .nextPC _ trivial).insert
    .x1 _ trivial |>.insert .PC _ trivial

/-- The stubUpper state retains the configured user profile. -/
theorem config_stubUpper : UserConfig (a.stubUpper s) :=
  (a.config_callLink h).otpRegisterState a.base 17 .x28 (codePC a.base 17) trivial

/-- The stubLoad state retains the configured user profile. -/
theorem config_stubLoad : UserConfig (a.stubLoad s) :=
  (a.config_stubUpper h).otpRegisterState a.base 18 .x28 a.callback trivial

/-- The paused state retains the configured user profile. -/
theorem config_paused : UserConfig (a.paused s) :=
  (((a.config_stubLoad h).counterState.sequentialState _).insert .nextPC _ trivial).insert
    .PC _ trivial

end Config

/-- The exact three-word scratch-memory effect of the prefix. -/
def savedMemory (a : CallInputs) (s : Mach) : Mach :=
  write64State (write64State (write64State s (stackAddress a.sp 24) a.ret)
    (stackAddress a.sp 16) a.savedS0) (stackAddress a.sp 8) a.savedS1

section Registers

variable (a : CallInputs) (s : Mach)

attribute [local simp] registerState storeState linkBodyState jumpBodyState registerBodyState
  storeBodyState commitState sequentialState counterState get?_insert

/-- All instructions after the saves preserve memory, including the external jump. -/
theorem paused_mem : (a.paused s).mem = (a.savedMemory s).mem := rfl

/-- The prefix commits the real imported function address. -/
theorem paused_pc :
    (a.paused s).regs.get? .PC = some a.callback := by simp [paused]

/-- Saved message, pad pointer and callback arguments survive the import trampoline. -/
theorem paused_registers :
    let t := a.paused s
    t.regs.get? .x2 = some (reservedSP a.sp) ∧ t.regs.get? .x1 = some (codePC a.base 10) ∧
      t.regs.get? .x8 = some a.pad ∧ t.regs.get? .x9 = some a.message ∧
      t.regs.get? .x10 = some a.pad ∧ t.regs.get? .x11 = some 1#64 := by
  simp [paused, stubLoad, stubUpper, callLink, callUpper, setArgument, setLength, captureMessage,
    capturePad, saveS1, saveS0, saveRA, reserve, codePC_next]

/-- The scratch saves preserve all compiled instruction words and the relocated callback slot. -/
theorem savedMemory_image {s : Mach} (image : ImageAt s a.base a.callback)
    (layout : RawLayout a.base a.sp a.pad a.callback a.ret) :
    ImageAt (a.savedMemory s) a.base a.callback :=
  ((image.write64State layout a.ret (by decide)).write64State layout a.savedS0
    (by decide)).write64State layout a.savedS1 (by decide)

/-- The paused machine retains the full executable image. -/
theorem paused_image {s : Mach} (image : ImageAt s a.base a.callback)
    (layout : RawLayout a.base a.sp a.pad a.callback a.ret) :
    ImageAt (a.paused s) a.base a.callback :=
  (a.savedMemory_image image layout).of_mem_eq (a.paused_mem s)

/-- All three original register values are installed as actual allocated stack bytes. -/
theorem paused_saved (hsp : 32 ≤ a.sp.toNat) :
    Word64At (a.paused s) (stackAddress a.sp 24) a.ret ∧
      Word64At (a.paused s) (stackAddress a.sp 16) a.savedS0 ∧
      Word64At (a.paused s) (stackAddress a.sp 8) a.savedS1 := by
  have h24 := word64At_write64State s (stackAddress a.sp 24) a.ret
  have h16 := word64At_write64State (write64State s (stackAddress a.sp 24) a.ret)
    (stackAddress a.sp 16) a.savedS0
  have h8 := word64At_write64State (write64State (write64State s (stackAddress a.sp 24) a.ret)
    (stackAddress a.sp 16) a.savedS0) (stackAddress a.sp 8) a.savedS1
  refine ⟨?_, ?_, h8.of_mem_eq (a.paused_mem s)⟩
  · exact ((h24.write64State a.savedS0
      (stackAddress_disjoint a.sp hsp (by decide) (by decide) (by decide) (by decide)
        (by decide))).write64State a.savedS1
      (stackAddress_disjoint a.sp hsp (by decide) (by decide) (by decide) (by decide)
        (by decide))).of_mem_eq (a.paused_mem s)
  · exact (h16.write64State a.savedS1
      (stackAddress_disjoint a.sp hsp (by decide) (by decide) (by decide) (by decide)
        (by decide))).of_mem_eq (a.paused_mem s)

/-- Every byte outside the reserved scratch interval is unchanged at the import stop. -/
theorem paused_mem_outside (hsp : 32 ≤ a.sp.toNat) (address : Nat)
    (hout : address < a.sp.toNat - 32 ∨ a.sp.toNat ≤ address) :
    (a.paused s).mem.get? address = s.mem.get? address := by
  have h24 := stackAddress_toNat a.sp hsp (offset := 24) (by decide)
  have h16 := stackAddress_toNat a.sp hsp (offset := 16) (by decide)
  have h8 := stackAddress_toNat a.sp hsp (offset := 8) (by decide)
  rw [a.paused_mem s, savedMemory]
  rw [write64State_get?_outside _ _ _ _ (by omega),
    write64State_get?_outside _ _ _ _ (by omega),
    write64State_get?_outside _ _ _ _ (by omega)]

/-- The callback sees the original pad byte. -/
theorem paused_pad
    (layout : RawLayout a.base a.sp a.pad a.callback a.ret) :
    (a.paused s).mem.get? a.pad.toNat = s.mem.get? a.pad.toNat := by
  apply a.paused_mem_outside s layout.stackLower
  have := layout.stackPad
  unfold disjointSpans at this
  omega

/-- Registers outside the prefix's explicit writes and execution bookkeeping are preserved. -/
theorem paused_reg_other (r : Register)
    (hout : r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x2,
      .x8, .x9, .x10, .x11, .x28]) :
    (a.paused s).regs.get? r = s.regs.get? r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
  obtain ⟨hpc, hn, hc, h1, h2, h8, h9, h10, h11, h28⟩ := hout
  simp [paused, stubLoad, stubUpper, callLink, callUpper, setArgument, setLength, captureMessage,
    capturePad, saveS1, saveS0, saveRA, reserve, Ne.symm hpc, Ne.symm hn, Ne.symm hc, Ne.symm h1,
    Ne.symm h2, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h28]

/-- The prefix preserves the platform state outside registers and scratch memory. -/
theorem paused_fields :
    let t := a.paused s
    t.choiceState = s.choiceState ∧ t.tags = s.tags ∧ t.cycleCount = s.cycleCount ∧
      t.sailOutput = s.sailOutput := ⟨rfl, rfl, rfl, rfl⟩

/-- Thirteen actual Sail steps reach the external callback with the original frame saved. -/
theorem runsTo_call {s : Mach} (h : UserConfig s)
    (layout : RawLayout a.base a.sp a.pad a.callback a.ret) (image : ImageAt s a.base a.callback)
    (hpc : s.regs.get? .PC = some a.base) (hsp : s.regs.get? .x2 = some a.sp)
    (hra : s.regs.get? .x1 = some a.ret) (hs0 : s.regs.get? .x8 = some a.savedS0)
    (hs1 : s.regs.get? .x9 = some a.savedS1)
    (hmessage : s.regs.get? .x10 = some a.message) (hpad : s.regs.get? .x11 = some a.pad)
    (code : BitVec 64 → Prop) (hcode : ∀ i < 20, code (codePC a.base i))
    (hout : ¬code a.callback) : RunsTo code (fun t => t = a.paused s) s := by
  have h24 : reservedSP a.sp + sign_extend 24#12 = stackAddress a.sp 24 := rfl
  have h16 : reservedSP a.sp + sign_extend 16#12 = stackAddress a.sp 16 := rfl
  have h8 : reservedSP a.sp + sign_extend 8#12 = stackAddress a.sp 8 := rfl
  have hreserve : a.sp + sign_extend 0xfe0#12 = reservedSP a.sp := rfl
  have hp1 : (a.reserve s).regs.get? .PC = some (codePC a.base 1) := by
    simp [reserve]
  have hp2 : (a.saveRA s).regs.get? .PC = some (codePC a.base 2) := by
    simp [saveRA]
  have hp3 : (a.saveS0 s).regs.get? .PC = some (codePC a.base 3) := by
    simp [saveS0]
  have hp4 : (a.saveS1 s).regs.get? .PC = some (codePC a.base 4) := by
    simp [saveS1]
  have hp5 : (a.capturePad s).regs.get? .PC = some (codePC a.base 5) := by
    simp [capturePad]
  have hp6 : (a.captureMessage s).regs.get? .PC = some (codePC a.base 6) := by
    simp [captureMessage]
  have hp7 : (a.setLength s).regs.get? .PC = some (codePC a.base 7) := by
    simp [setLength]
  have hp8 : (a.setArgument s).regs.get? .PC = some (codePC a.base 8) := by
    simp [setArgument]
  have hp9 : (a.callUpper s).regs.get? .PC = some (codePC a.base 9) := by
    simp [callUpper]
  have hp10 : (a.callLink s).regs.get? .PC = some (codePC a.base 17) := by
    simp [callLink]
  have hp11 : (a.stubUpper s).regs.get? .PC = some (codePC a.base 18) := by
    simp [stubUpper]
  have hp12 : (a.stubLoad s).regs.get? .PC = some (codePC a.base 19) := by
    simp [stubLoad]
  have step1 : rvStep s = some (a.reserve s) := by
    simpa only [reserve, registerState, hreserve, codePC_next] using
      step_reserve h (codePC a.base 0) a.sp (by simpa using hpc) hsp
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide)) (image.words ⟨0, by decide⟩)
  have hsp1 : (a.reserve s).regs.get? .x2 = some (reservedSP a.sp) := by
    simp [reserve]
  have hra1 : (a.reserve s).regs.get? .x1 = some a.ret := by
    simp [reserve, hra]
  have step2 : rvStep (a.reserve s) = some (a.saveRA s) := by
    simpa only [saveRA, storeState, codePC_next, h24] using
      step_save_ra (a.config_reserve h) (codePC a.base 1) (reservedSP a.sp) a.ret hp1 hsp1 hra1
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        ((image.words ⟨1, by decide⟩).of_mem_eq rfl)
        (by rw [h24]; exact layout.stack_inUserRam (by decide))
        (by rw [h24]; exact layout.stack_aligned (by decide) (by decide))
  have image2 : ImageAt (a.saveRA s) a.base a.callback :=
    (image.write64State layout a.ret (by decide)).of_mem_eq rfl
  have hsp2 : (a.saveRA s).regs.get? .x2 = some (reservedSP a.sp) := by
    simpa [saveRA] using hsp1
  have hs02 : (a.saveRA s).regs.get? .x8 = some a.savedS0 := by
    simp [saveRA, reserve, hs0]
  have step3 : rvStep (a.saveRA s) = some (a.saveS0 s) := by
    simpa only [saveS0, storeState, codePC_next, h16] using
      step_save_s0 (a.config_saveRA h) (codePC a.base 2) (reservedSP a.sp) a.savedS0 hp2 hsp2 hs02
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide)) (image2.words ⟨2, by decide⟩)
        (by rw [h16]; exact layout.stack_inUserRam (by decide))
        (by rw [h16]; exact layout.stack_aligned (by decide) (by decide))
  have image3 : ImageAt (a.saveS0 s) a.base a.callback :=
    (image2.write64State layout a.savedS0 (by decide)).of_mem_eq rfl
  have hsp3 : (a.saveS0 s).regs.get? .x2 = some (reservedSP a.sp) := by
    simpa [saveS0] using hsp2
  have hs13 : (a.saveS0 s).regs.get? .x9 = some a.savedS1 := by
    simp [saveS0, saveRA, reserve, hs1]
  have step4 : rvStep (a.saveS0 s) = some (a.saveS1 s) := by
    simpa only [saveS1, storeState, codePC_next, h8] using
      step_save_s1 (a.config_saveS0 h) (codePC a.base 3) (reservedSP a.sp) a.savedS1 hp3 hsp3 hs13
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide)) (image3.words ⟨3, by decide⟩)
        (by rw [h8]; exact layout.stack_inUserRam (by decide))
        (by rw [h8]; exact layout.stack_aligned (by decide) (by decide))
  have image4 : ImageAt (a.saveS1 s) a.base a.callback :=
    (a.savedMemory_image image layout).of_mem_eq rfl
  have hpad4 : (a.saveS1 s).regs.get? .x11 = some a.pad := by
    simp [saveS1, saveS0, saveRA, reserve, hpad]
  have step5 : rvStep (a.saveS1 s) = some (a.capturePad s) := by
    simpa only [capturePad, registerState, codePC_next] using
      step_capture_pad (a.config_saveS1 h) (codePC a.base 4) a.pad hp4 hpad4
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide)) (image4.words ⟨4, by decide⟩)
  have hmessage5 : (a.capturePad s).regs.get? .x10 = some a.message := by
    simp [capturePad, saveS1, saveS0, saveRA, reserve, hmessage]
  have step6 : rvStep (a.capturePad s) = some (a.captureMessage s) := by
    simpa only [captureMessage, registerState, codePC_next] using
      step_capture_message (a.config_capturePad h) (codePC a.base 5) a.message hp5 hmessage5
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        ((image4.words ⟨5, by decide⟩).of_mem_eq rfl)
  have step7 : rvStep (a.captureMessage s) = some (a.setLength s) := by
    simpa only [setLength, registerState, codePC_next] using
      step_length (a.config_captureMessage h) (codePC a.base 6) hp6
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        ((image4.words ⟨6, by decide⟩).of_mem_eq rfl)
  have hpad7 : (a.setLength s).regs.get? .x8 = some a.pad := by
    simp [setLength, captureMessage, capturePad]
  have step8 : rvStep (a.setLength s) = some (a.setArgument s) := by
    simpa only [setArgument, registerState, codePC_next] using
      step_argument (a.config_setLength h) (codePC a.base 7) a.pad hp7 hpad7
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        ((image4.words ⟨7, by decide⟩).of_mem_eq rfl)
  have step9 : rvStep (a.setArgument s) = some (a.callUpper s) := by
    simpa only [callUpper, registerState, codePC_next] using
      step_call_upper (a.config_setArgument h) (codePC a.base 8) hp8
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        ((image4.words ⟨8, by decide⟩).of_mem_eq rfl)
  have hra9 : (a.callUpper s).regs.get? .x1 = some (codePC a.base 8) := by
    simp [callUpper]
  have htarget : BitVec.addInt (codePC a.base 8) 36 = codePC a.base 17 := by
    rw [codePC, pcAt, addInt_compose]
    rfl
  have step10 : rvStep (a.callUpper s) = some (a.callLink s) := by
    simpa only [callLink, htarget] using
      step_call_link (a.config_callUpper h) (codePC a.base 9) (codePC a.base 8) hp9 hra9
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        (by rw [htarget]; exact codePC_aligned layout.codeRam layout.codeAlign (by decide))
        ((image4.words ⟨9, by decide⟩).of_mem_eq rfl)
  have step11 : rvStep (a.callLink s) = some (a.stubUpper s) := by
    simpa only [stubUpper, registerState, codePC_next] using
      step_stub_upper (a.config_callLink h) (codePC a.base 17) hp10
        (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        ((image4.words ⟨17, by decide⟩).of_mem_eq rfl)
  have ht3 : (a.stubUpper s).regs.get? .x28 = some (codePC a.base 17) := by
    simp [stubUpper]
  have hslot : codePC a.base 17 + sign_extend 12#12 = codePC a.base 20 := by
    change BitVec.addInt (codePC a.base 17) 12 = codePC a.base 20
    rw [codePC, pcAt, addInt_compose]
    rfl
  have step12 : rvStep (a.stubUpper s) = some (a.stubLoad s) := by
    simpa only [stubLoad, registerState, codePC_next] using
      step_stub_load (a.config_stubUpper h) (codePC a.base 18) (codePC a.base 17) a.callback
        hp11 ht3 (codePC_inUserRam layout.codeRam (by decide))
        (codePC_aligned layout.codeRam layout.codeAlign (by decide))
        ((image4.words ⟨18, by decide⟩).of_mem_eq rfl)
        (by rw [hslot]; exact slot_inUserRam layout.codeRam)
        (by rw [hslot]; exact slot_aligned layout.codeRam layout.codeAlign)
        (by rw [hslot]; exact image4.slot.of_mem_eq rfl)
  have hcallback : (a.stubLoad s).regs.get? .x28 = some a.callback := by
    simp [stubLoad]
  have step13 : rvStep (a.stubLoad s) = some (a.paused s) :=
    step_stub_jump (a.config_stubLoad h) (codePC a.base 19) a.callback hp12 hcallback
      (codePC_inUserRam layout.codeRam (by decide))
      (codePC_aligned layout.codeRam layout.codeAlign (by decide)) layout.callbackAlign
      ((image4.words ⟨19, by decide⟩).of_mem_eq rfl)
  refine .step hpc (by simpa using hcode 0 (by decide)) step1 ?_
  refine .step hp1 (hcode 1 (by decide)) step2 ?_
  refine .step hp2 (hcode 2 (by decide)) step3 ?_
  refine .step hp3 (hcode 3 (by decide)) step4 ?_
  refine .step hp4 (hcode 4 (by decide)) step5 ?_
  refine .step hp5 (hcode 5 (by decide)) step6 ?_
  refine .step hp6 (hcode 6 (by decide)) step7 ?_
  refine .step hp7 (hcode 7 (by decide)) step8 ?_
  refine .step hp8 (hcode 8 (by decide)) step9 ?_
  refine .step hp9 (hcode 9 (by decide)) step10 ?_
  refine .step hp10 (hcode 17 (by decide)) step11 ?_
  refine .step hp11 (hcode 18 (by decide)) step12 ?_
  refine .step hp12 (hcode 19 (by decide)) step13 ?_
  exact .leave (a.paused_pc s) hout rfl

end Registers

end CallInputs

end MetrologyAsm.OTP
