import MetrologyAsm.Examples.OTP.Decode
import MetrologyAsm.Sail.IntegerSteps

/-! # Actual Sail instruction steps for the OTP function -/

namespace MetrologyAsm.OTP

open RiscvZkvm.Sail.Functions Sail

/-- The call sets its target and saves the next instruction address in ra. -/
def linkBodyState (s : Mach) (pc target : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with
    regs := (prepared.regs.insert .nextPC target).insert .x1 (BitVec.addInt pc 4) }

/-- The import trampoline sets its target without changing the saved link register. -/
def jumpBodyState (s : Mach) (pc target : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert .nextPC target }

variable {s : Mach} (h : UserConfig s) (pc : BitVec 64)
include h

/-- Fetch the allocated instruction word after the wrapper's retirement-count update. -/
private theorem fetchInstruction (word : BitVec 32)
    (hpc : s.regs.get? .PC = some pc) (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false) (hword : Word32At s pc word) :
    runSail (fetch ()) (counterState s) = some (.F_Base word, counterState s) := by
  have hpc' : (counterState s).regs.get? .PC = some pc := by
    simp [counterState, Std.ExtDHashMap.get?_insert, hpc]
  exact h.counterState.fetch32 pc word hpc' hram halign hbase hword

/-- Reserve the compiler-declared thirty-two-byte stack frame. -/
theorem step_reserve (sp : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hinput : s.regs.get? .x2 = some sp)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0xfe010113#32) :
    rvStep s = some (commitState (registerBodyState s pc .x2 (sp + sign_extend (m := 64) 0xfe0#12))
      (BitVec.addInt pc 4)) := by
  have hinput' : (sequentialState (counterState s) pc).regs.get? .x2 = some sp := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hinput]
  have hbody := execute_ADDI_of_registers 0xfe0#12 (.Regidx 2#5) (.Regidx 2#5)
    sp (rX_bits_sp hinput')
    (wX_bits_sp (sequentialState (counterState s) pc)
      (sp + sign_extend (m := 64) 0xfe0#12))
  apply rvStep_register_instruction h pc 0xfe010113#32
    (.ITYPE (0xfe0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) .x2 (sp + sign_extend (m := 64) 0xfe0#12)
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0xfe010113#32, .ITYPE (0xfe0#12, .Regidx 2#5, .Regidx 2#5, .ADDI))
      (by simp [otpCases]))
  · exact hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- Preserve the pad pointer in the callee-saved s0 register. -/
theorem step_capture_pad (pad : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hinput : s.regs.get? .x11 = some pad)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00058413#32) :
    rvStep s = some (commitState (registerBodyState s pc .x8 pad)
      (BitVec.addInt pc 4)) := by
  have hinput' : (sequentialState (counterState s) pc).regs.get? .x11 = some pad := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hinput]
  have hbody := execute_ADDI_of_registers 0x000#12 (.Regidx 11#5) (.Regidx 8#5)
    pad (rX_bits_a1 hinput')
    (wX_bits_s0 (sequentialState (counterState s) pc)
      (pad + sign_extend (m := 64) 0x000#12))
  apply rvStep_register_instruction h pc 0x00058413#32
    (.ITYPE (0x000#12, .Regidx 11#5, .Regidx 8#5, .ADDI)) .x8 pad
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00058413#32, .ITYPE (0x000#12, .Regidx 11#5, .Regidx 8#5, .ADDI))
      (by simp [otpCases]))
  · simpa only [execute, registerBodyState,
      show sign_extend (m := 64) 0x000#12 = 0#64 by decide +kernel,
      BitVec.add_zero] using hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- Preserve the message in the callee-saved s1 register. -/
theorem step_capture_message (message : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hinput : s.regs.get? .x10 = some message)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00050493#32) :
    rvStep s = some (commitState (registerBodyState s pc .x9 message)
      (BitVec.addInt pc 4)) := by
  have hinput' : (sequentialState (counterState s) pc).regs.get? .x10 = some message := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hinput]
  have hbody := execute_ADDI_of_registers 0x000#12 (.Regidx 10#5) (.Regidx 9#5)
    message (rX_bits_a0 hinput')
    (wX_bits_s1 (sequentialState (counterState s) pc)
      (message + sign_extend (m := 64) 0x000#12))
  apply rvStep_register_instruction h pc 0x00050493#32
    (.ITYPE (0x000#12, .Regidx 10#5, .Regidx 9#5, .ADDI)) .x9 message
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00050493#32, .ITYPE (0x000#12, .Regidx 10#5, .Regidx 9#5, .ADDI))
      (by simp [otpCases]))
  · simpa only [execute, registerBodyState,
      show sign_extend (m := 64) 0x000#12 = 0#64 by decide +kernel,
      BitVec.add_zero] using hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- Set the randombytes length argument to one. -/
theorem step_length
    (hpc : s.regs.get? .PC = some pc)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00100593#32) :
    rvStep s = some (commitState (registerBodyState s pc .x11 1#64)
      (BitVec.addInt pc 4)) := by
  have hbody := execute_ADDI_of_registers 0x001#12 (.Regidx 0#5) (.Regidx 11#5)
    0#64 (rX_bits_zero _)
    (wX_bits_a1 (sequentialState (counterState s) pc)
      (0#64 + sign_extend (m := 64) 0x001#12))
  apply rvStep_register_instruction h pc 0x00100593#32
    (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) .x11 1#64
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00100593#32, .ITYPE (0x001#12, .Regidx 0#5, .Regidx 11#5, .ADDI))
      (by simp [otpCases]))
  · simpa only [execute, registerBodyState,
      show sign_extend (m := 64) 0x001#12 = 1#64 by decide +kernel,
      BitVec.zero_add] using hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- Place the saved pad pointer in the first import argument register. -/
theorem step_argument (pad : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hinput : s.regs.get? .x8 = some pad)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00040513#32) :
    rvStep s = some (commitState (registerBodyState s pc .x10 pad)
      (BitVec.addInt pc 4)) := by
  have hinput' : (sequentialState (counterState s) pc).regs.get? .x8 = some pad := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hinput]
  have hbody := execute_ADDI_of_registers 0x000#12 (.Regidx 8#5) (.Regidx 10#5)
    pad (rX_bits_s0 hinput')
    (wX_bits_a0 (sequentialState (counterState s) pc)
      (pad + sign_extend (m := 64) 0x000#12))
  apply rvStep_register_instruction h pc 0x00040513#32
    (.ITYPE (0x000#12, .Regidx 8#5, .Regidx 10#5, .ADDI)) .x10 pad
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00040513#32, .ITYPE (0x000#12, .Regidx 8#5, .Regidx 10#5, .ADDI))
      (by simp [otpCases]))
  · simpa only [execute, registerBodyState,
      show sign_extend (m := 64) 0x000#12 = 0#64 by decide +kernel,
      BitVec.add_zero] using hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- Release the compiler-declared stack frame. -/
theorem step_release (sp : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hinput : s.regs.get? .x2 = some sp)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x02010113#32) :
    rvStep s = some (commitState (registerBodyState s pc .x2 (sp + sign_extend (m := 64) 0x020#12))
      (BitVec.addInt pc 4)) := by
  have hinput' : (sequentialState (counterState s) pc).regs.get? .x2 = some sp := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hinput]
  have hbody := execute_ADDI_of_registers 0x020#12 (.Regidx 2#5) (.Regidx 2#5)
    sp (rX_bits_sp hinput')
    (wX_bits_sp (sequentialState (counterState s) pc)
      (sp + sign_extend (m := 64) 0x020#12))
  apply rvStep_register_instruction h pc 0x02010113#32
    (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) .x2 (sp + sign_extend (m := 64) 0x020#12)
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x02010113#32, .ITYPE (0x020#12, .Regidx 2#5, .Regidx 2#5, .ADDI))
      (by simp [otpCases]))
  · exact hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- Save the original return address in its scratch-stack slot. -/
theorem step_save_ra (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hvalue : s.regs.get? .x1 = some value)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00113c23#32)
    (hram : InUserRam (sp + sign_extend (m := 64) 24#12) 8)
    (hdataAlign : (sp + sign_extend (m := 64) 24#12).toNat % 8 = 0) :
    rvStep s = some (commitState
      (storeBodyState s pc (sp + sign_extend (m := 64) 24#12) value) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hsp' : (sequentialState (counterState s) pc).regs.get? .x2 = some sp := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hsp]
  have hvalue' : (sequentialState (counterState s) pc).regs.get? .x1 = some value := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hvalue]
  have hbody := hs.execute_STORE64 24#12 (.Regidx 1#5) (.Regidx 2#5) sp value
    hram hdataAlign (rX_bits_sp hsp') (rX_bits_ra hvalue')
  apply rvStep_memory_instruction h pc 0x00113c23#32
    (.STORE (24#12, .Regidx 1#5, .Regidx 2#5, 8)) (sp + sign_extend (m := 64) 24#12) value
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00113c23#32, .STORE (24#12, .Regidx 1#5, .Regidx 2#5, 8))
      (by simp [otpCases]))
  exact hbody

/-- Save the original s0 register in its scratch-stack slot. -/
theorem step_save_s0 (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hvalue : s.regs.get? .x8 = some value)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00813823#32)
    (hram : InUserRam (sp + sign_extend (m := 64) 16#12) 8)
    (hdataAlign : (sp + sign_extend (m := 64) 16#12).toNat % 8 = 0) :
    rvStep s = some (commitState
      (storeBodyState s pc (sp + sign_extend (m := 64) 16#12) value) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hsp' : (sequentialState (counterState s) pc).regs.get? .x2 = some sp := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hsp]
  have hvalue' : (sequentialState (counterState s) pc).regs.get? .x8 = some value := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hvalue]
  have hbody := hs.execute_STORE64 16#12 (.Regidx 8#5) (.Regidx 2#5) sp value
    hram hdataAlign (rX_bits_sp hsp') (rX_bits_s0 hvalue')
  apply rvStep_memory_instruction h pc 0x00813823#32
    (.STORE (16#12, .Regidx 8#5, .Regidx 2#5, 8)) (sp + sign_extend (m := 64) 16#12) value
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00813823#32, .STORE (16#12, .Regidx 8#5, .Regidx 2#5, 8))
      (by simp [otpCases]))
  exact hbody

/-- Save the original s1 register in its scratch-stack slot. -/
theorem step_save_s1 (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hvalue : s.regs.get? .x9 = some value)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00913423#32)
    (hram : InUserRam (sp + sign_extend (m := 64) 8#12) 8)
    (hdataAlign : (sp + sign_extend (m := 64) 8#12).toNat % 8 = 0) :
    rvStep s = some (commitState
      (storeBodyState s pc (sp + sign_extend (m := 64) 8#12) value) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hsp' : (sequentialState (counterState s) pc).regs.get? .x2 = some sp := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hsp]
  have hvalue' : (sequentialState (counterState s) pc).regs.get? .x9 = some value := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hvalue]
  have hbody := hs.execute_STORE64 8#12 (.Regidx 9#5) (.Regidx 2#5) sp value
    hram hdataAlign (rX_bits_sp hsp') (rX_bits_s1 hvalue')
  apply rvStep_memory_instruction h pc 0x00913423#32
    (.STORE (8#12, .Regidx 9#5, .Regidx 2#5, 8)) (sp + sign_extend (m := 64) 8#12) value
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00913423#32, .STORE (8#12, .Regidx 9#5, .Regidx 2#5, 8))
      (by simp [otpCases]))
  exact hbody

/-- Restore the original return address from its allocated stack word. -/
theorem step_restore_ra (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x01813083#32)
    (hram : InUserRam (sp + sign_extend (m := 64) 24#12) 8)
    (hdataAlign : (sp + sign_extend (m := 64) 24#12).toNat % 8 = 0)
    (hdata : Word64At s (sp + sign_extend (m := 64) 24#12) value) :
    rvStep s = some (commitState (registerBodyState s pc .x1 value) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hsp' : (sequentialState (counterState s) pc).regs.get? .x2 = some sp := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hsp]
  have hbody := hs.execute_LOAD64 24#12 (.Regidx 2#5) (.Regidx 1#5) sp value
    hram hdataAlign (rX_bits_sp hsp') hdata
    (wX_bits_ra (sequentialState (counterState s) pc) value)
  apply rvStep_register_instruction h pc 0x01813083#32
    (.LOAD (24#12, .Regidx 2#5, .Regidx 1#5, false, 8))
    .x1 value hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x01813083#32, .LOAD (24#12, .Regidx 2#5, .Regidx 1#5, false, 8))
      (by simp [otpCases]))
  · exact hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- Restore the original s0 register from its allocated stack word. -/
theorem step_restore_s0 (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x01013403#32)
    (hram : InUserRam (sp + sign_extend (m := 64) 16#12) 8)
    (hdataAlign : (sp + sign_extend (m := 64) 16#12).toNat % 8 = 0)
    (hdata : Word64At s (sp + sign_extend (m := 64) 16#12) value) :
    rvStep s = some (commitState (registerBodyState s pc .x8 value) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hsp' : (sequentialState (counterState s) pc).regs.get? .x2 = some sp := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hsp]
  have hbody := hs.execute_LOAD64 16#12 (.Regidx 2#5) (.Regidx 8#5) sp value
    hram hdataAlign (rX_bits_sp hsp') hdata
    (wX_bits_s0 (sequentialState (counterState s) pc) value)
  apply rvStep_register_instruction h pc 0x01013403#32
    (.LOAD (16#12, .Regidx 2#5, .Regidx 8#5, false, 8))
    .x8 value hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x01013403#32, .LOAD (16#12, .Regidx 2#5, .Regidx 8#5, false, 8))
      (by simp [otpCases]))
  · exact hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- Restore the original s1 register from its allocated stack word. -/
theorem step_restore_s1 (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00813483#32)
    (hram : InUserRam (sp + sign_extend (m := 64) 8#12) 8)
    (hdataAlign : (sp + sign_extend (m := 64) 8#12).toNat % 8 = 0)
    (hdata : Word64At s (sp + sign_extend (m := 64) 8#12) value) :
    rvStep s = some (commitState (registerBodyState s pc .x9 value) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hsp' : (sequentialState (counterState s) pc).regs.get? .x2 = some sp := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hsp]
  have hbody := hs.execute_LOAD64 8#12 (.Regidx 2#5) (.Regidx 9#5) sp value
    hram hdataAlign (rX_bits_sp hsp') hdata
    (wX_bits_s1 (sequentialState (counterState s) pc) value)
  apply rvStep_register_instruction h pc 0x00813483#32
    (.LOAD (8#12, .Regidx 2#5, .Regidx 9#5, false, 8))
    .x9 value hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00813483#32, .LOAD (8#12, .Regidx 2#5, .Regidx 9#5, false, 8))
      (by simp [otpCases]))
  · exact hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- The compiled unsigned load reads the callback's actual pad byte through s0. -/
theorem step_load_pad (pad : BitVec 64) (byte : BitVec 8)
    (hpc : s.regs.get? .PC = some pc) (hpad : s.regs.get? .x8 = some pad)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00044503#32) (hram : InUserRam pad 1)
    (hbyte : s.mem.get? pad.toNat = some byte) :
    rvStep s = some (commitState (registerBodyState s pc .x10 (byte.setWidth 64))
      (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hpad' : (sequentialState (counterState s) pc).regs.get? .x8 = some pad := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hpad]
  have hbody := hs.execute_LBU 0#12 (.Regidx 8#5) (.Regidx 10#5) pad byte
    (rX_bits_s0 hpad') (by simpa [sign_extend, Sail.BitVec.signExtend] using hram)
    (by simpa [sign_extend, Sail.BitVec.signExtend, sequentialState, counterState] using hbyte)
    (wX_bits_a0 (sequentialState (counterState s) pc) (byte.setWidth 64))
  apply rvStep_register_instruction h pc 0x00044503#32
    (.LOAD (0#12, .Regidx 8#5, .Regidx 10#5, true, 1)) .x10 (byte.setWidth 64)
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00044503#32, .LOAD (0#12, .Regidx 8#5, .Regidx 10#5, true, 1))
      (by simp [otpCases]))
  · exact hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- The compiled XOR combines the sampled pad and saved message through the full Sail wrapper. -/
theorem step_xor (pad message : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hpad : s.regs.get? .x10 = some pad)
    (hmessage : s.regs.get? .x9 = some message)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00954533#32) :
    rvStep s = some (commitState (registerBodyState s pc .x10 (pad ^^^ message))
      (BitVec.addInt pc 4)) := by
  have hpad' : (sequentialState (counterState s) pc).regs.get? .x10 = some pad := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hpad]
  have hmessage' : (sequentialState (counterState s) pc).regs.get? .x9 = some message := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hmessage]
  have hbody := execute_XOR_of_registers (.Regidx 10#5) (.Regidx 9#5) (.Regidx 10#5)
    pad message (rX_bits_a0 hpad') (rX_bits_s1 hmessage')
    (wX_bits_a0 (sequentialState (counterState s) pc) (pad ^^^ message))
  apply rvStep_register_instruction h pc 0x00954533#32
    (.RTYPE (.Regidx 9#5, .Regidx 10#5, .Regidx 10#5, .XOR)) .x10 (pad ^^^ message)
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00954533#32, .RTYPE (.Regidx 9#5, .Regidx 10#5, .Regidx 10#5, .XOR))
      (by simp [otpCases]))
  · exact hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- The zero-upper-immediate AUIPC records its current code address in ra. -/
theorem step_call_upper (hpc : s.regs.get? .PC = some pc)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00000097#32) :
    rvStep s = some (commitState (registerBodyState s pc .x1 pc) (BitVec.addInt pc 4)) := by
  have hpc' : (sequentialState (counterState s) pc).regs.get? .PC = some pc := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hpc]
  have hbody : execute_UTYPE 0#20 (.Regidx 1#5) .AUIPC
      (sequentialState (counterState s) pc) =
      .ok (.Retire_Success ()) (registerBodyState s pc .x1 pc) := by
    apply execute_AUIPC_of_registers 0#20 (.Regidx 1#5) pc hpc'
    simpa [sign_extend, Sail.BitVec.signExtend, registerBodyState] using wX_bits_ra _ pc
  apply rvStep_register_instruction h pc 0x00000097#32
    (.UTYPE (0#20, .Regidx 1#5, .AUIPC)) .x1 pc hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct (0x00000097#32, .UTYPE (0#20, .Regidx 1#5, .AUIPC)) (by simp [otpCases]))
  · exact hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- The zero-upper-immediate AUIPC records its current code address in t3. -/
theorem step_stub_upper (hpc : s.regs.get? .PC = some pc)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00000e17#32) :
    rvStep s = some (commitState (registerBodyState s pc .x28 pc) (BitVec.addInt pc 4)) := by
  have hpc' : (sequentialState (counterState s) pc).regs.get? .PC = some pc := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hpc]
  have hbody : execute_UTYPE 0#20 (.Regidx 28#5) .AUIPC
      (sequentialState (counterState s) pc) =
      .ok (.Retire_Success ()) (registerBodyState s pc .x28 pc) := by
    apply execute_AUIPC_of_registers 0#20 (.Regidx 28#5) pc hpc'
    simpa [sign_extend, Sail.BitVec.signExtend, registerBodyState] using wX_bits_t3 _ pc
  apply rvStep_register_instruction h pc 0x00000e17#32
    (.UTYPE (0#20, .Regidx 28#5, .AUIPC)) .x28 pc hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct (0x00000e17#32, .UTYPE (0#20, .Regidx 28#5, .AUIPC)) (by simp [otpCases]))
  · exact hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- The trampoline reads the relocated randombytes address through its actual code-relative slot. -/
theorem step_stub_load (base target : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hreg : s.regs.get? .x28 = some base)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00ce3e03#32)
    (hram : InUserRam (base + sign_extend (m := 64) 12#12) 8)
    (hdataAlign : (base + sign_extend (m := 64) 12#12).toNat % 8 = 0)
    (hdata : Word64At s (base + sign_extend (m := 64) 12#12) target) :
    rvStep s = some (commitState (registerBodyState s pc .x28 target) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hreg' : (sequentialState (counterState s) pc).regs.get? .x28 = some base := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hreg]
  have hbody := hs.execute_LOAD64 12#12 (.Regidx 28#5) (.Regidx 28#5) base target
    hram hdataAlign (rX_bits_t3 hreg') hdata
    (wX_bits_t3 (sequentialState (counterState s) pc) target)
  apply rvStep_register_instruction h pc 0x00ce3e03#32
    (.LOAD (12#12, .Regidx 28#5, .Regidx 28#5, false, 8)) .x28 target
    hpc hcode halign (by decide +kernel) hword
    (otp_decoder_correct
      (0x00ce3e03#32, .LOAD (12#12, .Regidx 28#5, .Regidx 28#5, false, 8))
      (by simp [otpCases]))
  · exact hbody
  · trivial
  · decide +kernel
  · decide +kernel

/-- The compiled call jumps to its trampoline and saves the continuation in ra. -/
theorem step_call_link (base : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hra : s.regs.get? .x1 = some base)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (htarget : (BitVec.addInt base 36).toNat % 4 = 0) (hword : Word32At s pc 0x024080e7#32) :
    rvStep s = some (commitState (linkBodyState s pc (BitVec.addInt base 36))
      (BitVec.addInt base 36)) := by
  have hs := h.counterState.sequentialState pc
  have hra' : (sequentialState (counterState s) pc).regs.get? .x1 = some base := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hra]
  have hn : (sequentialState (counterState s) pc).regs.get? .nextPC =
      some (BitVec.addInt pc 4) := by
    simp [sequentialState]
  have hm : BitVec.update (base + sign_extend (m := 64) 36#12) 0 0#1 = BitVec.addInt base 36 := by
    change BitVec.update (BitVec.addInt base 36) 0 0#1 = BitVec.addInt base 36
    exact clear_lowbit_self _ (aligned4_access htarget).1
  have hbody : execute_JALR 36#12 (.Regidx 1#5) (.Regidx 1#5)
      (sequentialState (counterState s) pc) =
      .ok (.Retire_Success ()) (linkBodyState s pc (BitVec.addInt base 36)) := by
    apply execute_JALR_of_registers hs 36#12 (.Regidx 1#5) (.Regidx 1#5) base (BitVec.addInt pc 4)
    · exact rX_bits_ra hra'
    · exact hn
    · simpa only [hm] using htarget
    · rw [hm]
      exact wX_bits_ra _ _
  apply rvStep_user_of_execute h pc 0x024080e7#32
    (.JALR (36#12, .Regidx 1#5, .Regidx 1#5)) (BitVec.addInt base 36) hpc
    (fetchInstruction h pc _ hpc hcode halign (by decide +kernel) hword)
  · exact decode_of_guarded h.counterState _ _
      (otp_decoder_correct
        (0x024080e7#32, .JALR (36#12, .Regidx 1#5, .Regidx 1#5)) (by simp [otpCases]))
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact (hs.insert .nextPC _ trivial).insert .x1 _ trivial
  · simp [linkBodyState, Std.ExtDHashMap.get?_insert]
  · simp [linkBodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

/-- The import trampoline reaches the callback while preserving the saved continuation. -/
theorem step_stub_jump (target : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hreg : s.regs.get? .x28 = some target)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0) (htarget : target.toNat % 4 = 0)
    (hword : Word32At s pc 0x000e0067#32) :
    rvStep s = some (commitState (jumpBodyState s pc target) target) := by
  have hs := h.counterState.sequentialState pc
  have hreg' : (sequentialState (counterState s) pc).regs.get? .x28 = some target := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hreg]
  have hn : (sequentialState (counterState s) pc).regs.get? .nextPC =
      some (BitVec.addInt pc 4) := by
    simp [sequentialState]
  have hm : BitVec.update (target + sign_extend (m := 64) 0#12) 0 0#1 = target := by
    simpa [sign_extend, Sail.BitVec.signExtend] using
      clear_lowbit_self target (aligned4_access htarget).1
  have hbody : execute_JALR 0#12 (.Regidx 28#5) (.Regidx 0#5)
      (sequentialState (counterState s) pc) =
      .ok (.Retire_Success ()) (jumpBodyState s pc target) := by
    apply execute_JALR_of_registers hs 0#12 (.Regidx 28#5) (.Regidx 0#5) target (BitVec.addInt pc 4)
    · exact rX_bits_t3 hreg'
    · exact hn
    · simpa only [hm] using htarget
    · rw [hm]
      rfl
  apply rvStep_user_of_execute h pc 0x000e0067#32
    (.JALR (0#12, .Regidx 28#5, .Regidx 0#5)) target hpc
    (fetchInstruction h pc _ hpc hcode halign (by decide +kernel) hword)
  · exact decode_of_guarded h.counterState _ _
      (otp_decoder_correct
        (0x000e0067#32, .JALR (0#12, .Regidx 28#5, .Regidx 0#5)) (by simp [otpCases]))
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact hs.insert .nextPC target trivial
  · simp [jumpBodyState]
  · simp [jumpBodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

/-- The compiled return restores the actual external return target through the full Sail wrapper. -/
theorem step_return (target : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hra : s.regs.get? .x1 = some target)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0) (htarget : target.toNat % 4 = 0)
    (hword : Word32At s pc 0x00008067#32) :
    rvStep s = some (commitState (retBodyState s pc target) target) :=
  rvStep_ret h pc target hpc hra hcode halign htarget hword

end MetrologyAsm.OTP
