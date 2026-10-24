import MetrologyAsm.Examples.OTP.Decode
import MetrologyAsm.Sail.IntegerSteps

/-! # Actual Sail instruction steps for the OTP function -/

namespace MetrologyAsm.OTP

open RiscvZkvm.Sail.Functions Sail
open Std.ExtDHashMap (get?_insert)

/-- The prepared state holds the address of the following instruction in the next-pc register. -/
private theorem nextPC_sequentialState (s : Mach) (pc : BitVec 64) :
    (sequentialState s pc).regs.get? .nextPC = some (BitVec.addInt pc 4) := by
  simp [sequentialState]

/-- The word decodes to the instruction in the OTP table and is not a compressed instruction. -/
private abbrev Decodes (word : BitVec 32) (inst : instruction) : Prop :=
  (word, inst) ∈ otpCases ∧ isRVC (Sail.BitVec.extractLsb word 15 0) = false

/-- A write to the destination is permitted and leaves the bookkeeping registers alone. -/
private abbrev RegOk (dst : Register) (value : RegisterType dst) : Prop :=
  userRegPolicy dst value ∧ dst ≠ .nextPC ∧ dst ≠ .minstret_increment

/-- The register-write body state for a doubleword value in a register of doubleword type. -/
private abbrev writeBody (s : Mach) (pc : BitVec 64) (dst : Register)
    (hty : RegisterType dst = BitVec 64) (value : BitVec 64) : Mach :=
  registerBodyState s pc dst (cast hty.symm value)

local macro "otp_decodes" : tactic => `(tactic| exact ⟨by simp [otpCases], by decide +kernel⟩)
local macro "otp_reg_ok" : tactic => `(tactic| refine ⟨trivial, ?_, ?_⟩ <;> decide)

variable {s : Mach} (h : UserConfig s) (pc : BitVec 64)
include h

/-- Fetch the instruction word after the wrapper's retirement-count update. -/
private theorem fetch_instruction (word : BitVec 32)
    (hpc : s.regs.get? .PC = some pc) (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false) (hword : Word32At s pc word) :
    runSail (fetch ()) (counterState s) = some (.F_Base word, counterState s) := by
  have hpc' : (counterState s).regs.get? .PC = some pc := by
    simp [counterState, get?_insert, hpc]
  exact h.counterState.fetch32 pc word hpc' hram halign hbase hword

/-- A register-writing instruction with a verified body takes one full machine step. -/
private theorem step_reg (word : BitVec 32) (inst : instruction) (dst : Register)
    (value : RegisterType dst)
    (hpc : s.regs.get? .PC = some pc) (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc word)
    (hbody : execute inst (sequentialState (counterState s) pc) =
      .ok (.Retire_Success ()) (registerBodyState s pc dst value))
    (hinst : Decodes word inst := by otp_decodes) (hdst : RegOk dst value := by otp_reg_ok) :
    rvStep s = some (commitState (registerBodyState s pc dst value) (BitVec.addInt pc 4)) :=
  rvStep_register_instruction h pc word inst dst value hpc hcode halign hinst.2 hword
    (otp_decoder_correct (word, inst) hinst.1) hbody hdst.1 hdst.2.1 hdst.2.2

/-- An immediate addition between two registers takes one full machine step. -/
private theorem step_addi (word : BitVec 32) (imm : BitVec 12) (rs rd : BitVec 5)
    (dst : Register) (hty : RegisterType dst = BitVec 64) (source value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc word)
    (hread : rX_bits (.Regidx rs) (sequentialState (counterState s) pc) =
      .ok source (sequentialState (counterState s) pc))
    (hwrite : ∀ w, wX_bits (.Regidx rd) w (sequentialState (counterState s) pc) =
      .ok () (writeBody s pc dst hty w))
    (hval : source + sign_extend imm = value)
    (hinst : Decodes word (.ITYPE (imm, .Regidx rs, .Regidx rd, .ADDI)) := by otp_decodes)
    (hdst : RegOk dst (cast hty.symm value) := by otp_reg_ok) :
    rvStep s = some (commitState (writeBody s pc dst hty value) (BitVec.addInt pc 4)) := by
  subst hval
  exact step_reg h pc word (.ITYPE (imm, .Regidx rs, .Regidx rd, .ADDI)) dst _ hpc hcode halign
    hword
    (execute_ADDI_of_registers imm _ _ source hread (hwrite _)) hinst hdst

/-- A register copy, an addition of zero, takes one full machine step. -/
private theorem step_mv (word : BitVec 32) (rs rd : BitVec 5) (dst : Register)
    (hty : RegisterType dst = BitVec 64) (value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc word)
    (hread : rX_bits (.Regidx rs) (sequentialState (counterState s) pc) =
      .ok value (sequentialState (counterState s) pc))
    (hwrite : ∀ w, wX_bits (.Regidx rd) w (sequentialState (counterState s) pc) =
      .ok () (writeBody s pc dst hty w))
    (hinst : Decodes word (.ITYPE (0x000#12, .Regidx rs, .Regidx rd, .ADDI)) := by otp_decodes)
    (hdst : RegOk dst (cast hty.symm value) := by otp_reg_ok) :
    rvStep s = some (commitState (writeBody s pc dst hty value) (BitVec.addInt pc 4)) :=
  step_addi h pc word 0x000#12 rs rd dst hty value value hpc hcode halign hword hread hwrite
    (by rw [show sign_extend 0x000#12 = 0#64 by decide +kernel, BitVec.add_zero])
    hinst hdst

/-- A doubleword store through the stack pointer takes one full machine step. -/
private theorem step_store_slot (word : BitVec 32) (imm : BitVec 12) (src : BitVec 5)
    (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc word)
    (hram : InUserRam (sp + sign_extend imm) 8)
    (hdataAlign : (sp + sign_extend imm).toNat % 8 = 0)
    (hsp : rX_bits (.Regidx 2#5) (sequentialState (counterState s) pc) =
      .ok sp (sequentialState (counterState s) pc))
    (hvalue : rX_bits (.Regidx src) (sequentialState (counterState s) pc) =
      .ok value (sequentialState (counterState s) pc))
    (hinst : Decodes word (.STORE (imm, .Regidx src, .Regidx 2#5, 8)) := by otp_decodes) :
    rvStep s = some (commitState
      (storeBodyState s pc (sp + sign_extend imm) value) (BitVec.addInt pc 4)) :=
  rvStep_memory_instruction h pc word _ _ value hpc hcode halign hinst.2 hword
    (otp_decoder_correct (word, _) hinst.1)
    ((h.counterState.sequentialState pc).execute_STORE64 imm _ _ sp value hram hdataAlign hsp
      hvalue)

/-- A doubleword load into a register takes one full machine step. -/
private theorem step_load_slot (word : BitVec 32) (imm : BitVec 12) (rs rd : BitVec 5)
    (dst : Register) (hty : RegisterType dst = BitVec 64) (base value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc word)
    (hram : InUserRam (base + sign_extend imm) 8)
    (hdataAlign : (base + sign_extend imm).toNat % 8 = 0)
    (hdata : Word64At s (base + sign_extend imm) value)
    (hbase : rX_bits (.Regidx rs) (sequentialState (counterState s) pc) =
      .ok base (sequentialState (counterState s) pc))
    (hwrite : ∀ w, wX_bits (.Regidx rd) w (sequentialState (counterState s) pc) =
      .ok () (writeBody s pc dst hty w))
    (hinst : Decodes word (.LOAD (imm, .Regidx rs, .Regidx rd, false, 8)) := by otp_decodes)
    (hdst : RegOk dst (cast hty.symm value) := by otp_reg_ok) :
    rvStep s = some (commitState (writeBody s pc dst hty value) (BitVec.addInt pc 4)) :=
  step_reg h pc word (.LOAD (imm, .Regidx rs, .Regidx rd, false, 8)) dst
    (cast hty.symm value) hpc hcode halign hword
    ((h.counterState.sequentialState pc).execute_LOAD64 imm _ _ base value hram hdataAlign hbase
      hdata (hwrite value)) hinst hdst

/-- An AUIPC with a zero immediate writes its own address to a register in one machine step. -/
private theorem step_auipc_zero (word : BitVec 32) (rd : BitVec 5) (dst : Register)
    (hty : RegisterType dst = BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc word)
    (hwrite : ∀ w, wX_bits (.Regidx rd) w (sequentialState (counterState s) pc) =
      .ok () (writeBody s pc dst hty w))
    (hinst : Decodes word (.UTYPE (0#20, .Regidx rd, .AUIPC)) := by otp_decodes)
    (hdst : RegOk dst (cast hty.symm pc) := by otp_reg_ok) :
    rvStep s = some (commitState (writeBody s pc dst hty pc) (BitVec.addInt pc 4)) := by
  refine step_reg h pc word _ dst (cast hty.symm pc) hpc hcode halign hword ?_ hinst hdst
  apply execute_AUIPC_of_registers 0#20 _ pc (sequentialState_get?_of_get? pc hpc)
  simpa [sign_extend, Sail.BitVec.signExtend, registerBodyState] using hwrite pc

/-- An aligned JALR takes one full machine step to its target. -/
private theorem step_jalr (word : BitVec 32) (imm : BitVec 12) (rs rd : BitVec 5)
    (value target : BitVec 64) (t : Mach)
    (hpc : s.regs.get? .PC = some pc) (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc word)
    (hread : rX_bits (.Regidx rs) (sequentialState (counterState s) pc) =
      .ok value (sequentialState (counterState s) pc))
    (hm : BitVec.update (value + sign_extend imm) 0 0#1 = target)
    (htarget : target.toNat % 4 = 0)
    (hwrite : wX_bits (.Regidx rd) (BitVec.addInt pc 4) { sequentialState (counterState s) pc with
      regs := (sequentialState (counterState s) pc).regs.insert .nextPC target } = .ok () t)
    (ht : UserConfig t) (hnext : t.regs.get? .nextPC = some target)
    (hflag : t.regs.get? .minstret_increment = some false)
    (hinst : Decodes word (.JALR (imm, .Regidx rs, .Regidx rd)) := by otp_decodes) :
    rvStep s = some (commitState t target) := by
  have hbody : execute_JALR imm (.Regidx rs) (.Regidx rd) (sequentialState (counterState s) pc) =
      .ok (.Retire_Success ()) t :=
    execute_JALR_of_registers (h.counterState.sequentialState pc) imm _ _ value
      (BitVec.addInt pc 4) hread (nextPC_sequentialState _ pc) (by simpa only [hm] using htarget)
      (by rw [hm]; exact hwrite)
  refine rvStep_user_of_execute h pc word _ target hpc
    (fetch_instruction h pc _ hpc hcode halign hinst.2 hword)
    (decode_of_guarded h.counterState _ _ (otp_decoder_correct (word, _) hinst.1)) ?_ ht hnext
    hflag
  rw [runSail_eq_some_iff]
  exact hbody

/-- Reserve the compiler-declared thirty-two-byte stack frame. -/
theorem step_reserve (sp : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hinput : s.regs.get? .x2 = some sp)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0xfe010113#32) :
    rvStep s = some (commitState (registerBodyState s pc .x2 (sp + sign_extend 0xfe0#12))
      (BitVec.addInt pc 4)) :=
  step_addi h pc 0xfe010113#32 0xfe0#12 2#5 2#5 .x2 rfl sp _ hpc hcode halign hword
    (rX_bits_sp (sequentialState_get?_of_get? pc hinput)) (wX_bits_sp _) rfl

/-- Preserve the pad pointer in the callee-saved s0 register. -/
theorem step_capture_pad (pad : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hinput : s.regs.get? .x11 = some pad)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00058413#32) :
    rvStep s = some (commitState (registerBodyState s pc .x8 pad) (BitVec.addInt pc 4)) :=
  step_mv h pc 0x00058413#32 11#5 8#5 .x8 rfl pad hpc hcode halign hword
    (rX_bits_a1 (sequentialState_get?_of_get? pc hinput)) (wX_bits_s0 _)

/-- Preserve the message in the callee-saved s1 register. -/
theorem step_capture_message (message : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hinput : s.regs.get? .x10 = some message)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00050493#32) :
    rvStep s = some (commitState (registerBodyState s pc .x9 message) (BitVec.addInt pc 4)) :=
  step_mv h pc 0x00050493#32 10#5 9#5 .x9 rfl message hpc hcode halign hword
    (rX_bits_a0 (sequentialState_get?_of_get? pc hinput)) (wX_bits_s1 _)

/-- Set the randombytes length argument to one. -/
theorem step_length
    (hpc : s.regs.get? .PC = some pc)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00100593#32) :
    rvStep s = some (commitState (registerBodyState s pc .x11 1#64) (BitVec.addInt pc 4)) :=
  step_addi h pc 0x00100593#32 0x001#12 0#5 11#5 .x11 rfl 0#64 1#64 hpc hcode halign hword
    (rX_bits_zero _) (wX_bits_a1 _) (by decide +kernel)

/-- Place the saved pad pointer in the first import argument register. -/
theorem step_argument (pad : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hinput : s.regs.get? .x8 = some pad)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00040513#32) :
    rvStep s = some (commitState (registerBodyState s pc .x10 pad) (BitVec.addInt pc 4)) :=
  step_mv h pc 0x00040513#32 8#5 10#5 .x10 rfl pad hpc hcode halign hword
    (rX_bits_s0 (sequentialState_get?_of_get? pc hinput)) (wX_bits_a0 _)

/-- Release the compiler-declared stack frame. -/
theorem step_release (sp : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hinput : s.regs.get? .x2 = some sp)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x02010113#32) :
    rvStep s = some (commitState (registerBodyState s pc .x2 (sp + sign_extend 0x020#12))
      (BitVec.addInt pc 4)) :=
  step_addi h pc 0x02010113#32 0x020#12 2#5 2#5 .x2 rfl sp _ hpc hcode halign hword
    (rX_bits_sp (sequentialState_get?_of_get? pc hinput)) (wX_bits_sp _) rfl

/-- Save the original return address in its saved stack slot. -/
theorem step_save_ra (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hvalue : s.regs.get? .x1 = some value)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00113c23#32)
    (hram : InUserRam (sp + sign_extend 24#12) 8)
    (hdataAlign : (sp + sign_extend 24#12).toNat % 8 = 0) :
    rvStep s = some (commitState
      (storeBodyState s pc (sp + sign_extend 24#12) value) (BitVec.addInt pc 4)) :=
  step_store_slot h pc 0x00113c23#32 24#12 1#5 sp value hpc hcode halign hword hram
    hdataAlign (rX_bits_sp (sequentialState_get?_of_get? pc hsp))
    (rX_bits_ra (sequentialState_get?_of_get? pc hvalue))

/-- Save the original s0 register in its saved stack slot. -/
theorem step_save_s0 (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hvalue : s.regs.get? .x8 = some value)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00813823#32)
    (hram : InUserRam (sp + sign_extend 16#12) 8)
    (hdataAlign : (sp + sign_extend 16#12).toNat % 8 = 0) :
    rvStep s = some (commitState
      (storeBodyState s pc (sp + sign_extend 16#12) value) (BitVec.addInt pc 4)) :=
  step_store_slot h pc 0x00813823#32 16#12 8#5 sp value hpc hcode halign hword hram
    hdataAlign (rX_bits_sp (sequentialState_get?_of_get? pc hsp))
    (rX_bits_s0 (sequentialState_get?_of_get? pc hvalue))

/-- Save the original s1 register in its saved stack slot. -/
theorem step_save_s1 (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hvalue : s.regs.get? .x9 = some value)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00913423#32)
    (hram : InUserRam (sp + sign_extend 8#12) 8)
    (hdataAlign : (sp + sign_extend 8#12).toNat % 8 = 0) :
    rvStep s = some (commitState
      (storeBodyState s pc (sp + sign_extend 8#12) value) (BitVec.addInt pc 4)) :=
  step_store_slot h pc 0x00913423#32 8#12 9#5 sp value hpc hcode halign hword hram
    hdataAlign (rX_bits_sp (sequentialState_get?_of_get? pc hsp))
    (rX_bits_s1 (sequentialState_get?_of_get? pc hvalue))

/-- Restore the original return address from its saved stack slot. -/
theorem step_restore_ra (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x01813083#32)
    (hram : InUserRam (sp + sign_extend 24#12) 8)
    (hdataAlign : (sp + sign_extend 24#12).toNat % 8 = 0)
    (hdata : Word64At s (sp + sign_extend 24#12) value) :
    rvStep s = some (commitState (registerBodyState s pc .x1 value) (BitVec.addInt pc 4)) :=
  step_load_slot h pc 0x01813083#32 24#12 2#5 1#5 .x1 rfl sp value hpc hcode halign hword hram
    hdataAlign hdata (rX_bits_sp (sequentialState_get?_of_get? pc hsp)) (wX_bits_ra _)

/-- Restore the original s0 register from its saved stack slot. -/
theorem step_restore_s0 (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x01013403#32)
    (hram : InUserRam (sp + sign_extend 16#12) 8)
    (hdataAlign : (sp + sign_extend 16#12).toNat % 8 = 0)
    (hdata : Word64At s (sp + sign_extend 16#12) value) :
    rvStep s = some (commitState (registerBodyState s pc .x8 value) (BitVec.addInt pc 4)) :=
  step_load_slot h pc 0x01013403#32 16#12 2#5 8#5 .x8 rfl sp value hpc hcode halign hword hram
    hdataAlign hdata (rX_bits_sp (sequentialState_get?_of_get? pc hsp)) (wX_bits_s0 _)

/-- Restore the original s1 register from its saved stack slot. -/
theorem step_restore_s1 (sp value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hsp : s.regs.get? .x2 = some sp)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00813483#32)
    (hram : InUserRam (sp + sign_extend 8#12) 8)
    (hdataAlign : (sp + sign_extend 8#12).toNat % 8 = 0)
    (hdata : Word64At s (sp + sign_extend 8#12) value) :
    rvStep s = some (commitState (registerBodyState s pc .x9 value) (BitVec.addInt pc 4)) :=
  step_load_slot h pc 0x00813483#32 8#12 2#5 9#5 .x9 rfl sp value hpc hcode halign hword hram
    hdataAlign hdata (rX_bits_sp (sequentialState_get?_of_get? pc hsp)) (wX_bits_s1 _)

/-- The compiled unsigned load reads the callback's actual pad byte through s0. -/
theorem step_load_pad (pad : BitVec 64) (byte : BitVec 8)
    (hpc : s.regs.get? .PC = some pc) (hpad : s.regs.get? .x8 = some pad)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00044503#32) (hram : InUserRam pad 1)
    (hbyte : s.mem.get? pad.toNat = some byte) :
    rvStep s = some (commitState (registerBodyState s pc .x10 (byte.setWidth 64))
      (BitVec.addInt pc 4)) :=
  step_reg h pc 0x00044503#32 (.LOAD (0#12, .Regidx 8#5, .Regidx 10#5, true, 1)) .x10
    (byte.setWidth 64) hpc hcode halign hword
    ((h.counterState.sequentialState pc).execute_LBU 0#12 (.Regidx 8#5) (.Regidx 10#5) pad byte
      (rX_bits_s0 (sequentialState_get?_of_get? pc hpad))
      (by simpa [sign_extend, Sail.BitVec.signExtend] using hram)
      (by simpa [sign_extend, Sail.BitVec.signExtend, sequentialState, counterState] using hbyte)
      (wX_bits_a0 _ _))

/-- The compiled XOR leaves the exclusive-or of the pad byte and saved message in a0. -/
theorem step_xor (pad message : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hpad : s.regs.get? .x10 = some pad)
    (hmessage : s.regs.get? .x9 = some message)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00954533#32) :
    rvStep s = some (commitState (registerBodyState s pc .x10 (pad ^^^ message))
      (BitVec.addInt pc 4)) :=
  step_reg h pc 0x00954533#32 (.RTYPE (.Regidx 9#5, .Regidx 10#5, .Regidx 10#5, .XOR)) .x10
    (pad ^^^ message) hpc hcode halign hword
    (execute_XOR_of_registers (.Regidx 10#5) (.Regidx 9#5) (.Regidx 10#5) pad message
      (rX_bits_a0 (sequentialState_get?_of_get? pc hpad))
      (rX_bits_s1 (sequentialState_get?_of_get? pc hmessage))
      (wX_bits_a0 _ _))

/-- The zero-upper-immediate AUIPC records its current code address in ra. -/
theorem step_call_upper (hpc : s.regs.get? .PC = some pc)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00000097#32) :
    rvStep s = some (commitState (registerBodyState s pc .x1 pc) (BitVec.addInt pc 4)) :=
  step_auipc_zero h pc 0x00000097#32 1#5 .x1 rfl hpc hcode halign hword (wX_bits_ra _)

/-- The zero-upper-immediate AUIPC records its current code address in t3. -/
theorem step_stub_upper (hpc : s.regs.get? .PC = some pc)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00000e17#32) :
    rvStep s = some (commitState (registerBodyState s pc .x28 pc) (BitVec.addInt pc 4)) :=
  step_auipc_zero h pc 0x00000e17#32 28#5 .x28 rfl hpc hcode halign hword (wX_bits_t3 _)

/-- The trampoline reads the relocated randombytes address through its actual code-relative slot. -/
theorem step_stub_load (base target : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hreg : s.regs.get? .x28 = some base)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hword : Word32At s pc 0x00ce3e03#32)
    (hram : InUserRam (base + sign_extend 12#12) 8)
    (hdataAlign : (base + sign_extend 12#12).toNat % 8 = 0)
    (hdata : Word64At s (base + sign_extend 12#12) target) :
    rvStep s = some (commitState (registerBodyState s pc .x28 target) (BitVec.addInt pc 4)) :=
  step_load_slot h pc 0x00ce3e03#32 12#12 28#5 28#5 .x28 rfl base target hpc hcode halign hword hram
    hdataAlign hdata (rX_bits_t3 (sequentialState_get?_of_get? pc hreg)) (wX_bits_t3 _)

/-- The compiled call jumps to its trampoline and saves the continuation in ra. -/
theorem step_call_link (base : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hra : s.regs.get? .x1 = some base)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (htarget : (BitVec.addInt base 36).toNat % 4 = 0) (hword : Word32At s pc 0x024080e7#32) :
    rvStep s = some (commitState (linkBodyState s pc (BitVec.addInt base 36))
      (BitVec.addInt base 36)) := by
  have hm : BitVec.update (base + sign_extend 36#12) 0 0#1 = BitVec.addInt base 36 := by
    change BitVec.update (BitVec.addInt base 36) 0 0#1 = BitVec.addInt base 36
    exact clear_lowbit_self _ (aligned4_access htarget).1
  have hs := h.counterState.sequentialState pc
  exact step_jalr h pc 0x024080e7#32 36#12 1#5 1#5 base _ _ hpc hcode halign hword
    (rX_bits_ra (sequentialState_get?_of_get? pc hra)) hm htarget (wX_bits_ra _ _)
    ((hs.insert .nextPC _ trivial).insert .x1 _ trivial)
    (by simp [linkBodyState, get?_insert])
    (by simp [linkBodyState, sequentialState, counterState, get?_insert])

/-- The import trampoline reaches the callback while preserving the saved continuation. -/
theorem step_stub_jump (target : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hreg : s.regs.get? .x28 = some target)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0) (htarget : target.toNat % 4 = 0)
    (hword : Word32At s pc 0x000e0067#32) :
    rvStep s = some (commitState (jumpBodyState s pc target) target) := by
  have hm : BitVec.update (target + sign_extend 0#12) 0 0#1 = target := by
    simpa [sign_extend, Sail.BitVec.signExtend] using
      clear_lowbit_self target (aligned4_access htarget).1
  have hs := h.counterState.sequentialState pc
  exact step_jalr h pc 0x000e0067#32 0#12 28#5 0#5 target _ _ hpc hcode halign hword
    (rX_bits_t3 (sequentialState_get?_of_get? pc hreg))
    hm htarget rfl (hs.insert .nextPC target trivial)
    (by simp [jumpBodyState])
    (by simp [jumpBodyState, sequentialState, counterState, get?_insert])

/-- The compiled return jumps to the return address in ra. -/
theorem step_return (target : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hra : s.regs.get? .x1 = some target)
    (hcode : InUserRam pc 4) (halign : pc.toNat % 4 = 0) (htarget : target.toNat % 4 = 0)
    (hword : Word32At s pc 0x00008067#32) :
    rvStep s = some (commitState (retBodyState s pc target) target) :=
  rvStep_ret h pc target hpc hra hcode halign htarget hword

end MetrologyAsm.OTP
