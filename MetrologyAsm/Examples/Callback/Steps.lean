import MetrologyAsm.Examples.Callback.Decode
import MetrologyAsm.Sail.ArithmeticRules
import MetrologyAsm.Sail.IntegerSteps

/-! # Complete Sail steps used by the callback fragment -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions Sail BitVec Std.ExtDHashMap

section

variable (s : Mach)

/-- The prepared instruction state after updating ra. -/
def importRaBodyState (pc value : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.x1 value }

/-- The prepared instruction state after updating sp. -/
def importSpBodyState (pc value : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.x2 value }

/-- The prepared instruction state after updating t3. -/
def importT3BodyState (pc value : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.x28 value }

/-- The prepared instruction state after setting a jump target and its link register. -/
def importLinkBodyState (pc target : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with
    regs := (prepared.regs.insert Register.nextPC target).insert Register.x1 (addInt pc 4) }

/-- The prepared instruction state after a jump without a link. -/
def importJumpBodyState (pc target : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.nextPC target }

end

private theorem import_fetch {s : Mach} (h : UserConfig s) (pc : BitVec 64) (word : BitVec 32)
    (hpc : s.regs.get? Register.PC = some pc) (hram : InUserRam pc 4)
    (halign : pc.toNat % 4 = 0) (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false)
    (hword : Word32At s pc word) :
    runSail (fetch ()) (counterState s) = some (.F_Base word, counterState s) := by
  have hpc' : (counterState s).regs.get? Register.PC = some pc := by
    simp [counterState, get?_insert, hpc]
  exact h.counterState.fetch32 pc word hpc' hram halign hbase hword

private theorem seq_get_of_get {s : Mach} {pc : BitVec 64} {r : Register} {v : RegisterType r}
    (h : s.regs.get? r = some v) (hn : r ≠ Register.nextPC)
    (hc : r ≠ Register.minstret_increment) :
    (sequentialState (counterState s) pc).regs.get? r = some v := by
  simp [sequentialState, counterState, get?_insert, h, hn.symm, hc.symm]

section

variable {s : Mach} (h : UserConfig s) (pc : BitVec 64)

include h

/-- A decoded ADDI on sp executes through the complete generated step wrapper. -/
theorem rvStep_addi_sp (sp : BitVec 64) (imm : BitVec 12) (word : BitVec 32)
    (hdecode : ext_decode word = guardedDecode (.ITYPE (imm, .Regidx 2#5, .Regidx 2#5, .ADDI)))
    (hpc : s.regs.get? Register.PC = some pc) (hsp : s.regs.get? Register.x2 = some sp)
    (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false) (hword : Word32At s pc word) :
    rvStep s = some (commitState
      (importSpBodyState s pc (sp + sign_extend imm)) (addInt pc 4)) := by
  have hsp' : (sequentialState (counterState s) pc).regs.get? Register.x2 = some sp :=
    seq_get_of_get hsp (by decide) (by decide)
  exact rvStep_register_instruction h pc word (.ITYPE (imm, .Regidx 2#5, .Regidx 2#5, .ADDI))
    Register.x2 (sp + sign_extend imm) hpc hram halign hbase hword hdecode
    (execute_ADDI_of_registers imm (.Regidx 2#5) (.Regidx 2#5) sp
      (rX_bits_sp hsp') (wX_bits_sp (sequentialState (counterState s) pc) _))
    trivial (by decide) (by decide)

/-- The zero-upper-immediate AUIPC into ra executes through the complete Sail wrapper. -/
theorem rvStep_auipc_ra (hpc : s.regs.get? Register.PC = some pc)
    (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0) (hword : Word32At s pc 0x00000097#32) :
    rvStep s = some (commitState (importRaBodyState s pc pc) (addInt pc 4)) := by
  have hpc' : (sequentialState (counterState s) pc).regs.get? Register.PC = some pc :=
    seq_get_of_get hpc (by decide) (by decide)
  refine rvStep_register_instruction h pc 0x00000097#32 (.UTYPE (0#20, .Regidx 1#5, .AUIPC))
    Register.x1 pc hpc hram halign (by decide +kernel) hword decode_importToy_call_upper ?_
    trivial (by decide) (by decide)
  apply execute_AUIPC_of_registers 0#20 (.Regidx 1#5) pc hpc'
  simpa [sign_extend, Sail.BitVec.signExtend, registerBodyState] using
    wX_bits_ra (sequentialState (counterState s) pc) pc

/-- The zero-upper-immediate AUIPC into t3 executes through the complete Sail wrapper. -/
theorem rvStep_auipc_t3 (hpc : s.regs.get? Register.PC = some pc)
    (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0) (hword : Word32At s pc 0x00000e17#32) :
    rvStep s = some (commitState (importT3BodyState s pc pc) (addInt pc 4)) := by
  have hpc' : (sequentialState (counterState s) pc).regs.get? Register.PC = some pc :=
    seq_get_of_get hpc (by decide) (by decide)
  refine rvStep_register_instruction h pc 0x00000e17#32 (.UTYPE (0#20, .Regidx 28#5, .AUIPC))
    Register.x28 pc hpc hram halign (by decide +kernel) hword decode_importToy_stub_upper ?_
    trivial (by decide) (by decide)
  apply execute_AUIPC_of_registers 0#20 (.Regidx 28#5) pc hpc'
  simpa [sign_extend, Sail.BitVec.signExtend, registerBodyState] using
    wX_bits_t3 (sequentialState (counterState s) pc) pc

/-- The callback restore load executes with all physical and virtual checks discharged. -/
theorem rvStep_import_restore (base value : BitVec 64) (hpc : s.regs.get? Register.PC = some pc)
    (hreg : s.regs.get? Register.x2 = some base) (hcode : InUserRam pc 4)
    (hpcAlign : pc.toNat % 4 = 0) (hram : InUserRam (addInt base 8) 8)
    (halign : (addInt base 8).toNat % 8 = 0) (hword : Word32At s pc 0x00813083#32)
    (hdata : Word64At s (addInt base 8) value) :
    rvStep s = some (commitState (importRaBodyState s pc value) (addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hreg' : (sequentialState (counterState s) pc).regs.get? Register.x2 = some base :=
    seq_get_of_get hreg (by decide) (by decide)
  refine rvStep_register_instruction h pc 0x00813083#32
    (.LOAD (8#12, .Regidx 2#5, .Regidx 1#5, false, 8)) Register.x1 value hpc hcode hpcAlign
    (by decide +kernel) hword decode_importToy_restore ?_ trivial (by decide) (by decide)
  apply hs.execute_LOAD64 8#12 (.Regidx 2#5) (.Regidx 1#5) base value
  · simpa [sign_extend, Sail.BitVec.signExtend, addInt] using hram
  · simpa [sign_extend, Sail.BitVec.signExtend, addInt] using halign
  · exact rX_bits_sp hreg'
  · simpa [sign_extend, Sail.BitVec.signExtend, addInt] using
      hdata.of_mem_eq (t := sequentialState (counterState s) pc) rfl
  · exact wX_bits_ra _ _

/-- The trampoline load of the import address into t3 executes with all checks discharged. -/
theorem rvStep_import_stub_load (base value : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc) (hreg : s.regs.get? Register.x28 = some base)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0)
    (hram : InUserRam (addInt base 12) 8) (halign : (addInt base 12).toNat % 8 = 0)
    (hword : Word32At s pc 0x00ce3e03#32) (hdata : Word64At s (addInt base 12) value) :
    rvStep s = some (commitState (importT3BodyState s pc value) (addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hreg' : (sequentialState (counterState s) pc).regs.get? Register.x28 = some base :=
    seq_get_of_get hreg (by decide) (by decide)
  refine rvStep_register_instruction h pc 0x00ce3e03#32
    (.LOAD (12#12, .Regidx 28#5, .Regidx 28#5, false, 8)) Register.x28 value hpc hcode hpcAlign
    (by decide +kernel) hword decode_importToy_stub_load ?_ trivial (by decide) (by decide)
  apply hs.execute_LOAD64 12#12 (.Regidx 28#5) (.Regidx 28#5) base value
  · simpa [sign_extend, Sail.BitVec.signExtend, addInt] using hram
  · simpa [sign_extend, Sail.BitVec.signExtend, addInt] using halign
  · exact rX_bits_t3 hreg'
  · simpa [sign_extend, Sail.BitVec.signExtend, addInt] using
      hdata.of_mem_eq (t := sequentialState (counterState s) pc) rfl
  · exact wX_bits_t3 _ _

/-- Saving ra on the scratch stack executes as one actual eight-byte Sail store. -/
theorem rvStep_import_save (sp ra : BitVec 64) (hpc : s.regs.get? Register.PC = some pc)
    (hsp : s.regs.get? Register.x2 = some sp) (hra : s.regs.get? Register.x1 = some ra)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0) (hram : InUserRam (addInt sp 8) 8)
    (halign : (addInt sp 8).toNat % 8 = 0) (hword : Word32At s pc 0x00113423#32) :
    rvStep s = some (commitState (storeBodyState s pc (addInt sp 8) ra) (addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hsp' : (sequentialState (counterState s) pc).regs.get? Register.x2 = some sp :=
    seq_get_of_get hsp (by decide) (by decide)
  have hra' : (sequentialState (counterState s) pc).regs.get? Register.x1 = some ra :=
    seq_get_of_get hra (by decide) (by decide)
  have hbody : execute_STORE 8#12 (.Regidx 1#5) (.Regidx 2#5) 8
      (sequentialState (counterState s) pc) = .ok (.Retire_Success ())
      (storeBodyState s pc (addInt sp 8) ra) := by
    simpa [sign_extend, Sail.BitVec.signExtend, addInt, storeBodyState] using
      hs.execute_STORE64 8#12 (.Regidx 1#5) (.Regidx 2#5) sp ra
        (by simpa [sign_extend, Sail.BitVec.signExtend, addInt] using hram)
        (by simpa [sign_extend, Sail.BitVec.signExtend, addInt] using halign)
        (rX_bits_sp hsp') (rX_bits_ra hra')
  exact rvStep_memory_instruction h pc 0x00113423#32
    (.STORE (8#12, .Regidx 1#5, .Regidx 2#5, 8)) (addInt sp 8) ra hpc hcode hpcAlign
    (by decide +kernel) hword decode_importToy_save hbody

/-- The call's linking JALR reaches its local trampoline and installs the continuation in ra. -/
theorem rvStep_import_link (value : BitVec 64) (hpc : s.regs.get? Register.PC = some pc)
    (hra : s.regs.get? Register.x1 = some value) (hcode : InUserRam pc 4)
    (hpcAlign : pc.toNat % 4 = 0) (htarget : (addInt value 20).toNat % 4 = 0)
    (hword : Word32At s pc 0x014080e7#32) :
    rvStep s = some (commitState (importLinkBodyState s pc (addInt value 20))
      (addInt value 20)) := by
  have hs := h.counterState.sequentialState pc
  have hra' : (sequentialState (counterState s) pc).regs.get? Register.x1 = some value :=
    seq_get_of_get hra (by decide) (by decide)
  have hn : (sequentialState (counterState s) pc).regs.get? Register.nextPC =
      some (addInt pc 4) := by simp [sequentialState]
  have hm : BitVec.update (value + sign_extend 20#12) 0 0#1 = addInt value 20 := by
    change BitVec.update (addInt value 20) 0 0#1 = addInt value 20
    exact clear_lowbit_self _ (aligned4_access htarget).1
  have hbody : execute_JALR 20#12 (.Regidx 1#5) (.Regidx 1#5)
      (sequentialState (counterState s) pc) = .ok (.Retire_Success ())
      (importLinkBodyState s pc (addInt value 20)) := by
    apply execute_JALR_of_registers hs 20#12 (.Regidx 1#5) (.Regidx 1#5) value (addInt pc 4)
    · exact rX_bits_ra hra'
    · exact hn
    · simpa only [hm] using htarget
    · rw [hm]
      exact wX_bits_ra _ _
  apply rvStep_user_of_execute h pc 0x014080e7#32
    (.JALR (20#12, .Regidx 1#5, .Regidx 1#5)) (addInt value 20) hpc
    (import_fetch h pc 0x014080e7#32 hpc hcode hpcAlign (by decide +kernel) hword)
  · exact decode_of_guarded h.counterState _ _ decode_importToy_call_link
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact (hs.insert .nextPC _ trivial).insert .x1 _ trivial
  · simp [importLinkBodyState, get?_insert]
  · simp [importLinkBodyState, sequentialState, counterState, get?_insert]

/-- The trampoline's indirect jump reaches the external callback without changing ra. -/
theorem rvStep_import_jump (target : BitVec 64) (hpc : s.regs.get? Register.PC = some pc)
    (hreg : s.regs.get? Register.x28 = some target) (hcode : InUserRam pc 4)
    (hpcAlign : pc.toNat % 4 = 0) (htarget : target.toNat % 4 = 0)
    (hword : Word32At s pc 0x000e0067#32) :
    rvStep s = some (commitState (importJumpBodyState s pc target) target) := by
  have hs := h.counterState.sequentialState pc
  have hreg' : (sequentialState (counterState s) pc).regs.get? Register.x28 = some target :=
    seq_get_of_get hreg (by decide) (by decide)
  have hn : (sequentialState (counterState s) pc).regs.get? Register.nextPC =
      some (addInt pc 4) := by simp [sequentialState]
  have hm : BitVec.update (target + sign_extend 0#12) 0 0#1 = target := by
    simpa [sign_extend, Sail.BitVec.signExtend] using
      clear_lowbit_self target (aligned4_access htarget).1
  have hbody : execute_JALR 0#12 (.Regidx 28#5) (.Regidx 0#5)
      (sequentialState (counterState s) pc) = .ok (.Retire_Success ())
      (importJumpBodyState s pc target) := by
    apply execute_JALR_of_registers hs 0#12 (.Regidx 28#5) (.Regidx 0#5) target (addInt pc 4)
    · exact rX_bits_t3 hreg'
    · exact hn
    · simpa only [hm] using htarget
    · rw [hm]
      rfl
  apply rvStep_user_of_execute h pc 0x000e0067#32
    (.JALR (0#12, .Regidx 28#5, .Regidx 0#5)) target hpc
    (import_fetch h pc 0x000e0067#32 hpc hcode hpcAlign (by decide +kernel) hword)
  · exact decode_of_guarded h.counterState _ _ decode_importToy_stub_jump
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact hs.insert .nextPC _ trivial
  · simp [importJumpBodyState]
  · simp [importJumpBodyState, sequentialState, counterState, get?_insert]

end

end MetrologyAsm
