import MetrologyAsm.Examples.Callback.Decode
import MetrologyAsm.Sail.ArithmeticRules

/-! # Complete Sail steps used by the callback fragment -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions Sail

/-- The prepared instruction state after updating ra. -/
def importRaBodyState (s : Mach) (pc value : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.x1 value }

/-- The prepared instruction state after updating sp. -/
def importSpBodyState (s : Mach) (pc value : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.x2 value }

/-- The prepared instruction state after updating t3. -/
def importT3BodyState (s : Mach) (pc value : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.x28 value }

/-- The prepared instruction state after setting a jump target and its link register. -/
def importLinkBodyState (s : Mach) (pc target : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with
    regs := (prepared.regs.insert Register.nextPC target).insert Register.x1 (BitVec.addInt pc 4) }

/-- The prepared instruction state after a jump without a link. -/
def importJumpBodyState (s : Mach) (pc target : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.nextPC target }

private theorem import_fetch {s : Mach} (h : UserConfig s) (pc : BitVec 64) (word : BitVec 32)
    (hpc : s.regs.get? Register.PC = some pc) (hram : InUserRam pc 4)
    (halign : pc.toNat % 4 = 0) (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false)
    (hword : Word32At s pc word) :
    runSail (fetch ()) (counterState s) = some (.F_Base word, counterState s) := by
  have hpc' : (counterState s).regs.get? Register.PC = some pc := by
    simp [counterState, Std.ExtDHashMap.get?_insert, hpc]
  exact h.counterState.fetch32 pc word hpc' hram halign hbase hword

/-- A decoded ADDI on sp executes through the complete generated step wrapper. -/
theorem rvStep_addi_sp {s : Mach} (h : UserConfig s) (pc sp : BitVec 64)
    (imm : BitVec 12) (word : BitVec 32)
    (hdecode : ext_decode word = guardedDecode (.ITYPE (imm, .Regidx 2#5, .Regidx 2#5, .ADDI)))
    (hpc : s.regs.get? Register.PC = some pc) (hsp : s.regs.get? Register.x2 = some sp)
    (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false) (hword : Word32At s pc word) :
    rvStep s = some (commitState
      (importSpBodyState s pc (sp + sign_extend (m := 64) imm)) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hsp' : (sequentialState (counterState s) pc).regs.get? Register.x2 = some sp := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hsp]
  have hbody := execute_ADDI_of_registers imm (.Regidx 2#5) (.Regidx 2#5) sp
    (rX_bits_sp hsp') (wX_bits_sp (sequentialState (counterState s) pc) _)
  apply rvStep_user_of_execute h pc word
    (.ITYPE (imm, .Regidx 2#5, .Regidx 2#5, .ADDI)) (BitVec.addInt pc 4) hpc
    (import_fetch h pc word hpc hram halign hbase hword)
  · exact decode_of_guarded h.counterState _ _ hdecode
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact hs.insert .x2 _ trivial
  · simp [importSpBodyState, sequentialState, Std.ExtDHashMap.get?_insert]
  · simp [importSpBodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

/-- The zero-upper-immediate AUIPC into ra executes through the complete Sail wrapper. -/
theorem rvStep_auipc_ra {s : Mach} (h : UserConfig s) (pc : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc) (hram : InUserRam pc 4)
    (halign : pc.toNat % 4 = 0) (hword : Word32At s pc 0x00000097#32) :
    rvStep s = some (commitState (importRaBodyState s pc pc) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hpc' : (sequentialState (counterState s) pc).regs.get? Register.PC = some pc := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hpc]
  have hbody : execute_UTYPE 0#20 (.Regidx 1#5) .AUIPC
      (sequentialState (counterState s) pc) = .ok (.Retire_Success ())
      (importRaBodyState s pc pc) := by
    apply execute_AUIPC_of_registers 0#20 (.Regidx 1#5) pc hpc'
    simpa [sign_extend, Sail.BitVec.signExtend, importRaBodyState] using
      wX_bits_ra (sequentialState (counterState s) pc) pc
  apply rvStep_user_of_execute h pc 0x00000097#32
    (.UTYPE (0#20, .Regidx 1#5, .AUIPC)) (BitVec.addInt pc 4) hpc
    (import_fetch h pc 0x00000097#32 hpc hram halign (by decide +kernel) hword)
  · exact decode_of_guarded h.counterState _ _ decode_importToy_call_upper
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact hs.insert .x1 _ trivial
  · simp [importRaBodyState, sequentialState, Std.ExtDHashMap.get?_insert]
  · simp [importRaBodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

/-- The zero-upper-immediate AUIPC into t3 executes through the complete Sail wrapper. -/
theorem rvStep_auipc_t3 {s : Mach} (h : UserConfig s) (pc : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc) (hram : InUserRam pc 4)
    (halign : pc.toNat % 4 = 0) (hword : Word32At s pc 0x00000e17#32) :
    rvStep s = some (commitState (importT3BodyState s pc pc) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hpc' : (sequentialState (counterState s) pc).regs.get? Register.PC = some pc := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hpc]
  have hbody : execute_UTYPE 0#20 (.Regidx 28#5) .AUIPC
      (sequentialState (counterState s) pc) = .ok (.Retire_Success ())
      (importT3BodyState s pc pc) := by
    apply execute_AUIPC_of_registers 0#20 (.Regidx 28#5) pc hpc'
    simpa [sign_extend, Sail.BitVec.signExtend, importT3BodyState] using
      wX_bits_t3 (sequentialState (counterState s) pc) pc
  apply rvStep_user_of_execute h pc 0x00000e17#32
    (.UTYPE (0#20, .Regidx 28#5, .AUIPC)) (BitVec.addInt pc 4) hpc
    (import_fetch h pc 0x00000e17#32 hpc hram halign (by decide +kernel) hword)
  · exact decode_of_guarded h.counterState _ _ decode_importToy_stub_upper
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact hs.insert .x28 _ trivial
  · simp [importT3BodyState, sequentialState, Std.ExtDHashMap.get?_insert]
  · simp [importT3BodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

/-- The callback restore load executes with all physical and virtual checks discharged. -/
theorem rvStep_import_restore {s : Mach} (h : UserConfig s) (pc base value : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc) (hreg : s.regs.get? Register.x2 = some base)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0)
    (hram : InUserRam (BitVec.addInt base 8) 8)
    (halign : (BitVec.addInt base 8).toNat % 8 = 0)
    (hword : Word32At s pc 0x00813083#32)
    (hdata : Word64At s (BitVec.addInt base 8) value) :
    rvStep s = some (commitState (importRaBodyState s pc value) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hreg' : (sequentialState (counterState s) pc).regs.get? Register.x2 = some base := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hreg]
  have hbody : execute_LOAD 8#12 (.Regidx 2#5) (.Regidx 1#5) false 8
      (sequentialState (counterState s) pc) = .ok (.Retire_Success ())
      (importRaBodyState s pc value) := by
    apply hs.execute_LOAD64 8#12 (.Regidx 2#5) (.Regidx 1#5) base value
    · simpa [sign_extend, Sail.BitVec.signExtend, BitVec.addInt] using hram
    · simpa [sign_extend, Sail.BitVec.signExtend, BitVec.addInt] using halign
    · exact rX_bits_sp hreg'
    · simpa [sign_extend, Sail.BitVec.signExtend, BitVec.addInt] using
        hdata.of_mem_eq (t := sequentialState (counterState s) pc) rfl
    · exact wX_bits_ra _ _
  apply rvStep_user_of_execute h pc 0x00813083#32
    (.LOAD (8#12, .Regidx 2#5, .Regidx 1#5, false, 8)) (BitVec.addInt pc 4) hpc
    (import_fetch h pc 0x00813083#32 hpc hcode hpcAlign (by decide +kernel) hword)
  · exact decode_of_guarded h.counterState _ _ decode_importToy_restore
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact hs.insert .x1 _ trivial
  · simp [importRaBodyState, sequentialState, Std.ExtDHashMap.get?_insert]
  · simp [importRaBodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

/-- The callback stub load load executes with all physical and virtual checks discharged. -/
theorem rvStep_import_stub_load {s : Mach} (h : UserConfig s) (pc base value : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc) (hreg : s.regs.get? Register.x28 = some base)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0)
    (hram : InUserRam (BitVec.addInt base 12) 8)
    (halign : (BitVec.addInt base 12).toNat % 8 = 0)
    (hword : Word32At s pc 0x00ce3e03#32)
    (hdata : Word64At s (BitVec.addInt base 12) value) :
    rvStep s = some (commitState (importT3BodyState s pc value) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hreg' : (sequentialState (counterState s) pc).regs.get? Register.x28 = some base := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hreg]
  have hbody : execute_LOAD 12#12 (.Regidx 28#5) (.Regidx 28#5) false 8
      (sequentialState (counterState s) pc) = .ok (.Retire_Success ())
      (importT3BodyState s pc value) := by
    apply hs.execute_LOAD64 12#12 (.Regidx 28#5) (.Regidx 28#5) base value
    · simpa [sign_extend, Sail.BitVec.signExtend, BitVec.addInt] using hram
    · simpa [sign_extend, Sail.BitVec.signExtend, BitVec.addInt] using halign
    · exact rX_bits_t3 hreg'
    · simpa [sign_extend, Sail.BitVec.signExtend, BitVec.addInt] using
        hdata.of_mem_eq (t := sequentialState (counterState s) pc) rfl
    · exact wX_bits_t3 _ _
  apply rvStep_user_of_execute h pc 0x00ce3e03#32
    (.LOAD (12#12, .Regidx 28#5, .Regidx 28#5, false, 8)) (BitVec.addInt pc 4) hpc
    (import_fetch h pc 0x00ce3e03#32 hpc hcode hpcAlign (by decide +kernel) hword)
  · exact decode_of_guarded h.counterState _ _ decode_importToy_stub_load
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact hs.insert .x28 _ trivial
  · simp [importT3BodyState, sequentialState, Std.ExtDHashMap.get?_insert]
  · simp [importT3BodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

/-- Saving ra on the scratch stack executes as one actual eight-byte Sail store. -/
theorem rvStep_import_save {s : Mach} (h : UserConfig s) (pc sp ra : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc) (hsp : s.regs.get? Register.x2 = some sp)
    (hra : s.regs.get? Register.x1 = some ra)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0)
    (hram : InUserRam (BitVec.addInt sp 8) 8) (halign : (BitVec.addInt sp 8).toNat % 8 = 0)
    (hword : Word32At s pc 0x00113423#32) :
    rvStep s = some (commitState
      (storeBodyState s pc (BitVec.addInt sp 8) ra) (BitVec.addInt pc 4)) := by
  have hs := h.counterState.sequentialState pc
  have hsp' : (sequentialState (counterState s) pc).regs.get? Register.x2 = some sp := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hsp]
  have hra' : (sequentialState (counterState s) pc).regs.get? Register.x1 = some ra := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hra]
  have hbody : execute_STORE 8#12 (.Regidx 1#5) (.Regidx 2#5) 8
      (sequentialState (counterState s) pc) = .ok (.Retire_Success ())
      (storeBodyState s pc (BitVec.addInt sp 8) ra) := by
    simpa [sign_extend, Sail.BitVec.signExtend, BitVec.addInt, storeBodyState] using
      hs.execute_STORE64 8#12 (.Regidx 1#5) (.Regidx 2#5) sp ra
        (by simpa [sign_extend, Sail.BitVec.signExtend, BitVec.addInt] using hram)
        (by simpa [sign_extend, Sail.BitVec.signExtend, BitVec.addInt] using halign)
        (rX_bits_sp hsp') (rX_bits_ra hra')
  apply rvStep_user_of_execute h pc 0x00113423#32
    (.STORE (8#12, .Regidx 1#5, .Regidx 2#5, 8)) (BitVec.addInt pc 4) hpc
    (import_fetch h pc 0x00113423#32 hpc hcode hpcAlign (by decide +kernel) hword)
  · exact decode_of_guarded h.counterState _ _ decode_importToy_save
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact hs.write64State _ _
  · simp [storeBodyState, sequentialState]
  · simp [storeBodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

/-- The call's linking JALR reaches its local trampoline and installs the continuation in ra. -/
theorem rvStep_import_link {s : Mach} (h : UserConfig s) (pc value : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc) (hra : s.regs.get? Register.x1 = some value)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0)
    (htarget : (BitVec.addInt value 20).toNat % 4 = 0)
    (hword : Word32At s pc 0x014080e7#32) :
    rvStep s = some (commitState (importLinkBodyState s pc (BitVec.addInt value 20))
      (BitVec.addInt value 20)) := by
  have hs := h.counterState.sequentialState pc
  have hra' : (sequentialState (counterState s) pc).regs.get? Register.x1 = some value := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hra]
  have hn : (sequentialState (counterState s) pc).regs.get? Register.nextPC =
      some (BitVec.addInt pc 4) := by simp [sequentialState]
  have hm : BitVec.update (value + sign_extend (m := 64) 20#12) 0 0#1 = BitVec.addInt value 20 := by
    change BitVec.update (BitVec.addInt value 20) 0 0#1 = BitVec.addInt value 20
    exact clear_lowbit_self _ (aligned4_access htarget).1
  have hbody : execute_JALR 20#12 (.Regidx 1#5) (.Regidx 1#5)
      (sequentialState (counterState s) pc) = .ok (.Retire_Success ())
      (importLinkBodyState s pc (BitVec.addInt value 20)) := by
    apply execute_JALR_of_registers hs 20#12 (.Regidx 1#5) (.Regidx 1#5) value (BitVec.addInt pc 4)
    · exact rX_bits_ra hra'
    · exact hn
    · simpa only [hm] using htarget
    · rw [hm]
      exact wX_bits_ra _ _
  apply rvStep_user_of_execute h pc 0x014080e7#32
    (.JALR (20#12, .Regidx 1#5, .Regidx 1#5)) (BitVec.addInt value 20) hpc
    (import_fetch h pc 0x014080e7#32 hpc hcode hpcAlign (by decide +kernel) hword)
  · exact decode_of_guarded h.counterState _ _ decode_importToy_call_link
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact (hs.insert .nextPC _ trivial).insert .x1 _ trivial
  · simp [importLinkBodyState, Std.ExtDHashMap.get?_insert]
  · simp [importLinkBodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

/-- The trampoline's indirect jump reaches the external callback without changing ra. -/
theorem rvStep_import_jump {s : Mach} (h : UserConfig s) (pc target : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc) (hreg : s.regs.get? Register.x28 = some target)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0) (htarget : target.toNat % 4 = 0)
    (hword : Word32At s pc 0x000e0067#32) :
    rvStep s = some (commitState (importJumpBodyState s pc target) target) := by
  have hs := h.counterState.sequentialState pc
  have hreg' : (sequentialState (counterState s) pc).regs.get? Register.x28 = some target := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hreg]
  have hn : (sequentialState (counterState s) pc).regs.get? Register.nextPC =
      some (BitVec.addInt pc 4) := by simp [sequentialState]
  have hm : BitVec.update (target + sign_extend (m := 64) 0#12) 0 0#1 = target := by
    simpa [sign_extend, Sail.BitVec.signExtend] using
      clear_lowbit_self target (aligned4_access htarget).1
  have hbody : execute_JALR 0#12 (.Regidx 28#5) (.Regidx 0#5)
      (sequentialState (counterState s) pc) = .ok (.Retire_Success ())
      (importJumpBodyState s pc target) := by
    apply execute_JALR_of_registers hs 0#12 (.Regidx 28#5) (.Regidx 0#5) target (BitVec.addInt pc 4)
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
  · simp [importJumpBodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

end MetrologyAsm
