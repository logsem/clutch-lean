import MetrologyAsm.Sail.ArithmeticRules
import MetrologyAsm.Sail.ByteRules

/-! # Full Sail steps from register or memory instruction-body effects -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions Sail
open Std.ExtDHashMap

/-- Prepare sequential execution and record one typed architectural register write. -/
def registerBodyState (s : Mach) (pc : BitVec 64) (destination : Register)
    (value : RegisterType destination) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert destination value }

/-- A profile-compatible destination write preserves the configured execution profile. -/
theorem UserConfig.registerBodyState {s : Mach} (h : UserConfig s) (pc : BitVec 64)
    (destination : Register) (value : RegisterType destination)
    (hpolicy : userRegPolicy destination value) :
    UserConfig (MetrologyAsm.registerBodyState s pc destination value) :=
  (h.counterState.sequentialState pc).insert destination value hpolicy

/-- Fetch, decode and a successful register body compose into the complete architectural step. -/
theorem rvStep_register_instruction {s : Mach} (h : UserConfig s)
    (pc : BitVec 64) (word : BitVec 32) (inst : instruction)
    (destination : Register) (value : RegisterType destination)
    (hpc : s.regs.get? .PC = some pc) (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false) (hword : Word32At s pc word)
    (hdecode : ext_decode word = guardedDecode inst)
    (hbody : execute inst (sequentialState (counterState s) pc) =
      .ok (.Retire_Success ()) (registerBodyState s pc destination value))
    (hpolicy : userRegPolicy destination value)
    (hnext : destination ≠ .nextPC) (hcount : destination ≠ .minstret_increment) :
    rvStep s =
      some (commitState (registerBodyState s pc destination value) (BitVec.addInt pc 4)) := by
  have hpc' : (counterState s).regs.get? .PC = some pc := by
    simp [counterState, get?_insert, hpc]
  have hfetch := h.counterState.fetch32 pc word hpc' hram halign hbase hword
  apply rvStep_user_of_execute h pc word inst (BitVec.addInt pc 4) hpc hfetch
    (decode_of_guarded h.counterState word inst hdecode)
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact h.registerBodyState pc destination value hpolicy
  · simp [registerBodyState, sequentialState, get?_insert, hnext]
  · simp [registerBodyState, sequentialState, counterState, get?_insert,
      hcount]

/-- Fetch, decode and a successful doubleword store body compose into the full step. -/
theorem rvStep_memory_instruction {s : Mach} (h : UserConfig s)
    (pc : BitVec 64) (word : BitVec 32) (inst : instruction) (address value : BitVec 64)
    (hpc : s.regs.get? .PC = some pc) (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false) (hword : Word32At s pc word)
    (hdecode : ext_decode word = guardedDecode inst)
    (hbody : execute inst (sequentialState (counterState s) pc) =
      .ok (.Retire_Success ()) (storeBodyState s pc address value)) :
    rvStep s = some (commitState (storeBodyState s pc address value) (BitVec.addInt pc 4)) := by
  have hpc' : (counterState s).regs.get? .PC = some pc := by
    simp [counterState, get?_insert, hpc]
  have hfetch := h.counterState.fetch32 pc word hpc' hram halign hbase hword
  apply rvStep_user_of_execute h pc word inst (BitVec.addInt pc 4) hpc hfetch
    (decode_of_guarded h.counterState word inst hdecode)
  · rw [runSail_eq_some_iff]
    exact hbody
  · exact (h.counterState.sequentialState pc).write64State address value
  · simp [storeBodyState, sequentialState]
  · simp [storeBodyState, sequentialState, counterState, get?_insert]

end MetrologyAsm
