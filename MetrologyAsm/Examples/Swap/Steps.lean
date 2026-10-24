import MetrologyAsm.Sail.InstructionRules
import MetrologyAsm.Sail.RegisterRules
import MetrologyAsm.Examples.Swap.Decode

/-! # Complete Sail step rules for the exchange loads and stores -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail
open Std.ExtDHashMap

/-- Entering the counter state keeps the program counter. -/
theorem counterState_get?_PC {s : Mach} {pc : BitVec 64} (hpc : s.regs.get? Register.PC = some pc) :
    (counterState s).regs.get? Register.PC = some pc := by
  simp [counterState, get?_insert, hpc]

/-- The exact prepared-state effect of loading a2. -/
def loadA2BodyState (s : Mach) (pc value : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.x12 value }

/-- The exact prepared-state effect of loading a3. -/
def loadA3BodyState (s : Mach) (pc value : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.x13 value }

variable {s : Mach} (h : UserConfig s) (pc address value : BitVec 64)
  (hpc : s.regs.get? Register.PC = some pc)

include h hpc

section Aligned

variable (halign : address.toNat % 8 = 0)

include halign

/-- The exchange load into a2 follows the complete Sail wrapper after successful RAM fetch/read. -/
theorem rvStep_ld_a2_of_mem
    (haddress : s.regs.get? Register.x10 = some address)
    (hfetch : runSail (fetch ()) (counterState s) = some (.F_Base 0x00053603#32, counterState s))
    (hread : mem_read (.Load .Data) .PBMT_PMA (.Physaddr address) 8 false false false
      (sequentialState (counterState s) pc) =
      .ok (.Ok value) (sequentialState (counterState s) pc)) :
    rvStep s = some (commitState (loadA2BodyState s pc value) (BitVec.addInt pc 4)) :=
  rvStep_ld_of_mem h pc address value 0x00053603#32 (.Regidx 10#5) (.Regidx 12#5) hpc
    halign (rX_bits_a0 (sequentialState_get?_of_get? pc haddress))
    (wX_bits_a2 _ _) decode_swap_ld_a2 hfetch hread
    ((h.counterState.sequentialState pc).insert .x12 value trivial)
    (by simp [loadA2BodyState, sequentialState, get?_insert])
    (by simp [loadA2BodyState, sequentialState, counterState, get?_insert])

/-- The exchange store from a3 follows the complete Sail wrapper after successful RAM operations. -/
theorem rvStep_sd_a3_of_mem
    (haddress : s.regs.get? Register.x10 = some address)
    (hvalue : s.regs.get? Register.x13 = some value)
    (hfetch : runSail (fetch ()) (counterState s) = some (.F_Base 0x00d53023#32, counterState s))
    (hea : mem_write_ea (.Physaddr address) 8 (.Store .Data) .PBMT_PMA false false false
      (sequentialState (counterState s) pc) =
      .ok (.Ok ()) (sequentialState (counterState s) pc))
    (hwrite : mem_write_value (.Physaddr address) 8 value (.Store .Data) .PBMT_PMA
      false false false (sequentialState (counterState s) pc) =
      .ok (.Ok true) (storeBodyState s pc address value)) :
    rvStep s = some (commitState (storeBodyState s pc address value) (BitVec.addInt pc 4)) :=
  rvStep_sd_of_mem h pc address value 0x00d53023#32 (.Regidx 13#5) (.Regidx 10#5) hpc halign
    (rX_bits_a0 (sequentialState_get?_of_get? pc haddress))
    (rX_bits_a3 (sequentialState_get?_of_get? pc hvalue)) decode_swap_sd_a3 hfetch hea hwrite

/-- The exchange load into a3 follows the complete Sail wrapper after successful RAM fetch/read. -/
theorem rvStep_ld_a3_of_mem
    (haddress : s.regs.get? Register.x11 = some address)
    (hfetch : runSail (fetch ()) (counterState s) = some (.F_Base 0x0005b683#32, counterState s))
    (hread : mem_read (.Load .Data) .PBMT_PMA (.Physaddr address) 8 false false false
      (sequentialState (counterState s) pc) =
      .ok (.Ok value) (sequentialState (counterState s) pc)) :
    rvStep s = some (commitState (loadA3BodyState s pc value) (BitVec.addInt pc 4)) :=
  rvStep_ld_of_mem h pc address value 0x0005b683#32 (.Regidx 11#5) (.Regidx 13#5) hpc
    halign (rX_bits_a1 (sequentialState_get?_of_get? pc haddress))
    (wX_bits_a3 _ _) decode_swap_ld_a3 hfetch hread
    ((h.counterState.sequentialState pc).insert .x13 value trivial)
    (by simp [loadA3BodyState, sequentialState, get?_insert])
    (by simp [loadA3BodyState, sequentialState, counterState, get?_insert])

/-- The exchange store from a2 follows the complete Sail wrapper after successful RAM operations. -/
theorem rvStep_sd_a2_of_mem
    (haddress : s.regs.get? Register.x11 = some address)
    (hvalue : s.regs.get? Register.x12 = some value)
    (hfetch : runSail (fetch ()) (counterState s) = some (.F_Base 0x00c5b023#32, counterState s))
    (hea : mem_write_ea (.Physaddr address) 8 (.Store .Data) .PBMT_PMA false false false
      (sequentialState (counterState s) pc) =
      .ok (.Ok ()) (sequentialState (counterState s) pc))
    (hwrite : mem_write_value (.Physaddr address) 8 value (.Store .Data) .PBMT_PMA
      false false false (sequentialState (counterState s) pc) =
      .ok (.Ok true) (storeBodyState s pc address value)) :
    rvStep s = some (commitState (storeBodyState s pc address value) (BitVec.addInt pc 4)) :=
  rvStep_sd_of_mem h pc address value 0x00c5b023#32 (.Regidx 12#5) (.Regidx 11#5) hpc halign
    (rX_bits_a1 (sequentialState_get?_of_get? pc haddress))
    (rX_bits_a2 (sequentialState_get?_of_get? pc hvalue)) decode_swap_sd_a2 hfetch hea hwrite

end Aligned

/-- The allocated exchange load into a2 takes one actual user-mode Sail step. -/
theorem rvStep_ld_a2
    (haddress : s.regs.get? Register.x10 = some address)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0)
    (hram : InUserRam address 8) (halign : address.toNat % 8 = 0)
    (hword : Word32At s pc 0x00053603#32) (hdata : Word64At s address value) :
    rvStep s = some (commitState (loadA2BodyState s pc value) (BitVec.addInt pc 4)) := by
  apply rvStep_ld_a2_of_mem h pc address value hpc halign haddress
  · exact h.counterState.fetch32 pc 0x00053603#32 (counterState_get?_PC hpc)
      hcode hpcAlign (by decide +kernel) hword
  · exact (h.counterState.sequentialState pc).mem_read64 hram halign hdata

/-- The allocated exchange store from a3 takes one actual user-mode Sail step. -/
theorem rvStep_sd_a3
    (haddress : s.regs.get? Register.x10 = some address)
    (hvalue : s.regs.get? Register.x13 = some value)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0)
    (hram : InUserRam address 8) (halign : address.toNat % 8 = 0)
    (hword : Word32At s pc 0x00d53023#32) :
    rvStep s = some (commitState (storeBodyState s pc address value) (BitVec.addInt pc 4)) := by
  apply rvStep_sd_a3_of_mem h pc address value hpc halign haddress hvalue
  · exact h.counterState.fetch32 pc 0x00d53023#32 (counterState_get?_PC hpc)
      hcode hpcAlign (by decide +kernel) hword
  · exact (h.counterState.sequentialState pc).mem_write_ea64 address hram halign
  · exact (h.counterState.sequentialState pc).mem_write64 address value hram halign

/-- The allocated exchange load into a3 takes one actual user-mode Sail step. -/
theorem rvStep_ld_a3
    (haddress : s.regs.get? Register.x11 = some address)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0)
    (hram : InUserRam address 8) (halign : address.toNat % 8 = 0)
    (hword : Word32At s pc 0x0005b683#32) (hdata : Word64At s address value) :
    rvStep s = some (commitState (loadA3BodyState s pc value) (BitVec.addInt pc 4)) := by
  apply rvStep_ld_a3_of_mem h pc address value hpc halign haddress
  · exact h.counterState.fetch32 pc 0x0005b683#32 (counterState_get?_PC hpc)
      hcode hpcAlign (by decide +kernel) hword
  · exact (h.counterState.sequentialState pc).mem_read64 hram halign hdata

/-- The allocated exchange store from a2 takes one actual user-mode Sail step. -/
theorem rvStep_sd_a2
    (haddress : s.regs.get? Register.x11 = some address)
    (hvalue : s.regs.get? Register.x12 = some value)
    (hcode : InUserRam pc 4) (hpcAlign : pc.toNat % 4 = 0)
    (hram : InUserRam address 8) (halign : address.toNat % 8 = 0)
    (hword : Word32At s pc 0x00c5b023#32) :
    rvStep s = some (commitState (storeBodyState s pc address value) (BitVec.addInt pc 4)) := by
  apply rvStep_sd_a2_of_mem h pc address value hpc halign haddress hvalue
  · exact h.counterState.fetch32 pc 0x00c5b023#32 (counterState_get?_PC hpc)
      hcode hpcAlign (by decide +kernel) hword
  · exact (h.counterState.sequentialState pc).mem_write_ea64 address hram halign
  · exact (h.counterState.sequentialState pc).mem_write64 address value hram halign

end MetrologyAsm
