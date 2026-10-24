import MetrologyAsm.Sail.FetchRules
import MetrologyAsm.Sail.ReturnRules

/-! # Complete Sail wrapper rules for user instructions -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail Register
open Std.ExtDHashMap

/-- Committing a completed instruction changes its architectural program counter. -/
def commitState (s : Mach) (pc : BitVec 64) : Mach :=
  { s with regs := s.regs.insert PC pc }

/-- The exact prepared-state effect of one doubleword store. -/
def storeBodyState (s : Mach) (pc address value : BitVec 64) : Mach :=
  write64State (sequentialState (counterState s) pc) address value

/-- A register value read from the original state survives the sequential-step preparation. -/
theorem sequentialState_get?_of_get? {s : Mach} {r : Register} {v : RegisterType r}
    (pc : BitVec 64) (hr : s.regs.get? r = some v) (hn : r ≠ nextPC := by decide)
    (hm : r ≠ minstret_increment := by decide) :
    (sequentialState (counterState s) pc).regs.get? r = some v := by
  simp [sequentialState, counterState, get?_insert, hr, Ne.symm hn, Ne.symm hm]

/-- A successful user fetch, decode, and body compose through the complete Sail step wrapper. -/
theorem rvStep_user_of_execute {s t : Mach} (h : UserConfig s)
    (pc : BitVec 64) (word : BitVec 32) (inst : instruction) (next : BitVec 64)
    (hpc : s.regs.get? PC = some pc)
    (hfetch : runSail (fetch ()) (counterState s) = some (.F_Base word, counterState s))
    (hdecode : runSail (ext_decode word) (counterState s) = some (inst, counterState s))
    (hexec : runSail (execute inst) (sequentialState (counterState s) pc) =
      some (.Retire_Success (), t))
    (ht : UserConfig t) (hnext : t.regs.get? nextPC = some next)
    (hflag : t.regs.get? minstret_increment = some false) :
    rvStep s = some { t with regs := t.regs.insert PC next } := by
  have hc := h.counterState
  have help : (counterState s).regs.get? elp = some 0#1 := by
    obtain ⟨v, hv, hp⟩ := hc.regs .elp
    simp only [userRegPolicy] at hp
    simpa [hp] using hv
  have hpc' : (counterState s).regs.get? PC = some pc := by
    simp [counterState, get?_insert, hpc]
  have hrun := run_hart_active_of_execute (counterState s) t .User pc word inst
    hc.privilege hc.dispatchInterrupt_none hfetch hdecode help hpc' hexec
  exact rvStep_of_retired s t .User word next h.privilege h.active h.count_disabled
    hrun ht.active hnext hflag

/-- A fetched aligned doubleword load into `rd` follows the complete Sail wrapper. -/
theorem rvStep_ld_of_mem {s t : Mach} (h : UserConfig s) (pc address value : BitVec 64)
    (word : BitVec 32) (rs1 rd : regidx)
    (hpc : s.regs.get? PC = some pc) (halign : address.toNat % 8 = 0)
    (hbase : rX_bits rs1 (sequentialState (counterState s) pc) =
      .ok address (sequentialState (counterState s) pc))
    (hwrite : wX_bits rd value (sequentialState (counterState s) pc) = .ok () t)
    (hdecode : ext_decode word = guardedDecode (.LOAD (0#12, rs1, rd, false, 8)))
    (hfetch : runSail (fetch ()) (counterState s) = some (.F_Base word, counterState s))
    (hread : mem_read (.Load .Data) .PBMT_PMA (.Physaddr address) 8 false false false
      (sequentialState (counterState s) pc) =
      .ok (.Ok value) (sequentialState (counterState s) pc))
    (ht : UserConfig t) (hnext : t.regs.get? nextPC = some (BitVec.addInt pc 4))
    (hflag : t.regs.get? minstret_increment = some false) :
    rvStep s = some (commitState t (BitVec.addInt pc 4)) := by
  have hc := h.counterState
  have hs := hc.sequentialState pc
  have hbody : execute_LOAD 0#12 rs1 rd false 8 (sequentialState (counterState s) pc) =
      .ok (.Retire_Success ()) t := by
    apply hs.execute_LOAD64_of_mem 0#12 rs1 rd address value
    · simpa [sign_extend, Sail.BitVec.signExtend] using halign
    · exact hbase
    · simpa [sign_extend, Sail.BitVec.signExtend] using hread
    · exact hwrite
  apply rvStep_user_of_execute h pc word (.LOAD (0#12, rs1, rd, false, 8))
    (BitVec.addInt pc 4) hpc hfetch
  · exact decode_of_guarded hc _ _ hdecode
  · exact (runSail_eq_some_iff _ _ _ _).mpr hbody
  · exact ht
  · exact hnext
  · exact hflag

/-- A fetched aligned doubleword store follows the complete Sail wrapper. -/
theorem rvStep_sd_of_mem {s : Mach} (h : UserConfig s) (pc address value : BitVec 64)
    (word : BitVec 32) (rs2 rs1 : regidx)
    (hpc : s.regs.get? PC = some pc) (halign : address.toNat % 8 = 0)
    (hbase : rX_bits rs1 (sequentialState (counterState s) pc) =
      .ok address (sequentialState (counterState s) pc))
    (hvalue : rX_bits rs2 (sequentialState (counterState s) pc) =
      .ok value (sequentialState (counterState s) pc))
    (hdecode : ext_decode word = guardedDecode (.STORE (0#12, rs2, rs1, 8)))
    (hfetch : runSail (fetch ()) (counterState s) = some (.F_Base word, counterState s))
    (hea : mem_write_ea (.Physaddr address) 8 (.Store .Data) .PBMT_PMA false false false
      (sequentialState (counterState s) pc) =
      .ok (.Ok ()) (sequentialState (counterState s) pc))
    (hwrite : mem_write_value (.Physaddr address) 8 value (.Store .Data) .PBMT_PMA
      false false false (sequentialState (counterState s) pc) =
      .ok (.Ok true) (storeBodyState s pc address value)) :
    rvStep s = some (commitState (storeBodyState s pc address value) (BitVec.addInt pc 4)) := by
  have hc := h.counterState
  have hs := hc.sequentialState pc
  have hbody : execute_STORE 0#12 rs2 rs1 8 (sequentialState (counterState s) pc) =
      .ok (.Retire_Success ()) (storeBodyState s pc address value) := by
    apply hs.execute_STORE64_of_mem 0#12 rs2 rs1 address value
    · simpa [sign_extend, Sail.BitVec.signExtend] using halign
    · exact hbase
    · exact hvalue
    · simpa [sign_extend, Sail.BitVec.signExtend] using hea
    · simpa [sign_extend, Sail.BitVec.signExtend] using hwrite
  apply rvStep_user_of_execute h pc word (.STORE (0#12, rs2, rs1, 8))
    (BitVec.addInt pc 4) hpc hfetch
  · exact decode_of_guarded hc _ _ hdecode
  · exact (runSail_eq_some_iff _ _ _ _).mpr hbody
  · exact hs.write64State address value
  · simp [storeBodyState, sequentialState]
  · simp [storeBodyState, sequentialState, counterState, get?_insert]

/-- The exact state returned by a user return instruction before committing its program counter. -/
def retBodyState (s : Mach) (pc ra : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert nextPC ra }

/-- The call sets its target and saves the next instruction address in ra. -/
def linkBodyState (s : Mach) (pc target : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with
    regs := (prepared.regs.insert nextPC target).insert x1 (BitVec.addInt pc 4) }

/-- The import trampoline sets its target without changing the saved link register. -/
def jumpBodyState (s : Mach) (pc target : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert nextPC target }

/-- A fetched exchange return executes the full generated step and jumps to ra. -/
theorem rvStep_ret_of_fetch {s : Mach} (h : UserConfig s) (pc ra : BitVec 64)
    (hpc : s.regs.get? PC = some pc)
    (hra : s.regs.get? x1 = some ra)
    (halign0 : BitVec.access ra 0 = 0#1) (halign1 : BitVec.access ra 1 = 0#1)
    (hfetch : runSail (fetch ()) (counterState s) = some (.F_Base 0x00008067#32, counterState s)) :
    rvStep s = some { (retBodyState s pc ra) with
      regs := (retBodyState s pc ra).regs.insert PC ra } := by
  have hc := h.counterState
  have hs := hc.sequentialState pc
  have hra' : (sequentialState (counterState s) pc).regs.get? x1 = some ra := by
    simp [sequentialState, counterState, get?_insert, hra]
  have hnext : (sequentialState (counterState s) pc).regs.get? nextPC =
      some (BitVec.addInt pc 4) := by
    simp [sequentialState]
  have hbody := execute_ret_eq hs ra (BitVec.addInt pc 4) hra' hnext halign0 halign1
  have ht : UserConfig (retBodyState s pc ra) := hs.insert .nextPC ra trivial
  apply rvStep_user_of_execute h pc 0x00008067#32
    (.JALR (0#12, .Regidx 1#5, .Regidx 0#5)) ra hpc hfetch
  · exact decode_of_guarded hc _ _ decode_ret
  · exact hbody
  · exact ht
  · simp [retBodyState]
  · simp [retBodyState, sequentialState, counterState, get?_insert]

/-- An allocated aligned return instruction performs the full generated user-mode Sail step. -/
theorem rvStep_ret {s : Mach} (h : UserConfig s) (pc ra : BitVec 64)
    (hpc : s.regs.get? PC = some pc)
    (hra : s.regs.get? x1 = some ra)
    (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0) (hraAlign : ra.toNat % 4 = 0)
    (hword : Word32At s pc 0x00008067#32) :
    rvStep s = some { (retBodyState s pc ra) with
      regs := (retBodyState s pc ra).regs.insert PC ra } := by
  have hbits := aligned4_access hraAlign
  apply rvStep_ret_of_fetch h pc ra hpc hra hbits.1 hbits.2
  have hpc' : (counterState s).regs.get? PC = some pc := by
    simp [counterState, get?_insert, hpc]
  exact h.counterState.fetch32 pc 0x00008067#32 hpc' hram halign (by decide +kernel) hword

end MetrologyAsm
