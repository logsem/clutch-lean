import MetrologyAsm.Sail.FetchRules
import MetrologyAsm.Sail.ReturnRules

/-! # Complete Sail wrapper rules for user instructions -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail

/-- Committing a completed instruction changes its architectural program counter. -/
def commitState (s : Mach) (pc : BitVec 64) : Mach :=
  { s with regs := s.regs.insert Register.PC pc }

/-- The exact prepared-state effect of one doubleword store. -/
def storeBodyState (s : Mach) (pc address value : BitVec 64) : Mach :=
  write64State (sequentialState (counterState s) pc) address value

/-- A successful user fetch, decode, and body compose through the complete Sail step wrapper. -/
theorem rvStep_user_of_execute {s t : Mach} (h : UserConfig s)
    (pc : BitVec 64) (word : BitVec 32) (inst : instruction) (next : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc)
    (hfetch : runSail (fetch ()) (counterState s) = some (.F_Base word, counterState s))
    (hdecode : runSail (ext_decode word) (counterState s) = some (inst, counterState s))
    (hexec : runSail (execute inst) (sequentialState (counterState s) pc) =
      some (.Retire_Success (), t))
    (ht : UserConfig t) (hnext : t.regs.get? Register.nextPC = some next)
    (hflag : t.regs.get? Register.minstret_increment = some false) :
    rvStep s = some { t with regs := t.regs.insert Register.PC next } := by
  have hc := h.counterState
  have help : (counterState s).regs.get? Register.elp = some 0#1 := by
    obtain ⟨v, hv, hp⟩ := hc.regs .elp
    simp only [userRegPolicy] at hp
    simpa [hp] using hv
  have hpc' : (counterState s).regs.get? Register.PC = some pc := by
    simp [counterState, Std.ExtDHashMap.get?_insert, hpc]
  have hrun := run_hart_active_of_execute (counterState s) t .User pc word inst
    hc.privilege hc.dispatchInterrupt_none hfetch hdecode help hpc' hexec
  exact rvStep_of_retired s t .User word next h.privilege h.active h.count_disabled
    hrun ht.active hnext hflag

/-- The exact state returned by a user return instruction before committing its program counter. -/
def retBodyState (s : Mach) (pc ra : BitVec 64) : Mach :=
  let prepared := sequentialState (counterState s) pc
  { prepared with regs := prepared.regs.insert Register.nextPC ra }

/-- A fetched exchange return executes the full generated step and jumps to ra. -/
theorem rvStep_ret_of_fetch {s : Mach} (h : UserConfig s) (pc ra : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc)
    (hra : s.regs.get? Register.x1 = some ra)
    (halign0 : BitVec.access ra 0 = 0#1) (halign1 : BitVec.access ra 1 = 0#1)
    (hfetch : runSail (fetch ()) (counterState s) = some (.F_Base 0x00008067#32, counterState s)) :
    rvStep s = some { (retBodyState s pc ra) with
      regs := (retBodyState s pc ra).regs.insert Register.PC ra } := by
  have hc := h.counterState
  have hs := hc.sequentialState pc
  have hra' : (sequentialState (counterState s) pc).regs.get? Register.x1 = some ra := by
    simp [sequentialState, counterState, Std.ExtDHashMap.get?_insert, hra]
  have hnext : (sequentialState (counterState s) pc).regs.get? Register.nextPC =
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
  · simp [retBodyState, sequentialState, counterState, Std.ExtDHashMap.get?_insert]

/-- An allocated aligned return instruction performs the full generated user-mode Sail step. -/
theorem rvStep_ret {s : Mach} (h : UserConfig s) (pc ra : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc)
    (hra : s.regs.get? Register.x1 = some ra)
    (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0) (hraAlign : ra.toNat % 4 = 0)
    (hword : Word32At s pc 0x00008067#32) :
    rvStep s = some { (retBodyState s pc ra) with
      regs := (retBodyState s pc ra).regs.insert Register.PC ra } := by
  have hbits := aligned4_access hraAlign
  apply rvStep_ret_of_fetch h pc ra hpc hra hbits.1 hbits.2
  have hpc' : (counterState s).regs.get? Register.PC = some pc := by
    simp [counterState, Std.ExtDHashMap.get?_insert, hpc]
  exact h.counterState.fetch32 pc 0x00008067#32 hpc' hram halign (by decide +kernel) hword

end MetrologyAsm
