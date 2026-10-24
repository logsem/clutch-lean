import MetrologyAsm.Profile.Rules
import MetrologyAsm.Sail.MemoryRules
import MetrologyAsm.Sail.GuardRules
import MetrologyAsm.Sail.Decode

/-! # Fetch and decode rules for ordinary user instructions -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail

/-- A four-byte aligned address has its two low bits clear. -/
theorem aligned4_access {a : BitVec 64} (halign : a.toNat % 4 = 0) :
    BitVec.access a 0 = 0#1 ∧ BitVec.access a 1 = 0#1 := by
  have hlow : a.extractLsb' 0 2 = 0#2 := by
    apply _root_.BitVec.eq_of_toNat_eq
    simpa [_root_.BitVec.extractLsb'_toNat] using halign
  have hzero : a.getLsbD 0 = false := by
    have hb := congrArg (fun v : BitVec 2 => v.getLsbD 0) hlow
    simpa using hb
  have hone : a.getLsbD 1 = false := by
    have hb := congrArg (fun v : BitVec 2 => v.getLsbD 1) hlow
    simpa using hb
  change _root_.BitVec.ofBool (a.getLsbD 0) = 0#1 ∧ _root_.BitVec.ofBool (a.getLsbD 1) = 0#1
  simp [-_root_.BitVec.getLsbD_eq_getElem, hzero, hone]

variable {s : Mach} (h : UserConfig s)

include h

section Fetch

variable (pc : BitVec 64) (word : BitVec 32)

/-- A successful physical instruction read lifts through bare translation and fetch checks. -/
theorem fetch_bytes32_of_mem_read
    (hmem : mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pc) 4 false false false s =
      .ok (.Ok word) s) :
    runSail (fetch_bytes pc pc 4) s = some (.FetchBytes_Success word, s) := by
  have htranslate := (runSail_eq_some_iff _ _ _ _).mp
    (h.translateAddr_user pc (.InstructionFetch ()) rfl)
  sail_simp [runSail, fetch_bytes, ext_fetch_check_pc, htranslate, hmem]

/-- Four-byte aligned ordinary instructions follow the generated single-word fetch path. -/
theorem fetch32_of_fetch_bytes
    (hpc : s.regs.get? Register.PC = some pc)
    (halign0 : BitVec.access pc 0 = 0#1) (halign1 : BitVec.access pc 1 = 0#1)
    (halign : is_aligned_vaddr (.Virtaddr pc) 4 = true)
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false)
    (hfetch : runSail (fetch_bytes pc pc 4) s = some (.FetchBytes_Success word, s)) :
    runSail (fetch ()) s = some (.F_Base word, s) := by
  have hzca := (runSail_eq_some_iff _ _ _ _).mp h.disabled_Zca
  have hbytes := (runSail_eq_some_iff _ _ _ _).mp hfetch
  have hziccif : currentlyEnabled .Ext_Ziccif s = .ok true s := by
    simp [currentlyEnabled, hartSupports, pure, EStateM.pure]
  sail_simp [runSail, fetch, get_config_rvfi, readReg_eq hpc, ext_fetch_check_pc, halign0, halign1,
    hzca, halign, hziccif, hbytes, hbase]

/-- PMA and PMP success suffice to fetch an allocated aligned ordinary user instruction. -/
theorem fetch32_of_guards
    (info : Phys_Mem_Access_Info)
    (hpc : s.regs.get? Register.PC = some pc)
    (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false)
    (hcheck : check_pma_with_pmp_priority (.InstructionFetch ()) .PBMT_PMA .User
      (.Physaddr pc) 4 false s = .ok (.Ok info) s)
    (hpmp : pmpCheck (.Physaddr pc) 4 (.InstructionFetch ()) .User s = .ok none s)
    (hword : Word32At s pc word) :
    runSail (fetch ()) s = some (.F_Base word, s) := by
  have haligned := is_aligned_vaddr_of_mod_eq_zero halign
  have hbits := aligned4_access halign
  have hchecked := checked_mem_read32_of_guards (.InstructionFetch ()) .User info hcheck
    (split_misaligned_of_aligned info haligned) hpmp (h.within_mmio_readable hram) hword
  have hread := h.mem_read_of_checked (.InstructionFetch ()) (.Physaddr pc) hchecked
  exact fetch32_of_fetch_bytes h pc word hpc hbits.1 hbits.2 haligned hbase
    (fetch_bytes32_of_mem_read h pc word hread)

/-- An allocated aligned ordinary instruction is fetched under the actual user profile. -/
theorem UserConfig.fetch32
    (hpc : s.regs.get? Register.PC = some pc)
    (hram : InUserRam pc 4) (halign : pc.toNat % 4 = 0)
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false)
    (hword : Word32At s pc word) :
    runSail (fetch ()) s = some (.F_Base word, s) :=
  fetch32_of_guards h pc word _ hpc hram halign hbase
    (h.check_pma_fetch hram (is_aligned_vaddr_of_mod_eq_zero halign))
    (h.pmp_fetch hram (by decide)) hword

end Fetch

/-- A guarded decoder equation decodes in any configured user state. -/
theorem decode_of_guarded (word : BitVec 32) (i : instruction)
    (hdecode : ext_decode word = guardedDecode i) :
    runSail (ext_decode word) s = some (i, s) := by
  rw [hdecode, runSail_eq_some_iff]
  exact guardedDecode_result i s false ((runSail_eq_some_iff _ _ _ _).mp h.disabled_Zicfilp)

end MetrologyAsm
