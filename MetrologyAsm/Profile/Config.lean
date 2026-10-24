import MetrologyAsm.Sail.StepRules

/-! # The prototype's user-mode machine profile -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail

/-- The main-memory region available to prototype code and logical heap embeddings. -/
def userRamRegion : PMA_Region :=
  { base := 0x80000000#64
    size := 0x80000000#64
    attributes :=
      { mem_type := .MainMemory
        cacheable := true
        coherent := true
        executable := true
        readable := true
        writable := true
        read_idempotent := true
        write_idempotent := true
        misaligned_exceptions :=
          { load_store := some .AlignmentException
            vector := some .AlignmentException
            amo := .AccessFault }
        atomic_support := .AMONone
        reservability := .RsrvNone
        supports_cbo_zero := false
        supports_pte_read := false
        supports_pte_write := false
        misaligned_atomicity_granule_size_exp := 0
        vector_misaligned_atomicity_granule_size_exp := 0 }
    include_in_device_tree := false }

/-- A nonwrapping physical access entirely within the prototype's main memory. -/
def InUserRam (address : BitVec 64) (width : Nat) : Prop :=
  0x80000000 ≤ address.toNat ∧ address.toNat + width ≤ 0x100000000

/-- Register constraints for user-mode execution; unlisted registers are unconstrained. -/
def userRegPolicy : (r : Register) → RegisterType r → Prop
  | .hart_state, v => v = .HART_ACTIVE ()
  | .cur_privilege, v => v = .User
  | .misa, v =>
    _get_Misa_MXL v = 2#2 ∧ _get_Misa_I v = 1#1 ∧ _get_Misa_M v = 1#1 ∧
      _get_Misa_U v = 1#1 ∧ _get_Misa_S v = 1#1 ∧ _get_Misa_C v = 0#1
  | .mstatus, v =>
    _get_Mstatus_SXL v = 2#2 ∧ _get_Mstatus_UXL v = 2#2 ∧ _get_Mstatus_MPRV v = 0#1
  | .satp, v => _get_Satp64_Mode v = 0#4
  | .mseccfg, v => _get_Seccfg_PMM v = 0#2 ∧ _get_Seccfg_MLPE v = 0#1
  | .menvcfg, v =>
    _get_MEnvcfg_PMM v = 0#2 ∧ _get_MEnvcfg_LPE v = 0#1 ∧ _get_MEnvcfg_SSE v = 0#1
  | .senvcfg, v =>
    _get_SEnvcfg_PMM v = 0#2 ∧ _get_SEnvcfg_LPE v = 0#1 ∧ _get_SEnvcfg_SSE v = 0#1
  | .mie, v => v = 0#64
  | .mcountinhibit, v => _get_Counterin_IR v = 1#1
  | .elp, v => v = 0#1
  | .fcsr, v => _get_Fcsr_FRM v = 0#3
  | .mtvec, v => _get_Mtvec_Mode v = 0#2
  | .stvec, v => _get_Mtvec_Mode v = 0#2
  | .htif_tohost_base, v => v = none
  | .pmpcfg_n, v => v[0] = 0x0f#8
  | .pmpaddr_n, v => v[0] = 0x40000000#64
  | .pma_regions, v => ∃ rest, v = userRamRegion :: rest
  | _, _ => True

/-- A complete Sail register file satisfying the prototype's user-mode constraints. -/
structure UserConfig (s : Mach) : Prop where
  /-- Every architectural and model register has a value satisfying its policy. -/
  regs : ∀ r, ∃ v, s.regs.get? r = some v ∧ userRegPolicy r v

namespace UserConfig

variable {s : Mach} (h : UserConfig s)

include h

/-- Every register is present in a configured machine state. -/
theorem present (r : Register) : ∃ v, s.regs.get? r = some v := by
  obtain ⟨v, hv, _⟩ := h.regs r
  exact ⟨v, hv⟩

/-- Configured code executes at user privilege. -/
theorem privilege : s.regs.get? Register.cur_privilege = some .User := by
  obtain ⟨v, hv, hp⟩ := h.regs .cur_privilege
  simp only [userRegPolicy] at hp
  simpa [hp] using hv

/-- Configured code starts in the active hart state. -/
theorem active :
    s.regs.get? Register.hart_state = some (.HART_ACTIVE ()) := by
  obtain ⟨v, hv, hp⟩ := h.regs .hart_state
  simp only [userRegPolicy] at hp
  simpa [hp] using hv

/-- The retirement counter stays disabled for every configured user instruction. -/
theorem count_disabled :
    runSail (should_inc_minstret .User) s = some (false, s) := by
  obtain ⟨inh, hinh, hp⟩ := h.regs .mcountinhibit
  obtain ⟨cfg, hcfg⟩ := h.present .minstretcfg
  simp only [userRegPolicy] at hp
  simp [runSail, should_inc_minstret, bind, EStateM.bind, readReg_eq hinh,
    readReg_eq hcfg, pure, EStateM.pure, hp]

/-- Changing memory or other state fields preserves the profile when the register file is fixed. -/
theorem of_regs_eq {t : Mach} (heq : t.regs = s.regs) : UserConfig t :=
  ⟨heq ▸ h.regs⟩

/-- A register update preserves the profile when its new value satisfies the register policy. -/
theorem insert (r : Register) (v : RegisterType r)
    (hv : userRegPolicy r v) : UserConfig { s with regs := s.regs.insert r v } := by
  constructor
  intro q
  by_cases heq : r = q
  · subst q
    exact ⟨v, by simp, hv⟩
  · obtain ⟨w, hw, hp⟩ := h.regs q
    refine ⟨w, ?_, hp⟩
    simp [Std.ExtDHashMap.get?_insert, heq, hw]

/-- Preparing the retirement flag preserves the user-mode profile. -/
theorem counterState : UserConfig (MetrologyAsm.counterState s) :=
  h.insert .minstret_increment false trivial

/-- Preparing a sequential next program counter preserves the user-mode profile. -/
theorem sequentialState (pc : BitVec 64) :
    UserConfig (MetrologyAsm.sequentialState s pc) :=
  h.insert .nextPC (BitVec.addInt pc 4) trivial

end UserConfig

end MetrologyAsm
