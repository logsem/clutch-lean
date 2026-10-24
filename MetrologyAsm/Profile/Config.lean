import MetrologyAsm.Sail.StepRules

/-! # The prototype's user-mode machine profile -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail
open Register

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

/-- The address of an uncompressed instruction relative to the image base. -/
def pcAt (base : BitVec 64) (i : Nat) : BitVec 64 :=
  BitVec.addInt base (4 * (i : Int))

/-- The first instruction is at the image base. -/
@[simp] theorem pcAt_zero (base : BitVec 64) : pcAt base 0 = base := by
  simp [pcAt, BitVec.addInt]

/-- Advancing an instruction address selects the next image word. -/
theorem pcAt_next (base : BitVec 64) (i : Nat) :
    BitVec.addInt (pcAt base i) 4 = pcAt base (i + 1) := by
  change (base + BitVec.ofInt 64 (4 * (i : Int))) + BitVec.ofInt 64 4 = _
  rw [BitVec.add_assoc, ← BitVec.ofInt_add]
  unfold pcAt BitVec.addInt
  congr 2

section Image

variable {base : BitVec 64} {n : Nat} (hram : InUserRam base (4 * n))

include hram

/-- Instruction addresses in a mapped image of `n` words do not wrap. -/
theorem pcAt_toNat {i : Nat} (hi : i ≤ n) : (pcAt base i).toNat = base.toNat + 4 * i := by
  have hsmall : 4 * i < 2 ^ 64 := by
    obtain ⟨_, hend⟩ := hram
    omega
  have hsum : base.toNat + 4 * i < 2 ^ 64 := by
    obtain ⟨_, hend⟩ := hram
    omega
  simp only [pcAt, BitVec.addInt, BitVec.toNat_add]
  have hcast : BitVec.ofInt 64 (4 * (i : Int)) = BitVec.ofNat 64 (4 * i) := by
    rw [show (4 * (i : Int)) = ((4 * i : Nat) : Int) by omega, BitVec.ofInt_natCast]
  rw [hcast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hsum]

/-- Each instruction of a mapped image is mapped. -/
theorem pcAt_inUserRam {i : Nat} (hi : i < n) : InUserRam (pcAt base i) 4 := by
  rw [InUserRam, pcAt_toNat hram (Nat.le_of_lt hi)]
  obtain ⟨hstart, hend⟩ := hram
  constructor <;> omega

/-- Each instruction of a four-byte-aligned mapped image is aligned. -/
theorem pcAt_aligned (halign : base.toNat % 4 = 0) {i : Nat} (hi : i < n) :
    (pcAt base i).toNat % 4 = 0 := by
  rw [pcAt_toNat hram (Nat.le_of_lt hi)]
  omega

end Image

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
theorem privilege : s.regs.get? cur_privilege = some .User := by
  obtain ⟨v, hv, hp⟩ := h.regs .cur_privilege
  simp only [userRegPolicy] at hp
  simpa [hp] using hv

/-- Configured code starts in the active hart state. -/
theorem active :
    s.regs.get? hart_state = some (.HART_ACTIVE ()) := by
  obtain ⟨v, hv, hp⟩ := h.regs .hart_state
  simp only [userRegPolicy] at hp
  simpa [hp] using hv

/-- The retirement counter is not incremented at user privilege in a configured state. -/
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
