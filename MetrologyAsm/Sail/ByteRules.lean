import MetrologyAsm.Sail.InstructionRules
import Std.Data.ExtHashMap.Lemmas

/-! # Single-byte memory effects and unsigned-load instruction rules -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions Sail
open Sail.ConcurrencyInterfaceV1

/-- Installing one owned byte preserves every non-memory field of the Sail state. -/
def write8State (s : Mach) (address : BitVec 64) (value : BitVec 8) : Mach :=
  { s with mem := s.mem.insert address.toNat value }

/-- Installing a byte realizes its exact physical memory lookup. -/
@[simp] theorem write8State_get (s : Mach) (address : BitVec 64) (value : BitVec 8) :
    (write8State s address value).mem.get? address.toNat = some value := by
  simp [write8State, Std.ExtHashMap.get?_eq_getElem?]

/-- Installing a byte preserves every physical memory address outside its cell. -/
theorem write8State_get_other (s : Mach) (address : BitVec 64) (value : BitVec 8) (a : Nat)
    (ha : address.toNat ≠ a) : (write8State s address value).mem.get? a = s.mem.get? a := by
  simp [write8State, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, ha]

/-- One-byte installation preserves the complete user-mode register profile. -/
theorem UserConfig.write8State {s : Mach} (h : UserConfig s)
    (address : BitVec 64) (value : BitVec 8) :
    UserConfig (MetrologyAsm.write8State s address value) :=
  h.of_regs_eq rfl

/-- Sail's byte-vector reader returns an allocated single byte without a state change. -/
theorem readBytes8_eq {s : Mach} {address : Nat} {value : BitVec 8}
    (h : s.mem.get? address = some value) :
    (PreSail.readBytes 1 address : SailM (BitVec 8 × Option Bool)) s = .ok (value, none) s := by
  simp [PreSail.readBytes, PreSail.readByte, Std.ExtHashMap.get?_eq_getElem?] at h ⊢
  simp [h, bind, EStateM.bind, Functor.map, EStateM.map, pure, EStateM.pure, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

/-- A plain one-byte RAM read returns the allocated byte unchanged. -/
theorem read_ram8_eq {s : Mach} {address : BitVec 64} {value : BitVec 8}
    (h : s.mem.get? address.toNat = some value) :
    read_ram .Read_plain (.Physaddr address) 1 false s = .ok (value, ()) s := by
  simp [RiscvZkvm.Sail.Functions.read_ram, PreSail.sail_mem_read, readBytes8_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- A single byte never crosses a virtual page boundary. -/
theorem split_on_page_boundary8_eq (s : Mach) (address : BitVec 64) :
    split_on_page_boundary address 1 s = .ok (1, 0) s := by
  have hlast : Sail.BitVec.subInt (Sail.BitVec.addInt address 1) 1 = address := by
    change address + 1#64 - 1#64 = address
    exact BitVec.add_sub_cancel _ _
  simp [split_on_page_boundary, hlast, pure, EStateM.pure]

/-- Successful physical guards reduce a one-byte read to its allocated RAM cell. -/
theorem checked_mem_read8_of_guards {s : Mach} {address : BitVec 64} {value : BitVec 8}
    (access : MemoryAccessType mem_payload) (priv : Privilege) (info : Phys_Mem_Access_Info)
    (hcheck : check_pma_with_pmp_priority access .PBMT_PMA priv (.Physaddr address) 1 false s =
      .ok (.Ok info) s)
    (hsplit : split_misaligned (.Physaddr address) 1 info.granule_size_exp info.splittable s =
      .ok (1, 1) s)
    (hpmp : pmpCheck (.Physaddr address) 1 access priv s = .ok none s)
    (hmmio : within_mmio_readable (.Physaddr address) 1 s = .ok false s)
    (hbyte : s.mem.get? address.toNat = some value) :
    checked_mem_read access .PBMT_PMA priv (.Physaddr address) 1 false false false false s =
      .ok (.Ok (value, ())) s := by
  simp [checked_mem_read, SailME.run, PreSail.PreSailME.run, hcheck, hsplit,
    read_kind_of_flags, misaligned_order, sys_misaligned_order_decreasing, untilFuelM,
    untilFuelM.go, bind, EStateM.bind, EStateM.map, pure, EStateM.pure, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure, MonadLift.monadLift,
    monadLift, liftM, Functor.map, Sail.assert, PreSail.assert, bits_of_physaddr,
    Sail.BitVec.addInt, hpmp, hmmio, read_ram8_eq hbyte, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']

namespace UserConfig

variable {s : Mach} (h : UserConfig s)
include h

/-- A configured RAM byte load reads its allocated physical cell unchanged. -/
theorem mem_read8 {address : BitVec 64} {value : BitVec 8}
    (hram : InUserRam address 1) (hbyte : s.mem.get? address.toNat = some value) :
    mem_read (.Load .Data) .PBMT_PMA (.Physaddr address) 1 false false false s =
      .ok (.Ok value) s := by
  have halign := is_aligned_vaddr_of_mod_eq_zero (a := address) (width := 1) (by omega)
  have hpmp := (runSail_eq_some_iff _ _ _ _).mp
    (h.pmpCheck_user hram (by decide) (.Load .Data) (Or.inr (Or.inl rfl)))
  apply h.mem_read_of_checked
  exact checked_mem_read8_of_guards (.Load .Data) .User _ (h.check_pma_load hram halign)
    (split_misaligned_of_aligned _ halign) hpmp (h.within_mmio_readable hram) hbyte

/-- A virtual byte load uses the configured bare translation and successful physical read. -/
theorem vmem_read_addr8_of_mem (address : BitVec 64) (value : BitVec 8)
    (hread : mem_read (.Load .Data) .PBMT_PMA (.Physaddr address) 1 false false false s =
      .ok (.Ok value) s) :
    vmem_read_addr (.Virtaddr address) 1 (.Load .Data) false false false s = .ok (.Ok value) s := by
  obtain ⟨m, hm, _⟩ := h.regs .mstatus
  have heff := (runSail_eq_some_iff _ _ _ _).mp (h.effectivePrivilege_user (.Load .Data) hm)
  have hmode := (runSail_eq_some_iff _ _ _ _).mp h.translationMode_user
  have htranslate := (runSail_eq_some_iff _ _ _ _).mp
    (h.translateAddr_user address (.Load .Data) rfl)
  have halign := is_aligned_vaddr_of_mod_eq_zero (a := address) (width := 1) (by omega)
  simp [vmem_read_addr, SailME.run, PreSail.PreSailME.run, halign,
    RiscvZkvm.Sail.Functions.not, split_on_page_boundary8_eq s address, bits_of_virtaddr,
    readReg_eq hm, readReg_eq h.privilege, heff, hmode, translate_and_read_value,
    htranslate, hread, sys_misaligned_order_decreasing, bind, EStateM.bind, EStateM.map,
    pure, EStateM.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.lift, ExceptT.pure, MonadLift.monadLift, monadLift, liftM, Functor.map,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']

/-- A byte load through a register uses that register's actual virtual address. -/
theorem vmem_read8_of_mem (rs : regidx) (base offset : BitVec 64) (value : BitVec 8)
    (hbase : rX_bits rs s = .ok base s)
    (hread : mem_read (.Load .Data) .PBMT_PMA (.Physaddr (base + offset))
      1 false false false s = .ok (.Ok value) s) :
    vmem_read rs offset 1 (.Load .Data) false false false s = .ok (.Ok value) s := by
  have htransform := (runSail_eq_some_iff _ _ _ _).mp
    (h.transform_effective_address_user (.Virtaddr (base + offset)) (.Load .Data))
  have haddr := h.vmem_read_addr8_of_mem (base + offset) value hread
  simp [vmem_read, get_transformed_data_addr, ext_data_get_addr, hbase, htransform,
    haddr, SailME.run, PreSail.PreSailME.run, bind, EStateM.bind, EStateM.map,
    pure, EStateM.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.lift, ExceptT.pure, MonadLift.monadLift, monadLift, liftM, Functor.map]

/-- An unsigned-byte load retires with its zero-extended byte written to the destination. -/
theorem execute_LBU {t : Mach} (imm : BitVec 12) (rs rd : regidx)
    (base : BitVec 64) (value : BitVec 8)
    (hbase : rX_bits rs s = .ok base s)
    (hram : InUserRam (base + sign_extend (m := 64) imm) 1)
    (hbyte : s.mem.get? (base + sign_extend (m := 64) imm).toNat = some value)
    (hwrite : wX_bits rd (value.setWidth 64) s = .ok () t) :
    execute_LOAD imm rs rd true 1 s = .ok (.Retire_Success ()) t := by
  have hread := h.vmem_read8_of_mem rs base _ value hbase (h.mem_read8 hram hbyte)
  simp [execute_LOAD, RiscvZkvm.Sail.Functions.xlen_bytes, hread, extend_value,
    zero_extend, Sail.BitVec.zeroExtend, hwrite, bind, EStateM.bind, pure, EStateM.pure,
    Sail.assert, PreSail.assert, RETIRE_SUCCESS]

end UserConfig

end MetrologyAsm
