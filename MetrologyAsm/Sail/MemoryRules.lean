import MetrologyAsm.Sail.GuardRules
import MetrologyAsm.Profile.Rules
import Std.Data.ExtHashMap.Lemmas
import Lean.Elab.Tactic.BVDecide

/-! # Bytewise Sail memory and doubleword instruction rules -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions Sail
open Sail.ConcurrencyInterfaceV1

/-- The little-endian bytes of a word are present at an address. -/
def WordAt (s : Mach) (a : BitVec 64) (width : Nat) (value : BitVec (8 * width)) : Prop :=
  ∀ i < width, s.mem.get? (a.toNat + i) = some (value.extractLsb' (8 * i) 8)

/-- Bytewise assertion that an address holds the eight little-endian bytes of a doubleword. -/
abbrev Word64At (s : Mach) (a : BitVec 64) (value : BitVec 64) : Prop := WordAt s a 8 value

/-- Bytewise assertion that an address holds the four little-endian bytes of an instruction word. -/
abbrev Word32At (s : Mach) (a : BitVec 64) (value : BitVec 32) : Prop := WordAt s a 4 value

/-- Writing a doubleword inserts its eight bytes and preserves every other state field. -/
def write64State (s : Mach) (a : BitVec 64) (value : BitVec 64) : Mach :=
  { s with mem := (List.range 8).foldl (fun mem i =>
      mem.insert (a.toNat + i) (value.extractLsb' (8 * i) 8)) s.mem }

/-- Sail's raw doubleword write has exactly the eight-byte update effect. -/
theorem writeBytes64_eq (s : Mach) (a : BitVec 64) (value : BitVec 64) :
    (PreSail.writeBytes (n := 8) a.toNat value : SailM Bool) s =
      .ok true (write64State s a value) := by
  rfl

/-- A doubleword write preserves the complete register file. -/
@[simp] theorem write64State_regs (s : Mach) (a value : BitVec 64) :
    (write64State s a value).regs = s.regs := rfl

/-- A doubleword write installs exactly its eight little-endian bytes. -/
theorem word64At_write64State (s : Mach) (a value : BitVec 64) :
    Word64At (write64State s a value) a value := by
  intro i hi
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [write64State, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, Nat.add_zero, Std.ExtHashMap.get?_eq_getElem?]
  all_goals simp only [Std.ExtHashMap.getElem?_insert]
  all_goals simp

/-- A doubleword write preserves each byte outside its eight-byte interval. -/
theorem write64State_get?_outside (s : Mach) (a value : BitVec 64) (k : Nat)
    (h : k < a.toNat ∨ a.toNat + 8 ≤ k) :
    (write64State s a value).mem.get? k = s.mem.get? k := by
  have h0 : a.toNat ≠ k := by omega
  have hk : ∀ i < 8, a.toNat + i ≠ k := by
    intro i hi
    omega
  simp [write64State, List.range_succ, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.getElem?_insert, h0, hk 1 (by omega), hk 2 (by omega),
    hk 3 (by omega), hk 4 (by omega), hk 5 (by omega), hk 6 (by omega), hk 7 (by omega)]

/-- Bytewise memory assertions are preserved by equal memory maps. -/
theorem WordAt.of_mem_eq {s t : Mach} {a : BitVec 64} {width : Nat}
    {value : BitVec (8 * width)} (h : WordAt s a width value) (heq : t.mem = s.mem) :
    WordAt t a width value := by
  unfold WordAt at h ⊢
  rw [heq]
  exact h

/-- Plain physical RAM writes perform the eight-byte memory update. -/
theorem write_ram64_eq (s : Mach) (a value : BitVec 64) :
    write_ram .Write_plain (.Physaddr a) 8 value () s = .ok true (write64State s a value) := by
  rfl

/-- Extracting all 64 bits of a doubleword returns it unchanged. -/
theorem extractLsb_63_zero_eq (value : BitVec 64) : Sail.BitVec.extractLsb value 63 0 = value := by
  change value.extractLsb' 0 64 = value
  exact BitVec.extractLsb'_eq_self

section

variable {s : Mach}

/-- Reading an allocated byte preserves the Sail state. -/
theorem readByte_eq {a : Nat} {value : BitVec 8}
    (h : s.mem.get? a = some value) : (PreSail.readByte a : SailM (BitVec 8)) s = .ok value s := by
  have h' : s.mem[a]? = some value := h
  simp [PreSail.readByte, h', bind, EStateM.bind, pure, EStateM.pure, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

/-- Reading eight allocated little-endian bytes returns their doubleword without state changes. -/
theorem readBytes64_eq {a : BitVec 64} {value : BitVec 64}
    (h : Word64At s a value) :
    (PreSail.readBytes 8 a.toNat : SailM (BitVec 64 × Option Bool)) s = .ok (value, none) s := by
  have h0 : s.mem[a.toNat]? = some (value.extractLsb' 0 8) := by simpa using h 0 (by decide)
  have h1 : s.mem[a.toNat + 1]? = some (value.extractLsb' 8 8) := h 1 (by decide)
  have h2 : s.mem[a.toNat + 2]? = some (value.extractLsb' 16 8) := h 2 (by decide)
  have h3 : s.mem[a.toNat + 3]? = some (value.extractLsb' 24 8) := h 3 (by decide)
  have h4 : s.mem[a.toNat + 4]? = some (value.extractLsb' 32 8) := h 4 (by decide)
  have h5 : s.mem[a.toNat + 5]? = some (value.extractLsb' 40 8) := h 5 (by decide)
  have h6 : s.mem[a.toNat + 6]? = some (value.extractLsb' 48 8) := h 6 (by decide)
  have h7 : s.mem[a.toNat + 7]? = some (value.extractLsb' 56 8) := h 7 (by decide)
  simp only [PreSail.readBytes, PreSail.readByte, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.get, get, MonadState.get, getThe, MonadStateOf.get, Nat.add_assoc,
    Nat.reduceAdd, Std.ExtHashMap.get?_eq_getElem?, h0, h1, h2, h3, h4, h5, h6, h7]
  congr 2
  clear h h0 h1 h2 h3 h4 h5 h6 h7 a
  bv_normalize

/-- Reading four allocated little-endian bytes returns their word without state changes. -/
theorem readBytes32_eq {a : BitVec 64} {value : BitVec 32}
    (h : Word32At s a value) :
    (PreSail.readBytes 4 a.toNat : SailM (BitVec 32 × Option Bool)) s = .ok (value, none) s := by
  have h0 : s.mem[a.toNat]? = some (value.extractLsb' 0 8) := by simpa using h 0 (by decide)
  have h1 : s.mem[a.toNat + 1]? = some (value.extractLsb' 8 8) := h 1 (by decide)
  have h2 : s.mem[a.toNat + 2]? = some (value.extractLsb' 16 8) := h 2 (by decide)
  have h3 : s.mem[a.toNat + 3]? = some (value.extractLsb' 24 8) := h 3 (by decide)
  simp only [PreSail.readBytes, PreSail.readByte, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.get, get, MonadState.get, getThe, MonadStateOf.get, Nat.add_assoc,
    Nat.reduceAdd, Std.ExtHashMap.get?_eq_getElem?, h0, h1, h2, h3]
  congr 2
  clear h h0 h1 h2 h3 a
  bv_normalize

/-- Writing a doubleword preserves every disjoint bytewise word assertion. -/
theorem WordAt.write64State {a b : BitVec 64} {width : Nat}
    {value : BitVec (8 * width)} (h : WordAt s b width value) (data : BitVec 64)
    (hdisjoint : a.toNat + 8 ≤ b.toNat ∨ b.toNat + width ≤ a.toNat) :
    WordAt (write64State s a data) b width value := by
  intro i hi
  rw [write64State_get?_outside s a data (b.toNat + i) (by omega)]
  exact h i hi

/-- Plain physical RAM reads return the allocated doubleword unchanged. -/
theorem read_ram64_eq {a value : BitVec 64} (h : Word64At s a value) :
    read_ram .Read_plain (.Physaddr a) 8 false s = .ok (value, ()) s := by
  simp [RiscvZkvm.Sail.Functions.read_ram, PreSail.sail_mem_read, bind, EStateM.bind,
    pure, EStateM.pure, readBytes64_eq h]

/-- Plain physical RAM reads return an allocated instruction word unchanged. -/
theorem read_ram32_eq {a : BitVec 64} {value : BitVec 32}
    (h : Word32At s a value) :
    read_ram .Read_plain (.Physaddr a) 4 false s = .ok (value, ()) s := by
  simp [RiscvZkvm.Sail.Functions.read_ram, PreSail.sail_mem_read, bind, EStateM.bind,
    pure, EStateM.pure, readBytes32_eq h]

/-- Physical instruction reads return the allocated word unchanged. -/
theorem read_ram32_fetch_eq {a : BitVec 64} {value : BitVec 32}
    (h : Word32At s a value) :
    read_ram .Read_ifetch (.Physaddr a) 4 false s = .ok (value, ()) s := by
  simp [RiscvZkvm.Sail.Functions.read_ram, PreSail.sail_mem_read, bind, EStateM.bind,
    pure, EStateM.pure, readBytes32_eq h]

/-- Successful physical access guards reduce a doubleword read to its allocated RAM bytes. -/
theorem checked_mem_read64_of_guards {a value : BitVec 64}
    (access : MemoryAccessType mem_payload) (priv : Privilege) (info : Phys_Mem_Access_Info)
    (hcheck : check_pma_with_pmp_priority access .PBMT_PMA priv (.Physaddr a) 8 false s =
      .ok (.Ok info) s)
    (hsplit : split_misaligned (.Physaddr a) 8 info.granule_size_exp info.splittable s =
      .ok (1, 8) s)
    (hpmp : pmpCheck (.Physaddr a) 8 access priv s = .ok none s)
    (hmmio : within_mmio_readable (.Physaddr a) 8 s = .ok false s)
    (hword : Word64At s a value) :
    checked_mem_read access .PBMT_PMA priv (.Physaddr a) 8 false false false false s =
      .ok (.Ok (value, ())) s := by
  simp [checked_mem_read, SailME.run, PreSail.PreSailME.run, hcheck, hsplit,
    read_kind_of_flags, misaligned_order, sys_misaligned_order_decreasing, untilFuelM,
    untilFuelM.go,
    bind, EStateM.bind, EStateM.map, pure, EStateM.pure, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure, MonadLift.monadLift,
    monadLift, liftM, Functor.map, Sail.assert, PreSail.assert, bits_of_physaddr,
    Sail.BitVec.addInt, hpmp, hmmio, read_ram64_eq hword, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']

/-- Successful physical access guards reduce an instruction-word read to its allocated RAM bytes. -/
theorem checked_mem_read32_of_guards {a : BitVec 64} {value : BitVec 32}
    (access : MemoryAccessType mem_payload) (priv : Privilege) (info : Phys_Mem_Access_Info)
    (hcheck : check_pma_with_pmp_priority access .PBMT_PMA priv (.Physaddr a) 4 false s =
      .ok (.Ok info) s)
    (hsplit : split_misaligned (.Physaddr a) 4 info.granule_size_exp info.splittable s =
      .ok (1, 4) s)
    (hpmp : pmpCheck (.Physaddr a) 4 access priv s = .ok none s)
    (hmmio : within_mmio_readable (.Physaddr a) 4 s = .ok false s)
    (hword : Word32At s a value) :
    checked_mem_read access .PBMT_PMA priv (.Physaddr a) 4 false false false false s =
      .ok (.Ok (value, ())) s := by
  simp [checked_mem_read, SailME.run, PreSail.PreSailME.run, hcheck, hsplit,
    read_kind_of_flags, misaligned_order, sys_misaligned_order_decreasing, untilFuelM,
    untilFuelM.go,
    bind, EStateM.bind, EStateM.map, pure, EStateM.pure, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure, MonadLift.monadLift,
    monadLift, liftM, Functor.map, Sail.assert, PreSail.assert, bits_of_physaddr,
    Sail.BitVec.addInt, hpmp, hmmio, read_ram32_eq hword, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']

/-- Successful physical access guards reduce a doubleword store to eight RAM byte writes. -/
theorem checked_mem_write64_of_guards (a value : BitVec 64)
    (access : MemoryAccessType mem_payload) (priv : Privilege) (info : Phys_Mem_Access_Info)
    (hcheck : check_pma_with_pmp_priority access .PBMT_PMA priv (.Physaddr a) 8 false s =
      .ok (.Ok info) s)
    (hsplit : split_misaligned (.Physaddr a) 8 info.granule_size_exp info.splittable s =
      .ok (1, 8) s)
    (hpmp : pmpCheck (.Physaddr a) 8 access priv s = .ok none s)
    (hmmio : within_mmio_writable (.Physaddr a) 8 s = .ok false s) :
    checked_mem_write (.Physaddr a) 8 value access .PBMT_PMA priv () false false false s =
      .ok (.Ok true) (write64State s a value) := by
  have hdata := extractLsb_63_zero_eq value
  simp [checked_mem_write, SailME.run, PreSail.PreSailME.run, hcheck, hsplit,
    write_kind_of_flags, misaligned_order, sys_misaligned_order_decreasing, untilFuelM,
    untilFuelM.go, bind, EStateM.bind, EStateM.map, pure, EStateM.pure, ExceptT.run,
    ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, monadLift, liftM, Functor.map, Sail.assert, PreSail.assert,
    bits_of_physaddr, Sail.BitVec.addInt, hpmp, hmmio, hdata, write_ram64_eq]

/-- Dropping memory metadata preserves a successful checked read. -/
theorem mem_read_priv_of_checked {width : Nat} {value : BitVec (8 * width)}
    (access : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (priv : Privilege)
    (a : physaddr)
    (hread : checked_mem_read access pbmt priv a width false false false false s =
      .ok (.Ok (value, ())) s) :
    mem_read_priv access pbmt priv a width false false false s = .ok (.Ok value) s := by
  simp [mem_read_priv, mem_read_priv_meta, hread, bind, EStateM.bind, pure, EStateM.pure,
    MemoryOpResult_drop_meta]

/-- The user RAM region lies above the platform interrupt-controller window. -/
theorem within_clint_userRam {a : BitVec 64} {width : Nat}
    (h : InUserRam a width) : within_clint (.Physaddr a) width s = .ok false s := by
  have hb : plat_clint_base = 33554432#64 := rfl
  have hs : plat_clint_size = 786432#64 := rfl
  have hout : ¬ ((a.toNat : Int) + width ≤ 34340864) := by
    have := h.1
    omega
  simp [within_clint, plat_have_clint, hb, hs, Sail.BitVec.toNatInt, hout,
    RiscvZkvm.Sail.Functions.not, pure, EStateM.pure]

/-- The user RAM region lies above the platform signal window. -/
theorem within_sig_userRam {a : BitVec 64} {width : Nat}
    (h : InUserRam a width) : within_sig (.Physaddr a) width s = .ok false s := by
  have hb : plat_sig_base = 201326592#64 := rfl
  have hs : plat_sig_size = 32#64 := rfl
  have hout : ¬ ((a.toNat : Int) + width ≤ 201326624) := by
    have := h.1
    omega
  simp [within_sig, plat_have_sig, hb, hs, Sail.BitVec.toNatInt, hout,
    RiscvZkvm.Sail.Functions.not, pure, EStateM.pure]

/-- An aligned access remains one physical access of its original width. -/
theorem split_misaligned_of_aligned {a : BitVec 64} {width : Nat}
    (info : Phys_Mem_Access_Info)
    (halign : is_aligned_vaddr (.Virtaddr a) width = true) :
    split_misaligned (.Physaddr a) width info.granule_size_exp info.splittable s =
      .ok (1, (width : Int)) s := by
  have hm : Int.tmod (Sail.BitVec.toNatInt a) width = 0 := by
    simpa only [is_aligned_vaddr, beq_iff_eq] using halign
  simp [split_misaligned, hm, pure, EStateM.pure]

end

/-- A successful virtual doubleword load followed by its register write retires successfully. -/
theorem execute_LOAD64_of_vmem {s t : Mach} (imm : BitVec 12) (rs1 rd : regidx)
    (value : BitVec 64)
    (hread : vmem_read rs1 (sign_extend imm) 8 (.Load .Data) false false false s =
      .ok (.Ok value) s)
    (hwrite : wX_bits rd value s = .ok () t) :
    execute_LOAD imm rs1 rd false 8 s = .ok (.Retire_Success ()) t := by
  have hext : extend_value false value = value := by
    simp [extend_value, sign_extend, Sail.BitVec.signExtend]
  simp [execute_LOAD, RiscvZkvm.Sail.Functions.xlen_bytes, bind, EStateM.bind,
    pure, EStateM.pure, Sail.assert,
    PreSail.assert, hread, hext, hwrite, RETIRE_SUCCESS]

/-- Reading a store source and successfully writing a virtual doubleword retires successfully. -/
theorem execute_STORE64_of_vmem {s t : Mach} (imm : BitVec 12) (rs2 rs1 : regidx)
    (value : BitVec 64)
    (hvalue : rX_bits rs2 s = .ok value s)
    (hwrite : vmem_write rs1 (sign_extend imm) 8 value (.Store .Data)
      false false false s = .ok (.Ok true) t) :
    execute_STORE imm rs2 rs1 8 s = .ok (.Retire_Success ()) t := by
  have hdata := extractLsb_63_zero_eq value
  simp [execute_STORE, RiscvZkvm.Sail.Functions.xlen_bytes, bind, EStateM.bind,
    pure, EStateM.pure, Sail.assert,
    PreSail.assert, hvalue, hdata, hwrite, RETIRE_SUCCESS]

/-- A successful checked write lifts through the physical-memory metadata wrapper. -/
theorem mem_write_value_priv_of_checked {s t : Mach} {width : Nat}
    (value : BitVec (8 * width)) (access : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (priv : Privilege) (a : physaddr)
    (hwrite : checked_mem_write a width value access pbmt priv () false false false s =
      .ok (.Ok true) t) :
    mem_write_value_priv a width value priv access pbmt false false false s = .ok (.Ok true) t := by
  simp [mem_write_value_priv, mem_write_value_priv_meta, default_meta, hwrite, bind,
    EStateM.bind, pure, EStateM.pure]

/-- An eight-byte aligned address has zero low three bits. -/
theorem aligned64_low_bits {a : BitVec 64} (halign : a.toNat % 8 = 0) :
    a.extractLsb' 0 3 = 0#3 := by
  apply BitVec.eq_of_toNat_eq
  simpa [BitVec.extractLsb'_toNat] using halign

/-- An aligned doubleword lies entirely within one virtual page. -/
theorem split_on_page_boundary64_eq (s : Mach) (a : BitVec 64)
    (halign : a.toNat % 8 = 0) :
    split_on_page_boundary a 8 s = .ok (8, 0) s := by
  have hbound : a.toNat + 7 < 2 ^ 64 := by
    have := a.isLt
    omega
  have hres : (a + 7#64).toNat = a.toNat + 7 := by
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt hbound]
  have hquot : (a.toNat + 7) / 4096 = a.toNat / 4096 := by omega
  have hadd : a + 8#64 - 1#64 = a + 7#64 := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hmask (x : BitVec 64) : x &&& 0xfffffffffffff000#64 = (x >>> 12) <<< 12 := by
    exact (BitVec.shiftLeft_ushiftRight (n := 12)).symm
  have hpage : (a &&& 0xfffffffffffff000#64) = ((a + 8#64 - 1#64) &&& 0xfffffffffffff000#64) := by
    rw [hmask, hmask, hadd]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hres, hquot]
  unfold split_on_page_boundary
  split
  · rfl
  · rename_i hcross
    apply False.elim
    apply hcross
    simp only [RiscvZkvm.Sail.Functions.pagesize_bits]
    have hmask' : Sail.BitVec.updateSubrange (ones (n := 64))
      ((((12 : Nat) : Int) - 1).toNat) 0 zeros = 0xfffffffffffff000#64 := by
      decide
    rw [hmask']
    exact beq_iff_eq.mpr hpage

namespace UserConfig

variable {s : Mach} (h : UserConfig s)

include h

/-- A doubleword write preserves the user-mode register profile. -/
theorem write64State (a value : BitVec 64) :
    UserConfig (write64State s a value) := h.of_regs_eq rfl

/-- A configured state has no HTIF tohost base address. -/
theorem htif_tohost_base_eq_none : s.regs.get? Register.htif_tohost_base = some none := by
  obtain ⟨base, hbase, hp⟩ := h.regs .htif_tohost_base
  simpa only [userRegPolicy] using hp ▸ hbase

/-- Configured user RAM reads use the RAM interface rather than MMIO. -/
theorem within_mmio_readable
    {a : BitVec 64} {width : Nat} (hram : InUserRam a width) :
    within_mmio_readable (.Physaddr a) width s = .ok false s := by
  have hnone := h.htif_tohost_base_eq_none
  simp [RiscvZkvm.Sail.Functions.within_mmio_readable, get_config_rvfi, within_clint_userRam hram,
    within_sig_userRam hram, within_htif_readable, within_htif_writable,
    readReg_eq hnone, bind, EStateM.bind, pure, EStateM.pure]

/-- Configured user RAM writes use the RAM interface rather than MMIO. -/
theorem within_mmio_writable
    {a : BitVec 64} {width : Nat} (hram : InUserRam a width) :
    within_mmio_writable (.Physaddr a) width s = .ok false s := by
  have hnone := h.htif_tohost_base_eq_none
  simp [RiscvZkvm.Sail.Functions.within_mmio_writable, get_config_rvfi, within_clint_userRam hram,
    within_sig_userRam hram, within_htif_writable, readReg_eq hnone,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Configured physical reads lift successful checked user-mode reads. -/
theorem mem_read_of_checked {width : Nat}
    {value : BitVec (8 * width)} (access : MemoryAccessType mem_payload) (a : physaddr)
    (hread : checked_mem_read access .PBMT_PMA .User a width false false false false s =
      .ok (.Ok (value, ())) s) :
    mem_read access .PBMT_PMA a width false false false s = .ok (.Ok value) s := by
  obtain ⟨m, hm, _⟩ := h.regs .mstatus
  have heff := (runSail_eq_some_iff _ _ _ _).mp (h.effectivePrivilege_user access hm)
  have hplain := mem_read_priv_of_checked access .PBMT_PMA .User a hread
  simp [mem_read, bind, EStateM.bind, readReg_eq hm, readReg_eq h.privilege, heff, hplain]

/-- Configured physical writes lift successful checked user-mode writes. -/
theorem mem_write_value_of_checked {t : Mach} {width : Nat}
    (value : BitVec (8 * width)) (access : MemoryAccessType mem_payload) (a : physaddr)
    (hwrite : checked_mem_write a width value access .PBMT_PMA .User () false false false s =
      .ok (.Ok true) t) :
    mem_write_value a width value access .PBMT_PMA false false false s = .ok (.Ok true) t := by
  obtain ⟨m, hm, _⟩ := h.regs .mstatus
  have heff := (runSail_eq_some_iff _ _ _ _).mp (h.effectivePrivilege_user access hm)
  have hplain := mem_write_value_priv_of_checked value access .PBMT_PMA .User a hwrite
  simp [mem_write_value, mem_write_value_meta, mem_write_value_priv, default_meta,
    bind, EStateM.bind, readReg_eq hm, readReg_eq h.privilege, heff] at hplain ⊢
  exact hplain

/-- An aligned user RAM load returns the allocated doubleword under PMA and PMP success. -/
theorem mem_read64_of_guards
    {a value : BitVec 64} (access : MemoryAccessType mem_payload) (info : Phys_Mem_Access_Info)
    (hram : InUserRam a 8) (halign : a.toNat % 8 = 0)
    (hcheck : check_pma_with_pmp_priority access .PBMT_PMA .User (.Physaddr a) 8 false s =
      .ok (.Ok info) s)
    (hpmp : pmpCheck (.Physaddr a) 8 access .User s = .ok none s)
    (hword : Word64At s a value) :
    mem_read access .PBMT_PMA (.Physaddr a) 8 false false false s = .ok (.Ok value) s := by
  apply h.mem_read_of_checked
  exact checked_mem_read64_of_guards access .User info hcheck
    (split_misaligned_of_aligned info (is_aligned_vaddr_of_mod_eq_zero halign)) hpmp
    (h.within_mmio_readable hram) hword

/-- An aligned user RAM store performs eight byte writes under PMA and PMP success. -/
theorem mem_write64_of_guards
    (a value : BitVec 64) (access : MemoryAccessType mem_payload) (info : Phys_Mem_Access_Info)
    (hram : InUserRam a 8) (halign : a.toNat % 8 = 0)
    (hcheck : check_pma_with_pmp_priority access .PBMT_PMA .User (.Physaddr a) 8 false s =
      .ok (.Ok info) s)
    (hpmp : pmpCheck (.Physaddr a) 8 access .User s = .ok none s) :
    mem_write_value (.Physaddr a) 8 value access .PBMT_PMA false false false s =
      .ok (.Ok true) (MetrologyAsm.write64State s a value) := by
  apply h.mem_write_value_of_checked
  exact checked_mem_write64_of_guards a value access .User info hcheck
    (split_misaligned_of_aligned info (is_aligned_vaddr_of_mod_eq_zero halign)) hpmp
    (h.within_mmio_writable hram)

/-- An aligned virtual doubleword load uses its successful physical user RAM read. -/
theorem vmem_read_addr64_of_mem
    (a value : BitVec 64) (halign : a.toNat % 8 = 0)
    (hread : mem_read (.Load .Data) .PBMT_PMA (.Physaddr a) 8 false false false s =
      .ok (.Ok value) s) :
    vmem_read_addr (.Virtaddr a) 8 (.Load .Data) false false false s = .ok (.Ok value) s := by
  obtain ⟨m, hm, _⟩ := h.regs .mstatus
  have heff := (runSail_eq_some_iff _ _ _ _).mp (h.effectivePrivilege_user (.Load .Data) hm)
  have hmode := (runSail_eq_some_iff _ _ _ _).mp h.translationMode_user
  have htranslate := (runSail_eq_some_iff _ _ _ _).mp (h.translateAddr_user a (.Load .Data) rfl)
  simp [vmem_read_addr, SailME.run, PreSail.PreSailME.run,
    is_aligned_vaddr_of_mod_eq_zero halign, RiscvZkvm.Sail.Functions.not,
    split_on_page_boundary64_eq s a halign, bits_of_virtaddr, readReg_eq hm,
    readReg_eq h.privilege, heff, hmode, translate_and_read_value, htranslate, hread,
    sys_misaligned_order_decreasing, bind, EStateM.bind, EStateM.map, pure, EStateM.pure,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, monadLift, liftM, Functor.map, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']

/-- An aligned virtual doubleword store uses successful physical user RAM write operations. -/
theorem vmem_write_addr64_of_mem {t : Mach}
    (a value : BitVec 64) (halign : a.toNat % 8 = 0)
    (hea : mem_write_ea (.Physaddr a) 8 (.Store .Data) .PBMT_PMA false false false s =
      .ok (.Ok ()) s)
    (hwrite : mem_write_value (.Physaddr a) 8 value (.Store .Data) .PBMT_PMA
      false false false s = .ok (.Ok true) t) :
    vmem_write_addr (.Virtaddr a) 8 value (.Store .Data) false false false s =
      .ok (.Ok true) t := by
  obtain ⟨m, hm, _⟩ := h.regs .mstatus
  have heff := (runSail_eq_some_iff _ _ _ _).mp (h.effectivePrivilege_user (.Store .Data) hm)
  have hmode := (runSail_eq_some_iff _ _ _ _).mp h.translationMode_user
  have htranslate := (runSail_eq_some_iff _ _ _ _).mp (h.translateAddr_user a (.Store .Data) rfl)
  have hdata := extractLsb_63_zero_eq value
  simp [vmem_write_addr, SailME.run, PreSail.PreSailME.run,
    is_aligned_vaddr_of_mod_eq_zero halign, RiscvZkvm.Sail.Functions.not,
    split_on_page_boundary64_eq s a halign, bits_of_virtaddr, readReg_eq hm,
    readReg_eq h.privilege, heff, hmode, htranslate, hea, hwrite, hdata,
    is_store_conditional, sys_misaligned_order_decreasing, bind, EStateM.bind, EStateM.map,
    pure, EStateM.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.lift, ExceptT.pure, MonadLift.monadLift, monadLift, liftM, Functor.map,
    Sail.assert, PreSail.assert]

/-- User-mode store address checks succeed under aligned PMA and PMP success. -/
theorem mem_write_ea64_of_guards
    (a : BitVec 64) (info : Phys_Mem_Access_Info) (halign : a.toNat % 8 = 0)
    (hcheck : check_pma_with_pmp_priority (.Store .Data) .PBMT_PMA .User
      (.Physaddr a) 8 false s = .ok (.Ok info) s)
    (hpmp : pmpCheck (.Physaddr a) 8 (.Store .Data) .User s = .ok none s) :
    mem_write_ea (.Physaddr a) 8 (.Store .Data) .PBMT_PMA false false false s = .ok (.Ok ()) s := by
  obtain ⟨m, hm, _⟩ := h.regs .mstatus
  have heff := (runSail_eq_some_iff _ _ _ _).mp (h.effectivePrivilege_user (.Store .Data) hm)
  have hsplit := split_misaligned_of_aligned (s := s) info (is_aligned_vaddr_of_mod_eq_zero halign)
  simp [mem_write_ea, SailME.run, PreSail.PreSailME.run, readReg_eq hm,
    readReg_eq h.privilege, heff, hcheck, hsplit, write_kind_of_flags, misaligned_order,
    sys_misaligned_order_decreasing, untilFuelM, untilFuelM.go, bind, EStateM.bind,
    EStateM.map, pure, EStateM.pure, ExceptT.run, ExceptT.mk, ExceptT.bind,
    ExceptT.bindCont, ExceptT.lift, ExceptT.pure, MonadLift.monadLift, monadLift,
    liftM, Functor.map, Sail.assert, PreSail.assert, bits_of_physaddr, Sail.BitVec.addInt, hpmp]

/-- A configured virtual load uses the pointer register and its physical RAM read. -/
theorem vmem_read64_of_mem (rs : regidx)
    (base offset value : BitVec 64) (halign : (base + offset).toNat % 8 = 0)
    (hbase : rX_bits rs s = .ok base s)
    (hread : mem_read (.Load .Data) .PBMT_PMA (.Physaddr (base + offset))
      8 false false false s = .ok (.Ok value) s) :
    vmem_read rs offset 8 (.Load .Data) false false false s = .ok (.Ok value) s := by
  have htransform := (runSail_eq_some_iff _ _ _ _).mp
    (h.transform_effective_address_user (.Virtaddr (base + offset)) (.Load .Data))
  have haddr := h.vmem_read_addr64_of_mem (base + offset) value halign hread
  simp [vmem_read, get_transformed_data_addr, ext_data_get_addr, hbase, htransform,
    haddr, SailME.run, PreSail.PreSailME.run, bind, EStateM.bind, EStateM.map,
    pure, EStateM.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.lift, ExceptT.pure, MonadLift.monadLift, monadLift, liftM, Functor.map]

/-- A configured virtual store uses the pointer register and its physical RAM operations. -/
theorem vmem_write64_of_mem {t : Mach} (rs : regidx)
    (base offset value : BitVec 64) (halign : (base + offset).toNat % 8 = 0)
    (hbase : rX_bits rs s = .ok base s)
    (hea : mem_write_ea (.Physaddr (base + offset)) 8 (.Store .Data) .PBMT_PMA
      false false false s = .ok (.Ok ()) s)
    (hwrite : mem_write_value (.Physaddr (base + offset)) 8 value (.Store .Data) .PBMT_PMA
      false false false s = .ok (.Ok true) t) :
    vmem_write rs offset 8 value (.Store .Data) false false false s = .ok (.Ok true) t := by
  have htransform := (runSail_eq_some_iff _ _ _ _).mp
    (h.transform_effective_address_user (.Virtaddr (base + offset)) (.Store .Data))
  have haddr := h.vmem_write_addr64_of_mem (base + offset) value halign hea hwrite
  simp [vmem_write, get_transformed_data_addr, ext_data_get_addr, hbase, htransform,
    haddr, SailME.run, PreSail.PreSailME.run, bind, EStateM.bind, EStateM.map,
    pure, EStateM.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.lift, ExceptT.pure, MonadLift.monadLift, monadLift, liftM, Functor.map]

/-- A generated doubleword load retires using its pointer register, RAM read, and register write. -/
theorem execute_LOAD64_of_mem {t : Mach}
    (imm : BitVec 12) (rs1 rd : regidx) (base value : BitVec 64)
    (halign : (base + sign_extend imm).toNat % 8 = 0)
    (hbase : rX_bits rs1 s = .ok base s)
    (hread : mem_read (.Load .Data) .PBMT_PMA
      (.Physaddr (base + sign_extend imm)) 8 false false false s = .ok (.Ok value) s)
    (hwrite : wX_bits rd value s = .ok () t) :
    execute_LOAD imm rs1 rd false 8 s = .ok (.Retire_Success ()) t := by
  exact execute_LOAD64_of_vmem imm rs1 rd value
    (h.vmem_read64_of_mem rs1 base _ value halign hbase hread) hwrite

/-- A generated doubleword store retires using its registers and physical RAM operations. -/
theorem execute_STORE64_of_mem {t : Mach}
    (imm : BitVec 12) (rs2 rs1 : regidx) (base value : BitVec 64)
    (halign : (base + sign_extend imm).toNat % 8 = 0)
    (hbase : rX_bits rs1 s = .ok base s) (hvalue : rX_bits rs2 s = .ok value s)
    (hea : mem_write_ea (.Physaddr (base + sign_extend imm)) 8 (.Store .Data)
      .PBMT_PMA false false false s = .ok (.Ok ()) s)
    (hwrite : mem_write_value (.Physaddr (base + sign_extend imm)) 8 value
      (.Store .Data) .PBMT_PMA false false false s = .ok (.Ok true) t) :
    execute_STORE imm rs2 rs1 8 s = .ok (.Retire_Success ()) t := by
  exact execute_STORE64_of_vmem imm rs2 rs1 value hvalue
    (h.vmem_write64_of_mem rs1 base _ value halign hbase hea hwrite)

/-- Configured aligned RAM fetches read any allocated instruction word unchanged. -/
theorem mem_read32_fetch
    {a : BitVec 64} {value : BitVec 32} (hram : InUserRam a 4)
    (halign : a.toNat % 4 = 0) (hword : Word32At s a value) :
    mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr a) 4 false false false s =
      .ok (.Ok value) s := by
  have ha := is_aligned_vaddr_of_mod_eq_zero halign
  have hcheck := h.check_pma_fetch hram ha
  have hpmp := (runSail_eq_some_iff _ _ _ _).mp
    (h.pmpCheck_user hram (by decide) (.InstructionFetch ()) (Or.inl rfl))
  apply h.mem_read_of_checked
  exact checked_mem_read32_of_guards (.InstructionFetch ()) .User _ hcheck
    (split_misaligned_of_aligned _ ha) hpmp (h.within_mmio_readable hram) hword

/-- Configured aligned RAM loads read any allocated doubleword unchanged. -/
theorem mem_read64 {a value : BitVec 64}
    (hram : InUserRam a 8) (halign : a.toNat % 8 = 0) (hword : Word64At s a value) :
    mem_read (.Load .Data) .PBMT_PMA (.Physaddr a) 8 false false false s = .ok (.Ok value) s := by
  have ha := is_aligned_vaddr_of_mod_eq_zero halign
  have hpmp := (runSail_eq_some_iff _ _ _ _).mp
    (h.pmpCheck_user hram (by decide) (.Load .Data) (Or.inr (Or.inl rfl)))
  exact h.mem_read64_of_guards (.Load .Data) _ hram halign (h.check_pma_load hram ha) hpmp hword

/-- Configured aligned RAM stores overwrite exactly eight doubleword bytes. -/
theorem mem_write64 (a value : BitVec 64)
    (hram : InUserRam a 8) (halign : a.toNat % 8 = 0) :
    mem_write_value (.Physaddr a) 8 value (.Store .Data) .PBMT_PMA false false false s =
      .ok (.Ok true) (MetrologyAsm.write64State s a value) := by
  have ha := is_aligned_vaddr_of_mod_eq_zero halign
  have hpmp := (runSail_eq_some_iff _ _ _ _).mp
    (h.pmpCheck_user hram (by decide) (.Store .Data) (Or.inr (Or.inr rfl)))
  exact h.mem_write64_of_guards a value (.Store .Data) _ hram halign
    (h.check_pma_store hram ha) hpmp

/-- Configured aligned RAM stores pass their address-only physical check. -/
theorem mem_write_ea64 (a : BitVec 64)
    (hram : InUserRam a 8) (halign : a.toNat % 8 = 0) :
    mem_write_ea (.Physaddr a) 8 (.Store .Data) .PBMT_PMA false false false s = .ok (.Ok ()) s := by
  have ha := is_aligned_vaddr_of_mod_eq_zero halign
  have hpmp := (runSail_eq_some_iff _ _ _ _).mp
    (h.pmpCheck_user hram (by decide) (.Store .Data) (Or.inr (Or.inr rfl)))
  exact h.mem_write_ea64_of_guards a _ halign (h.check_pma_store hram ha) hpmp

/-- A configured doubleword load retires with its exact destination-register write. -/
theorem execute_LOAD64 {t : Mach}
    (imm : BitVec 12) (rs1 rd : regidx) (base value : BitVec 64)
    (hram : InUserRam (base + sign_extend imm) 8)
    (halign : (base + sign_extend imm).toNat % 8 = 0)
    (hbase : rX_bits rs1 s = .ok base s)
    (hword : Word64At s (base + sign_extend imm) value)
    (hwrite : wX_bits rd value s = .ok () t) :
    execute_LOAD imm rs1 rd false 8 s = .ok (.Retire_Success ()) t := by
  exact h.execute_LOAD64_of_mem imm rs1 rd base value halign hbase
    (h.mem_read64 hram halign hword) hwrite

/-- A configured doubleword store retires after updating exactly its eight RAM bytes. -/
theorem execute_STORE64
    (imm : BitVec 12) (rs2 rs1 : regidx) (base value : BitVec 64)
    (hram : InUserRam (base + sign_extend imm) 8)
    (halign : (base + sign_extend imm).toNat % 8 = 0)
    (hbase : rX_bits rs1 s = .ok base s) (hvalue : rX_bits rs2 s = .ok value s) :
    execute_STORE imm rs2 rs1 8 s = .ok (.Retire_Success ())
      (MetrologyAsm.write64State s (base + sign_extend imm) value) := by
  exact h.execute_STORE64_of_mem imm rs2 rs1 base value halign hbase hvalue
    (h.mem_write_ea64 _ hram halign) (h.mem_write64 _ value hram halign)

end UserConfig

end MetrologyAsm
