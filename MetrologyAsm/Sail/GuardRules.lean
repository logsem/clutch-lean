import MetrologyAsm.Profile.Config

/-! # Physical memory guards for configured user execution -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions Sail
open Sail.BitVec (toNatInt extractLsb access zeroExtend)

variable {a : BitVec 64} {width : Nat}

/-- The three access kinds that ordinary user code performs on RAM. -/
abbrev OrdinaryAccess (access : MemoryAccessType mem_payload) : Prop :=
  access = .InstructionFetch () ∨ access = .Load .Data ∨ access = .Store .Data

section AddressGuards

/-- Natural alignment is exactly the alignment predicate used by generated Sail. -/
theorem is_aligned_vaddr_of_mod_eq_zero
    (h : a.toNat % width = 0) : is_aligned_vaddr (.Virtaddr a) width = true := by
  simp [is_aligned_vaddr, toNatInt, ← Int.ofNat_tmod, h]

/-- A single byte is always naturally aligned. -/
theorem is_aligned_vaddr_one (x : BitVec 64) : is_aligned_vaddr (.Virtaddr x) 1 = true :=
  is_aligned_vaddr_of_mod_eq_zero (Nat.mod_one _)

section InRam

variable (h : InUserRam a width)

include h

/-- The 64-bit encoding of the width of a user-RAM access is the width itself. -/
theorem to_bits_toNat_of_inUserRam :
    (to_bits (l := 64) width).toNat = width := by
  have hw : width < 2 ^ 64 := by rcases h with ⟨hl, hu⟩; omega
  simp [to_bits, get_slice_int, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]

/-- The configured RAM interval contains every nonwrapping access described by `InUserRam`. -/
theorem range_subset_userRam :
    range_subset a (to_bits width) 0x80000000#64 0x80000000#64 = true := by
  have hw' := to_bits_toNat_of_inUserRam h
  simp [range_subset, zopz0zIzJ_u, toNatInt,
    BitVec.toNat_sub, BitVec.toNat_add, hw']
  rcases h with ⟨hl, hu⟩
  omega

/-- The first configured PMA region is selected for an access within user RAM. -/
theorem matching_pma_region_userRam (rest : List PMA_Region) :
    matching_pma_region (userRamRegion :: rest) (.Physaddr a) width = some userRamRegion := by
  simp [matching_pma_region, matching_pma_region_bits_range, bits_of_physaddr,
    zero_extend, zeroExtend, userRamRegion, range_subset_userRam h]

/-- The first configured TOR entry completely matches every nonempty user-RAM access. -/
theorem pmpMatchAddr_userRam
    (hwidth : 0 < width) (s : Mach) :
    pmpMatchAddr (.Physaddr a) (to_bits width) 0x0f#8 0x40000000#64 0#64 s = .ok .PMP_Match s := by
  have hw' := to_bits_toNat_of_inUserRam h
  rcases h with ⟨hl, hu⟩
  have hzero : ¬ (a.toNat : Int) + width ≤ 0 := by omega
  have hbelow : ¬ 4294967296 ≤ a.toNat := by omega
  have hupper : (a.toNat : Int) + width ≤ 4294967296 := by omega
  simp [pmpMatchAddr, _get_Pmpcfg_ent_A, extractLsb,
    pmpAddrMatchType_encdec_backwards, zopz0zKzJ_u, pmpRangeMatch, toNatInt,
    hw', hzero, hbelow, hupper, pure, EStateM.pure]

end InRam

end AddressGuards

namespace UserConfig

variable {s : Mach} (h : UserConfig s)

include h

/-- Reading the first configured PMP address preserves the machine state. -/
theorem pmpReadAddrReg_zero :
    pmpReadAddrReg 0 s = .ok 0x40000000#64 s := by
  obtain ⟨cfg, hcfg, hcfgp⟩ := h.regs .pmpcfg_n
  obtain ⟨addr, haddr, haddrp⟩ := h.regs .pmpaddr_n
  simp only [userRegPolicy] at hcfgp haddrp
  simp [pmpReadAddrReg, readReg_eq hcfg, readReg_eq haddr, hcfgp, haddrp,
    sys_pmp_grain, _get_Pmpcfg_ent_A, extractLsb, access,
    bind, EStateM.bind, pure, EStateM.pure]

section AccessGuards

variable (hram : InUserRam a width)

include hram

section Pmp

variable (hwidth : 0 < width)

include hwidth

/-- The first PMP TOR entry permits every nonempty ordinary user-RAM access. -/
theorem pmpCheck_user
    (access : MemoryAccessType mem_payload)
    (haccess : OrdinaryAccess access) :
    runSail (pmpCheck (.Physaddr a) width access .User) s = some (none, s) := by
  obtain ⟨cfg, hcfg, hp⟩ := h.regs .pmpcfg_n
  simp only [userRegPolicy] at hp
  have hmem : (0 : Int) ∈ ({ stop := 15, step_pos := by decide } : IntRange) := by decide
  have hp' : cfg[(0 : Int)] = 0x0f#8 := by
    change cfg[(0 : Int).toNat] = 0x0f#8
    exact hp
  have haddr := h.pmpReadAddrReg_zero
  have hmatch := pmpMatchAddr_userRam hram hwidth s
  have hrwx : pmpCheckRWX 0x0f#8 access s = .ok true s := by
    rcases haccess with rfl | rfl | rfl <;> rfl
  simp [runSail, pmpCheck, sys_pmp_count,
    SailME.run, PreSail.PreSailME.run, SailME.throw, PreSail.PreSailME.throw,
    bind, EStateM.bind, pure, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, monadLift, liftM, Functor.map, forIn, forIn',
    IntRange.forIn']
  rw [IntRange.forIn'.loop]
  simp [hmem, readReg_eq hcfg, hp', haddr, hmatch, hrwx, zeros,
    bind, EStateM.bind, EStateM.map, pure, EStateM.pure, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure]
  rfl

/-- The configured PMP entry permits instruction fetches within user RAM. -/
theorem pmp_fetch :
    pmpCheck (.Physaddr a) width (.InstructionFetch ()) .User s = .ok none s :=
  (runSail_eq_some_iff _ _ _ _).mp (h.pmpCheck_user hram hwidth _ (Or.inl rfl))

/-- The configured PMP entry permits data loads within user RAM. -/
theorem pmp_load :
    pmpCheck (.Physaddr a) width (.Load .Data) .User s = .ok none s :=
  (runSail_eq_some_iff _ _ _ _).mp (h.pmpCheck_user hram hwidth _ (Or.inr (Or.inl rfl)))

/-- The configured PMP entry permits data stores within user RAM. -/
theorem pmp_store :
    pmpCheck (.Physaddr a) width (.Store .Data) .User s = .ok none s :=
  (runSail_eq_some_iff _ _ _ _).mp (h.pmpCheck_user hram hwidth _ (Or.inr (Or.inr rfl)))

end Pmp

section Aligned

variable (halign : is_aligned_vaddr (.Virtaddr a) width = true)

include halign

/-- Configured, aligned ordinary accesses pass the generated PMA check without state changes. -/
theorem pmaCheck_user
    (access : MemoryAccessType mem_payload)
    (haccess : OrdinaryAccess access) :
    runSail (pmaCheck (.Physaddr a) width access .PBMT_PMA false) s =
      some (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }, s) := by
  obtain ⟨regions, hregions, hp⟩ := h.regs .pma_regions
  simp only [userRegPolicy] at hp
  obtain ⟨rest, rfl⟩ := hp
  have hmatch := matching_pma_region_userRam hram rest
  simp only [userRamRegion] at hmatch
  have halign' : is_aligned_paddr (.Physaddr a) width = true := halign
  rcases haccess with rfl | rfl | rfl
  all_goals simp [runSail, pmaCheck, readReg_eq hregions, hmatch, override_PMA, userRamRegion,
    RiscvZkvm.Sail.Functions.not, mag_pma_check, is_mag_applicable_access, halign', assert,
    PreSail.assert, SailME.run, PreSail.PreSailME.run, bind, EStateM.bind, EStateM.map, pure,
    EStateM.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
    ExceptT.pure, MonadLift.monadLift, monadLift, liftM, Functor.map]

/-- PMA-priority checks preserve configured state and accept aligned ordinary user accesses. -/
theorem check_pma_with_pmp_priority_user
    (access : MemoryAccessType mem_payload)
    (haccess : OrdinaryAccess access) :
    runSail (check_pma_with_pmp_priority access .PBMT_PMA .User (.Physaddr a) width false) s =
      some (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }, s) := by
  have hpma := (runSail_eq_some_iff _ _ _ _).mp (h.pmaCheck_user hram halign access haccess)
  simp [runSail, check_pma_with_pmp_priority, hpma, bind, EStateM.bind, pure, EStateM.pure]

/-- Aligned instruction fetches pass the PMA-priority check. -/
theorem check_pma_fetch :
    check_pma_with_pmp_priority (.InstructionFetch ()) .PBMT_PMA .User (.Physaddr a) width false s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s :=
  (runSail_eq_some_iff _ _ _ _).mp (h.check_pma_with_pmp_priority_user hram halign _ (Or.inl rfl))

/-- Aligned data loads pass the PMA-priority check. -/
theorem check_pma_load :
    check_pma_with_pmp_priority (.Load .Data) .PBMT_PMA .User (.Physaddr a) width false s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s :=
  (runSail_eq_some_iff _ _ _ _).mp
    (h.check_pma_with_pmp_priority_user hram halign _ (Or.inr (Or.inl rfl)))

/-- Aligned data stores pass the PMA-priority check. -/
theorem check_pma_store :
    check_pma_with_pmp_priority (.Store .Data) .PBMT_PMA .User (.Physaddr a) width false s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s :=
  (runSail_eq_some_iff _ _ _ _).mp
    (h.check_pma_with_pmp_priority_user hram halign _ (Or.inr (Or.inr rfl)))

end Aligned

end AccessGuards

end UserConfig

end MetrologyAsm
