import MetrologyAsm.Examples.Swap.Steps
import MetrologyAsm.Examples.Swap.Layout

/-! # Symbolic execution of the exchange fragment -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail

/-- The machine after the first exchange load. -/
def swapState1 (s : Mach) (base x : BitVec 64) : Mach :=
  commitState (loadA2BodyState s base x) (BitVec.addInt base 4)

/-- The machine after the second exchange load. -/
def swapState2 (s : Mach) (base x y : BitVec 64) : Mach :=
  commitState (loadA3BodyState (swapState1 s base x) (BitVec.addInt base 4) y)
    (BitVec.addInt base 8)

/-- The machine after writing the second word into the first location. -/
def swapState3 (s : Mach) (base a x y : BitVec 64) : Mach :=
  commitState (storeBodyState (swapState2 s base x y) (BitVec.addInt base 8) a y)
    (BitVec.addInt base 12)

/-- The machine after writing the first word into the second location. -/
def swapState4 (s : Mach) (base a b x y : BitVec 64) : Mach :=
  commitState (storeBodyState (swapState3 s base a x y) (BitVec.addInt base 12) b x)
    (BitVec.addInt base 16)

/-- The exact terminal machine of the five-instruction exchange fragment. -/
def swapFinalState (s : Mach) (base a b x y ra : BitVec 64) : Mach :=
  commitState (retBodyState (swapState4 s base a b x y) (BitVec.addInt base 16) ra) ra

/-- The five little-endian instruction words occupy the exchange code image. -/
structure SwapImage (s : Mach) (base : BitVec 64) : Prop where
  /-- Load through a0 into a2. -/
  loadA2 : Word32At s base 0x00053603#32
  /-- Load through a1 into a3. -/
  loadA3 : Word32At s (BitVec.addInt base 4) 0x0005b683#32
  /-- Store a3 through a0. -/
  storeA3 : Word32At s (BitVec.addInt base 8) 0x00d53023#32
  /-- Store a2 through a1. -/
  storeA2 : Word32At s (BitVec.addInt base 12) 0x00c5b023#32
  /-- Return through ra. -/
  ret : Word32At s (BitVec.addInt base 16) 0x00008067#32

/-- The five instruction-entry addresses of the exchange fragment. -/
def swapPCs (base : BitVec 64) : List (BitVec 64) :=
  [base, BitVec.addInt base 4, BitVec.addInt base 8,
    BitVec.addInt base 12, BitVec.addInt base 16]

/-- Placement conditions under which one exchange call runs safely. -/
structure SwapPlacement (base a b ra : BitVec 64) : Prop where
  /-- Each instruction word is entirely within user RAM. -/
  codeRam : ∀ p ∈ swapPCs base, InUserRam p 4
  /-- Each instruction entry is aligned to four bytes. -/
  codeAlign : ∀ p ∈ swapPCs base, p.toNat % 4 = 0
  /-- The first data word is entirely within user RAM. -/
  ramA : InUserRam a 8
  /-- The second data word is entirely within user RAM. -/
  ramB : InUserRam b 8
  /-- The first data word is aligned to eight bytes. -/
  alignA : a.toNat % 8 = 0
  /-- The second data word is aligned to eight bytes. -/
  alignB : b.toNat % 8 = 0
  /-- The return target satisfies the generated model's instruction alignment. -/
  alignRA : ra.toNat % 4 = 0
  /-- The two logical data cells occupy disjoint byte intervals. -/
  dataDisjoint : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat
  /-- A write through the first pointer preserves every instruction word. -/
  codeDisjointA : ∀ p ∈ swapPCs base, a.toNat + 8 ≤ p.toNat ∨ p.toNat + 4 ≤ a.toNat
  /-- A write through the second pointer preserves every instruction word. -/
  codeDisjointB : ∀ p ∈ swapPCs base, b.toNat + 8 ≤ p.toNat ∨ p.toNat + 4 ≤ b.toNat

/-- The exchange addresses are precisely instruction indices below five. -/
theorem mem_swapPCs_iff (base p : BitVec 64) :
    p ∈ swapPCs base ↔ ∃ i < 5, p = pcAt base i := by
  constructor
  · intro hp
    simp only [swapPCs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, (pcAt_zero _).symm⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨3, by decide, rfl⟩
    · exact ⟨4, by decide, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp [swapPCs, pcAt, BitVec.addInt]

/-- Contiguous text placement and cell separation imply the per-instruction execution layout. -/
theorem SwapPlacement.of_bounds {base a b ra : BitVec 64}
    (hcode : InUserRam base 20) (hcodeAlign : base.toNat % 4 = 0)
    (ha : InUserRam a 8) (hb : InUserRam b 8)
    (haAlign : a.toNat % 8 = 0) (hbAlign : b.toNat % 8 = 0) (hraAlign : ra.toNat % 4 = 0)
    (hab : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat)
    (hca : a.toNat + 8 ≤ base.toNat ∨ base.toNat + 20 ≤ a.toNat)
    (hcb : b.toNat + 8 ≤ base.toNat ∨ base.toNat + 20 ≤ b.toNat) :
    SwapPlacement base a b ra := by
  refine ⟨?_, ?_, ha, hb, haAlign, hbAlign, hraAlign, hab, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := (mem_swapPCs_iff base p).mp hp
    exact pcAt_inUserRam hcode hi
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := (mem_swapPCs_iff base p).mp hp
    exact pcAt_aligned hcode hcodeAlign hi
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := (mem_swapPCs_iff base p).mp hp
    rw [pcAt_toNat hcode hi]
    rcases hca with hca | hca <;> omega
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := (mem_swapPCs_iff base p).mp hp
    rw [pcAt_toNat hcode hi]
    rcases hcb with hcb | hcb <;> omega

/-- The first load preserves the configured user profile. -/
theorem UserConfig.swapState1 {s : Mach} (h : UserConfig s) (base x : BitVec 64) :
    UserConfig (MetrologyAsm.swapState1 s base x) :=
  ((h.counterState.sequentialState base).insert .x12 x trivial).insert .PC _ trivial

/-- The second load preserves the configured user profile. -/
theorem UserConfig.swapState2 {s : Mach} (h : UserConfig s) (base x y : BitVec 64) :
    UserConfig (MetrologyAsm.swapState2 s base x y) :=
  (((h.swapState1 base x).counterState.sequentialState _).insert .x13 y trivial).insert
    .PC _ trivial

/-- The first store preserves the configured user profile. -/
theorem UserConfig.swapState3 {s : Mach} (h : UserConfig s) (base a x y : BitVec 64) :
    UserConfig (MetrologyAsm.swapState3 s base a x y) :=
  (((h.swapState2 base x y).counterState.sequentialState _).write64State a y).insert .PC _ trivial

/-- The second store preserves the configured user profile. -/
theorem UserConfig.swapState4 {s : Mach} (h : UserConfig s) (base a b x y : BitVec 64) :
    UserConfig (MetrologyAsm.swapState4 s base a b x y) :=
  (((h.swapState3 base a x y).counterState.sequentialState _).write64State b x).insert .PC _ trivial

/-- The terminal machine remains in the configured user profile. -/
theorem UserConfig.swapFinalState {s : Mach} (h : UserConfig s)
    (base a b x y ra : BitVec 64) : UserConfig (MetrologyAsm.swapFinalState s base a b x y ra) :=
  ((((h.swapState4 base a b x y).counterState.sequentialState _).insert .nextPC ra trivial).insert
    .PC ra trivial)

/-- The exchange has exactly its two eight-byte memory writes. -/
theorem swapFinalState_mem (s : Mach) (base a b x y ra : BitVec 64) :
    (swapFinalState s base a b x y ra).mem = (write64State (write64State s a y) b x).mem := by
  rfl

/-- The return commits ra as the terminal program counter. -/
theorem swapFinalState_pc (s : Mach) (base a b x y ra : BitVec 64) :
    (swapFinalState s base a b x y ra).regs.get? Register.PC = some ra := by
  simp [swapFinalState, commitState]

/-- The exchange preserves all registers except its two scratch registers and step bookkeeping. -/
theorem swapFinalState_reg_other (s : Mach) (base a b x y ra : BitVec 64) (r : Register)
    (h : r ∉ [Register.PC, .nextPC, .minstret_increment, .x12, .x13]) :
    (swapFinalState s base a b x y ra).regs.get? r = s.regs.get? r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨hpc, hn, hf, h12, h13⟩ := h
  simp [swapFinalState, swapState4, swapState3, swapState2, swapState1, commitState,
    retBodyState, loadA2BodyState, loadA3BodyState, storeBodyState, write64State,
    sequentialState, counterState, Std.ExtDHashMap.get?_insert,
    Ne.symm hpc, Ne.symm hn, Ne.symm hf, Ne.symm h12, Ne.symm h13]

/-- The terminal machine contains the two exchanged data words. -/
theorem swapFinalState_words (s : Mach) (base a b x y ra : BitVec 64)
    (hdisjoint : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    Word64At (swapFinalState s base a b x y ra) a y ∧
      Word64At (swapFinalState s base a b x y ra) b x := by
  have hfirst := (word64At_write64State s a y).write64State x hdisjoint.symm
  have hsecond := word64At_write64State (write64State s a y) b x
  exact ⟨hfirst.of_mem_eq (swapFinalState_mem _ _ _ _ _ _ _),
    hsecond.of_mem_eq (swapFinalState_mem _ _ _ _ _ _ _)⟩

/-- Every byte outside both logical data cells is preserved by the exchange. -/
theorem swapFinalState_mem_outside (s : Mach) (base a b x y ra : BitVec 64) (k : Nat)
    (ha : k < a.toNat ∨ a.toNat + 8 ≤ k) (hb : k < b.toNat ∨ b.toNat + 8 ≤ k) :
    (swapFinalState s base a b x y ra).mem.get? k = s.mem.get? k := by
  rw [swapFinalState_mem, write64State_get?_outside _ _ _ _ hb,
    write64State_get?_outside _ _ _ _ ha]

/-- The five actual Sail steps exchange two arbitrary disjoint words and return through ra. -/
theorem swap_runsTo {s : Mach} (h : UserConfig s) (base a b x y ra : BitVec 64)
    (layout : SwapPlacement base a b ra) (image : SwapImage s base)
    (hpc : s.regs.get? Register.PC = some base)
    (ha0 : s.regs.get? Register.x10 = some a) (ha1 : s.regs.get? Register.x11 = some b)
    (hra : s.regs.get? Register.x1 = some ra)
    (hdataA : Word64At s a x) (hdataB : Word64At s b y)
    (code : BitVec 64 → Prop) (hcode : ∀ p ∈ swapPCs base, code p) (hout : ¬code ra) :
    RunsTo code (fun t => t = swapFinalState s base a b x y ra) s := by
  have hm0 : base ∈ swapPCs base := by simp [swapPCs]
  have hm4 : BitVec.addInt base 4 ∈ swapPCs base := by simp [swapPCs]
  have hm8 : BitVec.addInt base 8 ∈ swapPCs base := by simp [swapPCs]
  have hm12 : BitVec.addInt base 12 ∈ swapPCs base := by simp [swapPCs]
  have hm16 : BitVec.addInt base 16 ∈ swapPCs base := by simp [swapPCs]
  have hpc1 : (swapState1 s base x).regs.get? Register.PC = some (BitVec.addInt base 4) := by
    simp [swapState1, commitState]
  have hpc2 : (swapState2 s base x y).regs.get? Register.PC = some (BitVec.addInt base 8) := by
    simp [swapState2, commitState]
  have hpc3 : (swapState3 s base a x y).regs.get? Register.PC = some (BitVec.addInt base 12) := by
    simp [swapState3, commitState]
  have hpc4 : (swapState4 s base a b x y).regs.get? Register.PC = some (BitVec.addInt base 16) := by
    simp [swapState4, commitState]
  have hstep1 : rvStep s = some (swapState1 s base x) := by
    exact rvStep_ld_a2 h base a x hpc ha0 (layout.codeRam _ hm0)
      (layout.codeAlign _ hm0) layout.ramA layout.alignA image.loadA2 hdataA
  have ha1' : (swapState1 s base x).regs.get? Register.x11 = some b := by
    simp [swapState1, commitState, loadA2BodyState, sequentialState, counterState,
      Std.ExtDHashMap.get?_insert, ha1]
  have hstep2 : rvStep (swapState1 s base x) = some (swapState2 s base x y) := by
    have hw : Word32At (swapState1 s base x) (BitVec.addInt base 4) 0x0005b683#32 :=
      image.loadA3.of_mem_eq rfl
    have hd : Word64At (swapState1 s base x) b y := hdataB.of_mem_eq rfl
    simpa [swapState2, BitVec.addInt, BitVec.add_assoc] using
      rvStep_ld_a3 (h.swapState1 base x) (BitVec.addInt base 4) b y hpc1 ha1'
        (layout.codeRam _ hm4) (layout.codeAlign _ hm4) layout.ramB layout.alignB hw hd
  have ha0' : (swapState2 s base x y).regs.get? Register.x10 = some a := by
    simp [swapState2, swapState1, commitState, loadA2BodyState, loadA3BodyState,
      sequentialState, counterState, Std.ExtDHashMap.get?_insert, ha0]
  have hy : (swapState2 s base x y).regs.get? Register.x13 = some y := by
    simp [swapState2, commitState, loadA3BodyState, Std.ExtDHashMap.get?_insert]
  have hstep3 : rvStep (swapState2 s base x y) = some (swapState3 s base a x y) := by
    have hw : Word32At (swapState2 s base x y) (BitVec.addInt base 8) 0x00d53023#32 :=
      image.storeA3.of_mem_eq rfl
    simpa [swapState3, BitVec.addInt, BitVec.add_assoc] using
      rvStep_sd_a3 (h.swapState2 base x y) (BitVec.addInt base 8) a y hpc2 ha0' hy
        (layout.codeRam _ hm8) (layout.codeAlign _ hm8) layout.ramA layout.alignA hw
  have ha1'' : (swapState3 s base a x y).regs.get? Register.x11 = some b := by
    simp [swapState3, swapState2, swapState1, commitState, storeBodyState,
      loadA2BodyState, loadA3BodyState, sequentialState, counterState,
      Std.ExtDHashMap.get?_insert, ha1]
  have hx : (swapState3 s base a x y).regs.get? Register.x12 = some x := by
    simp [swapState3, swapState2, swapState1, commitState, storeBodyState,
      loadA2BodyState, loadA3BodyState, sequentialState, counterState,
      Std.ExtDHashMap.get?_insert]
  have hstep4 : rvStep (swapState3 s base a x y) = some (swapState4 s base a b x y) := by
    have hw : Word32At (swapState3 s base a x y) (BitVec.addInt base 12) 0x00c5b023#32 :=
      (image.storeA2.write64State y (layout.codeDisjointA _ hm12)).of_mem_eq rfl
    simpa [swapState4, BitVec.addInt, BitVec.add_assoc] using
      rvStep_sd_a2 (h.swapState3 base a x y) (BitVec.addInt base 12) b x hpc3 ha1'' hx
        (layout.codeRam _ hm12) (layout.codeAlign _ hm12) layout.ramB layout.alignB hw
  have hra' : (swapState4 s base a b x y).regs.get? Register.x1 = some ra := by
    simp [swapState4, swapState3, swapState2, swapState1, commitState, storeBodyState,
      loadA2BodyState, loadA3BodyState, sequentialState, counterState,
      Std.ExtDHashMap.get?_insert, hra]
  have hstep5 : rvStep (swapState4 s base a b x y) = some (swapFinalState s base a b x y ra) := by
    have hw : Word32At (swapState4 s base a b x y) (BitVec.addInt base 16) 0x00008067#32 :=
      ((image.ret.write64State y (layout.codeDisjointA _ hm16)).write64State x
        (layout.codeDisjointB _ hm16)).of_mem_eq rfl
    exact rvStep_ret (h.swapState4 base a b x y) (BitVec.addInt base 16) ra hpc4 hra'
      (layout.codeRam _ hm16) (layout.codeAlign _ hm16) layout.alignRA hw
  refine .step hpc (hcode _ hm0) hstep1 ?_
  refine .step hpc1 (hcode _ hm4) hstep2 ?_
  refine .step hpc2 (hcode _ hm8) hstep3 ?_
  refine .step hpc3 (hcode _ hm12) hstep4 ?_
  refine .step hpc4 (hcode _ hm16) hstep5 ?_
  exact .leave (swapFinalState_pc _ _ _ _ _ _ _) hout rfl

end MetrologyAsm
