import MetrologyAsm.Examples.Callback.Steps

/-! # Plain Sail execution to an import stop and from its continuation -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions Sail Register Std.ExtDHashMap

/-- An instruction's byte offset in the callback source. -/
def importPC (base : BitVec 64) (offset : Int) : BitVec 64 := BitVec.addInt base offset

/-- A zero image displacement leaves the image base unchanged. -/
@[simp]
theorem importPC_zero (base : BitVec 64) : importPC base 0 = base := by
  simp [importPC, BitVec.addInt]

/-- The scratch stack pointer after reserving sixteen bytes. -/
def importReservedSP (sp : BitVec 64) : BitVec 64 := BitVec.addInt sp (-16)

/-- The eight-byte scratch slot preserving the original return address. -/
def importSavedAddress (sp : BitVec 64) : BitVec 64 := BitVec.addInt sp (-8)

/-- All executable instruction entries of the callback fragment and trampoline. -/
def importToyPCs (base : BitVec 64) : List (BitVec 64) :=
  [base, importPC base 4, importPC base 8, importPC base 12, importPC base 16,
    importPC base 20, importPC base 24, importPC base 28, importPC base 32, importPC base 36]

/-- The saved return address is eight bytes above the reserved stack pointer. -/
theorem importSavedAddress_eq (sp : BitVec 64) :
    BitVec.addInt (importReservedSP sp) 8 = importSavedAddress sp := by
  rw [importReservedSP, addInt_compose]
  rfl

/-- Releasing the scratch frame restores the original stack pointer. -/
theorem importReservedSP_cancel (sp : BitVec 64) :
    BitVec.addInt (importReservedSP sp) 16 = sp := by
  rw [importReservedSP, addInt_compose]
  simp [BitVec.addInt]

/-- The signed reserve immediate has its intended sixteen-byte meaning. -/
theorem importReserve_imm : sign_extend 0xff0#12 = BitVec.ofInt 64 (-16) := by
  decide +kernel

/-- The callback image supplies every actual instruction and the relocated callback slot. -/
structure ImportToyImageAt (s : Mach) (base callback : BitVec 64) : Prop where
  /-- The emitted reserve instruction word. -/
  reserve : Word32At s base 0xff010113#32
  /-- The emitted save instruction word. -/
  save : Word32At s (importPC base 4) 0x00113423#32
  /-- The emitted callUpper instruction word. -/
  callUpper : Word32At s (importPC base 8) 0x00000097#32
  /-- The emitted callLink instruction word. -/
  callLink : Word32At s (importPC base 12) 0x014080e7#32
  /-- The emitted restore instruction word. -/
  restore : Word32At s (importPC base 16) 0x00813083#32
  /-- The emitted release instruction word. -/
  release : Word32At s (importPC base 20) 0x01010113#32
  /-- The emitted ret instruction word. -/
  ret : Word32At s (importPC base 24) 0x00008067#32
  /-- The emitted stubUpper instruction word. -/
  stubUpper : Word32At s (importPC base 28) 0x00000e17#32
  /-- The emitted stubLoad instruction word. -/
  stubLoad : Word32At s (importPC base 32) 0x00ce3e03#32
  /-- The emitted stubJump instruction word. -/
  stubJump : Word32At s (importPC base 36) 0x000e0067#32
  /-- The relocated read-only slot contains the actual callback address. -/
  slot : Word64At s (importPC base 40) callback

/-- The physical access and separation conditions used by the callback execution. -/
structure ImportToyPlacement (base sp ra callback : BitVec 64) : Prop where
  /-- All instruction words are mapped. -/
  codeRam : ∀ p ∈ importToyPCs base, InUserRam p 4
  /-- All instruction entries are aligned. -/
  codeAlign : ∀ p ∈ importToyPCs base, p.toNat % 4 = 0
  /-- The scratch save slot is mapped. -/
  saveRam : InUserRam (importSavedAddress sp) 8
  /-- The scratch save slot is aligned. -/
  saveAlign : (importSavedAddress sp).toNat % 8 = 0
  /-- The read-only import-address slot is mapped. -/
  slotRam : InUserRam (importPC base 40) 8
  /-- The read-only import-address slot is aligned. -/
  slotAlign : (importPC base 40).toNat % 8 = 0
  /-- The callback entry obeys the model's instruction alignment. -/
  callbackAlign : callback.toNat % 4 = 0
  /-- The original return address obeys the model's instruction alignment. -/
  returnAlign : ra.toNat % 4 = 0
  /-- The scratch write preserves every emitted instruction. -/
  codeDisjoint : ∀ p ∈ importToyPCs base,
    (importSavedAddress sp).toNat + 8 ≤ p.toNat ∨ p.toNat + 4 ≤ (importSavedAddress sp).toNat
  /-- The scratch write preserves the relocated import-address slot. -/
  slotDisjoint : (importSavedAddress sp).toNat + 8 ≤ (importPC base 40).toNat ∨
    (importPC base 40).toNat + 8 ≤ (importSavedAddress sp).toNat

/-- The three original source words executed after the callback returns. -/
structure ImportContinuationImageAt (s : Mach) (base : BitVec 64) : Prop where
  /-- Restore the saved original ra. -/
  restore : Word32At s (importPC base 16) 0x00813083#32
  /-- Release the scratch frame. -/
  release : Word32At s (importPC base 20) 0x01010113#32
  /-- Return to the original caller. -/
  ret : Word32At s (importPC base 24) 0x00008067#32

section

variable (s : Mach) (base sp ra callback : BitVec 64)

/-- The machine after reserving the scratch frame. -/
def importState1 : Mach :=
  commitState (importSpBodyState s base (importReservedSP sp)) (importPC base 4)

/-- The machine after saving the original return address. -/
def importState2 : Mach :=
  commitState (storeBodyState (importState1 s base sp) (importPC base 4)
    (importSavedAddress sp) ra) (importPC base 8)

/-- The machine after forming the local call's upper PC-relative address. -/
def importState3 : Mach :=
  commitState (importRaBodyState (importState2 s base sp ra) (importPC base 8)
    (importPC base 8)) (importPC base 12)

/-- The linking local jump enters the import trampoline. -/
def importState4 : Mach :=
  commitState (importLinkBodyState (importState3 s base sp ra) (importPC base 12)
    (importPC base 28)) (importPC base 28)

/-- The trampoline forms the upper address of its import slot. -/
def importState5 : Mach :=
  commitState (importT3BodyState (importState4 s base sp ra) (importPC base 28)
    (importPC base 28)) (importPC base 32)

/-- The trampoline loads its relocated callback address. -/
def importState6 : Mach :=
  commitState (importT3BodyState (importState5 s base sp ra) (importPC base 32) callback)
    (importPC base 36)

/-- The exact paused machine at the external callback entry. -/
def importCallState : Mach :=
  commitState (importJumpBodyState (importState6 s base sp ra callback) (importPC base 36)
    callback) callback

/-- The resumed machine after restoring the original return address. -/
def importResumeState1 : Mach :=
  commitState (importRaBodyState s (importPC base 16) ra) (importPC base 20)

/-- The resumed machine after restoring the original stack pointer. -/
def importResumeState2 : Mach :=
  commitState (importSpBodyState (importResumeState1 s base ra) (importPC base 20) sp)
    (importPC base 24)

/-- The exact terminal machine after an arbitrary compatible callback resumption. -/
def importReturnState : Mach :=
  commitState (retBodyState (importResumeState2 s base sp ra) (importPC base 24) ra) ra

end

section

variable (s : Mach) (base sp ra callback : BitVec 64)

/-- The callback prefix writes exactly the original return address into its scratch slot. -/
theorem importCallState_mem :
    (importCallState s base sp ra callback).mem =
      (write64State s (importSavedAddress sp) ra).mem := by
  rfl

/-- The external jump commits the callback entry as the program counter. -/
theorem importCallState_pc :
    (importCallState s base sp ra callback).regs.get? PC = some callback := by
  simp [importCallState, commitState]

/-- The post-callback continuation does not modify any memory byte. -/
theorem importReturnState_mem :
    (importReturnState s base sp ra).mem = s.mem := by
  rfl

/-- The continuation restores the original stack pointer. -/
theorem importReturnState_sp :
    (importReturnState s base sp ra).regs.get? x2 = some sp := by
  simp [importReturnState, importResumeState2, commitState, retBodyState, importSpBodyState,
    sequentialState, counterState, get?_insert]

/-- The resumed continuation returns to the original saved return address. -/
theorem importReturnState_pc :
    (importReturnState s base sp ra).regs.get? PC = some ra := by
  simp [importReturnState, commitState]

/-- The paused call retains the scratch frame reserved by the original invocation. -/
theorem importCallState_sp :
    (importCallState s base sp ra callback).regs.get? x2 = some (importReservedSP sp) := by
  simp [importCallState, importState6, importState5, importState4, importState3,
    importState2, importState1, commitState, importJumpBodyState, importT3BodyState,
    importLinkBodyState, importRaBodyState, importSpBodyState, storeBodyState,
    sequentialState, counterState, get?_insert]

/-- The paused call's link points to the first original continuation instruction. -/
theorem importCallState_ra :
    (importCallState s base sp ra callback).regs.get? x1 = some (importPC base 16) := by
  simp [importCallState, importState6, importState5, importState4, commitState,
    importJumpBodyState, importT3BodyState, importLinkBodyState, sequentialState,
    counterState, get?_insert, importPC, addInt_compose]

/-- The paused call retains its saved original return address as actual allocated bytes. -/
theorem importCallState_saved :
    Word64At (importCallState s base sp ra callback) (importSavedAddress sp) ra :=
  (word64At_write64State s _ ra).of_mem_eq (importCallState_mem _ _ _ _ _)

/-- Every byte outside the eight-byte scratch save is unchanged at the import stop. -/
theorem importCallState_mem_outside (a : Nat)
    (hout : a < (importSavedAddress sp).toNat ∨ (importSavedAddress sp).toNat + 8 ≤ a) :
    (importCallState s base sp ra callback).mem.get? a = s.mem.get? a := by
  rw [importCallState_mem, write64State_get?_outside _ _ _ _ hout]

/-- The import prefix changes only its link, stack, trampoline temporary, and step bookkeeping. -/
theorem importCallState_reg_other (r : Register)
    (hout : r ∉ [PC, .nextPC, .minstret_increment, .x1, .x2, .x28]) :
    (importCallState s base sp ra callback).regs.get? r = s.regs.get? r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
  obtain ⟨hpc, hn, hf, h1, h2, h28⟩ := hout
  simp [importCallState, importState6, importState5, importState4, importState3,
    importState2, importState1, commitState, importJumpBodyState, importT3BodyState,
    importLinkBodyState, importRaBodyState, importSpBodyState, storeBodyState,
    sequentialState, counterState, get?_insert,
    Ne.symm hpc, Ne.symm hn, Ne.symm hf, Ne.symm h1, Ne.symm h2, Ne.symm h28]

/-- The continuation changes only PC, step bookkeeping, ra and sp. -/
theorem importReturnState_reg_other (r : Register)
    (hout : r ∉ [PC, .nextPC, .minstret_increment, .x1, .x2]) :
    (importReturnState s base sp ra).regs.get? r = s.regs.get? r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
  obtain ⟨hpc, hn, hf, h1, h2⟩ := hout
  simp [importReturnState, importResumeState2, importResumeState1, commitState,
    importRaBodyState, importSpBodyState, retBodyState, sequentialState, counterState,
    get?_insert, Ne.symm hpc, Ne.symm hn, Ne.symm hf, Ne.symm h1, Ne.symm h2]

/-- Import-prefix execution preserves the nonregister platform state. -/
theorem importCallState_fields :
    (importCallState s base sp ra callback).choiceState = s.choiceState ∧
      (importCallState s base sp ra callback).tags = s.tags ∧
      (importCallState s base sp ra callback).cycleCount = s.cycleCount ∧
      (importCallState s base sp ra callback).sailOutput = s.sailOutput :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Continuation execution preserves the nonregister platform state after the callback. -/
theorem importReturnState_fields :
    (importReturnState s base sp ra).choiceState = s.choiceState ∧
      (importReturnState s base sp ra).tags = s.tags ∧
      (importReturnState s base sp ra).cycleCount = s.cycleCount ∧
      (importReturnState s base sp ra).sailOutput = s.sailOutput :=
  ⟨rfl, rfl, rfl, rfl⟩

end

section

variable {s : Mach} {base callback : BitVec 64} (h : ImportToyImageAt s base callback)

include h

/-- Register-only preparation preserves the complete callback image. -/
theorem ImportToyImageAt.of_mem_eq {t : Mach} (hm : t.mem = s.mem) :
    ImportToyImageAt t base callback := by
  exact ⟨h.reserve.of_mem_eq hm, h.save.of_mem_eq hm, h.callUpper.of_mem_eq hm,
    h.callLink.of_mem_eq hm, h.restore.of_mem_eq hm, h.release.of_mem_eq hm, h.ret.of_mem_eq hm,
    h.stubUpper.of_mem_eq hm, h.stubLoad.of_mem_eq hm, h.stubJump.of_mem_eq hm,
    h.slot.of_mem_eq hm⟩

/-- The scratch save preserves the full executable image and the relocated callback address. -/
theorem ImportToyImageAt.write64State {sp ra : BitVec 64}
    (layout : ImportToyPlacement base sp ra callback) :
    ImportToyImageAt (write64State s (importSavedAddress sp) ra) base callback := by
  have hd := layout.codeDisjoint
  exact ⟨h.reserve.write64State ra (hd _ (by simp [importToyPCs])),
    h.save.write64State ra (hd _ (by simp [importToyPCs])),
    h.callUpper.write64State ra (hd _ (by simp [importToyPCs])),
    h.callLink.write64State ra (hd _ (by simp [importToyPCs])),
    h.restore.write64State ra (hd _ (by simp [importToyPCs])),
    h.release.write64State ra (hd _ (by simp [importToyPCs])),
    h.ret.write64State ra (hd _ (by simp [importToyPCs])),
    h.stubUpper.write64State ra (hd _ (by simp [importToyPCs])),
    h.stubLoad.write64State ra (hd _ (by simp [importToyPCs])),
    h.stubJump.write64State ra (hd _ (by simp [importToyPCs])),
    h.slot.write64State ra layout.slotDisjoint⟩

/-- The installed full callback image contains the post-callback continuation. -/
theorem ImportToyImageAt.continuation : ImportContinuationImageAt s base :=
  ⟨h.restore, h.release, h.ret⟩

/-- The paused call preserves the complete source image and callback slot. -/
theorem importCallState_image {sp ra : BitVec 64}
    (layout : ImportToyPlacement base sp ra callback) :
    ImportToyImageAt (importCallState s base sp ra callback) base callback :=
  (h.write64State layout).of_mem_eq (importCallState_mem _ _ _ _ _)

end

/-- Pointwise memory preservation retains all continuation instructions across arbitrary resumes. -/
theorem ImportContinuationImageAt.of_mem_get_eq {s t : Mach} {base : BitVec 64}
    (h : ImportContinuationImageAt s base) (hm : ∀ a, t.mem.get? a = s.mem.get? a) :
    ImportContinuationImageAt t base := by
  exact ⟨fun i hi => by rw [hm]; exact h.restore i hi,
    fun i hi => by rw [hm]; exact h.release i hi, fun i hi => by rw [hm]; exact h.ret i hi⟩

section

variable {s : Mach} (h : UserConfig s) (base sp ra callback : BitVec 64)

include h

/-- The importState1 transition preserves the configured user profile. -/
theorem UserConfig.importState1 :
    UserConfig (MetrologyAsm.importState1 s base sp) := by
  exact ((h.counterState.sequentialState base).insert .x2 _ trivial).insert .PC _ trivial

/-- The importState2 transition preserves the configured user profile. -/
theorem UserConfig.importState2 :
    UserConfig (MetrologyAsm.importState2 s base sp ra) := by
  have hs := (h.importState1 base sp).counterState.sequentialState (importPC base 4)
  exact (hs.write64State _ _).insert .PC _ trivial

/-- The importState3 transition preserves the configured user profile. -/
theorem UserConfig.importState3 :
    UserConfig (MetrologyAsm.importState3 s base sp ra) := by
  have hs := (h.importState2 base sp ra).counterState.sequentialState (importPC base 8)
  exact (hs.insert .x1 _ trivial).insert .PC _ trivial

/-- The importState4 transition preserves the configured user profile. -/
theorem UserConfig.importState4 :
    UserConfig (MetrologyAsm.importState4 s base sp ra) := by
  have hs := (h.importState3 base sp ra).counterState.sequentialState (importPC base 12)
  exact ((hs.insert .nextPC _ trivial).insert .x1 _ trivial).insert .PC _ trivial

/-- The importState5 transition preserves the configured user profile. -/
theorem UserConfig.importState5 :
    UserConfig (MetrologyAsm.importState5 s base sp ra) := by
  have hs := (h.importState4 base sp ra).counterState.sequentialState (importPC base 28)
  exact (hs.insert .x28 _ trivial).insert .PC _ trivial

/-- The importState6 transition preserves the configured user profile. -/
theorem UserConfig.importState6 :
    UserConfig (MetrologyAsm.importState6 s base sp ra callback) := by
  have hs := (h.importState5 base sp ra).counterState.sequentialState (importPC base 32)
  exact (hs.insert .x28 _ trivial).insert .PC _ trivial

/-- The importCallState transition preserves the configured user profile. -/
theorem UserConfig.importCallState :
    UserConfig (MetrologyAsm.importCallState s base sp ra callback) := by
  have hs := (h.importState6 base sp ra callback).counterState.sequentialState (importPC base 36)
  exact (hs.insert .nextPC _ trivial).insert .PC _ trivial

/-- Restoring ra preserves the user profile. -/
theorem UserConfig.importResumeState1 :
    UserConfig (MetrologyAsm.importResumeState1 s base ra) :=
  ((h.counterState.sequentialState _).insert .x1 _ trivial).insert .PC _ trivial

/-- Releasing the scratch frame preserves the user profile. -/
theorem UserConfig.importResumeState2 :
    UserConfig (MetrologyAsm.importResumeState2 s base sp ra) :=
  (((h.importResumeState1 base ra).counterState.sequentialState _).insert .x2 _ trivial).insert
    .PC _ trivial

/-- Returning from the callback continuation preserves the user profile. -/
theorem UserConfig.importReturnState :
    UserConfig (MetrologyAsm.importReturnState s base sp ra) := by
  have hs := (h.importResumeState2 base sp ra).counterState.sequentialState (importPC base 24)
  exact (hs.insert .nextPC _ trivial).insert .PC _ trivial

/-- Executing the import prefix reaches the callback entry with the original ra saved. -/
theorem importToy_runsTo_call (layout : ImportToyPlacement base sp ra callback)
    (image : ImportToyImageAt s base callback)
    (hpc : s.regs.get? PC = some base) (hsp : s.regs.get? x2 = some sp)
    (hra : s.regs.get? x1 = some ra)
    (code : BitVec 64 → Prop) (hcode : ∀ p ∈ importToyPCs base, code p)
    (hout : ¬code callback) :
    RunsTo code (fun t => t = importCallState s base sp ra callback) s := by
  have hm0 : base ∈ importToyPCs base := by simp [importToyPCs]
  have hm4 : importPC base 4 ∈ importToyPCs base := by simp [importToyPCs]
  have hm8 : importPC base 8 ∈ importToyPCs base := by simp [importToyPCs]
  have hm12 : importPC base 12 ∈ importToyPCs base := by simp [importToyPCs]
  have hm28 : importPC base 28 ∈ importToyPCs base := by simp [importToyPCs]
  have hm32 : importPC base 32 ∈ importToyPCs base := by simp [importToyPCs]
  have hm36 : importPC base 36 ∈ importToyPCs base := by simp [importToyPCs]
  have hpc1 : (importState1 s base sp).regs.get? PC = some (importPC base 4) := by
    simp [importState1, commitState]
  have hpc2 : (importState2 s base sp ra).regs.get? PC = some (importPC base 8) := by
    simp [importState2, commitState]
  have hpc3 : (importState3 s base sp ra).regs.get? PC = some (importPC base 12) := by
    simp [importState3, commitState]
  have hpc4 : (importState4 s base sp ra).regs.get? PC = some (importPC base 28) := by
    simp [importState4, commitState]
  have hpc5 : (importState5 s base sp ra).regs.get? PC = some (importPC base 32) := by
    simp [importState5, commitState]
  have hpc6 : (importState6 s base sp ra callback).regs.get? PC =
      some (importPC base 36) := by simp [importState6, commitState]
  have hstep1 : rvStep s = some (importState1 s base sp) := by
    simpa [importState1, importReservedSP, importPC, importReserve_imm, BitVec.addInt] using
      rvStep_addi_sp h base sp 0xff0#12 0xff010113#32 decode_importToy_reserve hpc hsp
        (layout.codeRam _ hm0) (layout.codeAlign _ hm0) (by decide +kernel) image.reserve
  have hsp1 : (importState1 s base sp).regs.get? x2 = some (importReservedSP sp) := by
    simp [importState1, importSpBodyState, commitState, get?_insert]
  have hra1 : (importState1 s base sp).regs.get? x1 = some ra := by
    simp [importState1, importSpBodyState, commitState, sequentialState, counterState,
      get?_insert, hra]
  have hstep2 : rvStep (importState1 s base sp) = some (importState2 s base sp ra) := by
    have hw : Word32At (importState1 s base sp) (importPC base 4) 0x00113423#32 :=
      image.save.of_mem_eq rfl
    simpa [importState2, importPC, addInt_compose, importSavedAddress_eq] using
      rvStep_import_save (h.importState1 base sp) (importPC base 4) (importReservedSP sp) ra
        hpc1 hsp1 hra1 (layout.codeRam _ hm4) (layout.codeAlign _ hm4)
        (by simpa only [importSavedAddress_eq] using layout.saveRam)
        (by simpa only [importSavedAddress_eq] using layout.saveAlign) hw
  have hstored : ImportToyImageAt (importState2 s base sp ra) base callback :=
    (image.write64State layout).of_mem_eq rfl
  have hstep3 : rvStep (importState2 s base sp ra) = some (importState3 s base sp ra) := by
    simpa [importState3, importPC, addInt_compose] using
      rvStep_auipc_ra (h.importState2 base sp ra) (importPC base 8) hpc2
        (layout.codeRam _ hm8) (layout.codeAlign _ hm8) hstored.callUpper
  have hra3 : (importState3 s base sp ra).regs.get? x1 = some (importPC base 8) := by
    simp [importState3, importRaBodyState, commitState, get?_insert]
  have hstep4 : rvStep (importState3 s base sp ra) = some (importState4 s base sp ra) := by
    have hw : Word32At (importState3 s base sp ra) (importPC base 12) 0x014080e7#32 :=
      hstored.callLink.of_mem_eq rfl
    simpa [importState4, importPC, addInt_compose] using
      rvStep_import_link (h.importState3 base sp ra) (importPC base 12) (importPC base 8)
        hpc3 hra3 (layout.codeRam _ hm12) (layout.codeAlign _ hm12)
        (by simpa [importPC, addInt_compose] using layout.codeAlign _ hm28) hw
  have hstep5 : rvStep (importState4 s base sp ra) = some (importState5 s base sp ra) := by
    have hw : Word32At (importState4 s base sp ra) (importPC base 28) 0x00000e17#32 :=
      hstored.stubUpper.of_mem_eq rfl
    simpa [importState5, importPC, addInt_compose] using
      rvStep_auipc_t3 (h.importState4 base sp ra) (importPC base 28) hpc4
        (layout.codeRam _ hm28) (layout.codeAlign _ hm28) hw
  have ht3 : (importState5 s base sp ra).regs.get? x28 = some (importPC base 28) := by
    simp [importState5, importT3BodyState, commitState, get?_insert]
  have hstep6 : rvStep (importState5 s base sp ra) = some (importState6 s base sp ra callback) := by
    have hw : Word32At (importState5 s base sp ra) (importPC base 32) 0x00ce3e03#32 :=
      hstored.stubLoad.of_mem_eq rfl
    have hd : Word64At (importState5 s base sp ra) (importPC base 40) callback :=
      hstored.slot.of_mem_eq rfl
    simpa [importState6, importPC, addInt_compose] using
      rvStep_import_stub_load (h.importState5 base sp ra) (importPC base 32)
        (importPC base 28) callback hpc5 ht3 (layout.codeRam _ hm32) (layout.codeAlign _ hm32)
        (by simpa [importPC, addInt_compose] using layout.slotRam)
        (by simpa [importPC, addInt_compose] using layout.slotAlign) hw
        (by simpa [importPC, addInt_compose] using hd)
  have hcallback : (importState6 s base sp ra callback).regs.get? x28 = some callback := by
    simp [importState6, importT3BodyState, commitState, get?_insert]
  have hstep7 : rvStep (importState6 s base sp ra callback) =
      some (importCallState s base sp ra callback) := by
    have hw : Word32At (importState6 s base sp ra callback) (importPC base 36) 0x000e0067#32 :=
      hstored.stubJump.of_mem_eq rfl
    exact rvStep_import_jump (h.importState6 base sp ra callback) (importPC base 36) callback
      hpc6 hcallback (layout.codeRam _ hm36) (layout.codeAlign _ hm36) layout.callbackAlign hw
  refine .step hpc (hcode _ hm0) hstep1 ?_
  refine .step hpc1 (hcode _ hm4) hstep2 ?_
  refine .step hpc2 (hcode _ hm8) hstep3 ?_
  refine .step hpc3 (hcode _ hm12) hstep4 ?_
  refine .step hpc4 (hcode _ hm28) hstep5 ?_
  refine .step hpc5 (hcode _ hm32) hstep6 ?_
  refine .step hpc6 (hcode _ hm36) hstep7 ?_
  exact .leave (importCallState_pc _ _ _ _ _) hout rfl

/-- Executing the continuation returns to the original caller. -/
theorem importToy_runsTo_return (layout : ImportToyPlacement base sp ra callback)
    (image : ImportContinuationImageAt s base)
    (hpc : s.regs.get? PC = some (importPC base 16))
    (hsp : s.regs.get? x2 = some (importReservedSP sp))
    (hsaved : Word64At s (importSavedAddress sp) ra)
    (code : BitVec 64 → Prop) (hcode : ∀ p ∈ importToyPCs base, code p) (hout : ¬code ra) :
    RunsTo code (fun t => t = importReturnState s base sp ra) s := by
  have hm16 : importPC base 16 ∈ importToyPCs base := by simp [importToyPCs]
  have hm20 : importPC base 20 ∈ importToyPCs base := by simp [importToyPCs]
  have hm24 : importPC base 24 ∈ importToyPCs base := by simp [importToyPCs]
  have hpc1 : (importResumeState1 s base ra).regs.get? PC =
      some (importPC base 20) := by simp [importResumeState1, commitState]
  have hpc2 : (importResumeState2 s base sp ra).regs.get? PC =
      some (importPC base 24) := by simp [importResumeState2, commitState]
  have hstep1 : rvStep s = some (importResumeState1 s base ra) := by
    simpa [importResumeState1, importPC, addInt_compose] using
      rvStep_import_restore h (importPC base 16) (importReservedSP sp) ra hpc hsp
        (layout.codeRam _ hm16) (layout.codeAlign _ hm16)
        (by simpa only [importSavedAddress_eq] using layout.saveRam)
        (by simpa only [importSavedAddress_eq] using layout.saveAlign) image.restore
        (by simpa only [importSavedAddress_eq] using hsaved)
  have hsp1 : (importResumeState1 s base ra).regs.get? x2 = some (importReservedSP sp) := by
    simp [importResumeState1, importRaBodyState, commitState, sequentialState, counterState,
      get?_insert, hsp]
  have hvalue : importReservedSP sp + sign_extend 16#12 = sp := by
    change BitVec.addInt (importReservedSP sp) 16 = sp
    exact importReservedSP_cancel sp
  have hstep2 : rvStep (importResumeState1 s base ra) = some (importResumeState2 s base sp ra) := by
    have hw : Word32At (importResumeState1 s base ra) (importPC base 20) 0x01010113#32 :=
      image.release.of_mem_eq rfl
    simpa [importResumeState2, importPC, addInt_compose, hvalue] using
      rvStep_addi_sp (h.importResumeState1 base ra) (importPC base 20) (importReservedSP sp)
        16#12 0x01010113#32 decode_importToy_release hpc1 hsp1
        (layout.codeRam _ hm20) (layout.codeAlign _ hm20) (by decide +kernel) hw
  have hra2 : (importResumeState2 s base sp ra).regs.get? x1 = some ra := by
    simp [importResumeState2, importResumeState1, importSpBodyState, importRaBodyState,
      commitState, sequentialState, counterState, get?_insert]
  have hstep3 : rvStep (importResumeState2 s base sp ra) =
      some (importReturnState s base sp ra) := by
    have hw : Word32At (importResumeState2 s base sp ra) (importPC base 24) 0x00008067#32 :=
      image.ret.of_mem_eq rfl
    exact rvStep_ret (h.importResumeState2 base sp ra) (importPC base 24) ra hpc2 hra2
      (layout.codeRam _ hm24) (layout.codeAlign _ hm24) layout.returnAlign hw
  refine .step hpc (hcode _ hm16) hstep1 ?_
  refine .step hpc1 (hcode _ hm20) hstep2 ?_
  refine .step hpc2 (hcode _ hm24) hstep3 ?_
  exact .leave (importReturnState_pc _ _ _ _) hout rfl

end

end MetrologyAsm
