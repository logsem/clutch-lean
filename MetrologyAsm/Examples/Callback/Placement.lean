import MetrologyAsm.ABI.Lemmas
import MetrologyAsm.Examples.Callback.Execution

/-! # Physical placement extracted from the callback ABI facets -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions

/-- Every byte offset in the installed callback image has its nonwrapping natural address. -/
theorem importPC_toNat {base : BitVec 64} (hram : InUserRam base 48)
    {offset : Nat} (hoff : offset < 48) :
    (importPC base (offset : Int)).toNat = base.toNat + offset := by
  have ho : offset < 2 ^ 64 := by omega
  have hs : base.toNat + offset < 2 ^ 64 := by
    obtain ⟨_, hb⟩ := hram
    omega
  simp only [importPC, Sail.BitVec.addInt, BitVec.ofInt_natCast, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt hs]

/-- Each complete instruction within the installed image is mapped into user RAM. -/
theorem importPC_inUserRam {base : BitVec 64} (hram : InUserRam base 48)
    {offset : Nat} (hoff : offset + 4 ≤ 48) : InUserRam (importPC base (offset : Int)) 4 := by
  rw [InUserRam, importPC_toNat hram (by omega)]
  obtain ⟨hl, hh⟩ := hram
  constructor <;> omega

/-- Aligned image offsets preserve the generated model's instruction alignment. -/
theorem importPC_aligned {base : BitVec 64} (hram : InUserRam base 48)
    (halign : base.toNat % 4 = 0) {offset : Nat} (hoff : offset < 48)
    (hoAlign : offset % 4 = 0) : (importPC base (offset : Int)).toNat % 4 = 0 := by
  rw [importPC_toNat hram hoff, Nat.add_mod, halign, hoAlign]

/-- A zero image displacement leaves the image base unchanged. -/
@[simp]
theorem importPC_zero (base : BitVec 64) : importPC base 0 = base := by
  simp [importPC, Sail.BitVec.addInt]

/-- Every callback instruction is indexed by one of the first ten word offsets. -/
theorem mem_importToyPCs_iff (base p : BitVec 64) :
    p ∈ importToyPCs base ↔ ∃ i : Nat, i < 10 ∧ p = importPC base (4 * (i : Int)) := by
  constructor
  · intro hp
    simp only [importToyPCs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, (importPC_zero _).symm⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨3, by decide, rfl⟩
    · exact ⟨4, by decide, rfl⟩
    · exact ⟨5, by decide, rfl⟩
    · exact ⟨6, by decide, rfl⟩
    · exact ⟨7, by decide, rfl⟩
    · exact ⟨8, by decide, rfl⟩
    · exact ⟨9, by decide, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
        i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [importToyPCs, importPC, Sail.BitVec.addInt]

/-- The complete callback image contains forty executable bytes and one eight-byte import slot. -/
@[simp]
theorem importToyImage_length : importToyImage.bytes.length = 48 := by rfl

/-- The callback fragment and its trampoline contain ten uncompressed instructions. -/
@[simp]
theorem importToyImage_textLen : importToyImage.textLen = 40 := by rfl

/-- The callback fragment begins at the start of its assembled image. -/
@[simp]
theorem importToyImage_entry : importToyImage.entry = 0 := by rfl

/-- The callback image has one read-only relocation slot at byte forty. -/
@[simp]
theorem importToyImage_slots : importToyImage.importSlots = [("cb", 40)] := by rfl

/-- Executable callback addresses occupy precisely its forty text bytes. -/
theorem codeRange_importToy (ι : Placement) (p : BitVec 64) :
    codeRange ι importToyCode p ↔ inSpan ι.codeBase.toNat 40 p.toNat := by
  constructor
  · rintro ⟨image, hi, hp⟩
    have heq : image = importToyImage := Except.ok.inj (hi.symm.trans assemble_importToyImage)
    simpa [heq] using hp
  · intro hp
    exact ⟨importToyImage, assemble_importToyImage, hp⟩

/-- The full callback image includes the read-only address slot. -/
theorem imageByte_importToy (ι : Placement) (p : Nat) :
    imageByte ι importToyCode p ↔ inSpan ι.codeBase.toNat 48 p := by
  constructor
  · rintro ⟨image, hi, hp⟩
    have heq : image = importToyImage := Except.ok.inj (hi.symm.trans assemble_importToyImage)
    simpa [heq] using hp
  · intro hp
    exact ⟨importToyImage, assemble_importToyImage, hp⟩

/-- Every executable callback byte belongs to the complete assembled image. -/
theorem imageByte_of_codeRange_importToy (ι : Placement) (p : BitVec 64)
    (h : codeRange ι importToyCode p) : imageByte ι importToyCode p.toNat := by
  apply (imageByte_importToy ι _).mpr
  have hp := (codeRange_importToy ι p).mp h
  simp only [inSpan] at hp ⊢
  omega

/-- The entry image maps the complete callback code and relocation slot into user RAM. -/
theorem codeImage_importToy_ram (ι : Placement) (s : Mach)
    (h : codeImage ι importToyCode [] s) : InUserRam ι.codeBase 48 := by
  obtain ⟨image, hi, hram, _⟩ := h
  have heq : image = importToyImage := Except.ok.inj (hi.symm.trans assemble_importToyImage)
  simpa [heq] using hram

/-- The entry image has the ABI's eight-byte code-base alignment. -/
theorem codeImage_importToy_aligned (ι : Placement) (s : Mach)
    (h : codeImage ι importToyCode [] s) : ι.codeBase.toNat % 8 = 0 := by
  obtain ⟨image, hi, hram, halign, _⟩ := h
  exact halign

/-- The installed callback source fixes its entry PC at the open image base. -/
theorem codeImage_importToy_pc (ι : Placement) (s : Mach)
    (h : codeImage ι importToyCode [] s) : pc s = some ι.codeBase := by
  obtain ⟨image, hi, hram, halign, hentry, hpc, _⟩ := h
  have heq : image = importToyImage := Except.ok.inj (hi.symm.trans assemble_importToyImage)
  subst image
  simpa only [importToyImage_entry, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hpc

/-- Subtracting the scratch-save displacement does not wrap an ABI stack pointer. -/
theorem importSavedAddress_toNat (sp : BitVec 64) (hb : 16 ≤ sp.toNat) :
    (importSavedAddress sp).toNat = sp.toNat - 8 := by
  have hsub : importSavedAddress sp = sp - 8#64 := by
    unfold importSavedAddress Sail.BitVec.addInt
    rw [BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
    rfl
  have hle : 8#64 ≤ sp := by
    rw [BitVec.le_def]
    change 8 ≤ sp.toNat
    omega
  rw [hsub, BitVec.toNat_sub_of_le hle]
  rfl

/-- The eight-byte save is mapped whenever the original sixteen-byte scratch frame is mapped. -/
theorem importSavedAddress_inUserRam (sp : BitVec 64) (hb : 16 ≤ sp.toNat)
    (hram : InUserRam (BitVec.ofNat 64 (sp.toNat - 16)) 16) :
    InUserRam (importSavedAddress sp) 8 := by
  have hsmall : sp.toNat - 16 < 2 ^ 64 := by have := sp.isLt; omega
  have hstart : (BitVec.ofNat 64 (sp.toNat - 16)).toNat = sp.toNat - 16 := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  rw [InUserRam, hstart] at hram
  rw [InUserRam, importSavedAddress_toNat sp hb]
  constructor <;> omega

/-- A sixteen-byte aligned ABI stack pointer gives an eight-byte aligned save slot. -/
theorem importSavedAddress_aligned (sp : BitVec 64) (hb : 16 ≤ sp.toNat)
    (ha : sp.toNat % 16 = 0) : (importSavedAddress sp).toNat % 8 = 0 := by
  rw [importSavedAddress_toNat sp hb]
  omega

/-- Every saved-ra byte is inside the scratch interval owned by the original invocation. -/
theorem importSavedAddress_inStack (sp : BitVec 64) (hb : 16 ≤ sp.toNat) (a : Nat)
    (ha : inSpan (importSavedAddress sp).toNat 8 a) : stackByte importToyCode sp a := by
  rw [importSavedAddress_toNat sp hb] at ha
  change sp.toNat - 16 ≤ a ∧ a < sp.toNat - 16 + 16
  obtain ⟨hl, hh⟩ := ha
  constructor <;> omega

/-- Every actual compatible callback entry supplies the layout required by all ten Sail steps. -/
theorem ImportToyPlacement.of_RVCompat (ι : Placement) (s : Mach)
    (heap : LocHeap BoundaryValue) (h : RVCompat ι importToyCode [] heap s) :
    ∃ sp, s.regs.get? Register.x2 = some sp ∧
      ImportToyPlacement ι.codeBase sp ι.retAddr (ι.importAddr "cb") := by
  obtain ⟨_, _, _, hcode, himports, hreturn, hstack, _⟩ := h
  have hram := codeImage_importToy_ram ι s hcode
  have halign8 := codeImage_importToy_aligned ι s hcode
  have halign4 : ι.codeBase.toNat % 4 = 0 := by omega
  obtain ⟨sp, hsp, hspAlign, hspBound, hstackRam, hstackSep⟩ := hstack
  change 16 ≤ sp.toNat at hspBound
  change InUserRam (BitVec.ofNat 64 (sp.toNat - 16)) 16 at hstackRam
  have hdisjoint : disjointSpans (importSavedAddress sp).toNat 8 ι.codeBase.toNat 48 := by
    apply disjointSpans_of_no_overlap _ _ _ _ (by decide) (by decide)
    intro address hsave himage
    have hs := importSavedAddress_inStack sp hspBound address hsave
    exact (hstackSep address hs).2.1 ((imageByte_importToy ι address).mpr himage)
  change (importSavedAddress sp).toNat + 8 ≤ ι.codeBase.toNat ∨
    ι.codeBase.toNat + 48 ≤ (importSavedAddress sp).toNat at hdisjoint
  have hcallback : (ι.importAddr "cb").toNat % 4 = 0 := by
    exact (himports.1 "cb" ⟨[], .int 64⟩ (by simp [importToyCode])).2.2
  have hslotNat : (importPC ι.codeBase 40).toNat = ι.codeBase.toNat + 40 :=
    importPC_toNat hram (offset := 40) (by decide)
  refine ⟨sp, hsp, ?_⟩
  refine ⟨?_, ?_, importSavedAddress_inUserRam sp hspBound hstackRam,
    importSavedAddress_aligned sp hspBound hspAlign, ?_, ?_, hcallback,
    hreturn.2.1, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := (mem_importToyPCs_iff ι.codeBase p).mp hp
    have hcast : 4 * (i : Int) = ((4 * i : Nat) : Int) := by omega
    rw [hcast]
    exact importPC_inUserRam hram (by omega)
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := (mem_importToyPCs_iff ι.codeBase p).mp hp
    have hcast : 4 * (i : Int) = ((4 * i : Nat) : Int) := by omega
    rw [hcast]
    exact importPC_aligned hram halign4 (by omega) (by omega)
  · rw [InUserRam, hslotNat]
    obtain ⟨hl, hh⟩ := hram
    constructor <;> omega
  · rw [hslotNat]
    omega
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := (mem_importToyPCs_iff ι.codeBase p).mp hp
    have hcast : 4 * (i : Int) = ((4 * i : Nat) : Int) := by omega
    rw [hcast, importPC_toNat hram (offset := 4 * i) (by omega)]
    rcases hdisjoint with hdisjoint | hdisjoint <;> omega
  · rw [hslotNat]
    rcases hdisjoint with hdisjoint | hdisjoint <;> omega

end MetrologyAsm
