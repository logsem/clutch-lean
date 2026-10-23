import MetrologyAsm.Examples.OTP.Layout
import MetrologyAsm.Examples.OTP.Decode
import MetrologyAsm.ABI.Lemmas

/-! # Physical placement and entry addresses derived from the actual OTP ABI facets -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm Sail

/-- The physical OTP footprint occupies exactly its single owned byte. -/
theorem footprintByte_otp (ι : Placement) (message : Int) (pad : Loc) (address : Nat) :
    footprintByte ι otpCode (otpArgs message pad) address ↔ address = (ι.addr pad).toNat :=
  footprintByte_single_byte ι otpCode (otpArgs message pad) pad rfl address

/-- The emitted text occupies precisely eighty executable bytes. -/
theorem codeRange_otp (ι : Placement) (p : BitVec 64) :
    codeRange ι otpCode p ↔ inSpan ι.codeBase.toNat 80 p.toNat := by
  constructor
  · rintro ⟨image, hi, hp⟩
    have heq : image = otpImage := Except.ok.inj (hi.symm.trans assemble_otpImage)
    simpa [heq] using hp
  · exact fun hp => ⟨otpImage, assemble_otpImage, hp⟩

/-- The complete installed image also contains the eight-byte read-only import slot. -/
theorem imageByte_otp (ι : Placement) (address : Nat) :
    imageByte ι otpCode address ↔ inSpan ι.codeBase.toNat 88 address := by
  constructor
  · rintro ⟨image, hi, hp⟩
    have heq : image = otpImage := Except.ok.inj (hi.symm.trans assemble_otpImage)
    simpa [heq] using hp
  · exact fun hp => ⟨otpImage, assemble_otpImage, hp⟩

/-- Every executable OTP address belongs to the complete installed image. -/
theorem imageByte_of_codeRange (ι : Placement) (p : BitVec 64)
    (h : codeRange ι otpCode p) : imageByte ι otpCode p.toNat := by
  apply (imageByte_otp ι _).mpr
  have hp := (codeRange_otp ι p).mp h
  simp only [inSpan] at hp ⊢
  omega

/-- Each compiled instruction starts within the ABI's executable interval. -/
theorem codeRange_codePC (ι : Placement) (hram : InUserRam ι.codeBase 88)
    {index : Nat} (hi : index < 20) : codeRange ι otpCode (codePC ι.codeBase index) := by
  rw [codeRange_otp, inSpan, codePC_toNat hram (by omega)]
  constructor <;> omega

/-- The actual code-image facet fixes the image extent, alignment and entry PC. -/
theorem codeImage_facts (ι : Placement) (s : Mach) (message : Int) (pad : Loc)
    (h : codeImage ι otpCode (otpArgs message pad) s) :
    InUserRam ι.codeBase 88 ∧ ι.codeBase.toNat % 8 = 0 ∧ pc s = some ι.codeBase := by
  obtain ⟨image, hi, hram, halign, _, hpc, _⟩ := h
  have heq : image = otpImage := Except.ok.inj (hi.symm.trans assemble_otpImage)
  subst image
  refine ⟨hram, halign, ?_⟩
  simpa only [show otpImage.entry = 0 from rfl, Nat.add_zero, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] using hpc

/-- Every compatible OTP entry supplies the raw layout needed by all twenty Sail steps. -/
theorem rawLayout_of_RVCompat (ι : Placement) (s : Mach) (message : Int) (pad : Loc)
    (heap : LocHeap BoundaryValue) (h : RVCompat ι otpCode (otpArgs message pad) heap s) :
    ∃ sp, s.regs.get? .x2 = some sp ∧
      RawLayout ι.codeBase sp (ι.addr pad) (ι.importAddr "randombytes") ι.retAddr := by
  obtain ⟨hplace, _, _, hcode, himports, hreturn, hstack, _⟩ := h
  obtain ⟨hram, halign, _⟩ := codeImage_facts ι s message pad hcode
  obtain ⟨sp, hsp, hspAlign, hspBound, hstackRam, hstackSep⟩ := hstack
  change 32 ≤ sp.toNat at hspBound
  change InUserRam (BitVec.ofNat 64 (sp.toNat - 32)) 32 at hstackRam
  have hpadRam : InUserRam (ι.addr pad) 1 := by
    simpa only [padRegion, Nat.reduceDiv, Nat.mul_one] using
      (hplace.1 (padRegion pad) (by simp)).2.2.1
  have hcodePad : disjointSpans ι.codeBase.toNat 88 (ι.addr pad).toNat 1 := by
    obtain ⟨image, hi, _, _, _, _, _, hsep⟩ := hcode
    have heq : image = otpImage := Except.ok.inj (hi.symm.trans assemble_otpImage)
    subst image
    simpa only [otpImage_length, padRegion, Nat.reduceDiv, Nat.mul_one] using
      hsep (padRegion pad) (by simp)
  have hcodeStack : disjointSpans ι.codeBase.toNat 88 (sp.toNat - 32) 32 := by
    apply disjointSpans_of_no_overlap _ _ _ _ (by decide) (by decide)
    intro address himage hscratch
    exact (hstackSep address hscratch).2.1 ((imageByte_otp ι address).mpr himage)
  have hstackPad : disjointSpans (sp.toNat - 32) 32 (ι.addr pad).toNat 1 := by
    apply disjointSpans_of_no_overlap _ _ _ _ (by decide) (by decide)
    intro address hscratch hpad
    have haddress : address = (ι.addr pad).toNat := by
      obtain ⟨hl, hu⟩ := hpad
      omega
    exact (hstackSep address hscratch).1 ((footprintByte_otp ι message pad address).mpr haddress)
  have hcallbackAlign : (ι.importAddr "randombytes").toNat % 4 = 0 :=
    (himports.1 "randombytes" ⟨[.array 8 (.arg 1), .uint 64], .unit⟩ (by simp [otpCode,
      otpSig])).2.2
  exact ⟨sp, hsp, hram, halign, hspBound, hspAlign, hstackRam, hpadRam,
    hcodeStack, hcodePad, hstackPad, hcallbackAlign, hreturn.2.1⟩

end MetrologyAsm.OTP
