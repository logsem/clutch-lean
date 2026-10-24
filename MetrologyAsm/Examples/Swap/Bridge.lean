import MetrologyAsm.ABI.Lemmas
import MetrologyAsm.Examples.Swap.Boundary
import MetrologyAsm.Examples.Swap.Execution
import MetrologyAsm.Examples.Swap.Source

/-! # The source-to-Sail exchange boundary -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions Sail.BitVec

/-- The exact image emitted by the checked assembler for the exchange source. -/
def exchangeImage : Image := (assemble swapAsm).toOption.get (by decide +kernel)

/-- The source assembler emits the exchange image without an error. -/
theorem assemble_exchange : assemble swapCode.prog = .ok exchangeImage := by rfl

/-- Any successful assembly of the exchange source is the exchange image. -/
theorem image_eq_exchangeImage {image : Image} (hi : assemble swapCode.prog = .ok image) :
    image = exchangeImage :=
  Except.ok.inj (hi.symm.trans assemble_exchange)

/-- The exchange's assembled executable region has twenty bytes. -/
@[simp] theorem exchangeImage_textLen : exchangeImage.textLen = 20 := by rfl

/-- The exchange's complete image has twenty-four bytes including alignment padding. -/
@[simp] theorem exchangeImage_length : exchangeImage.bytes.length = 24 := by rfl

/-- The exchange's entry point is the first instruction. -/
@[simp] theorem exchangeImage_entry : exchangeImage.entry = 0 := by rfl

/-- The exchange does not contain external import slots. -/
@[simp] theorem exchangeImage_slots : exchangeImage.importSlots = [] := by rfl

section

variable (ι : Placement)

/-- The exchange code interval is precisely its assembled twenty-byte text region. -/
theorem codeRange_exchange (p : BitVec 64) :
    codeRange ι swapCode p ↔ inSpan ι.codeBase.toNat 20 p.toNat := by
  constructor
  · rintro ⟨image, hi, hp⟩
    have heq : image = exchangeImage := image_eq_exchangeImage hi
    simpa [heq] using hp
  · intro hp
    exact ⟨exchangeImage, assemble_exchange, hp⟩

/-- Every exchange code byte is also an image byte. -/
theorem imageByte_of_codeRange_exchange (p : BitVec 64)
    (hp : codeRange ι swapCode p) : imageByte ι swapCode p.toNat := by
  refine ⟨exchangeImage, assemble_exchange, ?_⟩
  have h := (codeRange_exchange ι p).mp hp
  simp only [exchangeImage_length, inSpan] at *
  omega

/-- The installed exchange image puts the entry counter exactly at the open code base. -/
theorem codeImage_exchange_pc (args : List BoundaryValue) (s : Mach)
    (h : codeImage ι swapCode args s) : pc s = some ι.codeBase := by
  obtain ⟨image, hi, _, _, _, hpc, _⟩ := h
  have heq := image_eq_exchangeImage hi
  subst image
  simpa only [exchangeImage_entry, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hpc

/-- The installed exchange image maps the complete executable interval into user RAM. -/
theorem codeImage_exchange_ram (args : List BoundaryValue) (s : Mach)
    (h : codeImage ι swapCode args s) : InUserRam ι.codeBase 20 := by
  obtain ⟨image, hi, hram, _⟩ := h
  have heq := image_eq_exchangeImage hi
  subst image
  simp only [exchangeImage_length, InUserRam] at hram ⊢
  omega

/-- Installing the checked source image supplies every instruction word used by Sail. -/
theorem SwapImage.of_codeImage (args : List BoundaryValue) (s : Mach)
    (h : codeImage ι swapCode args s) : SwapImage s ι.codeBase := by
  obtain ⟨image, hi, hram, halign, hentry, hpc, hbytes, hdisjoint⟩ := h
  have heq := image_eq_exchangeImage hi
  subst image
  have hram20 : InUserRam ι.codeBase 20 := codeImage_exchange_ram ι args s
    ⟨exchangeImage, assemble_exchange, hram, halign, hentry, hpc, hbytes, hdisjoint⟩
  have h4 : (addInt ι.codeBase 4).toNat = ι.codeBase.toNat + 4 :=
    pcAt_toNat hram20 (i := 1) (by decide)
  have h8 : (addInt ι.codeBase 8).toNat = ι.codeBase.toNat + 8 :=
    pcAt_toNat hram20 (i := 2) (by decide)
  have h12 : (addInt ι.codeBase 12).toNat = ι.codeBase.toNat + 12 :=
    pcAt_toNat hram20 (i := 3) (by decide)
  have h16 : (addInt ι.codeBase 16).toNat = ι.codeBase.toNat + 16 :=
    pcAt_toNat hram20 (i := 4) (by decide)
  have hbytes' : ∀ i byte, exchangeImage.bytes[i]? = some byte →
      s.mem.get? (ι.codeBase.toNat + i) = some (BitVec.ofNat 8 byte.toNat) := by
    simpa only [relocatedBytes, exchangeImage_slots, List.foldl_nil] using hbytes
  constructor <;> intro i hi <;>
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals try simp only [h4, h8, h12, h16, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]
  all_goals first
    | exact hbytes' 0 0x03 rfl
    | exact hbytes' 1 0x36 rfl
    | exact hbytes' 2 0x05 rfl
    | exact hbytes' 3 0x00 rfl
    | exact hbytes' 4 0x83 rfl
    | exact hbytes' 5 0xb6 rfl
    | exact hbytes' 6 0x05 rfl
    | exact hbytes' 7 0x00 rfl
    | exact hbytes' 8 0x23 rfl
    | exact hbytes' 9 0x30 rfl
    | exact hbytes' 10 0xd5 rfl
    | exact hbytes' 11 0x00 rfl
    | exact hbytes' 12 0x23 rfl
    | exact hbytes' 13 0xb0 rfl
    | exact hbytes' 14 0xc5 rfl
    | exact hbytes' 15 0x00 rfl
    | exact hbytes' 16 0x67 rfl
    | exact hbytes' 17 0x80 rfl
    | exact hbytes' 18 0x00 rfl
    | exact hbytes' 19 0x00 rfl

/-- The two signed words decode to their exact finite logical fragment. -/
theorem decodeF_exchange (s : Mach) (l k : Loc) (values : Loc → Int)
    (hne : l ≠ k) (hl : inRange true 64 (values l) = true)
    (hk : inRange true 64 (values k) = true)
    (hwordl : Word64At s (ι.addr l) (BitVec.ofInt 64 (values l)))
    (hwordk : Word64At s (ι.addr k) (BitVec.ofInt 64 (values k))) :
    decodeF ι swapCode [.loc l, .loc k] {l, k} s = some (integerHeap {l, k} values) := by
  have hregions := swap_callRegions l k
  apply decodeF_integerHeap
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with ha | ha
  · subst a
    refine ⟨⟨l, 1, 64, true⟩, ?_, ?_⟩
    · simp [hregions, Region.cells]
    · exact decodeCell_signed64 ι _ l s (values l) rfl rfl hl hwordl
  · subst a
    refine ⟨⟨k, 1, 64, true⟩, ?_, ?_⟩
    · simp [hregions, Region.cells, hne]
    · exact decodeCell_signed64 ι _ k s (values k) rfl rfl hk hwordk

/-- A unit-returning fragment has its decoded return observation at the return address. -/
theorem observe_ret_unit (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (s : Mach) (heap : LocHeap BoundaryValue) (word : BitVec 64)
    (hresult : code.sig.result = .unit) (hpc : pc s = some ι.retAddr)
    (hheap : decodeF ι code args F s = some heap)
    (hword : argumentRegister s 0 = some word) :
    observe ι code args F s = some (.ret .unit heap) := by
  simp [observe, hpc, hheap, hword, hresult, decodeValue]

/-- Compatible exchange facets imply all placement conditions used by actual Sail execution. -/
theorem SwapPlacement.of_RVCompat (s : Mach) (l k : Loc)
    (heap : LocHeap BoundaryValue) (hne : l ≠ k)
    (h : RVCompat ι swapCode [.loc l, .loc k] heap s) :
    SwapPlacement ι.codeBase (ι.addr l) (ι.addr k) ι.retAddr := by
  obtain ⟨hfoot, _, _, himage, _, hret, _, _⟩ := h
  have hregions := swap_callRegions l k
  have hleft : Region.mk l 1 64 true ∈ callRegions swapCode [.loc l, .loc k] := by
    simp [hregions]
  have hright : Region.mk k 1 64 true ∈ callRegions swapCode [.loc l, .loc k] := by
    simp [hregions]
  have hl := hfoot.1 _ hleft
  have hk := hfoot.1 _ hright
  have hneq : Region.mk l 1 64 true ≠ Region.mk k 1 64 true := by
    intro heq
    exact hne (congrArg Region.base heq)
  have hsep := hfoot.2 _ hleft _ hright hneq
  obtain ⟨image, hi, hram, halign, _, _, _, hseparate⟩ := himage
  have heq := image_eq_exchangeImage hi
  subst image
  have hca := hseparate _ hleft
  have hcb := hseparate _ hright
  apply SwapPlacement.of_bounds
  · simp only [exchangeImage_length, InUserRam] at hram ⊢
    omega
  · omega
  · simpa using hl.2.2.1
  · simpa using hk.2.2.1
  · exact hl.1
  · exact hk.1
  · exact hret.2.1
  · simpa [disjointSpans] using hsep
  · simp only [exchangeImage_length, disjointSpans, Nat.reduceDiv, Nat.one_mul] at hca
    omega
  · simp only [exchangeImage_length, disjointSpans, Nat.reduceDiv, Nat.one_mul] at hcb
    omega

/-- The logical entry contents supply the two input words for the actual Sail loads. -/
theorem swap_words_of_contents (s : Mach) (l k : Loc) (old : Loc → Int)
    (h : footprintContents ι swapCode [.loc l, .loc k] (integerHeap {l, k} old) s) :
    Word64At s (ι.addr l) (BitVec.ofInt 64 (old l)) ∧
      Word64At s (ι.addr k) (BitVec.ofInt 64 (old k)) := by
  have hregions := swap_callRegions l k
  have hl : Region.mk l 1 64 true ∈ callRegions swapCode [.loc l, .loc k] := by
    simp [hregions]
  have hk : Region.mk k 1 64 true ∈ callRegions swapCode [.loc l, .loc k] := by
    simp [hregions]
  obtain ⟨zl, hzl, _, hwl⟩ := h.2 _ hl 0 (by simp)
  obtain ⟨zk, hzk, _, hwk⟩ := h.2 _ hk 0 (by simp)
  have hel : zl = old l := by simpa using hzl.symm
  have hek : zk = old k := by simpa using hzk.symm
  subst zl
  subst zk
  exact ⟨by simpa using hwl, by simpa using hwk⟩

/-- The exchange's two concrete writes preserve the full foreign-call memory frame. -/
theorem swapFinalState_memoryFrame (s : Mach) (l k : Loc)
    (x y : BitVec 64) (hstack : stackPlacement ι swapCode [.loc l, .loc k] s) :
    memoryFrame ι swapCode [.loc l, .loc k] s
      (swapFinalState s ι.codeBase (ι.addr l) (ι.addr k) x y ι.retAddr) := by
  obtain ⟨sp, hsp, _⟩ := hstack
  refine ⟨sp, hsp, ?_⟩
  intro a ha _
  have key : ∀ m, m = l ∨ m = k → ¬ inSpan (ι.addr m).toNat 8 a := by
    rintro m hm hb
    refine ha ⟨⟨m, 1, 64, true⟩, ?_, by simpa using hb⟩
    rcases hm with rfl | rfl <;>
      simp [callRegions, regions, swapCode, swapSig, boundaryArgs, ArgKind.region,
        locValue, BoundaryValue.toVal]
  apply swapFinalState_mem_outside
  · have hnot := key l (Or.inl rfl)
    unfold inSpan at hnot
    omega
  · have hnot := key k (Or.inr rfl)
    unfold inSpan at hnot
    omega

end

section Frame

variable (s : Mach) (base a b x y ra : BitVec 64)

/-- The exchange preserves the architectural and model configuration frame. -/
theorem swapFinalState_configurationFrame :
    configurationFrame s (swapFinalState s base a b x y ra) := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro r hscratch _ hbookkeeping
  apply swapFinalState_reg_other
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hbookkeeping ⊢
  refine ⟨hbookkeeping.1, hbookkeeping.2.1, hbookkeeping.2.2, ?_, ?_⟩
  · intro heq
    subst r
    exact hscratch (by decide +kernel)
  · intro heq
    subst r
    exact hscratch (by decide +kernel)

/-- The exchange restores the complete integer callee-saved register set. -/
theorem swapFinalState_calleeSavedRestored :
    calleeSavedRestored s (swapFinalState s base a b x y ra) := by
  intro r hr
  apply swapFinalState_reg_other
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- The exchange preserves the configured user profile and its external trap targets. -/
theorem swapFinalState_machineConfiguration (ι : Placement) (code : Code)
    (h : machineConfiguration ι code s) :
    machineConfiguration ι code (swapFinalState s base a b x y ra) := by
  refine ⟨h.1.swapFinalState base a b x y ra, ?_⟩
  have hmtvec := swapFinalState_reg_other s base a b x y ra Register.mtvec (by decide +kernel)
  have hstvec := swapFinalState_reg_other s base a b x y ra Register.stvec (by decide +kernel)
  simpa only [hmtvec, hstvec] using h.2

end Frame

end MetrologyAsm
