import MetrologyAsm.Examples.Swap.Boundary
import MetrologyAsm.Examples.Support

/-! # A concrete compatible entry machine for the exchange fragment -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions
open Sail.ConcurrencyInterfaceV1
open Std.ExtDHashMap

/-- The assembled exchange image, equal to the assembler output by `assemble_swapWitnessImage`. -/
def swapWitnessImage : Image :=
  (assemble swapAsm).toOption.getD ⟨[], 0, 0, 0, [], [], []⟩

/-- The concrete witness uses exactly the assembled source image. -/
theorem assemble_swapWitnessImage : assemble swapAsm = .ok swapWitnessImage := by
  rfl

/-- Any successful assembly of the exchange source is the witness image. -/
theorem swapWitness_image_of_assemble {image : Image} (h : assemble swapAsm = .ok image) :
    image = swapWitnessImage := by
  rw [assemble_swapWitnessImage] at h
  exact (Except.ok.inj h).symm

/-- The witness's full image contains its twenty text bytes and four alignment bytes. -/
theorem swapWitnessImage_length : swapWitnessImage.bytes.length = 24 := by
  rfl

/-- The exchange begins at the first byte of its executable image. -/
theorem swapWitnessImage_entry : swapWitnessImage.entry = 0 := by
  rfl

/-- The assembled image is installed before allocating the two disjoint data words. -/
noncomputable def swapWitnessCodeState : Mach :=
  { witnessRegisters with
    mem := witnessImageBytes swapWitnessImage.bytes 0x80000000 witnessRegisters.mem }

/-- A concrete raw entry machine stores the two logical integers in disjoint RAM doublewords. -/
noncomputable def swapWitnessState (l k : Loc) (old : Loc → Int) : Mach :=
  write64State (write64State swapWitnessCodeState 0x80001000#64 (BitVec.ofInt 64 (old l)))
    0x80001008#64 (BitVec.ofInt 64 (old k))

set_option maxRecDepth 100000 in
/-- Installing the code bytes preserves the user profile. -/
theorem swapWitnessCodeState_config : UserConfig swapWitnessCodeState :=
  witnessRegisters_config.of_regs_eq rfl

/-- Every logical integer pair has a raw witness satisfying the user profile. -/
theorem swapWitnessState_config (l k : Loc) (old : Loc → Int) :
    UserConfig (swapWitnessState l k old) :=
  (swapWitnessCodeState_config.write64State _ _).write64State _ _

/-- The witness's registers are those of the underlying entry registers. -/
@[simp]
theorem swapWitnessState_regs (l k : Loc) (old : Loc → Int) :
    (swapWitnessState l k old).regs = witnessRegisters.regs := by
  simp [swapWitnessState, swapWitnessCodeState]

/-- Membership in the exchange's call regions names its two signed doubleword regions. -/
theorem swap_callRegions_mem {l k : Loc} {r : Region} :
    r ∈ callRegions swapCode [.loc l, .loc k] ↔ r = ⟨l, 1, 64, true⟩ ∨ r = ⟨k, 1, 64, true⟩ := by
  rw [swap_callRegions]
  simp

variable (l k : Loc) (old : Loc → Int)

/-- The witness's allocated words encode the two original logical integers. -/
theorem swapWitnessState_words :
    Word64At (swapWitnessState l k old) 0x80001000#64 (BitVec.ofInt 64 (old l)) ∧
      Word64At (swapWitnessState l k old) 0x80001008#64 (BitVec.ofInt 64 (old k)) := by
  exact ⟨(word64At_write64State swapWitnessCodeState _ _).write64State _ (by decide +kernel),
    word64At_write64State _ _ _⟩

/-- Every actual assembled byte survives allocating the two distant data words. -/
theorem swapWitness_codeByte (i : Nat) (byte : UInt8)
    (hi : swapWitnessImage.bytes[i]? = some byte) :
    (swapWitnessState l k old).mem.get? (0x80000000 + i) = some (BitVec.ofNat 8 byte.toNat) := by
  have hib : i < 24 := by
    have hib := (List.getElem?_eq_some_iff.mp hi).1
    rwa [swapWitnessImage_length] at hib
  have ha : 0x80000000 + i < (0x80001000#64).toNat := by
    change 0x80000000 + i < 0x80001000
    omega
  have hb : 0x80000000 + i < (0x80001008#64).toNat := by
    change 0x80000000 + i < 0x80001008
    omega
  rw [swapWitnessState, write64State_get?_outside _ _ _ _ (Or.inl hb),
    write64State_get?_outside _ _ _ _ (Or.inl ha)]
  exact witnessImageBytes_get _ _ _ _ _ hi

/-- Every address beyond the complete assembled image is outside that image. -/
theorem swapWitness_not_imageByte (address : Nat) (hout : 0x80000000 + 24 ≤ address) :
    ¬ imageByte (witnessPlacement l) swapCode address := by
  rintro ⟨image, himage, hspan⟩
  cases swapWitness_image_of_assemble himage
  change 0x80000000 ≤ address ∧ address < 0x80000000 + swapWitnessImage.bytes.length at hspan
  rw [swapWitnessImage_length] at hspan
  omega

/-- Every address beyond the complete assembled image is outside executable text. -/
theorem swapWitness_not_codeRange (address : BitVec 64) (hout : 0x80000000 + 24 ≤ address.toNat) :
    ¬ codeRange (witnessPlacement l) swapCode address := by
  rintro ⟨image, himage, hspan⟩
  cases swapWitness_image_of_assemble himage
  have hlength : swapWitnessImage.textLen = 20 := rfl
  change 0x80000000 ≤ address.toNat ∧ address.toNat < 0x80000000 + swapWitnessImage.textLen at hspan
  rw [hlength] at hspan
  omega

/-- The exchange has no import addresses to assign. -/
theorem swapWitness_importPlacement :
    importPlacement (witnessPlacement l) swapCode [.loc l, .loc k] := by
  simp [importPlacement, swapCode, swapSig]

/-- The zero-stack-bound exchange requires no stack bytes, while sp itself is mapped and aligned. -/
theorem swapWitness_stackPlacement :
    stackPlacement (witnessPlacement l) swapCode [.loc l, .loc k] (swapWitnessState l k old) := by
  refine ⟨0x80004000#64, ?_, ?_, ?_, ?_, ?_⟩
  · simp [witnessRegisters, get?_insert]
  · decide +kernel
  · simp [swapCode, swapSig]
  · change InUserRam 0x80004000#64 0
    unfold InUserRam
    decide +kernel
  · intro address hstack
    simp only [stackByte, swapCode, swapSig, inSpan, Nat.sub_zero, Nat.add_zero] at hstack
    omega

/-- Direct trap vectors are outside text and distinct from the ordinary return target. -/
theorem swapWitness_machineConfiguration :
    machineConfiguration (witnessPlacement l) swapCode (swapWitnessState l k old) := by
  refine ⟨swapWitnessState_config l k old, ?_⟩
  have hmt : (swapWitnessState l k old).regs.get? Register.mtvec = some 0x80003000#64 := by
    simp [witnessRegisters, get?_insert]
  have hst : (swapWitnessState l k old).regs.get? Register.stvec = some 0x80003000#64 := by
    simp [witnessRegisters]
  intro value hv
  simp only [hmt, hst, List.mem_cons, List.not_mem_nil, or_false, or_self] at hv
  subst value
  refine ⟨0x80003000#64, rfl, swapWitness_not_codeRange l 0x80003000#64 (by decide +kernel), ?_, ?_⟩
  · change 0x80003000#64 ≠ 0x80002000#64
    decide +kernel
  · simp [swapCode, swapSig]

variable (hne : l ≠ k)

include hne

/-- The witness places its two logical cells into disjoint aligned physical doublewords. -/
theorem swapWitness_footprintPlacement :
    footprintPlacement (witnessPlacement l) swapCode [.loc l, .loc k] := by
  constructor
  · intro r hr
    rw [swap_callRegions_mem] at hr
    rcases hr with rfl | rfl
    all_goals simp [witnessPlacement, Ne.symm hne, InUserRam]
  · intro r hr q hq hneRegion
    rw [swap_callRegions_mem] at hr hq
    rcases hr with rfl | rfl <;> rcases hq with rfl | rfl
    · exact (hneRegion rfl).elim
    · simp [witnessPlacement, Ne.symm hne, disjointSpans]
    · simp [witnessPlacement, Ne.symm hne, disjointSpans]
    · exact (hneRegion rfl).elim

/-- The witness realizes every integer in the original two-cell fragment. -/
theorem swapWitness_footprintContents
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true) :
    footprintContents (witnessPlacement l) swapCode [.loc l, .loc k]
      (integerHeap {l, k} old) (swapWitnessState l k old) := by
  have hw := swapWitnessState_words l k old
  apply swap_footprintContents _ _ l k old hne hl hk
  · simpa [witnessPlacement] using hw.1
  · simpa [witnessPlacement, Ne.symm hne] using hw.2

/-- The witness binds exactly the two declared pointer-argument registers. -/
theorem swapWitness_argumentBindings :
    argumentBindings (witnessPlacement l) [.loc l, .loc k] (swapWitnessState l k old) := by
  intro i v hv
  have hib : i < 2 := by
    have hib := (List.getElem?_eq_some_iff.mp hv).1
    simpa using hib
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
    subst v
    simp [argumentRegister, argumentWord, witnessRegisters, witnessPlacement, get?_insert]
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hv
    subst v
    simp [argumentRegister, argumentWord, witnessRegisters, witnessPlacement, Ne.symm hne,
      get?_insert]

/-- The complete assembled exchange image is installed and separated from its owned data. -/
theorem swapWitness_codeImage :
    codeImage (witnessPlacement l) swapCode [.loc l, .loc k] (swapWitnessState l k old) := by
  refine ⟨swapWitnessImage, assemble_swapWitnessImage, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [swapWitnessImage_length]
    change InUserRam 0x80000000#64 24
    unfold InUserRam
    decide +kernel
  · change (0x80000000#64).toNat % 8 = 0
    decide +kernel
  · decide +kernel
  · simp [pc, witnessRegisters,
      witnessPlacement, get?_insert, swapWitnessImage_entry]
  · intro i byte hi
    change swapWitnessImage.bytes[i]? = some byte at hi
    exact swapWitness_codeByte l k old i byte hi
  · intro r hr
    rw [swap_callRegions_mem] at hr
    rcases hr with rfl | rfl <;>
      simp [witnessPlacement, Ne.symm hne, swapWitnessImage_length, disjointSpans]

/-- Every address above both allocated words is outside the complete footprint. -/
theorem swapWitness_not_footprintByte (address : Nat)
    (hout : 0x80001010 ≤ address) :
    ¬ footprintByte (witnessPlacement l) swapCode [.loc l, .loc k] address := by
  rintro ⟨r, hr, hspan⟩
  rw [swap_callRegions_mem] at hr
  rcases hr with rfl | rfl
  all_goals { simp [witnessPlacement, Ne.symm hne, inSpan] at hspan; omega }

/-- The witness's return target is aligned and separate from the full image and footprint. -/
theorem swapWitness_returnPlacement :
    returnPlacement (witnessPlacement l) swapCode [.loc l, .loc k] (swapWitnessState l k old) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [witnessRegisters, witnessPlacement, get?_insert]
  · change (0x80002000#64).toNat % 4 = 0
    decide +kernel
  · exact swapWitness_not_imageByte l 0x80002000 (by decide +kernel)
  · exact swapWitness_not_footprintByte l k hne 0x80002000 (by decide +kernel)
  · simp [swapCode, swapSig]

/-- The explicit machine and placement satisfy every RV entry facet for the exchange. -/
theorem swapWitness_compatible
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true) :
    RVCompat (witnessPlacement l) swapCode [.loc l, .loc k]
      (integerHeap {l, k} old) (swapWitnessState l k old) := by
  exact ⟨swapWitness_footprintPlacement l k hne,
    swapWitness_footprintContents l k old hne hl hk,
    swapWitness_argumentBindings l k old hne, swapWitness_codeImage l k old hne,
    swapWitness_importPlacement l k, swapWitness_returnPlacement l k old hne,
    swapWitness_stackPlacement l k old, swapWitness_machineConfiguration l k old⟩

/-- Every pair of distinct cells whose two values fit in 64 bits has a compatible entry state. -/
theorem swap_compat_exists
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true) :
    ∃ ι s, RVCompat ι swapCode [.loc l, .loc k] (integerHeap {l, k} old) s :=
  ⟨witnessPlacement l, swapWitnessState l k old, swapWitness_compatible l k old hne hl hk⟩

end MetrologyAsm
