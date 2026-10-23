import MetrologyAsm.SwapBoundary
import MetrologyAsm.ConfigWitness

/-! # A concrete compatible entry machine for the exchange fragment -/

set_option maxRecDepth 100000

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions
open Sail.ConcurrencyInterfaceV1

/-- The actual assembled exchange image, with an unreachable fallback for the total definition. -/
def swapWitnessImage : Image :=
  (assemble swapAsm).toOption.getD ⟨[], 0, 0, 0, [], [], []⟩

/-- The concrete witness uses exactly the assembled source image. -/
theorem assemble_swapWitnessImage : assemble swapAsm = .ok swapWitnessImage := by
  rfl

/-- The witness's full image contains its twenty text bytes and four alignment bytes. -/
theorem swapWitnessImage_length : swapWitnessImage.bytes.length = 24 := by
  rfl

/-- The exchange begins at the first byte of its executable image. -/
theorem swapWitnessImage_entry : swapWitnessImage.entry = 0 := by
  rfl

/-- Install consecutive image bytes into a finite Sail byte memory. -/
def witnessImageBytes : List UInt8 → Nat → Std.ExtHashMap Nat (BitVec 8) →
    Std.ExtHashMap Nat (BitVec 8)
  | [], _, mem => mem
  | byte :: bytes, base, mem =>
    (witnessImageBytes bytes (base + 1) mem).insert base (BitVec.ofNat 8 byte.toNat)

/-- Every installed image byte is available at its consecutive physical address. -/
theorem witnessImageBytes_get (bytes : List UInt8) (base : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (i : Nat) (byte : UInt8)
    (hi : bytes[i]? = some byte) :
    (witnessImageBytes bytes base mem).get? (base + i) = some (BitVec.ofNat 8 byte.toNat) := by
  induction bytes generalizing base i with
  | nil => simp at hi
  | cons head bytes ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst byte
      simp [witnessImageBytes]
    | succ i =>
      have hne : base ≠ base + (i + 1) := by omega
      have htail := ih (base + 1) i (by simpa using hi)
      simpa [witnessImageBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert,
        hne, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail

/-- A concrete aligned placement for two distinct logical cells. -/
def swapWitnessPlacement (l : Loc) : Placement where
  addr k := if k = l then 0x80001000#64 else 0x80001008#64
  codeBase := 0x80000000#64
  importAddr _ := 0x80005000#64
  retAddr := 0x80002000#64

/-- The witness's active register state keeps the formal profile and installs the ABI bindings. -/
noncomputable def swapWitnessRegisters : Mach :=
  let s := profileWitness
  let regs := s.regs.insert Register.PC 0x80000000#64
  let regs := regs.insert .x1 0x80002000#64
  let regs := regs.insert .x2 0x80004000#64
  let regs := regs.insert .x10 0x80001000#64
  let regs := regs.insert .x11 0x80001008#64
  let regs := regs.insert .mtvec 0x80003000#64
  let regs := regs.insert .stvec 0x80003000#64
  { s with regs }

/-- The assembled image is installed before allocating the two disjoint data words. -/
noncomputable def swapWitnessCodeState : Mach :=
  { swapWitnessRegisters with
    mem := witnessImageBytes swapWitnessImage.bytes 0x80000000 swapWitnessRegisters.mem }

/-- A concrete raw entry machine stores the two logical integers in disjoint RAM doublewords. -/
noncomputable def swapWitnessState (l k : Loc) (old : Loc → Int) : Mach :=
  write64State (write64State swapWitnessCodeState 0x80001000#64 (BitVec.ofInt 64 (old l)))
    0x80001008#64 (BitVec.ofInt 64 (old k))

/-- The witness's register installation satisfies the complete open user profile. -/
theorem swapWitnessRegisters_config : UserConfig swapWitnessRegisters := by
  exact (((((((profileWitness_config.insert .PC _ trivial).insert .x1 _ trivial).insert
    .x2 _ trivial).insert .x10 _ trivial).insert .x11 _ trivial).insert .mtvec _
    (by simp only [userRegPolicy]; decide +kernel)).insert .stvec _
    (by simp only [userRegPolicy]; decide +kernel))

/-- Installing the code bytes preserves the user profile. -/
theorem swapWitnessCodeState_config : UserConfig swapWitnessCodeState :=
  swapWitnessRegisters_config.of_regs_eq rfl

/-- Every logical integer pair has a raw witness satisfying the user profile. -/
theorem swapWitnessState_config (l k : Loc) (old : Loc → Int) :
    UserConfig (swapWitnessState l k old) :=
  (swapWitnessCodeState_config.write64State _ _).write64State _ _

/-- The witness's allocated words encode the two original logical integers. -/
theorem swapWitnessState_words (l k : Loc) (old : Loc → Int) :
    Word64At (swapWitnessState l k old) 0x80001000#64 (BitVec.ofInt 64 (old l)) ∧
      Word64At (swapWitnessState l k old) 0x80001008#64 (BitVec.ofInt 64 (old k)) := by
  exact ⟨(word64At_write64State swapWitnessCodeState _ _).write64State _ (by decide +kernel),
    word64At_write64State _ _ _⟩

/-- The witness places its two logical cells into disjoint aligned physical doublewords. -/
theorem swapWitness_footprintPlacement (l k : Loc) (hne : l ≠ k) :
    footprintPlacement (swapWitnessPlacement l) swapCode [.loc l, .loc k] := by
  constructor
  · intro r hr
    rw [swap_callRegions] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals simp [swapWitnessPlacement, Ne.symm hne, InUserRam]
  · intro r hr q hq hneRegion
    rw [swap_callRegions] at hr hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hq
    rcases hr with rfl | rfl <;> rcases hq with rfl | rfl
    · exact (hneRegion rfl).elim
    · simp [swapWitnessPlacement, Ne.symm hne, disjointSpans]
    · simp [swapWitnessPlacement, Ne.symm hne, disjointSpans]
    · exact (hneRegion rfl).elim

/-- The witness realizes every integer in the original two-cell fragment. -/
theorem swapWitness_footprintContents (l k : Loc) (old : Loc → Int) (hne : l ≠ k)
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true) :
    footprintContents (swapWitnessPlacement l) swapCode [.loc l, .loc k]
      (integerHeap {l, k} old) (swapWitnessState l k old) := by
  have hw := swapWitnessState_words l k old
  apply swap_footprintContents _ _ l k old hne hl hk
  · simpa [swapWitnessPlacement] using hw.1
  · simpa [swapWitnessPlacement, Ne.symm hne] using hw.2

/-- The witness binds exactly the two declared pointer-argument registers. -/
theorem swapWitness_argumentBindings (l k : Loc) (old : Loc → Int) (hne : l ≠ k) :
    argumentBindings (swapWitnessPlacement l) [.loc l, .loc k] (swapWitnessState l k old) := by
  intro i v hv
  have hib : i < 2 := by
    have hib := (List.getElem?_eq_some_iff.mp hv).1
    simpa using hib
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
    subst v
    simp [argumentRegister, argumentWord, swapWitnessState, swapWitnessCodeState,
      swapWitnessRegisters, swapWitnessPlacement, Std.ExtDHashMap.get?_insert]
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hv
    subst v
    simp [argumentRegister, argumentWord, swapWitnessState, swapWitnessCodeState,
      swapWitnessRegisters, swapWitnessPlacement, Ne.symm hne, Std.ExtDHashMap.get?_insert]

/-- Every actual assembled byte survives allocating the two distant data words. -/
theorem swapWitness_codeByte (l k : Loc) (old : Loc → Int) (i : Nat) (byte : UInt8)
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

/-- The complete assembled exchange image is installed and separated from its owned data. -/
theorem swapWitness_codeImage (l k : Loc) (old : Loc → Int) (hne : l ≠ k) :
    codeImage (swapWitnessPlacement l) swapCode [.loc l, .loc k] (swapWitnessState l k old) := by
  refine ⟨swapWitnessImage, assemble_swapWitnessImage, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [swapWitnessImage_length]
    change InUserRam 0x80000000#64 24
    unfold InUserRam
    decide +kernel
  · change (0x80000000#64).toNat % 8 = 0
    decide +kernel
  · decide +kernel
  · simp [pc, swapWitnessState, swapWitnessCodeState, swapWitnessRegisters,
      swapWitnessPlacement, Std.ExtDHashMap.get?_insert, swapWitnessImage_entry]
  · intro i byte hi
    change swapWitnessImage.bytes[i]? = some byte at hi
    exact swapWitness_codeByte l k old i byte hi
  · intro r hr
    rw [swap_callRegions] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      simp [swapWitnessPlacement, Ne.symm hne, swapWitnessImage_length, disjointSpans]

/-- Every address beyond the complete assembled image is outside that image. -/
theorem swapWitness_not_imageByte (l : Loc) (address : Nat)
    (hout : 0x80000000 + 24 ≤ address) :
    ¬ imageByte (swapWitnessPlacement l) swapCode address := by
  rintro ⟨image, himage, hspan⟩
  change assemble swapAsm = .ok image at himage
  rw [assemble_swapWitnessImage] at himage
  cases himage
  change 0x80000000 ≤ address ∧ address < 0x80000000 + swapWitnessImage.bytes.length at hspan
  rw [swapWitnessImage_length] at hspan
  omega

/-- Every address beyond the complete assembled image is outside executable text. -/
theorem swapWitness_not_codeRange (l : Loc) (address : BitVec 64)
    (hout : 0x80000000 + 24 ≤ address.toNat) :
    ¬ codeRange (swapWitnessPlacement l) swapCode address := by
  rintro ⟨image, himage, hspan⟩
  change assemble swapAsm = .ok image at himage
  rw [assemble_swapWitnessImage] at himage
  cases himage
  have hlength : swapWitnessImage.textLen = 20 := rfl
  change 0x80000000 ≤ address.toNat ∧ address.toNat < 0x80000000 + swapWitnessImage.textLen at hspan
  rw [hlength] at hspan
  omega

/-- Every address above both allocated words is outside the complete footprint. -/
theorem swapWitness_not_footprintByte (l k : Loc) (hne : l ≠ k) (address : Nat)
    (hout : 0x80001010 ≤ address) :
    ¬ footprintByte (swapWitnessPlacement l) swapCode [.loc l, .loc k] address := by
  rintro ⟨r, hr, hspan⟩
  rw [swap_callRegions] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  all_goals { simp [swapWitnessPlacement, Ne.symm hne, inSpan] at hspan; omega }

/-- The exchange has no import addresses to assign. -/
theorem swapWitness_importPlacement (l k : Loc) :
    importPlacement (swapWitnessPlacement l) swapCode [.loc l, .loc k] := by
  simp [importPlacement, swapCode, swapSig]

/-- The witness's return target is aligned and separate from the full image and footprint. -/
theorem swapWitness_returnPlacement (l k : Loc) (old : Loc → Int) (hne : l ≠ k) :
    returnPlacement (swapWitnessPlacement l) swapCode [.loc l, .loc k]
      (swapWitnessState l k old) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [swapWitnessState, swapWitnessCodeState, swapWitnessRegisters,
      swapWitnessPlacement, Std.ExtDHashMap.get?_insert]
  · change (0x80002000#64).toNat % 4 = 0
    decide +kernel
  · exact swapWitness_not_imageByte l 0x80002000 (by decide +kernel)
  · exact swapWitness_not_footprintByte l k hne 0x80002000 (by decide +kernel)
  · simp [swapCode, swapSig]

/-- The zero-stack-bound exchange requires no stack bytes, while sp itself is mapped and aligned. -/
theorem swapWitness_stackPlacement (l k : Loc) (old : Loc → Int) :
    stackPlacement (swapWitnessPlacement l) swapCode [.loc l, .loc k]
      (swapWitnessState l k old) := by
  refine ⟨0x80004000#64, ?_, ?_, ?_, ?_, ?_⟩
  · simp [swapWitnessState, swapWitnessCodeState, swapWitnessRegisters,
      Std.ExtDHashMap.get?_insert]
  · decide +kernel
  · simp [swapCode, swapSig]
  · change InUserRam 0x80004000#64 0
    unfold InUserRam
    decide +kernel
  · intro address hstack
    simp only [stackByte, swapCode, swapSig, inSpan, Nat.sub_zero, Nat.add_zero] at hstack
    omega

/-- Direct trap vectors are outside text and distinct from the ordinary return target. -/
theorem swapWitness_machineConfiguration (l k : Loc) (old : Loc → Int) :
    machineConfiguration (swapWitnessPlacement l) swapCode (swapWitnessState l k old) := by
  refine ⟨swapWitnessState_config l k old, ?_⟩
  have hmt : (swapWitnessState l k old).regs.get? Register.mtvec = some 0x80003000#64 := by
    simp [swapWitnessState, swapWitnessCodeState, swapWitnessRegisters,
      Std.ExtDHashMap.get?_insert]
  have hst : (swapWitnessState l k old).regs.get? Register.stvec = some 0x80003000#64 := by
    simp [swapWitnessState, swapWitnessCodeState, swapWitnessRegisters]
  intro value hv
  simp only [hmt, hst, List.mem_cons, List.not_mem_nil, or_false, or_self] at hv
  subst value
  refine ⟨0x80003000#64, rfl, swapWitness_not_codeRange l 0x80003000#64 (by decide +kernel), ?_, ?_⟩
  · change 0x80003000#64 ≠ 0x80002000#64
    decide +kernel
  · simp [swapCode, swapSig]

/-- The explicit machine and placement satisfy every RV entry facet for the exchange. -/
theorem swapWitness_compatible (l k : Loc) (old : Loc → Int) (hne : l ≠ k)
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true) :
    RVCompat (swapWitnessPlacement l) swapCode [.loc l, .loc k]
      (integerHeap {l, k} old) (swapWitnessState l k old) := by
  exact ⟨swapWitness_footprintPlacement l k hne,
    swapWitness_footprintContents l k old hne hl hk,
    swapWitness_argumentBindings l k old hne, swapWitness_codeImage l k old hne,
    swapWitness_importPlacement l k, swapWitness_returnPlacement l k old hne,
    swapWitness_stackPlacement l k old, swapWitness_machineConfiguration l k old⟩

/-- The exchange specification has a genuine compatible entry state for every signed input pair. -/
theorem swap_compat_exists (l k : Loc) (old : Loc → Int) (hne : l ≠ k)
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true) :
    ∃ ι s, RVCompat ι swapCode [.loc l, .loc k] (integerHeap {l, k} old) s :=
  ⟨swapWitnessPlacement l, swapWitnessState l k old, swapWitness_compatible l k old hne hl hk⟩

end MetrologyAsm
