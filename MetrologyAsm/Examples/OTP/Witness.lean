import MetrologyAsm.Examples.OTP.ImageBridge
import MetrologyAsm.Examples.Support

/-! # A genuine compatible entry for each valid byte message and private pad heap -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm Sail

variable (message : Int) (pad : Loc) (byte : Int)

/-- Distinct mapped code, pad, return, trap, stack and callback addresses. -/
abbrev otpWitnessPlacement : Placement := witnessPlacement pad

/-- The sole logical pad location has the designated aligned physical byte address. -/
@[simp] theorem otpWitnessPlacement_pad :
    (otpWitnessPlacement pad).addr pad = 0x80001000#64 := by
  simp [witnessPlacement]

/-- Install the argument registers, private pad byte and actual relocated compiler image. -/
noncomputable def otpWitnessState : Mach :=
  { witnessRegisters with
    regs := (witnessRegisters.regs.insert .x10 (BitVec.ofInt 64 message)).insert .x11 0x80001000#64
    mem := witnessImageBytes (relocatedBytes (otpWitnessPlacement pad) otpImage) 0x80000000
      (witnessRegisters.mem.insert 0x80001000 (BitVec.ofInt 8 byte)) }

/-- The installed relocated image has its certified eighty-eight-byte extent. -/
theorem relocatedBytes_otp_length (ι : Placement) : (relocatedBytes ι otpImage).length = 88 := by
  rw [relocatedBytes_otp]
  simp

set_option maxRecDepth 100000 in
/-- Installing the arguments and bytes preserves the complete open user-mode profile. -/
theorem otpWitnessState_config :
    UserConfig (otpWitnessState message pad byte) :=
  ((witnessRegisters_config.insert .x10 (BitVec.ofInt 64 message) trivial).insert
    .x11 0x80001000#64 trivial).of_regs_eq rfl

/-- Installing the code image preserves the initialized private pad byte. -/
theorem otpWitnessState_byte :
    (otpWitnessState message pad byte).mem.get? 0x80001000 = some (BitVec.ofInt 8 byte) := by
  change (witnessImageBytes _ _ _).get? _ = _
  rw [witnessImageBytes_get_outside _ _ _ _ (by rw [relocatedBytes_otp_length]; decide +kernel)]
  simp

/-- The single logical byte region has a mapped, aligned, nonzero physical placement. -/
theorem otpWitness_footprintPlacement :
    footprintPlacement (otpWitnessPlacement pad) otpCode (otpArgs message pad) := by
  constructor
  · intro r hr
    simp only [otp_regions, List.mem_singleton] at hr
    subst r
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [padRegion]
    · simp [padRegion]
    · simp only [padRegion, otpWitnessPlacement_pad, Nat.reduceDiv, Nat.mul_one]
      unfold InUserRam
      decide +kernel
    · intro i hi
      obtain rfl : i = 0 := by change i < 1 at hi; omega
      simp [padRegion]
  · intro r hr q hq hne
    simp only [otp_regions, List.mem_singleton] at hr hq
    exact (hne (hr.trans hq.symm)).elim

/-- The physical pad realizes its valid logical singleton byte heap. -/
theorem otpWitness_footprintContents
    (hm : inRange false 64 message = true) (hb : inRange false 8 byte = true) :
    footprintContents (otpWitnessPlacement pad) otpCode (otpArgs message pad)
      (padHeap pad byte) (otpWitnessState message pad byte) := by
  refine ⟨otp_validFragment message pad byte hm hb, ?_⟩
  intro r hr i hi
  simp only [otp_regions, List.mem_singleton] at hr
  subst r
  obtain rfl : i = 0 := by change i < 1 at hi; omega
  refine ⟨byte, by simp [padRegion], hb, ?_⟩
  have hw := (wordAt8_iff (otpWitnessState message pad byte) 0x80001000#64
    (BitVec.ofInt 8 byte)).mpr (otpWitnessState_byte message pad byte)
  simpa [padRegion] using hw

/-- The witness exposes the message and pad pointer in the two psABI argument registers. -/
theorem otpWitness_argumentBindings :
    argumentBindings (otpWitnessPlacement pad) (otpArgs message pad)
      (otpWitnessState message pad byte) := by
  intro i v hv
  cases i with
  | zero =>
    cases hv
    simp [argumentRegister, argumentWord, otpWitnessState, Std.ExtDHashMap.get?_insert]
  | succ i =>
    cases i with
    | zero =>
      cases hv
      simp [argumentRegister, argumentWord, otpWitnessState]
    | succ i => simp [otpArgs] at hv

/-- The complete actual relocated compiler image is installed at its aligned entry address. -/
theorem otpWitness_codeImage :
    codeImage (otpWitnessPlacement pad) otpCode (otpArgs message pad)
      (otpWitnessState message pad byte) := by
  refine ⟨otpImage, assemble_otpImage, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [otpImage_length]
    change InUserRam 0x80000000#64 88
    unfold InUserRam
    decide +kernel
  · change (0x80000000#64).toNat % 8 = 0
    decide +kernel
  · rw [otpImage_entry, otpImage_textLen]
    decide +kernel
  · simp [pc, otpWitnessState, witnessPlacement, witnessRegisters,
      otpImage_entry, Std.ExtDHashMap.get?_insert]
  · intro i value hi
    exact witnessImageBytes_get _ _ _ _ _ hi
  · intro r hr
    simp only [otp_regions, List.mem_singleton] at hr
    subst r
    simp only [padRegion, otpImage_length, otpWitnessPlacement_pad, Nat.reduceDiv, Nat.mul_one]
    change disjointSpans 0x80000000 88 0x80001000 1
    unfold disjointSpans
    decide +kernel

/-- Any address above the complete image is not an installed source byte. -/
theorem otpWitness_not_imageByte (address : Nat)
    (hout : 0x80000000 + 88 ≤ address) : ¬imageByte (otpWitnessPlacement pad) otpCode address := by
  rw [imageByte_otp]
  change ¬(0x80000000 ≤ address ∧ address < 0x80000000 + 88)
  omega

/-- An address above the complete image cannot be an executable source instruction. -/
theorem otpWitness_not_codeRange (address : BitVec 64)
    (hout : 0x80000000 + 88 ≤ address.toNat) :
    ¬codeRange (otpWitnessPlacement pad) otpCode address :=
  fun h => otpWitness_not_imageByte pad address.toNat hout (imageByte_of_codeRange _ _ h)

/-- An address distinct from the pad address is outside the one-byte footprint. -/
theorem otpWitness_not_footprintByte (address : Nat)
    (hne : address ≠ 0x80001000) :
    ¬footprintByte (otpWitnessPlacement pad) otpCode (otpArgs message pad) address := by
  simpa [footprintByte_otp] using hne

/-- The only import of the compiled OTP is randombytes with its fixed signature. -/
theorem otpCode_import {name : String} {sig : CallSig} (h : (name, sig) ∈ otpCode.sig.imports) :
    name = "randombytes" ∧ sig = ⟨[.array 8 (.arg 1), .uint 64], .unit⟩ := by
  simpa [otpCode, otpSig] using h

/-- The single randombytes import is aligned and separated from code and pad. -/
theorem otpWitness_importPlacement :
    importPlacement (otpWitnessPlacement pad) otpCode (otpArgs message pad) := by
  constructor
  · intro name sig hmem
    obtain ⟨rfl, rfl⟩ := otpCode_import hmem
    refine ⟨otpWitness_not_imageByte pad _ ?_,
      otpWitness_not_footprintByte message pad _ ?_, ?_⟩
    · change 0x80000000 + 88 ≤ 0x80005000
      decide +kernel
    · change 0x80005000 ≠ 0x80001000
      decide +kernel
    · change (0x80005000#64).toNat % 4 = 0
      decide +kernel
  · intro n sig m ty hn hm hne
    exact (hne ((otpCode_import hn).1.trans (otpCode_import hm).1.symm)).elim

/-- The original caller's return address is an aligned external stop distinct from randombytes. -/
theorem otpWitness_returnPlacement :
    returnPlacement (otpWitnessPlacement pad) otpCode (otpArgs message pad)
      (otpWitnessState message pad byte) := by
  refine ⟨?_, ?_, otpWitness_not_imageByte pad _ ?_,
    otpWitness_not_footprintByte message pad _ ?_, ?_⟩
  · simp [otpWitnessState, witnessPlacement, witnessRegisters,
      Std.ExtDHashMap.get?_insert]
  · change (0x80002000#64).toNat % 4 = 0
    decide +kernel
  · change 0x80000000 + 88 ≤ 0x80002000
    decide +kernel
  · change 0x80002000 ≠ 0x80001000
    decide +kernel
  · intro name sig _
    change 0x80002000#64 ≠ 0x80005000#64
    decide +kernel

/-- The compiler's thirty-two-byte scratch interval is mapped and separated from all stops/data. -/
theorem otpWitness_stackPlacement :
    stackPlacement (otpWitnessPlacement pad) otpCode (otpArgs message pad)
      (otpWitnessState message pad byte) := by
  refine ⟨0x80004000#64, ?_, by decide +kernel, ?_, ?_, ?_⟩
  · simp [otpWitnessState, witnessRegisters, Std.ExtDHashMap.get?_insert]
  · change 32 ≤ (0x80004000#64).toNat
    decide +kernel
  · change InUserRam 0x80003fe0#64 32
    unfold InUserRam
    decide +kernel
  · intro address hs
    change 0x80003fe0 ≤ address ∧ address < 0x80004000 at hs
    refine ⟨otpWitness_not_footprintByte message pad _ (by omega),
      otpWitness_not_imageByte pad _ (by omega), ?_, ?_⟩
    · change address ≠ 0x80002000
      omega
    · intro name sig _
      change address ≠ 0x80005000
      omega

/-- The direct trap vectors are outside executable code and both ordinary external stops. -/
theorem otpWitness_machineConfiguration :
    machineConfiguration (otpWitnessPlacement pad) otpCode (otpWitnessState message pad byte) := by
  refine ⟨otpWitnessState_config message pad byte, ?_⟩
  have hmt : (otpWitnessState message pad byte).regs.get? .mtvec = some 0x80003000#64 := by
    simp [otpWitnessState, witnessRegisters, Std.ExtDHashMap.get?_insert]
  have hst : (otpWitnessState message pad byte).regs.get? .stvec = some 0x80003000#64 := by
    simp [otpWitnessState, witnessRegisters, Std.ExtDHashMap.get?_insert]
  intro value hv
  simp only [hmt, hst, List.mem_cons, List.not_mem_nil, or_false, or_self] at hv
  subst value
  refine ⟨0x80003000#64, rfl, otpWitness_not_codeRange pad _ (by decide +kernel), ?_, ?_⟩
  · change 0x80003000#64 ≠ 0x80002000#64
    decide +kernel
  · intro name sig _
    change 0x80003000#64 ≠ 0x80005000#64
    decide +kernel

/-- Every valid message/pad fragment has a genuine compatible machine with actual source bytes. -/
theorem otp_compat_exists
    (hm : inRange false 64 message = true) (hb : inRange false 8 byte = true) :
    ∃ ι s, RVCompat ι otpCode (otpArgs message pad) (padHeap pad byte) s := by
  exact ⟨otpWitnessPlacement pad, otpWitnessState message pad byte,
    otpWitness_footprintPlacement message pad, otpWitness_footprintContents message pad byte hm hb,
    otpWitness_argumentBindings message pad byte, otpWitness_codeImage message pad byte,
    otpWitness_importPlacement message pad, otpWitness_returnPlacement message pad byte,
    otpWitness_stackPlacement message pad byte, otpWitness_machineConfiguration message pad byte⟩

end MetrologyAsm.OTP
