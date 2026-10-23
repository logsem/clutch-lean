import MetrologyAsm.Examples.OTP.Responses
import MetrologyAsm.Examples.OTP.Frames

/-! # Decoding the actual OTP callback and final ciphertext observations -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm Sail

/-- The original one-cell pointer decodes to its logical pad location. -/
theorem decodePointer_pad (ι : Placement) (message : Int) (pad : Loc) :
    decodePointer ι otpCode (otpArgs message pad) (ι.addr pad) = some (.loc pad) := by
  simp [decodePointer, footprintLocations, pointerWord, padRegion]

/-- The allocated byte determines exactly the owned singleton fragment. -/
theorem decodeF_padHeap (ι : Placement) (s : Mach) (message : Int) (pad : Loc) (byte : Int)
    (hrange : inRange false 8 byte = true)
    (hbyte : s.mem.get? (ι.addr pad).toNat = some (BitVec.ofInt 8 byte)) :
    decodeF ι otpCode (otpArgs message pad) {pad} s = some (padHeap pad byte) := by
  apply decodeF_integerHeap
  intro l hl
  have heq : l = pad := by simpa using hl
  subst l
  refine ⟨padRegion pad, ?_, ?_⟩
  · simp
  · exact decodeCell_unsigned8 ι (padRegion pad) pad s byte rfl rfl hrange hbyte

/-- A compatible singleton byte heap is represented by that byte at its physical pad address. -/
theorem byte_of_footprintContents (ι : Placement) (s : Mach) (message : Int) (pad : Loc)
    (byte : Int) (h : footprintContents ι otpCode (otpArgs message pad) (padHeap pad byte) s) :
    s.mem.get? (ι.addr pad).toNat = some (BitVec.ofInt 8 byte) := by
  obtain ⟨value, hv, _, hw⟩ := h.2 (padRegion pad) (by simp) 0 (by simp [padRegion])
  have heq : value = byte := by simpa [padRegion] using hv.symm
  subst value
  apply (wordAt8_iff _ _ _).mp
  simpa [padRegion] using hw

/-- The constant callback length has its declared unsigned scalar decoding. -/
theorem decodeValue_one (ι : Placement) (message : Int) (pad : Loc) :
    decodeValue ι otpCode (otpArgs message pad) (.uint 64) 1#64 = some (.int 1) := rfl

/-- The actual external address, registers and byte memory decode to the declared callback call. -/
theorem observe_call (ι : Placement) (s : Mach) (message : Int) (pad : Loc) (byte : Int)
    (hpc : pc s = some (ι.importAddr "randombytes"))
    (hne : ι.retAddr ≠ ι.importAddr "randombytes")
    (ha0 : s.regs.get? .x10 = some (ι.addr pad)) (ha1 : s.regs.get? .x11 = some 1#64)
    (hrange : inRange false 8 byte = true)
    (hbyte : s.mem.get? (ι.addr pad).toNat = some (BitVec.ofInt 8 byte)) :
    observe ι otpCode (otpArgs message pad) {pad} s =
      some (.call "randombytes" [.loc pad, .int 1] (padHeap pad byte)) := by
  have hheap := decodeF_padHeap ι s message pad byte hrange hbyte
  have himports : otpCode.sig.imports =
      [("randombytes", ⟨[.array 8 (.arg 1), .uint 64], .unit⟩)] := rfl
  have hpointer : decodeValue ι otpCode (otpArgs message pad) (.array 8 (.arg 1))
      (ι.addr pad) = some (.loc pad) := decodePointer_pad ι message pad
  apply observe_call_of_reads ι otpCode (otpArgs message pad) {pad} s "randombytes"
    ⟨[.array 8 (.arg 1), .uint 64], .unit⟩ [.loc pad, .int 1] (padHeap pad byte)
    hpc hne hheap himports
  simp [argumentRegister, ha0, ha1, hpointer, decodeValue_one]

/-- A representable unsigned result decodes exactly at the original caller's return address. -/
theorem observe_ret (ι : Placement) (s : Mach) (message : Int) (pad : Loc) (byte result : Int)
    (hpc : pc s = some ι.retAddr)
    (ha0 : s.regs.get? .x10 = some (BitVec.ofInt 64 result))
    (hrange : inRange false 8 byte = true) (hresult : inRange false 64 result = true)
    (hbyte : s.mem.get? (ι.addr pad).toNat = some (BitVec.ofInt 8 byte)) :
    observe ι otpCode (otpArgs message pad) {pad} s =
      some (.ret (.int result) (padHeap pad byte)) := by
  have hheap := decodeF_padHeap ι s message pad byte hrange hbyte
  have hbounds : 0 ≤ result ∧ result < 2 ^ 64 := by simpa [inRange] using hresult
  have hvalue : ((BitVec.ofInt 64 result).toNat : Int) = result := by
    change ((result % 18446744073709551616).toNat : Int) = result
    rw [Int.emod_eq_of_lt hbounds.1 (show result < 18446744073709551616 by simpa using hbounds.2)]
    exact Int.toNat_of_nonneg hbounds.1
  have hresultKind : otpCode.sig.result = .uint 64 := rfl
  apply observe_ret_of_reads ι otpCode (otpArgs message pad) {pad} s
    (BitVec.ofInt 64 result) (.int result) (padHeap pad byte) hpc hheap ha0
  simp only [hresultKind, decodeValue, BitVec.setWidth_eq, hvalue, hresult, ite_true]

/-- The machine's unsigned byte extension is the byte's unsigned doubleword encoding. -/
theorem byte_setWidth64 (byte : Int) (hrange : inRange false 8 byte = true) :
    (BitVec.ofInt 8 byte).setWidth 64 = BitVec.ofInt 64 byte := by
  have hb : 0 ≤ byte ∧ byte < 256 := by simpa [inRange] using hrange
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth]
  change (byte % 256).toNat % 18446744073709551616 = (byte % 18446744073709551616).toNat
  rw [Int.emod_eq_of_lt hb.1 hb.2,
    Int.emod_eq_of_lt hb.1 (show byte < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show byte.toNat < 18446744073709551616 by omega)]

end MetrologyAsm.OTP
