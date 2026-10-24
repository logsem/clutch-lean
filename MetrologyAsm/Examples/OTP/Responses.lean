import MetrologyAsm.Examples.OTP.Boundary
import MetrologyAsm.Examples.OTP.Byte
import Metrology.ProbLang.Asm.OneCall

/-! # The valid byte response and canonical interaction of the compiled OTP -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm Std.ExtTreeMap

/-- The signature check requires a uint64 message and a byte integer at the pad location. -/
theorem otp_check_iff (message : Int) (pad : Loc) (heap : LocHeap BoundaryValue) :
    check otpCode.sig.toCallSig (boundaryArgs (otpArgs message pad))
      (valueHeap (rT := Empty) heap) = true ↔
      inRange false 64 message = true ∧
        ∃ byte, heap[pad]? = some (.int byte) ∧ inRange false 8 byte = true := by
  rcases hc : heap[pad]? with _ | value
  · simp [check, otpCode, otpSig, otpArgs, boundaryArgs, regions, ArgKind.check, ArgKind.region,
      locValue, BoundaryValue.toVal, Len.resolve, Region.check, intFits, intValue,
      Region.compatible, Region.cells, ArgKind.validResult, valueHeap, hc,
      BEq.beq, instBEqRegion.beq]
  · cases value <;> simp [check, otpCode, otpSig, otpArgs, boundaryArgs, regions, ArgKind.check,
      ArgKind.region, locValue, BoundaryValue.toVal, Len.resolve, Region.check, intFits, intValue,
      Region.compatible, Region.cells, ArgKind.validResult, valueHeap, hc, BEq.beq,
      instBEqRegion.beq]

/-- A heap restricted to the single pad cell is determined by the integer stored there. -/
theorem heap_eq_padHeap (pad : Loc) (heap : LocHeap BoundaryValue) (byte : Int)
    (hrestrict : heap = restrict {pad} heap) (hbyte : heap[pad]? = some (.int byte)) :
    heap = padHeap pad byte := by
  apply ext_getElem?
  intro l
  rw [padHeap_get]
  by_cases hl : l = pad
  · simpa [hl] using hbyte
  · have heq := congrArg (fun heap : LocHeap BoundaryValue => heap[l]?) hrestrict
    simpa [hl] using heq

/-- Embedding a heap as ProbLang values preserves its fixed-footprint restriction. -/
private theorem restrict_of_valueHeap (F : Finset Loc) (heap : LocHeap BoundaryValue)
    (h : valueHeap (rT := Empty) heap = restrict F (valueHeap heap)) : heap = restrict F heap := by
  apply ext_getElem?
  intro l
  by_cases hl : l ∈ F
  · simp [hl]
  · have heq := congrArg (fun heap : LocHeap (Val Empty) => heap[l]?) h
    have hnone : heap[l]? = none := by simpa [valueHeap, hl] using heq
    simp [hl, hnone]

/-- Valid fragments are precisely singleton representable byte heaps and uint64 messages. -/
theorem otp_validFragment_iff (message : Int) (pad : Loc) (heap : LocHeap BoundaryValue) :
    validFragment otpCode (otpArgs message pad) heap ↔
      ∃ byte, heap = padHeap pad byte ∧ inRange false 64 message = true ∧
        inRange false 8 byte = true := by
  constructor
  · intro h
    obtain ⟨hm, byte, hb, hr⟩ := (otp_check_iff message pad heap).mp h.2.2
    exact ⟨byte, heap_eq_padHeap pad heap byte (by simpa using h.2.1) hb, hm, hr⟩
  · rintro ⟨byte, rfl, hm, hb⟩
    exact otp_validFragment message pad byte hm hb

/-- A valid randombytes response returns unit and may replace the owned pad with any byte. -/
theorem otp_response_iff (message : Int) (pad : Loc) (r : BoundaryValue)
    (heap : LocHeap BoundaryValue) :
    rv.ResponseOK otpCode (otpArgs message pad) {pad} "randombytes" r heap ↔
      r = .unit ∧ ∃ byte, heap = padHeap pad byte ∧ inRange false 64 message = true ∧
        inRange false 8 byte = true := by
  change boundaryResponseOK otpCode (otpArgs message pad) {pad} "randombytes" r heap ↔ _
  constructor
  · rintro ⟨_, _, hrestrict, hcheck, sig, hsig, _, hresult⟩
    have heq : sig = ⟨[.array 8 (.arg 1), .uint 64], .unit⟩ := by
      simpa [otpCode, otpSig] using hsig
    subst sig
    have hr : r = .unit := by
      change ArgKind.check [] ∅ r.toVal .unit = true at hresult
      cases r <;> simp [ArgKind.check, BoundaryValue.toVal] at hresult ⊢
    obtain ⟨hm, byte, hb, hrange⟩ := (otp_check_iff message pad heap).mp hcheck
    exact ⟨hr, byte, heap_eq_padHeap pad heap byte (restrict_of_valueHeap _ _ hrestrict) hb,
      hm, hrange⟩
  · rintro ⟨rfl, byte, rfl, hm, hb⟩
    refine ⟨rfl, ?_, ?_, otp_boundary_check message pad byte hm hb,
      ⟨[.array 8 (.arg 1), .uint 64], .unit⟩, by simp [otpCode, otpSig], rfl, rfl⟩
    · exact (otp_footprint message pad).symm
    · apply ext_getElem?
      intro l
      by_cases hl : l = pad <;> simp [valueHeap, padHeap, hl]

/-- The byte stored at the sole owned pad location, with an irrelevant default on invalid heaps. -/
def padValue (pad : Loc) (heap : LocHeap BoundaryValue) : Int :=
  match heap[pad]? with
  | some (.int byte) => byte
  | _ => 0

/-- Reading a constructed byte fragment exposes its stored byte. -/
@[simp] theorem padValue_padHeap (pad : Loc) (byte : Int) :
    padValue pad (padHeap pad byte) = byte := by simp [padValue]

/-- The canonical tree with footprint `{pad}`: a randombytes call, then XOR with the message. -/
noncomputable def otpTree (message : Int) (pad : Loc) (initial : Int) : Interaction BoundaryValue :=
  rv.canonicalize otpCode (otpArgs message pad) {pad}
    (.call "randombytes" [.loc pad, .int 1] (padHeap pad initial) fun _ heap =>
      .ret (.int (byteXor message (padValue pad heap))) heap)

/-- Valid responses compute the ciphertext; invalid branches use the canonical invalid tree. -/
noncomputable def otpNext (message : Int) (pad : Loc) (r : BoundaryValue)
    (heap : LocHeap BoundaryValue) : Interaction BoundaryValue :=
  open Classical in
  if rv.ResponseOK otpCode (otpArgs message pad) {pad} "randombytes" r heap then
    .ret (.int (byteXor message (padValue pad heap))) heap
  else
    rv.invalidTree

/-- The OTP interaction fixes every invalid callback branch. -/
theorem otpTree_canonical (message : Int) (pad : Loc) (initial : Int) :
    rv.Canonical otpCode (otpArgs message pad) {pad} (otpTree message pad initial) :=
  rv.canonicalize_canonical otpCode (otpArgs message pad) {pad} _

/-- The canonical tree has one actual randombytes call. -/
theorem otpTree_eq (message : Int) (pad : Loc) (initial : Int) :
    otpTree message pad initial =
      .call "randombytes" [.loc pad, .int 1] (padHeap pad initial) (otpNext message pad) := rfl

/-- Every valid randombytes response selects the expected return node. -/
theorem otpNext_valid (message : Int) (pad : Loc) (r : BoundaryValue)
    (heap : LocHeap BoundaryValue)
    (hr : rv.ResponseOK otpCode (otpArgs message pad) {pad} "randombytes" r heap) :
    otpNext message pad r heap = .ret (.int (byteXor message (padValue pad heap))) heap := by
  exact ite_eq_left hr

end MetrologyAsm.OTP
