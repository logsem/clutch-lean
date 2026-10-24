import MetrologyAsm.Examples.OTP.Source
import MetrologyAsm.ABI.ByteResume
import Metrology.ProbLang.Asm.Fragments

/-! # The OTP argument tuple and its owned logical byte -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm Iris.Std

/-- Pass the scalar message followed by the private pad pointer in psABI order. -/
def otpArgs (message : Int) (pad : Loc) : List BoundaryValue := [.int message, .loc pad]

/-- The sole logical region contains one unsigned eight-bit pad cell. -/
def padRegion (pad : Loc) : Region := ⟨pad, 1, 8, false⟩

/-- The finite fragment stores the current private pad byte. -/
def padHeap (pad : Loc) (byte : Int) : LocHeap BoundaryValue := integerHeap {pad} (fun _ => byte)

/-- The declared scalar/pointer tuple describes exactly its one-byte region. -/
@[simp] theorem otp_regions (message : Int) (pad : Loc) :
    callRegions otpCode (otpArgs message pad) = [padRegion pad] := rfl

/-- The one-byte region owns only its base logical location. -/
@[simp] theorem padRegion_cells (pad : Loc) : (padRegion pad).cells = {pad} := by
  simp [padRegion, Region.cells]

/-- The OTP footprint consists of precisely the private pad cell. -/
@[simp] theorem otp_footprint (message : Int) (pad : Loc) :
    callFootprint otpCode (otpArgs message pad) = {pad} := by
  simp [callFootprint, footprint, otpCode, otpSig, otpArgs, regions, boundaryArgs,
    ArgKind.region, locValue, BoundaryValue.toVal, Len.resolve, Region.cells]

/-- Lookup exposes the pad byte and no other logical cell. -/
@[simp] theorem padHeap_get (pad : Loc) (byte : Int) (l : Loc) :
    (padHeap pad byte)[l]? = if l = pad then some (.int byte) else none := by
  simp [padHeap]

/-- Restriction retains the OTP's singleton integer fragment. -/
@[simp] theorem restrict_padHeap (pad : Loc) (byte : Int) :
    restrict {pad} (padHeap pad byte) = padHeap pad byte := by simp [padHeap]

/-- The one-cell snapshot restores exactly the corresponding logical byte heap. -/
@[simp] theorem restore_padSnapshot (pad : Loc) (byte : Int) :
    HeapSnapshot.restore [(pad, byte)] = padHeap pad byte := by
  simp [padHeap, integerHeap, integerSnapshot, footprintLocations, HeapSnapshot.restore]

/-- Archiving the owned logical byte produces its sole location/value pair. -/
theorem snapshot_padHeap (pad : Loc) (byte : Int) :
    snapshot (padHeap pad byte) = some [(pad, byte)] := by
  have hp := LawfulFiniteMap.toList_ofList
    (M := LocHeap) (l := [(pad, BoundaryValue.int byte)]) (by simp [NoDupKeys])
  have hlist : FiniteMap.toList
      (PartialMap.ofList [(pad, BoundaryValue.int byte)] : LocHeap BoundaryValue) =
        [(pad, BoundaryValue.int byte)] := List.perm_singleton.mp hp
  change (PartialMap.ofList [(pad, BoundaryValue.int byte)] :
    LocHeap BoundaryValue).toList = [(pad, BoundaryValue.int byte)] at hlist
  simp [padHeap, integerHeap, integerSnapshot, footprintLocations, HeapSnapshot.restore,
    snapshot, hlist]

/-- Every byte in `[0, 256)` is a representable unsigned doubleword. -/
theorem inRange_word_of_byte {m : Int} (hm : 0 ≤ m ∧ m < 256) : inRange false 64 m = true := by
  simp [inRange]
  omega

/-- A byte passes the unsigned eight-bit check exactly when it lies in `[0, 256)`. -/
theorem inRange_eight_iff {b : Int} : inRange false 8 b = true ↔ 0 ≤ b ∧ b < 256 := by
  simp [inRange]

/-- The single pad region passes its Boolean self-aliasing check. -/
theorem padRegion_beq_self (pad : Loc) : (padRegion pad == padRegion pad) = true := by
  simp [padRegion, BEq.beq, instBEqRegion.beq]

/-- Representable message and pad values pass the actual dynamic signature checks. -/
theorem otp_boundary_check (message : Int) (pad : Loc) (byte : Int)
    (hmessage : inRange false 64 message = true) (hbyte : inRange false 8 byte = true) :
    check otpCode.sig.toCallSig (boundaryArgs (otpArgs message pad))
      (valueHeap (padHeap pad byte)) = true := by
  simp [check, otpCode, otpSig, otpArgs, boundaryArgs, regions, ArgKind.check, ArgKind.region,
    locValue, BoundaryValue.toVal, Len.resolve, Region.check, intFits, intValue, Region.compatible,
    Region.cells, ArgKind.validResult, hmessage, hbyte, padHeap, BEq.beq, instBEqRegion.beq]

/-- The representable pad fragment is exactly a valid initial or resumed OTP heap. -/
theorem otp_validFragment (message : Int) (pad : Loc) (byte : Int)
    (hmessage : inRange false 64 message = true) (hbyte : inRange false 8 byte = true) :
    validFragment otpCode (otpArgs message pad) (padHeap pad byte) := by
  refine ⟨rfl, ?_, otp_boundary_check message pad byte hmessage hbyte⟩
  rw [otp_footprint, restrict_padHeap]

end MetrologyAsm.OTP
