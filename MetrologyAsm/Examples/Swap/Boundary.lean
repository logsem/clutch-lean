import MetrologyAsm.ABI.Interface
import MetrologyAsm.Examples.Swap.Source
import Metrology.ProbLang.Asm.Fragments

/-! # Boundary checks for the exchange fragment -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm

/-- One signed doubleword region owns exactly its base location. -/
@[simp]
theorem signed64_cells (l : Loc) : (Region.mk l 1 64 true).cells = {l} := by
  simp [Region.cells]

/-- The exchange signature has no ambiguous imports and a supported unit result. -/
theorem swap_signature_valid : swapCode.sig.valid = true := by
  rfl

/-- Distinct signed doubleword cells satisfy the pointer aliasing check. -/
theorem signed64_compatible {l₁ l₂ : Loc} (hne : l₁ ≠ l₂) :
    (Region.mk l₁ 1 64 true).compatible (Region.mk l₂ 1 64 true) = true := by
  simp [Region.compatible, hne]

/-- A signed doubleword region compares equal to itself in the generated Boolean equality. -/
theorem signed64_beq_self (l : Loc) :
    (Region.mk l 1 64 true == Region.mk l 1 64 true) = true := by
  simp [BEq.beq, instBEqRegion.beq]

section

variable (l₁ l₂ : Loc)

/-- The raw two-pointer tuple has the exchange's two signed regions. -/
theorem swap_callRegions :
    callRegions swapCode [.loc l₁, .loc l₂] = [⟨l₁, 1, 64, true⟩, ⟨l₂, 1, 64, true⟩] := by
  rfl

/-- Membership in the exchange's call regions names its two signed doubleword regions. -/
theorem swap_callRegions_mem {l₁ l₂ : Loc} {r : Region} :
    r ∈ callRegions swapCode [.loc l₁, .loc l₂] ↔
      r = ⟨l₁, 1, 64, true⟩ ∨ r = ⟨l₂, 1, 64, true⟩ := by
  rw [swap_callRegions]
  simp

/-- The raw two-pointer tuple owns exactly the two supplied locations. -/
theorem swap_callFootprint :
    callFootprint swapCode [.loc l₁, .loc l₂] = {l₁, l₂} := by
  simp [callFootprint, footprint, swapCode, swapSig, regions, boundaryArgs,
    ArgKind.region, locValue, BoundaryValue.toVal, Region.cells]

/-- The two representable integer cells pass the exchange's scalar boundary checks. -/
theorem swap_boundary_check (old : Loc → Int) (hne : l₁ ≠ l₂)
    (h₁ : inRange true 64 (old l₁) = true) (h₂ : inRange true 64 (old l₂) = true) :
    check swapCode.sig.toCallSig (boundaryArgs [.loc l₁, .loc l₂])
      (valueHeap (integerHeap {l₁, l₂} old)) = true := by
  simp [check, swapCode, swapSig, boundaryArgs, regions, ArgKind.check, ArgKind.region,
    locValue, BoundaryValue.toVal, Region.check, intFits, intValue,
    Region.compatible, Region.cells, ArgKind.validResult, signed64_beq_self,
    h₁, h₂, hne, Ne.symm hne]

/-- The finite signed integer fragment is a valid exchange-call heap. -/
theorem swap_validFragment (old : Loc → Int) (hne : l₁ ≠ l₂)
    (h₁ : inRange true 64 (old l₁) = true) (h₂ : inRange true 64 (old l₂) = true) :
    validFragment swapCode [.loc l₁, .loc l₂] (integerHeap {l₁, l₂} old) := by
  refine ⟨swap_signature_valid, ?_, swap_boundary_check l₁ l₂ old hne h₁ h₂⟩
  rw [swap_callFootprint, restrict_integerHeap]

end

/-- Allocated signed words realize the exchange's complete logical footprint. -/
theorem swap_footprintContents (ι : Placement) (s : Mach) (l₁ l₂ : Loc)
    (old : Loc → Int) (hne : l₁ ≠ l₂)
    (h₁ : inRange true 64 (old l₁) = true) (h₂ : inRange true 64 (old l₂) = true)
    (hw₁ : Word64At s (ι.addr l₁) (BitVec.ofInt 64 (old l₁)))
    (hw₂ : Word64At s (ι.addr l₂) (BitVec.ofInt 64 (old l₂))) :
    footprintContents ι swapCode [.loc l₁, .loc l₂] (integerHeap {l₁, l₂} old) s := by
  refine ⟨swap_validFragment l₁ l₂ old hne h₁ h₂, ?_⟩
  intro r hr i hi
  rw [swap_callRegions_mem] at hr
  rcases hr with rfl | rfl <;> obtain rfl : i = 0 := by simpa using hi
  · exact ⟨old l₁, by simp, h₁, by simpa using hw₁⟩
  · exact ⟨old l₂, by simp, h₂, by simpa using hw₂⟩

end MetrologyAsm
