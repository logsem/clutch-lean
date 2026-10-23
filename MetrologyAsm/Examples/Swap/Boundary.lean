import MetrologyAsm.ABI.Interface
import MetrologyAsm.Examples.Swap.Source
import Metrology.ProbLang.Asm.Fragments

/-! # Boundary checks for the exchange fragment -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm

/-- The original two-pointer tuple of an exchange call. -/
def swapArgs (l k : Loc) : List BoundaryValue := [.loc l, .loc k]

/-- A pointer argument owns one signed doubleword cell. -/
def swapRegion (l : Loc) : Region := ⟨l, 1, 64, true⟩

/-- The scalar exchange arguments describe two signed doubleword regions. -/
theorem callRegions_swap (l₁ l₂ : Loc) :
    callRegions swapCode (swapArgs l₁ l₂) = [swapRegion l₁, swapRegion l₂] := by
  rfl

/-- The raw two-pointer tuple has the exchange's two signed regions. -/
theorem swap_callRegions (l₁ l₂ : Loc) :
    callRegions swapCode [.loc l₁, .loc l₂] =
      [⟨l₁, 1, 64, true⟩, ⟨l₂, 1, 64, true⟩] := callRegions_swap l₁ l₂

/-- One signed doubleword region owns exactly its base location. -/
@[simp]
theorem signed64_cells (l : Loc) : (Region.mk l 1 64 true).cells = {l} := by
  simp [Region.cells]

/-- The exchange footprint consists of its two pointer locations. -/
theorem callFootprint_swap (l₁ l₂ : Loc) :
    callFootprint swapCode (swapArgs l₁ l₂) = {l₁, l₂} := by
  simp [swapArgs, callFootprint, footprint, swapCode, swapSig, regions, boundaryArgs,
    ArgKind.region, locValue, BoundaryValue.toVal, Region.cells]

/-- The raw two-pointer tuple owns exactly the two supplied locations. -/
theorem swap_callFootprint (l₁ l₂ : Loc) :
    callFootprint swapCode [.loc l₁, .loc l₂] = {l₁, l₂} := callFootprint_swap l₁ l₂

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

/-- The two representable integer cells pass the exchange's scalar boundary checks. -/
theorem swap_boundary_check (l₁ l₂ : Loc) (old : Loc → Int) (hne : l₁ ≠ l₂)
    (h₁ : inRange true 64 (old l₁) = true) (h₂ : inRange true 64 (old l₂) = true) :
    check swapCode.sig.toCallSig (boundaryArgs [.loc l₁, .loc l₂])
      (valueHeap (rT := Empty) (integerHeap {l₁, l₂} old)) = true := by
  simp [check, swapCode, swapSig, boundaryArgs, regions, ArgKind.check, ArgKind.region,
    locValue, BoundaryValue.toVal, Region.check, intFits, intValue,
    Region.compatible, Region.cells, ArgKind.validResult, signed64_beq_self,
    h₁, h₂, hne, Ne.symm hne]

/-- The finite signed integer fragment is a valid exchange-call heap. -/
theorem swap_validFragment (l₁ l₂ : Loc) (old : Loc → Int) (hne : l₁ ≠ l₂)
    (h₁ : inRange true 64 (old l₁) = true) (h₂ : inRange true 64 (old l₂) = true) :
    validFragment swapCode [.loc l₁, .loc l₂] (integerHeap {l₁, l₂} old) := by
  refine ⟨swap_signature_valid, ?_, swap_boundary_check l₁ l₂ old hne h₁ h₂⟩
  rw [swap_callFootprint, restrict_integerHeap]

/-- Allocated signed words realize the exchange's complete logical footprint. -/
theorem swap_footprintContents (ι : Placement) (s : Mach) (l₁ l₂ : Loc)
    (old : Loc → Int) (hne : l₁ ≠ l₂)
    (h₁ : inRange true 64 (old l₁) = true) (h₂ : inRange true 64 (old l₂) = true)
    (hw₁ : Word64At s (ι.addr l₁) (BitVec.ofInt 64 (old l₁)))
    (hw₂ : Word64At s (ι.addr l₂) (BitVec.ofInt 64 (old l₂))) :
    footprintContents ι swapCode [.loc l₁, .loc l₂] (integerHeap {l₁, l₂} old) s := by
  refine ⟨swap_validFragment l₁ l₂ old hne h₁ h₂, ?_⟩
  intro r hr i hi
  rw [swap_callRegions] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have heq : i = 0 := by simpa using hi
    subst i
    refine ⟨old l₁, by simp, h₁, ?_⟩
    simpa using hw₁
  · have heq : i = 0 := by simpa using hi
    subst i
    refine ⟨old l₂, by simp, h₂, ?_⟩
    simpa using hw₂

end MetrologyAsm
