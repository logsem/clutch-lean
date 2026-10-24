import MetrologyAsm.Examples.Callback.Source
import MetrologyAsm.ABI.Resume
import Metrology.ProbLang.Asm.OneCall

/-! # Boundary values and the canonical callback interaction -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm Std.ExtTreeMap

/-- The scalar callback fragment owns no logical pointer regions. -/
@[simp] theorem importToy_regions : callRegions importToyCode [] = [] := rfl

/-- The scalar callback fragment owns the empty logical footprint. -/
@[simp] theorem importToy_footprint : callFootprint importToyCode [] = ∅ := rfl

/-- The callback fragment is a valid fragment with no regions. -/
theorem importToy_valid_empty : validFragment importToyCode [] ∅ := by
  exact ⟨rfl, rfl, rfl⟩

/-- The finite interaction calls the external function and returns its representable reply. -/
noncomputable def importToyTree : Interaction BoundaryValue :=
  rv.canonicalize importToyCode [] ∅ (.call "cb" [] ∅ fun r heap => .ret r heap)

/-- The canonical callback interaction is canonical for the callback fragment. -/
theorem importToyTree_canonical : rv.Canonical importToyCode [] ∅ importToyTree :=
  rv.canonicalize_canonical importToyCode [] ∅ _

section

variable (r : BoundaryValue) (heap : LocHeap BoundaryValue)

/-- Embedding boundary scalars preserves whether the logical heap is empty. -/
theorem valueHeap_eq_empty_iff :
    valueHeap (rT := Empty) heap = ∅ ↔ heap = ∅ := by
  constructor
  · intro h
    apply ext_getElem?
    intro l
    have hl := congrArg (fun h : LocHeap (Val Empty) => h[l]?) h
    simp only [valueHeap, getElem?_map, getElem?_empty] at hl ⊢
    cases he : heap[l]? with
    | none => rfl
    | some v => simp [he] at hl
  · rintro rfl
    apply ext_getElem?
    intro l
    simp [valueHeap]

/-- A callback response consists exactly of a signed doubleword and the empty heap. -/
theorem importToy_response_iff :
    rv.ResponseOK importToyCode [] ∅ "cb" r heap ↔
      ∃ z, r = .int z ∧ heap = ∅ ∧ inRange true 64 z = true := by
  change boundaryResponseOK importToyCode [] ∅ "cb" r heap ↔ _
  cases r <;> simp [boundaryResponseOK, responseOK, importToyCode, boundaryArgs, Sig.valid,
    footprint, regions, restrict_empty_heap, valueHeap_eq_empty_iff, check, checkResult,
    ArgKind.check, intFits, intValue, BoundaryValue.toVal, ArgKind.validResult]

/-- The continuation returns a valid response and otherwise the invalid tree. -/
noncomputable def importToyNext : Interaction BoundaryValue :=
  open Classical in
  if rv.ResponseOK importToyCode [] ∅ "cb" r heap then .ret r heap else rv.invalidTree

/-- Every valid callback response selects its corresponding return node. -/
theorem importToyNext_valid (hr : rv.ResponseOK importToyCode [] ∅ "cb" r heap) :
    importToyNext r heap = .ret r heap := by
  classical
  exact ite_eq_left hr

end

/-- The canonical callback interaction has its explicit first call and continuation. -/
theorem importToyTree_eq : importToyTree = .call "cb" [] ∅ importToyNext := by
  classical
  rfl

end MetrologyAsm
