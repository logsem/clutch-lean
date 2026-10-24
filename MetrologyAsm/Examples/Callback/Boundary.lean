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

/-- Restricting a logical heap to the empty footprint removes every cell. -/
theorem restrict_empty_heap {V : Type} (heap : LocHeap V) : restrict ∅ heap = ∅ := by
  apply ext_getElem?
  intro l
  simp [restrict_get]

/-- Embedding boundary scalars preserves whether the logical heap is empty. -/
theorem valueHeap_eq_empty_iff (heap : LocHeap BoundaryValue) :
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

/-- The callback fragment is a valid fragment with no regions. -/
theorem importToy_valid_empty : validFragment importToyCode [] ∅ := by
  exact ⟨rfl, rfl, rfl⟩

/-- A callback response consists exactly of a signed doubleword and the empty heap. -/
theorem importToy_response_iff (r : BoundaryValue) (heap : LocHeap BoundaryValue) :
    rv.ResponseOK importToyCode [] ∅ "cb" r heap ↔
      ∃ z, r = .int z ∧ heap = ∅ ∧ inRange true 64 z = true := by
  change boundaryResponseOK importToyCode [] ∅ "cb" r heap ↔ _
  cases r <;> simp [boundaryResponseOK, responseOK, importToyCode, boundaryArgs, Sig.valid,
    footprint, regions, restrict_empty_heap, valueHeap_eq_empty_iff, check, checkResult,
    ArgKind.check, intFits, intValue, BoundaryValue.toVal, ArgKind.validResult]

/-- The finite interaction calls the external function and returns its representable reply. -/
noncomputable def importToyTree : Interaction BoundaryValue :=
  rv.canonicalize importToyCode [] ∅ (.call "cb" [] ∅ fun r heap => .ret r heap)

/-- Continuation: return a valid response, otherwise the invalid tree. -/
noncomputable def importToyNext (r : BoundaryValue) (heap : LocHeap BoundaryValue) :
    Interaction BoundaryValue :=
  open Classical in
  if rv.ResponseOK importToyCode [] ∅ "cb" r heap then .ret r heap else rv.invalidTree

/-- The canonical callback interaction is canonical for the callback fragment. -/
theorem importToyTree_canonical : rv.Canonical importToyCode [] ∅ importToyTree :=
  rv.canonicalize_canonical importToyCode [] ∅ _

/-- The canonical callback interaction has its explicit first call and continuation. -/
theorem importToyTree_eq : importToyTree = .call "cb" [] ∅ importToyNext := by
  classical
  rfl

/-- Every valid callback response selects its corresponding return node. -/
theorem importToyNext_valid (r : BoundaryValue) (heap : LocHeap BoundaryValue)
    (hr : rv.ResponseOK importToyCode [] ∅ "cb" r heap) :
    importToyNext r heap = .ret r heap := by
  classical
  exact ite_eq_left hr

end MetrologyAsm
