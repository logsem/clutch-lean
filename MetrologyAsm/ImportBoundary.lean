import MetrologyAsm.ImportToy
import MetrologyAsm.RVResume
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

/-- The empty fragment passes the scalar callback fragment's signature checks. -/
theorem importToy_valid_empty : validFragment importToyCode [] ∅ := by
  refine ⟨rfl, rfl, rfl⟩

/-- A callback response consists exactly of a signed doubleword and the empty heap. -/
theorem importToy_response_iff (r : BoundaryValue) (heap : LocHeap BoundaryValue) :
    rv.ResponseOK importToyCode [] ∅ "cb" r heap ↔
      ∃ z, r = .int z ∧ heap = ∅ ∧ inRange true 64 z = true := by
  change boundaryResponseOK importToyCode [] ∅ "cb" r heap ↔ _
  simp only [boundaryResponseOK, responseOK, importToyCode, boundaryArgs, List.map_nil,
    Sig.valid, List.map_cons, List.map_nil, List.nodup_cons, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_self, decide_true, List.all_cons,
    List.all_nil, Bool.and_true, ArgKind.validResult]
  simp only [footprint, regions, List.zip_nil_right, List.filterMap_nil, List.foldl_nil,
    restrict_empty_heap, valueHeap_eq_empty_iff]
  cases r <;> simp [check, checkResult, ArgKind.check, intFits, intValue,
    BoundaryValue.toVal, regions, ArgKind.validResult]

/-- The finite interaction calls the external function and returns its representable reply. -/
noncomputable def importToyTree : Interaction BoundaryValue :=
  rv.canonicalize importToyCode [] ∅ (.call "cb" [] ∅ fun r heap => .ret r heap)

/-- The callback continuation returns representable responses and fixes every invalid branch. -/
noncomputable def importToyNext (r : BoundaryValue) (heap : LocHeap BoundaryValue) :
    Interaction BoundaryValue :=
  open Classical in
  if rv.ResponseOK importToyCode [] ∅ "cb" r heap then .ret r heap else rv.invalidTree

/-- The callback tree fixes every unrepresentable continuation. -/
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
