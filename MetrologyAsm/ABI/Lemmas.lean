import MetrologyAsm.ABI.Interface
import Metrology.ProbLang.Asm.Fragments

/-! # Decoding and evaluation rules for the Sail boundary -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm

/-- Decoded footprint and import-argument reads determine an external call observation. -/
theorem observe_call_of_reads (ι : Placement) (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (s : Mach) (name : String) (sig : CallSig)
    (values : List BoundaryValue) (heap : LocHeap BoundaryValue)
    (hpc : pc s = some (ι.importAddr name)) (hne : ι.retAddr ≠ ι.importAddr name)
    (hheap : decodeF ι code args F s = some heap) (himports : code.sig.imports = [(name, sig)])
    (hvalues : sig.args.zipIdx.mapM (fun entry => (argumentRegister s entry.2).bind
      (fun word => decodeValue ι code args entry.1 word)) = some values) :
    observe ι code args F s = some (.call name values heap) := by
  simp [observe, hpc, hheap, Ne.symm hne, himports, hvalues]

/-- Decoded footprint and result-register reads determine a return observation. -/
theorem observe_ret_of_reads (ι : Placement) (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (s : Mach) (word : BitVec 64) (value : BoundaryValue)
    (heap : LocHeap BoundaryValue) (hpc : pc s = some ι.retAddr)
    (hheap : decodeF ι code args F s = some heap) (hword : argumentRegister s 0 = some word)
    (hvalue : decodeValue ι code args code.sig.result word = some value) :
    observe ι code args F s = some (.ret value heap) := by
  simp [observe, hpc, hheap, hword, hvalue]

/-- A call observation in a one-import image means the pc is the import address. -/
theorem observe_call_pc_of_single_import (ι : Placement) (code : Code)
    (args : List BoundaryValue) (F : Finset Loc) (s : Mach) (name : String) (sig : CallSig)
    (values : List BoundaryValue) (heap : LocHeap BoundaryValue)
    (himports : code.sig.imports = [(name, sig)])
    (h : observe ι code args F s = some (.call name values heap)) :
    pc s = some (ι.importAddr name) := by
  cases hp : pc s with
  | none => simp [observe, hp] at h
  | some p =>
    cases hf : decodeF ι code args F s with
    | none => simp [observe, hp, hf] at h
    | some fragment =>
      by_cases hr : p = ι.retAddr
      · cases hw : argumentRegister s 0 with
        | none => simp [observe, hp, hf, hr, hw] at h
        | some word =>
          cases hv : decodeValue ι code args code.sig.result word <;>
            simp [observe, hp, hf, hr, hw, hv] at h
      · by_cases hc : p = ι.importAddr name
        · simp only [hc]
        · simp [observe, hp, hf, hr, himports, hc] at h

/-- Nonempty nonwrapping intervals with no common byte have separated endpoints. -/
theorem disjointSpans_of_no_overlap (a n b m : Nat) (hn : 0 < n) (hm : 0 < m)
    (h : ∀ p, inSpan a n p → ¬inSpan b m p) : disjointSpans a n b m := by
  by_cases hleft : a + n ≤ b
  · exact Or.inl hleft
  · apply Or.inr
    by_contra hright
    by_cases hab : a ≤ b
    · exact h b ⟨hab, by omega⟩ ⟨le_rfl, by omega⟩
    · exact h a ⟨le_rfl, by omega⟩ ⟨by omega, by omega⟩

/-- A relocated callback-address byte is its corresponding little-endian word slice. -/
theorem bitVec_of_importByte {width : Nat} (word : BitVec width) (i : Nat) :
    BitVec.ofNat 8 (UInt8.ofNat (word.toNat / 2 ^ (8 * i))).toNat = word.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- Configuration preservation composes across successive machine phases. -/
theorem configurationFrame.trans {s t u : Mach} (hst : configurationFrame s t)
    (htu : configurationFrame t u) : configurationFrame s u := by
  refine ⟨?_, htu.2.1.trans hst.2.1, htu.2.2.1.trans hst.2.2.1,
    htu.2.2.2.1.trans hst.2.2.2.1, htu.2.2.2.2.trans hst.2.2.2.2⟩
  intro r hs hc hb
  exact (htu.1 r hs hc hb).trans (hst.1 r hs hc hb)

/-- Configuration preservation retains the original external trap targets. -/
theorem machineConfiguration.of_configurationFrame (ι : Placement) (code : Code) {s t : Mach}
    (hs : machineConfiguration ι code s) (ht : UserConfig t) (hframe : configurationFrame s t) :
    machineConfiguration ι code t := by
  refine ⟨ht, ?_⟩
  have hmt := hframe.1 Register.mtvec (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hst := hframe.1 Register.stvec (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa only [hmt, hst] using hs.2

/-- Decoding an empty footprint succeeds without reading the Sail state. -/
@[simp] theorem decodeF_empty (ι : Placement) (code : Code) (args : List BoundaryValue) (s : Mach) :
    decodeF ι code args ∅ s = some ∅ := by
  simp [decodeF, footprintLocations, Iris.Std.PartialMap.ofList]

/-- A single byte region occupies exactly the physical address of its logical base. -/
theorem footprintByte_single_byte (ι : Placement) (code : Code) (args : List BoundaryValue)
    (l : Loc) (hregions : callRegions code args = [⟨l, 1, 8, false⟩]) (a : Nat) :
    footprintByte ι code args a ↔ a = (ι.addr l).toNat := by
  simp [footprintByte, hregions, inSpan]
  omega

/-- Reading a representable signed doubleword recovers its original logical integer. -/
theorem decodeCell_signed64 (ι : Placement) (r : Region) (l : Loc) (s : Mach) (z : Int)
    (hwidth : r.width = 64) (hsigned : r.signed = true)
    (hrange : inRange true 64 z = true)
    (hword : Word64At s (ι.addr l) (BitVec.ofInt 64 z)) :
    decodeCell ι r l s = some (.int z) := by
  have hbounds : -(2 ^ 63 : Int) ≤ z ∧ z < 2 ^ 63 := by
    simpa [inRange] using hrange
  have hdecode : (BitVec.ofInt 64 z).toInt = z :=
    BitVec.toInt_ofInt_eq_self (by decide) hbounds.1 hbounds.2
  obtain ⟨base, length, width, signed⟩ := r
  cases hwidth
  cases hsigned
  simp only [decodeCell, Nat.reduceDiv, ite_true]
  simp only [runSail, readBytes64_eq hword]
  simp [hdecode, hrange]

private theorem mapM_eq_some_map {α β : Type} (xs : List α) (f : α → Option β)
    (g : α → β) (h : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.mapM_cons, h x (by simp), ih fun y hy => h y (by simp [hy])]

/-- Pointwise successful Sail cell reads reconstruct exactly the finite logical integer fragment. -/
theorem decodeF_integerHeap (ι : Placement) (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (s : Mach) (values : Loc → Int)
    (hcell : ∀ l ∈ F, ∃ r,
      (callRegions code args).find? (fun r => decide (l ∈ r.cells)) = some r ∧
        decodeCell ι r l s = some (.int (values l))) :
    decodeF ι code args F s = some (integerHeap F values) := by
  have hentries : (footprintLocations F).mapM (fun l => do
      let r ← (callRegions code args).find? (fun r => decide (l ∈ r.cells))
      return (l, ← decodeCell ι r l s)) =
        some ((footprintLocations F).map fun l => (l, BoundaryValue.int (values l))) := by
    apply mapM_eq_some_map
    intro l hl
    obtain ⟨r, hr, hd⟩ := hcell l ((mem_footprintLocations F l).mp hl)
    simp [hr, hd]
  unfold decodeF
  rw [hentries]
  change some _ = some _
  congr 1
  simp only [integerHeap, integerSnapshot, HeapSnapshot.restore, List.map_map,
    Function.comp_def]

/-- A nonvacuous universal return specification determines the Sail-backed evaluator. -/
theorem rv_eval_ret (code : Code) (args : List BoundaryValue)
    (heap output : LocHeap BoundaryValue) (value : BoundaryValue)
    (hentry : ∃ ι s, RVCompat ι code args heap s)
    (hspec : RVSpec code args heap (.ret value output)) :
    rv.eval code args (callFootprint code args) heap = some (.ret value output) := by
  exact rv.eval_ret_eq_some code args _ heap output value
    (fun ι s P Q => rv_runs_agree ι code s P Q)
    (fun ι s t a b => rv_exit_det ι code args _ s t a b) hentry hspec

end MetrologyAsm
