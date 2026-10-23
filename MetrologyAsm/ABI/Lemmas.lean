import MetrologyAsm.ABI.Interface
import Metrology.ProbLang.Asm.Fragments

/-! # Decoding and evaluation rules for the Sail boundary -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm Sail.ConcurrencyInterfaceV1

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
    simp only [List.mapM_cons, h x (List.mem_cons_self ..)]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

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
  apply rv.eval_ret_eq_some code args (callFootprint code args) heap output value
  · exact fun ι s P Q => rv_runs_agree ι code s P Q
  · exact fun ι s t a b => rv_exit_det ι code args (callFootprint code args) s t a b
  · exact hentry
  · exact hspec

end MetrologyAsm
