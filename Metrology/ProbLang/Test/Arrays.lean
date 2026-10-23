module

public import Metrology.ProbLang.HeadStep
public import Metrology.ProbLang.Interp.BigStepIO
meta import Metrology.ProbLang.Interp.BigStepIO
import Metrology.ProbLang.Syntax.Notation

/-! # Consecutive allocation and location-offset checks -/

@[expose] public section

namespace ProbLang.Test.Arrays

open Exp MeasureTheory

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

example (l z : Int) : BinOp.eval .offset pl(#loc l) pl(#z) = some (pl(#loc (l + z)) : Exp rT) :=
  rfl

example (v : Val rT) (σ : State rT) : headStep ⟨.allocN pl(#0) v.1, σ⟩ = 0 := by
  simp [headStep, asValM]

example (v : Val rT) (σ : State rT) : headStep ⟨.allocN pl(#(-3)) v.1, σ⟩ = 0 := by
  simp [headStep, asValM]

example (v : Val rT) (σ : State rT) (i : Nat) (hi : i < 32) :
    (LocHeap.allocN σ.heap v 32)[σ.heap.fresh + i]? = some v := by
  rw [LocHeap.allocN_get?]
  have hlo := le_add_of_nonneg_right (a := σ.heap.fresh) (Int.natCast_nonneg i)
  have hhi := add_lt_add_left (Int.ofNat_lt.mpr hi) σ.heap.fresh
  exact ite_eq_left ⟨hlo, by simpa [add_comm] using hhi⟩

example (v : Val rT) (σ : State rT) (n : Nat) (l : Loc) (hl : l < σ.heap.fresh) :
    (LocHeap.allocN σ.heap v n)[l]? = σ.heap[l]? := by
  rw [LocHeap.allocN_get?]
  simp [not_le_of_gt hl]

/-- A block update through an interior pointer, read back through the same pointer. -/
def updateInterior : Exp Float := pl(
  let a := allocN(#3, #0);
  (a +ₗ #1) ← #7;
  !(a +ₗ #1))

-- Both evaluators agree on the interior-pointer update.
#eval show IO Unit from do
  let σ : State Float := ⟨∅, ∅⟩
  let envResult ← Interp.run (.eval [] updateInterior σ)
  let substResult ← Interp.runSubst ⟨updateInterior, σ⟩
  unless envResult.val.rb == pl(#7) && substResult.expr == pl(#7) do
    throw (IO.userError "block allocation or interior update returned the wrong result")

end ProbLang.Test.Arrays
