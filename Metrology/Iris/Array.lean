module

public import Metrology.Iris.AppProgram
public import Metrology.ProbLang.Syntax.HeapArray
import Metrology.Iris.LocalBI

/-! # Ownership of consecutive heap cells -/

@[expose] public section

open Iris Iris.BI Iris.ProofMode Std.ExtTreeMap

namespace ProbLang

open _root_.ProbLang.LocHeap State

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]

local bi IProp GF

/-- Ownership of a consecutive block initialized with one value. -/
def appArrayFrag (l : Loc) (v : Val rT) : Nat → IProp GF
  | 0 => emp
  | n + 1 => iprop(appHeapFrag l v ∗ appArrayFrag (l + 1) v n)

/-- Allocating a block produces ownership of all its cells. -/
theorem app_state_heap_allocN (v : Val rT) (n : Nat) {σ : State rT} : iprop%
    ⊢ appStateAuth σ ==∗
      appStateAuth (σ.update_heap (fun h => allocN h v n)) ∗
        appArrayFrag σ.heap.fresh v n := by
  induction n generalizing σ with
  | zero =>
    simp only [allocN, update_heap, appArrayFrag]
    iintro Hσ
    imodintro
    iframe
  | succ n ih =>
    iintro Hσ
    imod app_state_heap_alloc v $$ Hσ with ⟨Hσ, Hl⟩
    imod ih $$ Hσ with ⟨Hσ, Hls⟩
    imodintro
    isimp only [update_heap, ← insert_eq_PartialMap_insert,
      fresh_insert] at Hls
    isimp only [update_heap, ← insert_eq_PartialMap_insert] at Hσ
    simp only [allocN, update_heap, appArrayFrag]
    iframe

end ProbLang
