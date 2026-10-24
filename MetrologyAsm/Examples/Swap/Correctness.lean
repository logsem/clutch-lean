import MetrologyAsm.Examples.Swap.Evaluation
import Metrology.Micrometer.Asm
import Metrology.Iris.LocalBI

/-! # The assembled exchange under Micrometer's shared weakest precondition -/

open Iris Iris.Std Iris.BI Iris.ProofMode GradedLifting

namespace ProbLang

open Asm BigSepL

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {GF : BundledGFunctors}

local bi IProp GF

/-- The sorted integer footprint of two distinct cells is their ordinary separating ownership. -/
theorem integerValues_pair [AppGS rT GF] (l k : Loc) (values : Loc → Int) (hne : l ≠ k) : iprop%
    appHeapFragment (integerValues {l, k} values) ⊣⊢
      appHeapFrag l (.int (values l)) ∗ appHeapFrag k (.int (values k)) := by
  classical
  have hnodup : [l, k].Nodup := by simp [hne]
  have hperm : (footprintLocations {l, k}).Perm [l, k] := by
    simpa [footprintLocations] using
      (Finset.sort_perm_toList ([l, k].toFinset) (· ≤ ·)).trans (List.toFinset_toList hnodup)
  have hp := hperm.map (fun a => (a, Val.int (rT := rT) (values a)))
  have hbig := bigSepL_perm (Φ := fun entry : Loc × Val rT =>
    (appHeapFrag entry.1 entry.2 : IProp GF)) hp
  exact hbig.trans (bigSepL_cons.trans (sep_congr .rfl bigSepL_singleton))

end ProbLang

namespace MetrologyAsm

open ProbLang ProbLang.Asm MicrometerWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {GF : BundledGFunctors}

local bi IProp GF

variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} [MicrometerGS rT hlc GF] [BudgetGS B GF]
  [L.IsLawful] [L.IsTopAbsorbing] {E : CoPset} {Φ : Val rT → IProp GF}

/-- An actual Sail evaluator result exchanges the two ordinary owned cells. -/
theorem wp_swap_of_eval (env : FfiEnv rT) (henv : env.machine = rv)
    (l k : Loc) (old : Loc → Int) (hne : l ≠ k)
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true)
    (heval : rv.eval swapCode [.loc l, .loc k] (callFootprint swapCode [.loc l, .loc k])
      (integerHeap {l, k} old) =
      some (.ret .unit (integerHeap {l, k} (swapValues old l k)))) : iprop%
    appHeapFrag l (.int (old l)) ∗ appHeapFrag k (.int (old k)) ∗
      ▷ (appHeapFrag l (.int (old k)) ∗ appHeapFrag k (.int (old l)) -∗ Φ .unit) ⊢
      wpFor (primStepWith env) L E
      (.asm (.lit (.code swapCode)) (argumentTuple [.loc l, .loc k])) Φ := by
  have hinput := swap_validFragment l k old hne hl hk
  have houtput : validFragment swapCode [.loc l, .loc k] (integerHeap {l, k} (swapValues old l k)) ∧
      checkResult swapCode.sig.toCallSig (boundaryArgs [.loc l, .loc k])
        swapCode.sig.result BoundaryValue.unit.toVal = true := by
    refine ⟨swap_validFragment l k (swapValues old l k) hne ?_ ?_, rfl⟩
    · simpa [swapValues] using hk
    · simpa [swapValues, hne.symm] using hl
  have heval' : env.machine.eval swapCode [.loc l, .loc k] (callFootprint swapCode [.loc l, .loc k])
      (integerHeap (callFootprint swapCode [.loc l, .loc k]) old) =
      some (.ret .unit (integerHeap (callFootprint swapCode [.loc l, .loc k])
        (swapValues old l k))) := by simpa only [henv, swap_callFootprint] using heval
  have hpost : appHeapFragment (integerValues {l, k} (swapValues old l k)) ⊣⊢
      appHeapFrag l (.int (old k)) ∗ appHeapFrag k (.int (old l)) := by
    simpa [swapValues, hne.symm] using integerValues_pair l k (swapValues old l k) hne
  iintro ⟨Hl, Hk, HΦ⟩
  iapply wp_asm_of_eval env swapCode [.loc l, .loc k] old (swapValues old l k) .unit
    rfl (by simpa only [swap_callFootprint] using hinput) heval'
    (by simpa only [swap_callFootprint] using houtput)
  isimp only [swap_callFootprint, BoundaryValue.toVal]
  isplitl [Hl Hk]
  · iapply (integerValues_pair l k old hne).2
    iframe
  · iintro !> Hnew
    iapply HΦ
    iapply hpost.1 $$ Hnew

/-- The actual assembled Sail exchange satisfies the ordinary two-cell weakest-precondition rule. -/
theorem wp_swap (env : FfiEnv rT) (henv : env.machine = rv)
    (l k : Loc) (old : Loc → Int) (hne : l ≠ k)
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true) : iprop%
    appHeapFrag l (.int (old l)) ∗ appHeapFrag k (.int (old k)) ∗
      ▷ (appHeapFrag l (.int (old k)) ∗ appHeapFrag k (.int (old l)) -∗ Φ .unit) ⊢
      wpFor (primStepWith env) L E
      (.asm (.lit (.code swapCode)) (argumentTuple [.loc l, .loc k])) Φ :=
  wp_swap_of_eval env henv l k old hne hl hk (swap_eval l k old hne hl hk)

/-- The assembled exchange returns unit with the original values stored in opposite cells. -/
theorem wp_swap_spec (env : FfiEnv rT) (henv : env.machine = rv)
    (l k : Loc) (old : Loc → Int) (hne : l ≠ k)
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true) : iprop%
    appHeapFrag l (.int (old l)) ∗ appHeapFrag k (.int (old k)) ⊢
      wpFor (primStepWith env) L E
      (.asm (.lit (.code swapCode)) (argumentTuple [.loc l, .loc k]))
      (fun v => iprop(⌜v = .unit⌝ ∗
        appHeapFrag l (.int (old k)) ∗ appHeapFrag k (.int (old l)))) := by
  iintro ⟨Hl, Hk⟩
  iapply wp_swap env henv l k old hne hl hk
  iframe Hl Hk
  iintro !> ⟨Hl, Hk⟩
  iframe Hl Hk
  ipureintro
  rfl

end MetrologyAsm
