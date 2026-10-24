module

public import Metrology.Iris.AppProgram
public import Metrology.ProbLang.Syntax.HeapFragment
import Metrology.Iris.LocalBI

/-! # Ownership and exchange of finite heap fragments -/

@[expose] public section

open Iris Iris.BI Iris.ProofMode Std.ExtTreeMap Prod List

namespace ProbLang

variable {rT : Type}

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {GF : BundledGFunctors} [AppGS rT GF]
local bi IProp GF

/-- Separating ownership of every cell in a finite heap fragment. -/
abbrev appHeapFragment (entries : List (Loc × Val rT)) : IProp GF :=
  [∗list] entry ∈ entries, appHeapFrag entry.1 entry.2

/-- A finite fragment agrees with every lookup in the authoritative heap. -/
theorem app_state_lookup_fragment (entries : List (Loc × Val rT)) {σ : State rT} : iprop%
    ⊢ appStateAuth σ -∗ appHeapFragment entries -∗
      ⌜∀ entry ∈ entries, σ.heap[entry.1]? = some entry.2⌝ := by
  induction entries with
  | nil =>
    iintro Hσ Hfragment
    ipureintro
    simp
  | cons entry entries ih =>
    obtain ⟨l, v⟩ := entry
    iintro Hσ Hfragment
    icases Hfragment with ⟨Hl, Htail⟩
    ihave %hhead := app_state_lookup_heap $$ Hσ Hl
    ihave %htail := ih $$ Hσ Htail
    ipureintro
    intro entry hmem
    rcases mem_cons.mp hmem with heq | hmem
    · subst entry
      exact hhead
    · exact htail entry hmem

/-- Exchange finite fragment ownership while updating exactly the matching heap locations. -/
theorem app_state_update_fragment (input output : List (Loc × Val rT))
    (hkeys : input.map fst = output.map fst)
    (hnodup : (input.map fst).Nodup) {σ : State rT} : iprop%
    ⊢ appStateAuth σ -∗ appHeapFragment input ==∗
      appStateAuth (σ.writeFragment output) ∗ appHeapFragment output := by
  induction input generalizing output σ with
  | nil =>
    cases output with
    | nil =>
      iintro Hσ Hfragment
      imodintro
      simp only [State.writeFragment, State.update_heap, LocHeap.writeFragment, foldl_nil]
      iframe
    | cons entry output => simp at hkeys
  | cons entry input ih =>
    obtain ⟨l, v⟩ := entry
    cases output with
    | nil => simp at hkeys
    | cons replacement output =>
      obtain ⟨key, w⟩ := replacement
      simp only [map_cons] at hkeys hnodup
      obtain ⟨rfl, htailkeys⟩ := List.cons.inj hkeys
      have htail := (nodup_cons.mp hnodup).2
      iintro Hσ Hfragment
      icases Hfragment with ⟨Hl, Htail⟩
      imod app_state_update_heap (w := w) $$ Hσ Hl with ⟨Hσ, Hl⟩
      isimp only [← insert_eq_PartialMap_insert] at Hσ
      imod ih output htailkeys htail $$ Hσ Htail with ⟨Hσ, Htail⟩
      imodintro
      rw [State.writeFragment_cons]
      iframe

end ProbLang
