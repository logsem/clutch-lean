module

public import Metrology.Iris.SpecUpdate
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.DetStep
import Metrology.Iris.LocalBI

/-! # Spec-side stepping rules

The rules `step_pure`, `step_alloc`, `step_load`, `step_store`, `step_alloctape` and `step_rand`
advance the spec program `⤇ K[e]` under `specUpdate`. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI COFE ProbLang MeasureTheory.Measure DetHeadStep ExtTreeMap State

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

/-! ## Spec stepping rules (the `step_*` family) -/

section Rules

/-! Each rule checks the configuration against `⤇`, updates the ghost state and exhibits the
deterministic step. -/

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] [SpecGS rT GF]
variable {E : CoPset} (K : Ectx rT)
local bi IProp GF

/-- Spec step: a pure reduction `e ⇝ⁿ e'` under an evaluation context `K`. -/
theorem step_pure {e e' : Exp rT} {φ : Prop} {n : ℕ}
    (Hφ : φ) [Hex : PureExec φ n e e'] :
    ⤇ (K.fill e) ⊢ specUpdate rT E (⤇ (K.fill e')) := by
  have HexK : PureExec φ n (K.fill e) (K.fill e') := PureExec.fill K
  iintro HK
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %rfl := specAuth_specFrag_agree $$ Hρ HK
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  imodintro
  iexists ⟨K.fill e', σ⟩, n
  isplitr
  · ipureintro; exact pexecN_of_PureExec σ Hφ
  isplitl [HρNew] <;> iassumption

/-- Spec step: heap allocation, returning a fresh location with its points-to. -/
theorem step_alloc {v : Exp rT} (hv : IsVal v) :
    ⤇ (K.fill (.alloc v)) ⊢
      specUpdate rT E iprop(∃ (l : Loc), (⤇ (K.fill pl(#loc l))) ∗ (l ↦ₛ ⟨v, hv, hv.lc⟩)) := by
  iintro HK
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %rfl := specAuth_specFrag_agree $$ Hρ HK
  set l := σ.heap.fresh with hl
  set σ' := σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l ⟨v, hv, hv.lc⟩)
    with hσ'
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HAlloc := spec_auth_heap_alloc (e := K.fill pl(#loc l)) $$ HρNew
  imod HAlloc with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill pl(#loc l), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq : σ.update_heap (·.insert σ.heap.fresh ⟨v, hv, hv.lc⟩) = σ' := by
      simp [hσ', update_heap, insert_eq_PartialMap_insert, hl]
    rw [← hstate_eq]
    exact ((alloc hv σ).toDetStep).fill K
  isplitl [HρFinal]
  · iassumption
  iexists σ.heap.fresh
  isplitl [HKNew] <;> iassumption

/-- Spec step: load from a location whose points-to is owned. -/
theorem step_load {l : Loc} {v : Val rT} :
    iprop((⤇ (K.fill pl(!#loc l))) ∗ (l ↦ₛ v)) ⊢
      specUpdate rT E iprop((⤇ (K.fill (Exp.ofVal v))) ∗ (l ↦ₛ v)) := by
  iintro ⟨HK, Hl⟩
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %rfl := specAuth_specFrag_agree $$ Hρ HK
  ihave %hlk := spec_auth_lookup_heap $$ Hρ Hl
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  imodintro
  iexists ⟨K.fill (Exp.ofVal v), σ⟩, 1
  isplitr
  · ipureintro
    exact pexecN_1_of_DetStep (((load σ hlk).toDetStep).fill K)
  iframe

/-- Spec step: store to a location whose points-to is owned, updating it. -/
theorem step_store {l : Loc} {e : Exp rT} {v_old v_new : Val rT}
    (hnew : e.toVal? = some v_new) :
    iprop((⤇ (K.fill (.store pl(#loc l) e))) ∗ (l ↦ₛ v_old)) ⊢
      specUpdate rT E iprop((⤇ (K.fill pl(#()))) ∗ (l ↦ₛ v_new)) := by
  iintro ⟨HK, Hl⟩
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %rfl := specAuth_specFrag_agree $$ Hρ HK
  ihave %hlk := spec_auth_lookup_heap $$ Hρ Hl
  set σ' := σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l v_new) with hσ'
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HUpd := spec_auth_update_heap $$ HρNew Hl
  imod HUpd with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill pl(#()), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq : σ.update_heap (·.insert l v_new) = σ' := by
      simp [hσ', update_heap, insert_eq_PartialMap_insert]
    rw [← hstate_eq]
    exact ((store σ hlk hnew).toDetStep).fill K
  iframe

/-- Spec step: tape allocation, returning a fresh label with its empty tape. -/
theorem step_alloctape (z : Int) :
    ⤇ (K.fill (pl(tape(#z)))) ⊢
      specUpdate rT E iprop(∃ (l : Loc),
        (⤇ (K.fill pl(#lbl l))) ∗ (l ↪ₛ Tape.empty z)) := by
  iintro HK
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %rfl := specAuth_specFrag_agree $$ Hρ HK
  set l := σ.tapes.fresh with hl
  set σ' := σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l (Tape.empty z)) with hσ'
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HAlloc := spec_auth_tape_alloc (e := K.fill pl(#lbl l)) $$ HρNew
  imod HAlloc with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill pl(#lbl l), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq : σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z)) = σ' := by
      simp [hσ', update_tapes, insert_eq_PartialMap_insert, hl]
    rw [← hstate_eq]
    exact ((DetHeadStep.tape σ).toDetStep).fill K
  isplitl [HρFinal]
  · iassumption
  iexists σ.tapes.fresh
  isplitl [HKNew] <;> iassumption

/-- Spec step: `rand` reads and pops the head of a non-empty owned tape. -/
theorem step_rand {z : Int} (l : Loc)
    (n : { k : Int // 0 ≤ k ∧ k < z }) (ns : List { k : Int // 0 ≤ k ∧ k < z }) :
    iprop((⤇ (K.fill (pl(rand(#z, #lbl l))))) ∗ (l ↪ₛ ⟨z, n :: ns⟩)) ⊢
      specUpdate rT E iprop((⤇ (K.fill pl(#int n))) ∗ (l ↪ₛ ⟨z, ns⟩)) := by
  iintro ⟨HK, Hl⟩
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %rfl := specAuth_specFrag_agree $$ Hρ HK
  ihave %hlk := spec_auth_lookup_tape $$ Hρ Hl
  set σ' := σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l ⟨z, ns⟩) with hσ'
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HUpd := spec_auth_update_tape $$ HρNew Hl
  imod HUpd with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill pl(#int n), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq : σ.update_tapes (·.insert l ⟨z, ns⟩) = σ' := by
      simp [hσ', update_tapes, insert_eq_PartialMap_insert]
    rw [← hstate_eq]
    exact ((rand_tape l n ns hlk).toDetStep).fill K
  iframe

end Rules

end ProbLang
