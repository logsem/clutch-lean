module

public import Metrology.Iris.SpecUpdate
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.DetStep
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Spec-side stepping rules

Rules `step_pure`, `step_alloc`, `step_load`, `step_store`, `step_alloctape`, `step_rand` advance
the spec program `⤇ K[e]` under `specUpdate`, using the ghost state of `SpecProgram.lean`. -/

open Std Iris Iris.Std Iris.BI COFE ProbLang MeasureTheory.Measure

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

/-! ## Deterministic steps give Dirac `pexecN` -/

/-- A deterministic step `DetStep ρ ρ'` makes one-step execution the Dirac measure at `ρ'`. -/
theorem pexecN_1_of_DetStep {ρ ρ' : Cfg rT} (h : DetStep ρ ρ') :
    pexecN 1 ρ = dirac ρ' := by
  rw [pexecN_one]
  obtain ⟨-, h2⟩ := h
  have hnv : ¬ ρ.expr.isValue := by
    refine val_stuck (σ := ρ.2) ?_
    simp [h2]
  rw [stepOrFinal_not_isValue hnv]
  exact h2

/-- `n`-step version of `pexecN_1_of_DetStep`. -/
theorem pexecN_of_DetExec {n : ℕ} {ρ ρ' : Cfg rT} (h : DetExec n ρ ρ') :
    pexecN n ρ = dirac ρ' := by
  induction n generalizing ρ with
  | zero => obtain ⟨⟨rfl⟩⟩ := h.det_exec; rfl
  | succ k ih =>
    obtain ⟨ρmid, hstep, hrest⟩ := h.det_exec
    rw [show k + 1 = 1 + k from Nat.add_comm _ _, pexecN_plus,
        pexecN_1_of_DetStep hstep,
        dirac_bind pexecN_measurable, ih ⟨hrest⟩]

/-- Pure steps `nsteps PureStep n e1 e2` are deterministic executions at any fixed state `σ`. -/
theorem DetExec.of_nsteps_PureStep {n : ℕ} {e1 e2 : Exp rT} (σ : State rT)
    (h : nsteps PureStep n e1 e2) :
    DetExec n ⟨e1, σ⟩ ⟨e2, σ⟩ := by
  induction n generalizing e1 with
  | zero => simp [nsteps] at h; subst h; exact ⟨rfl⟩
  | succ k ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    exact (ih hrest).succ ⟨hstep.safe σ, hstep.det σ⟩

/-- Under `PureExec φ n e1 e2` and `φ`, `n`-step execution is the Dirac measure at `⟨e2, σ⟩`. -/
theorem pexecN_of_PureExec {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    [h : PureExec φ n e1 e2] (σ : State rT) (hφ : φ) :
    pexecN n (⟨e1, σ⟩ : Cfg rT) = dirac ⟨e2, σ⟩ :=
  pexecN_of_DetExec (DetExec.of_nsteps_PureStep σ (h.pure_exec hφ))

/-! ## Tape head steps as deterministic (heap ones are in `DetStep.lean`) -/

/-- Tape allocation: `tape #z` deterministically allocates a fresh empty tape of
bound `z`. -/
theorem DetHeadStep.tape {z : Int} (σ : State rT) :
    DetHeadStep ⟨pl(tape(#z)), σ⟩
      ⟨pl(#lbl σ.tapes.fresh),
       σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))⟩ :=
  .of_det _ _
    (by obtain ⟨_, hd⟩ := Exp.toVal?_eq_some_of_isValue (e := (pl(#int z) : Exp rT)) ⟨.lit⟩;
        simp [Exp.decompItem, hd])
    (by simp [headStep])

/-- Tape rand: with `σ.tapes[α] = some ⟨z, n :: ns⟩`, the random sample
`rand z α` deterministically returns `n` and pops the head. -/
theorem DetHeadStep.rand_tape {z : Int} (l : Loc)
    (n : { k : Int // 0 ≤ k ∧ k < z }) (ns : List { k : Int // 0 ≤ k ∧ k < z })
    {σ : State rT} (htape : σ.tapes[l]? = some ⟨z, n :: ns⟩) :
    DetHeadStep ⟨pl(rand(#z, #lbl l)), σ⟩
      ⟨pl(#int n), σ.update_tapes (·.insert l ⟨z, ns⟩)⟩ :=
  .of_det _ _
    (by obtain ⟨_, hd1⟩ := Exp.toVal?_eq_some_of_isValue (e := (pl(#lbl l) : Exp rT)) ⟨.lit⟩
        obtain ⟨_, hd2⟩ := Exp.toVal?_eq_some_of_isValue (e := (pl(#int z) : Exp rT)) ⟨.lit⟩
        simp [Exp.decompItem, hd1, hd2])
    (by simp [headStep, htape])

/-! ## Spec stepping rules (the `step_*` family) -/

section Rules

/-! Each rule checks the configuration against `⤇`, updates the ghost state and exhibits the
deterministic step, at `defaultSpecUpdateGS` (where `specInterp` is `Cfg.specAuth`). -/

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
      simp [hσ', State.update_heap, ExtTreeMap.insert_eq_PartialMap_insert, hl]
    rw [← hstate_eq]
    exact ((DetHeadStep.alloc hv σ).toDetStep).fill K
  isplitl [HρFinal]
  · iassumption
  iexists σ.heap.fresh
  isplitl [HKNew] <;> iassumption

/-- Spec step: load from a location whose points-to we own. -/
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
    exact pexecN_1_of_DetStep (((DetHeadStep.load σ hlk).toDetStep).fill K)
  iframe

/-- Spec step: store to a location whose points-to we own, updating it. -/
theorem step_store {l : Loc} {e : Exp rT} {v_old v_new : Val rT}
    (_hv : IsVal e) (hnew : e.toVal? = some v_new) :
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
  ihave HUpd := spec_auth_update_heap (l := l) $$ HρNew Hl
  imod HUpd with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill pl(#()), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq : σ.update_heap (·.insert l v_new) = σ' := by
      simp [hσ', State.update_heap, ExtTreeMap.insert_eq_PartialMap_insert]
    rw [← hstate_eq]
    exact ((DetHeadStep.store σ hlk hnew).toDetStep).fill K
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
      simp [hσ', State.update_tapes, ExtTreeMap.insert_eq_PartialMap_insert, hl]
    rw [← hstate_eq]
    exact ((DetHeadStep.tape σ).toDetStep).fill K
  isplitl [HρFinal]
  · iassumption
  iexists σ.tapes.fresh
  isplitl [HKNew] <;> iassumption

/-- Spec step: `rand` reads and pops the head of a non-empty tape we own. -/
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
  ihave HUpd := spec_auth_update_tape (l := l) $$ HρNew Hl
  imod HUpd with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill pl(#int n), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq : σ.update_tapes (·.insert l ⟨z, ns⟩) = σ' := by
      simp [hσ', State.update_tapes, ExtTreeMap.insert_eq_PartialMap_insert]
    rw [← hstate_eq]
    exact ((DetHeadStep.rand_tape l n ns hlk).toDetStep).fill K
  iframe

end Rules

end ProbLang
