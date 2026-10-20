module

public import Metrology.Iris.SpecUpdate
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.DetStep

@[expose] public section

/-! # Spec-side stepping rules

Rules `step_*` advance the spec program under `specUpdate`, e.g. `step_pure`, `step_rand`. -/

open Std Iris Iris.Std Iris.BI COFE ProbLang

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

/-! ## Bridge: `DetStep` ⇒ `pexecN 1 ρ = MeasureTheory.Measure.dirac ρ'` -/

/-- One-step deterministic advance: `DetStep ρ ρ'` gives `pexecN 1 ρ = dirac ρ'`. -/
theorem pexecN_1_of_DetStep {ρ ρ' : Cfg rT} (h : DetStep ρ ρ') :
    pexecN 1 ρ = MeasureTheory.Measure.dirac ρ' := by
  rw [pexecN_one]
  obtain ⟨-, h2⟩ := h
  have hnv : ¬ ρ.expr.isValue := by
    refine val_stuck (σ := ρ.2) ?_
    simp [h2]
  rw [stepOrFinal_not_isValue hnv]
  exact h2

/-- `n`-step version: `DetExec n ρ ρ'` gives `pexecN n ρ = dirac ρ'`. -/
theorem pexecN_of_DetExec {n : ℕ} {ρ ρ' : Cfg rT} (h : DetExec n ρ ρ') :
    pexecN n ρ = MeasureTheory.Measure.dirac ρ' := by
  induction n generalizing ρ with
  | zero => obtain ⟨⟨rfl⟩⟩ := h.det_exec; rfl
  | succ k ih =>
    obtain ⟨ρmid, hstep, hrest⟩ := h.det_exec
    rw [show k + 1 = 1 + k from Nat.add_comm _ _, pexecN_plus,
        pexecN_1_of_DetStep hstep,
        MeasureTheory.Measure.dirac_bind pexecN_measurable, ih ⟨hrest⟩]

/-- `nsteps PureStep n e1 e2` at a fixed state gives `DetExec n ⟨e1,σ⟩ ⟨e2,σ⟩`. -/
theorem DetExec.of_nsteps_PureStep {n : ℕ} {e1 e2 : Exp rT} (σ : State rT)
    (h : nsteps PureStep n e1 e2) :
    DetExec n ⟨e1, σ⟩ ⟨e2, σ⟩ := by
  induction n generalizing e1 with
  | zero => simp [nsteps] at h; subst h; exact ⟨rfl⟩
  | succ k ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    exact (ih hrest).succ ⟨hstep.safe σ, hstep.det σ⟩

/-- `PureExec φ n e1 e2 + φ` gives `pexecN n ⟨e1,σ⟩ = dirac ⟨e2,σ⟩`. -/
theorem pexecN_of_PureExec {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    [h : PureExec φ n e1 e2] (σ : State rT) (hφ : φ) :
    pexecN n (⟨e1, σ⟩ : Cfg rT) = MeasureTheory.Measure.dirac ⟨e2, σ⟩ :=
  pexecN_of_DetExec (DetExec.of_nsteps_PureStep σ (h.pure_exec hφ))

/-- Bridge: `ExtTreeMap.insert` and `PartialMap.insert` agree extensionally. -/
theorem ExtTreeMap.insert_eq_PartialMap_insert {V : Type _}
    (h : LocHeap V) (l : Loc) (v : V) :
    h.insert l v = PartialMap.insert h l v :=
  ExtTreeMap.ext_getElem? fun k => by
    show (h.insert l v)[k]? = (h.alter l (fun _ => some v))[k]?
    simp [ExtTreeMap.getElem?_insert, ExtTreeMap.getElem?_alter]

/-! ## Per-redex `DetHeadStep` lemmas (tape-flavored)

The heap variants `DetHeadStep.alloc`/`load`/`store` already live in `DetStep.lean`.
The two below are tape-specific and used by `step_alloctape` / `step_rand`. -/

/-- Tape allocation: `tape #z` deterministically allocates a fresh empty tape of
bound `z`. -/
theorem DetHeadStep.tape {z : Int} (σ : State rT) :
    DetHeadStep ⟨pl(tape(#(.int z))), σ⟩
      ⟨pl(#(.lbl σ.tapes.fresh)),
       σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))⟩ :=
  .of_det _ _
    (by obtain ⟨_, hd⟩ := Exp.toVal?_eq_some_of_isValue (e := (pl(#(.int z)) : Exp rT)) ⟨.lit⟩;
        simp [Exp.decompItem, hd])
    (by simp [headStep])

/-- Tape rand: with `σ.tapes[α] = some ⟨z, n :: ns⟩`, the random sample
`rand z α` deterministically returns `n` and pops the head. -/
theorem DetHeadStep.rand_tape {z : Int} (l : Loc)
    (n : { k : Int // 0 ≤ k ∧ k < z }) (ns : List { k : Int // 0 ≤ k ∧ k < z })
    {σ : State rT} (htape : σ.tapes[l]? = some ⟨z, n :: ns⟩) :
    DetHeadStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩
      ⟨pl(#(.int n)), σ.update_tapes (·.insert l ⟨z, ns⟩)⟩ :=
  .of_det _ _
    (by obtain ⟨_, hd1⟩ := Exp.toVal?_eq_some_of_isValue (e := (pl(#(.lbl l)) : Exp rT)) ⟨.lit⟩
        obtain ⟨_, hd2⟩ := Exp.toVal?_eq_some_of_isValue (e := (pl(#(.int z)) : Exp rT)) ⟨.lit⟩
        simp [Exp.decompItem, hd1, hd2])
    (by simp [headStep, htape])

/-! ## Stepping rules over `Cfg.specAuth` -/

section Rules

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] [SpecGS rT GF]

/-- Pure reduction under an evaluation context. -/
theorem step_pure {E : CoPset} (K : Ectx rT) {e e' : Exp rT} {φ : Prop} {n : ℕ}
    (Hφ : φ) [Hex : PureExec φ n e e'] :
    ⤇ (K.fill e) ⊢@{IProp GF} specUpdate rT E (⤇ (K.fill e')) := by
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

/-- Allocation under an evaluation context. -/
theorem step_alloc {E : CoPset} (K : Ectx rT) {v : Exp rT} (hv : IsVal v) :
    ⤇ (K.fill (.alloc v)) ⊢@{IProp GF}
      specUpdate rT E iprop(∃ (l : Loc), (⤇ (K.fill pl(#(.loc l)))) ∗ (l ↦ₛ ⟨v, hv, hv.lc⟩)) := by
  iintro HK
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %rfl := specAuth_specFrag_agree $$ Hρ HK
  set l := σ.heap.fresh with hl
  set σ' := σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l ⟨v, hv, hv.lc⟩)
    with hσ'
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HAlloc := spec_auth_heap_alloc
    (e := K.fill pl(#(.loc l))) $$ HρNew
  imod HAlloc with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill pl(#(.loc l)), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq :
        σ.update_heap (·.insert σ.heap.fresh ⟨v, hv, hv.lc⟩) = σ' := by
      simp [hσ', State.update_heap, ExtTreeMap.insert_eq_PartialMap_insert, hl]
    rw [← hstate_eq]
    exact ((DetHeadStep.alloc hv σ).toDetStep).fill K
  isplitl [HρFinal]
  · iassumption
  iexists σ.heap.fresh
  isplitl [HKNew] <;> iassumption

/-- Heap load under an evaluation context. -/
theorem step_load {E : CoPset} (K : Ectx rT) {l : Loc} {v : Val rT} :
    iprop((⤇ (K.fill pl(!#(.loc l)))) ∗ (l ↦ₛ v)) ⊢@{IProp GF}
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

/-- Heap store under an evaluation context. -/
theorem step_store {E : CoPset} (K : Ectx rT) {l : Loc} {e : Exp rT} {v_old v_new : Val rT}
    (hv : IsVal e) (hnew : e.toVal? = some v_new) :
    iprop((⤇ (K.fill (.store pl(#(.loc l)) e))) ∗ (l ↦ₛ v_old)) ⊢@{IProp GF}
      specUpdate rT E iprop((⤇ (K.fill pl(#(.unit)))) ∗ (l ↦ₛ v_new)) := by
  iintro ⟨HK, Hl⟩
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %rfl := specAuth_specFrag_agree $$ Hρ HK
  ihave %hlk := spec_auth_lookup_heap $$ Hρ Hl
  set σ' := σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l v_new)
    with hσ'
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HUpd := spec_auth_update_heap
    (l := l) $$ HρNew Hl
  imod HUpd with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill pl(#(.unit)), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq : σ.update_heap (·.insert l v_new) = σ' := by
      simp [hσ', State.update_heap, ExtTreeMap.insert_eq_PartialMap_insert]
    rw [← hstate_eq]
    exact ((DetHeadStep.store hv σ hlk hnew).toDetStep).fill K
  iframe

/-- Allocate a tape under an evaluation context. -/
theorem step_alloctape {E : CoPset} (K : Ectx rT) (z : Int) :
    ⤇ (K.fill (pl(tape(#(.int z))))) ⊢@{IProp GF}
      specUpdate rT E iprop(∃ (l : Loc),
        (⤇ (K.fill pl(#(.lbl l)))) ∗ (l ↪ₛ Tape.empty z)) := by
  iintro HK
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %rfl := specAuth_specFrag_agree $$ Hρ HK
  set l := σ.tapes.fresh with hl
  set σ' := σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l (Tape.empty z))
    with hσ'
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HAlloc := spec_auth_tape_alloc
    (e := K.fill pl(#(.lbl l))) $$ HρNew
  imod HAlloc with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill pl(#(.lbl l)), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq :
        σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z)) = σ' := by
      simp [hσ', State.update_tapes, ExtTreeMap.insert_eq_PartialMap_insert, hl]
    rw [← hstate_eq]
    exact ((DetHeadStep.tape σ).toDetStep).fill K
  isplitl [HρFinal]
  · iassumption
  iexists σ.tapes.fresh
  isplitl [HKNew] <;> iassumption

/-- Read from a non-empty tape under an evaluation context. -/
theorem step_rand {E : CoPset} (K : Ectx rT) {z : Int} (l : Loc)
    (n : { k : Int // 0 ≤ k ∧ k < z }) (ns : List { k : Int // 0 ≤ k ∧ k < z }) :
    iprop((⤇ (K.fill (pl(rand(#(.int z), #(.lbl l)))))) ∗ (l ↪ₛ ⟨z, n :: ns⟩))
        ⊢@{IProp GF}
      specUpdate rT E iprop((⤇ (K.fill pl(#(.int n)))) ∗ (l ↪ₛ ⟨z, ns⟩)) := by
  iintro ⟨HK, Hl⟩
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %rfl := specAuth_specFrag_agree $$ Hρ HK
  ihave %hlk := spec_auth_lookup_tape $$ Hρ Hl
  set σ' := σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l ⟨z, ns⟩)
    with hσ'
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HUpd := spec_auth_update_tape
    (l := l) $$ HρNew Hl
  imod HUpd with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill pl(#(.int n)), σ'⟩, 1
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
