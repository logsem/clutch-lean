module

public import Metrology.ProbLang.CtxStep
public import Metrology.ProbLang.Syntax.Subset

@[expose] public section

/-! # Stepping stays in a syntactic subset
Head and primitive steps keep a configuration in its subset, and leave a state without tapes
alone outside the subset with tapes. -/

noncomputable section

open MeasureTheory Measure Std

namespace ProbLang

variable {rT : Type} {F : Features}

/-- Storing a value of the subset keeps the heap in the subset. -/
theorem State.InSubset.insert {σ : State rT} (hσ : σ.InSubset F) {ℓ : Loc} {v : Val rT}
    (hv : v.InSubset F) : (σ.updateHeap (·.insert ℓ v)).InSubset F := by
  refine ⟨?_, hσ.2⟩
  intro ℓ' v' h
  simp only [State.updateHeap, ExtTreeMap.getElem?_insert] at h
  split at h
  · cases h
    exact hv
  · exact hσ.1 ℓ' v' h

/-- Allocating a block of a value of the subset keeps the heap in the subset. -/
theorem State.InSubset.allocN {σ : State rT} (hσ : σ.InSubset F) {v : Val rT}
    (hv : v.InSubset F) (n : ℕ) : (σ.updateHeap (LocHeap.allocN · v n)).InSubset F := by
  refine ⟨?_, hσ.2⟩
  intro ℓ v' h
  simp only [State.updateHeap, LocHeap.allocN_get?] at h
  split at h
  · cases h
    exact hv
  · exact hσ.1 ℓ v' h

/-- Inserting a tape whose values lie in the subset keeps the state in the subset. -/
theorem State.InSubset.insertTape {σ : State rT} (hσ : σ.InSubset F) {α : Lbl}
    {t : Tape rT} (ht : t.arg.InSubset F ∧ ∀ k w, t.presamples k = some w → w.InSubset F) :
    (σ.updateTapes (·.insert α t)).InSubset F := by
  refine ⟨hσ.1, ?_⟩
  intro β t' hlookup
  simp only [State.updateTapes, ExtTreeMap.getElem?_insert] at hlookup
  split at hlookup
  · cases hlookup
    exact ht
  · exact hσ.2 β t' hlookup

/-- Shifting a tape preserves membership of all its stored values. -/
theorem Tape.inSubset_shift {t : Tape rT}
    (ht : t.arg.InSubset F ∧ ∀ k w, t.presamples k = some w → w.InSubset F) :
    t.shift.arg.InSubset F ∧ ∀ k w, t.shift.presamples k = some w → w.InSubset F := by
  refine ⟨ht.1, ?_⟩
  intro k w hw
  exact ht.2 (k + 1) w hw

variable [MeasurableSpace rT] [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangFFI rT]
  [ProbLangObs rT]

namespace HeadStepSupport

variable {e1 e2 : Exp rT} {σ1 σ2 : State rT} (h : HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩)
  (he : e1.InSubset F)
include h he

open Exp.InSubset (open')

/-- Outside the subset with tapes, a head step from a state without tapes leaves the tapes alone. -/
theorem tapes_eq (hF : F .tape = false) (ht : σ1.tapes = ∅) : σ2.tapes = σ1.tapes := by
  cases h <;> first
    | rfl
    | (subst_vars; rfl)
    | simp_all [Exp.InSubset, Exp.inSubset]

/-- Outside the subsets with sampling and foreign calls, a head step stays in the subset. -/
theorem inSubset [ProbLangDist.IsIntValued rT] (hσ : σ1.InSubset F) (hu : F .urand = false)
    (hs : F .sample = false) (hf : F .ffi = false) :
    e2.InSubset F ∧ σ2.InSubset F := by
  cases h <;> simp only [Exp.InSubset, Exp.inSubset, Bool.and_eq_true] at he
  case BetaLamS he' =>
    subst he'
    exact ⟨open' he.1 he.2, hσ⟩
  case BetaFixS he' =>
    subst he'
    refine ⟨?_, hσ⟩
    simp only [Exp.InSubset, Exp.inSubset, Bool.and_eq_true]
    exact ⟨open' he.1 he.1, he.2⟩
  case UnOpS hev => exact ⟨UnOp.inSubset_eval hev.symm, hσ⟩
  case BinOpS hev => exact ⟨BinOp.inSubset_eval hev.symm, hσ⟩
  case ScrutSuccessS hm =>
    refine ⟨?_, hσ⟩
    simpa [Exp.InSubset, Exp.inSubset] using Pat.inSubset_tryMatch he hm
  case LoadS hl he' =>
    subst he'
    exact ⟨hσ.1 _ _ hl, hσ⟩
  case AllocS hv _ hσ' | StoreS hv _ hσ' =>
    subst hσ'
    refine ⟨rfl, hσ.insert ?_⟩
    show Exp.InSubset F (Exp.ofVal _)
    rw [Exp.ofVal_of_toVal_some hv]
    simpa using he
  case AllocNS hv _ _ hσ' =>
    subst hσ'
    refine ⟨rfl, hσ.allocN ?_ _⟩
    show Exp.InSubset F (Exp.ofVal _)
    rw [Exp.ofVal_of_toVal_some hv]
    simpa using he.2
  case TapeS hv _ hσ' =>
    subst hσ'
    refine ⟨rfl, hσ.insertTape ⟨?_, ?_⟩⟩
    · simp only [Tape.empty]
      show Exp.InSubset F (Exp.ofVal _)
      rw [Exp.ofVal_of_toVal_some hv]
      exact he.2
    · simp [Tape.empty]
  case SampleTapeS _ _ hhead htape hσ' =>
    subst hσ'
    have ht := hσ.2 _ _ htape
    exact ⟨ht.2 0 _ hhead, hσ.insertTape (Tape.inSubset_shift ht)⟩
  case UnifIntS | UnifIntTapeOtherS =>
    obtain ⟨z, rfl⟩ := ProbLangDist.exists_int_of_dist_pos (by assumption)
    exact ⟨rfl, hσ⟩
  case UnifIntTapeEmptyS =>
    obtain ⟨z, rfl⟩ := ProbLangDist.exists_int_of_dist_pos (by assumption)
    subst_vars
    exact ⟨rfl, hσ.insertTape (Tape.inSubset_shift (hσ.2 _ _ (by assumption)))⟩
  case SampleS | SampleTapeEmptyS | SampleTapeOtherS =>
    simp only [Features.allowsFamily] at he
    split at he
    · simp_all
    · split at he <;> simp_all
  case RandvarS _ _ hσ' =>
    subst hσ'
    exact ⟨rfl, hσ⟩
  case TestS => exact ⟨rfl, hσ⟩
  all_goals simp_all [Exp.InSubset, Exp.inSubset]

end HeadStepSupport

variable [ProbLangDist.IsIntValued rT]

/-- Outside sampling and foreign calls, a positive-mass step stays in the subset. -/
theorem Cfg.InSubset.primStep_succ {e e' : Exp rT} {σ σ' : State rT}
    (hρ : Cfg.InSubset F ⟨e, σ⟩) (hu : F .urand = false)
    (hs : F .sample = false) (hf : F .ffi = false)
    (h : 0 < primStep ⟨e, σ⟩ {⟨e', σ'⟩}) :
    Cfg.InSubset F ⟨e', σ'⟩ ∧ (F .tape = false → σ.tapes = ∅ → σ'.tapes = σ.tapes) := by
  obtain ⟨he, hσ⟩ := hρ
  rcases hd : e.decomp with ⟨K, e0⟩
  obtain ⟨hK, he0⟩ := he.decomp
  simp only [hd] at hK he0
  simp only [primStep, hd] at h
  obtain ⟨⟨e1, σ1⟩, heq, hpos⟩ := map_singleton_pos (by measurability) (Ectx.fillCfg_injective K) h
  simp only [Ectx.fillCfg, Cfg.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hsupp := Possible.headStepSupport (possible_iff_pos.mpr hpos)
  obtain ⟨he1, hσ1⟩ := hsupp.inSubset he0 hσ hu hs hf
  exact ⟨⟨Ectx.inSubset_fill_mpr K e1 ⟨hK, he1⟩, hσ1⟩, fun hF => hsupp.tapes_eq he0 hF⟩

end ProbLang
