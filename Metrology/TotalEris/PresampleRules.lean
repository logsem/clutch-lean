module

public import Metrology.TotalEris.TotalPrimitiveLaws
public import Metrology.TotalEris.TotalLifting
public import Metrology.TotalEris.Glm
public import Metrology.TotalEris.ErrorRules
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Presample rules

The rules in this file fill either one chosen hole or every hole of a unified family tape. The
support predicates are stated by observable tape coordinates, rather than as images, so they remain
measurable when the sampled value type is uncountable.
-/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang

variable {rT : Type _}

/-! ## Measurable supports -/

namespace Tape

/-- Tapes obtained by filling position `k` of `t` with a value in `S`. -/
def fillAtSupport (t : Tape rT) (k : ℕ) (S : Set (Val rT)) : Set (Tape rT) :=
  {u | u.name = t.name ∧ u.arg = t.arg ∧
    (∃ w ∈ S, u.presamples k = some w) ∧
    ∀ j, j ≠ k → u.presamples j = t.presamples j}

/-- The coordinate description of `fillAtSupport` is measurable. -/
theorem measurableSet_fillAtSupport [MeasurableSpace rT] [LawfulProbLangℝ rT]
    {t : Tape rT} {k : ℕ} {S : Set (Val rT)} (hS : MeasurableSet S) :
    MeasurableSet (fillAtSupport t k S) := by
  have hname : MeasurableSet {u : Tape rT | u.name = t.name} :=
    Tape.measurable_name (measurableSet_singleton _)
  have harg : MeasurableSet {u : Tape rT | u.arg = t.arg} :=
    Tape.measurable_arg (measurableSet_singleton _)
  have hk : MeasurableSet {u : Tape rT | ∃ w ∈ S, u.presamples k = some w} := by
    have heq : {u : Tape rT | ∃ w ∈ S, u.presamples k = some w} =
        (fun u : Tape rT => u.presamples k) ⁻¹' (some '' S) := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image]
      exact ⟨fun ⟨w, hw, heq⟩ => ⟨w, hw, heq.symm⟩,
        fun ⟨w, hw, heq⟩ => ⟨w, hw, heq.symm⟩⟩
    rw [heq]
    exact (Tape.measurable_presamples_apply k) (MeasurableSet.image_some hS)
  have hrest : MeasurableSet
      {u : Tape rT | ∀ j, j ≠ k → u.presamples j = t.presamples j} := by
    have heq : {u : Tape rT | ∀ j, j ≠ k → u.presamples j = t.presamples j} =
        ⋂ j : ℕ, if j = k then Set.univ else
          {u : Tape rT | u.presamples j = t.presamples j} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h j
        by_cases hj : j = k
        · simp [hj]
        · simpa [hj] using h j hj
      · intro h j hj
        simpa [hj] using h j
    rw [heq]
    refine MeasurableSet.iInter fun j => ?_
    split_ifs
    · exact MeasurableSet.univ
    · exact (Tape.measurable_presamples_apply j) (measurableSet_singleton _)
  exact hname.inter (harg.inter (hk.inter hrest))

/-- Filling an empty position maps `S` exactly onto `fillAtSupport`. -/
theorem fillAt_image_eq {t : Tape rT} {k : ℕ} {S : Set (Val rT)}
    (hk : t.presamples k = none) :
    (fun w => t.fillAt k w) '' S = fillAtSupport t k S := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨rfl, rfl, ⟨w, hw, ?_⟩, ?_⟩
    · simp [Tape.fillAt, Presamples.fillAt_of_none hk]
    · intro j hj
      simp [Tape.fillAt, Presamples.fillAt_of_none hk, hj]
  · rintro ⟨hname, harg, ⟨w, hw, hkw⟩, hrest⟩
    refine ⟨w, hw, ?_⟩
    cases t with
    | mk tn ta tp =>
      cases u with
      | mk un ua up =>
        simp only at hname harg hkw hrest hk ⊢
        subst un
        subst ua
        apply Tape.toTuple_injective
        apply Prod.ext
        · rfl
        apply Prod.ext
        · rfl
        change Presamples.fillAt tp k w = up
        rw [Presamples.fillAt_of_none hk]
        funext j
        by_cases hj : j = k
        · subst j
          simpa using hkw.symm
        · simpa [hj] using (hrest j hj).symm

/-- Tapes obtained by filling every hole of `t`. -/
def fillAllSupport (t : Tape rT) : Set (Tape rT) :=
  {u | u.name = t.name ∧ u.arg = t.arg ∧
    (∀ k, ∃ w, u.presamples k = some w) ∧
    ∀ k w, t.presamples k = some w → u.presamples k = some w}

/-- The coordinate description of `fillAllSupport` is measurable. -/
theorem measurableSet_fillAllSupport [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (t : Tape rT) : MeasurableSet (fillAllSupport t) := by
  have hname : MeasurableSet {u : Tape rT | u.name = t.name} :=
    Tape.measurable_name (measurableSet_singleton _)
  have harg : MeasurableSet {u : Tape rT | u.arg = t.arg} :=
    Tape.measurable_arg (measurableSet_singleton _)
  have hfull : MeasurableSet {u : Tape rT | ∀ k, ∃ w, u.presamples k = some w} := by
    have heq : {u : Tape rT | ∀ k, ∃ w, u.presamples k = some w} =
        ⋂ k : ℕ, (fun u : Tape rT => u.presamples k) ⁻¹' ({none}ᶜ) := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      constructor
      · intro h k
        obtain ⟨w, hw⟩ := h k
        simp [hw]
      · intro h k
        rcases hk : u.presamples k with _ | w
        · exact (h k hk).elim
        · exact ⟨w, rfl⟩
    rw [heq]
    exact MeasurableSet.iInter fun k =>
      (Tape.measurable_presamples_apply k) MeasurableSet.singleton_none.compl
  have hkeep : MeasurableSet
      {u : Tape rT | ∀ k w, t.presamples k = some w → u.presamples k = some w} := by
    have heq : {u : Tape rT | ∀ k w, t.presamples k = some w → u.presamples k = some w} =
        ⋂ k : ℕ, match t.presamples k with
          | none => Set.univ
          | some w => {u : Tape rT | u.presamples k = some w} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h k
        rcases hk : t.presamples k with _ | w
        · trivial
        · exact h k w hk
      · intro h k w hkw
        simpa [hkw] using h k
    rw [heq]
    refine MeasurableSet.iInter fun k => ?_
    rcases hk : t.presamples k with _ | w
    · exact MeasurableSet.univ
    · exact (Tape.measurable_presamples_apply k) (measurableSet_singleton _)
  exact hname.inter (harg.inter (hfull.inter hkeep))

/-- Filling every hole maps all streams exactly onto `fillAllSupport`. -/
theorem fillAll_range_eq (t : Tape rT) :
    Set.range t.fillAll = fillAllSupport t := by
  ext u
  constructor
  · rintro ⟨ω, rfl⟩
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact fun k => ⟨(t.presamples k).getD (ω k), by simp [Tape.fillAll]⟩
    · intro k w hkw
      simp [Tape.fillAll, hkw]
  · rintro ⟨hname, harg, hfull, hkeep⟩
    let ω : ℕ → Val rT := fun k => (u.presamples k).getD .unit
    refine ⟨ω, ?_⟩
    cases t with
    | mk tn ta tp =>
      cases u with
      | mk un ua up =>
        simp only at hname harg hfull hkeep ⊢
        subst un
        subst ua
        apply Tape.toTuple_injective
        apply Prod.ext
        · rfl
        apply Prod.ext
        · rfl
        funext k
        obtain ⟨w, hw⟩ := hfull k
        rcases ht : tp k with _ | v
        · change some ((tp k).getD ((up k).getD .unit)) = up k
          simp [ht, hw]
        · have hu := hkeep k v ht
          change some ((tp k).getD ((up k).getD .unit)) = up k
          simp [ht, hu]

end Tape

namespace TotalEris

/-- States obtained by filling position `k` of tape `α` from `S`. -/
def presampleAtSupport (σ : State rT) (α : Loc) (t : Tape rT) (k : ℕ)
    (S : Set (Val rT)) : Set (State rT) :=
  {σ' | σ'.heap = σ.heap ∧ σ'.rvs = σ.rvs ∧
    σ'.tapes[α]? ∈ some '' t.fillAtSupport k S ∧
    ∀ β, β ≠ α → σ'.tapes[β]? = σ.tapes[β]?}

/-- The support of one-position presampling is measurable. -/
theorem measurableSet_presampleAtSupport [MeasurableSpace rT] [LawfulProbLangℝ rT]
    {σ : State rT} {α : Loc} {t : Tape rT} {k : ℕ} {S : Set (Val rT)}
    (hS : MeasurableSet S) : MeasurableSet (presampleAtSupport σ α t k S) := by
  have hheap : MeasurableSet {σ' : State rT | σ'.heap = σ.heap} :=
    State.measurable_heap (measurableSet_singleton _)
  have hrvs : MeasurableSet {σ' : State rT | σ'.rvs = σ.rvs} :=
    State.measurable_rvs (measurableSet_singleton _)
  have hhere : MeasurableSet
      {σ' : State rT | σ'.tapes[α]? ∈ some '' t.fillAtSupport k S} :=
    ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
      (MeasurableSet.image_some (Tape.measurableSet_fillAtSupport hS))
  have hother : MeasurableSet
      {σ' : State rT | ∀ β, β ≠ α → σ'.tapes[β]? = σ.tapes[β]?} := by
    have heq : {σ' : State rT | ∀ β, β ≠ α → σ'.tapes[β]? = σ.tapes[β]?} =
        ⋂ β : Loc, if β = α then Set.univ else
          {σ' : State rT | σ'.tapes[β]? = σ.tapes[β]?} := by
      ext σ'
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h β
        by_cases hβ : β = α
        · simp [hβ]
        · simpa [hβ] using h β hβ
      · intro h β hβ
        simpa [hβ] using h β
    rw [heq]
    refine MeasurableSet.iInter fun β => ?_
    split_ifs
    · exact MeasurableSet.univ
    · exact ((LocHeap.measurable_getElem? β).comp State.measurable_tapes)
        (measurableSet_singleton _)
  exact hheap.inter (hrvs.inter (hhere.inter hother))

/-- The state support is the image used by `tapePresampleAt`. -/
theorem presampleAt_image_eq {σ : State rT} {α : Loc} {t : Tape rT} {k : ℕ}
    {S : Set (Val rT)} (ht : σ.tapes[α]? = some t) (hk : t.presamples k = none) :
    (fun w => σ.updateTapes (·.insert α (t.fillAt k w))) '' S =
      presampleAtSupport σ α t k S := by
  ext σ'
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨rfl, rfl, ?_, ?_⟩
    · refine ⟨t.fillAt k w, ?_, (State.upd_tape_some _ _ _).symm⟩
      rw [← Tape.fillAt_image_eq hk]
      exact ⟨w, hw, rfl⟩
    · exact fun β hβ => State.upd_diff_tape_tot hβ
  · rintro ⟨hheap, hrvs, ⟨u, hu, hlookup⟩, hother⟩
    have hu' : u ∈ (fun w => t.fillAt k w) '' S := (Tape.fillAt_image_eq hk).symm ▸ hu
    obtain ⟨w, hw, rfl⟩ := hu'
    refine ⟨w, hw, ?_⟩
    cases σ with
    | mk heap tapes rvs =>
      cases σ' with
      | mk heap' tapes' rvs' =>
        change heap' = heap at hheap
        change rvs' = rvs at hrvs
        change some (t.fillAt k w) = tapes'[α]? at hlookup
        change ∀ β, β ≠ α → tapes'[β]? = tapes[β]? at hother
        subst heap'
        subst rvs'
        change State.mk heap (tapes.insert α (t.fillAt k w)) rvs =
          State.mk heap tapes' rvs
        apply congrArg (fun ts => State.mk heap ts rvs)
        apply Std.ExtTreeMap.ext_getElem?
        intro β
        by_cases hβ : β = α
        · subst β
          simpa [Std.ExtTreeMap.getElem?_insert] using hlookup
        · simpa [Std.ExtTreeMap.getElem?_insert, Ne.symm hβ] using
            (hother β hβ).symm

/-- States obtained by filling every hole of tape `α`. -/
def presampleAllSupport (σ : State rT) (α : Loc) (t : Tape rT) : Set (State rT) :=
  {σ' | σ'.heap = σ.heap ∧ σ'.rvs = σ.rvs ∧
    σ'.tapes[α]? ∈ some '' t.fillAllSupport ∧
    ∀ β, β ≠ α → σ'.tapes[β]? = σ.tapes[β]?}

/-- The support of whole-stream presampling is measurable. -/
theorem measurableSet_presampleAllSupport [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (σ : State rT) (α : Loc) (t : Tape rT) :
    MeasurableSet (presampleAllSupport σ α t) := by
  have hheap : MeasurableSet {σ' : State rT | σ'.heap = σ.heap} :=
    State.measurable_heap (measurableSet_singleton _)
  have hrvs : MeasurableSet {σ' : State rT | σ'.rvs = σ.rvs} :=
    State.measurable_rvs (measurableSet_singleton _)
  have hhere : MeasurableSet
      {σ' : State rT | σ'.tapes[α]? ∈ some '' t.fillAllSupport} :=
    ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
      (MeasurableSet.image_some (Tape.measurableSet_fillAllSupport t))
  have hother : MeasurableSet
      {σ' : State rT | ∀ β, β ≠ α → σ'.tapes[β]? = σ.tapes[β]?} := by
    have heq : {σ' : State rT | ∀ β, β ≠ α → σ'.tapes[β]? = σ.tapes[β]?} =
        ⋂ β : Loc, if β = α then Set.univ else
          {σ' : State rT | σ'.tapes[β]? = σ.tapes[β]?} := by
      ext σ'
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h β
        by_cases hβ : β = α
        · simp [hβ]
        · simpa [hβ] using h β hβ
      · intro h β hβ
        simpa [hβ] using h β
    rw [heq]
    refine MeasurableSet.iInter fun β => ?_
    split_ifs
    · exact MeasurableSet.univ
    · exact ((LocHeap.measurable_getElem? β).comp State.measurable_tapes)
        (measurableSet_singleton _)
  exact hheap.inter (hrvs.inter (hhere.inter hother))

/-- The whole-stream state support is the image used by `tapePresampleAll`. -/
theorem presampleAll_range_eq {σ : State rT} {α : Loc} {t : Tape rT}
    (ht : σ.tapes[α]? = some t) :
    Set.range (fun ω => σ.updateTapes (·.insert α (t.fillAll ω))) =
      presampleAllSupport σ α t := by
  ext σ'
  constructor
  · rintro ⟨ω, rfl⟩
    refine ⟨rfl, rfl, ?_, ?_⟩
    · refine ⟨t.fillAll ω, ?_, (State.upd_tape_some _ _ _).symm⟩
      rw [← Tape.fillAll_range_eq t]
      exact ⟨ω, rfl⟩
    · exact fun β hβ => State.upd_diff_tape_tot hβ
  · rintro ⟨hheap, hrvs, ⟨u, hu, hlookup⟩, hother⟩
    have hu' : u ∈ Set.range t.fillAll := (Tape.fillAll_range_eq t).symm ▸ hu
    obtain ⟨ω, rfl⟩ := hu'
    refine ⟨ω, ?_⟩
    cases σ with
    | mk heap tapes rvs =>
      cases σ' with
      | mk heap' tapes' rvs' =>
        change heap' = heap at hheap
        change rvs' = rvs at hrvs
        change some (t.fillAll ω) = tapes'[α]? at hlookup
        change ∀ β, β ≠ α → tapes'[β]? = tapes[β]? at hother
        subst heap'
        subst rvs'
        change State.mk heap (tapes.insert α (t.fillAll ω)) rvs =
          State.mk heap tapes' rvs
        apply congrArg (fun ts => State.mk heap ts rvs)
        apply Std.ExtTreeMap.ext_getElem?
        intro β
        by_cases hβ : β = α
        · subst β
          simpa [Std.ExtTreeMap.getElem?_insert] using hlookup
        · simpa [Std.ExtTreeMap.getElem?_insert, Ne.symm hβ] using
            (hother β hβ).symm

/-! ## Program-logic rules -/

variable [MeasurableSpace rT] [LawfulProbLangℝ rT] [ProbLangDist rT]
  [ProbLangDist.IsIntValued rT] [ProbLangFFI rT] [ProbLangObs rT]
  {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Presample one empty tape position while distributing an expected error credit. -/
theorem twp_presample_adv_comp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {α : Loc} {t : Tape rT} {k : ℕ} {S : Set (Val rT)}
    {ε₁ : ENNReal} {ε₂ : Val rT → ENNReal}
    (hk : t.presamples k = none) (hS : MeasurableSet S)
    (hconc : Concentrated t.dist S) (hd : t.dist ≠ 0)
    (hε₂ : Measurable ε₂) (hInt : (∫⁻ w, ε₂ w ∂t.dist) ≤ ε₁)
    (hv : e.toVal? = none) : iprop%
    ↯ε₁ ∗ appTapesFrag α t ∗
      (∀ w, ⌜w ∈ S⌝ -∗ ↯(ε₂ w) -∗ appTapesFrag α (t.fillAt k w) -∗ tglWp E e Φ) ⊢
      tglWp E e Φ := by
  iintro ⟨Herr, Htape, Hcont⟩
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  ihave %hlookup := app_state_lookup_tape $$ Hσ Htape
  ihave ⟨Hε_now, Herr, %hLe⟩ := errInterp_supply_bound $$ [$Hε_now $Herr]
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  have hErase := ErasableExpr.tapePresampleAt hlookup hd k
  have hMeas := measurableSet_presampleAtSupport (σ := σ₁) (α := α) (t := t)
    (k := k) hS
  have hMap : tapePresampleAt σ₁ α k =
      t.dist.map fun w => σ₁.updateTapes (·.insert α (t.fillAt k w)) :=
    tapePresampleAt_eq_map hlookup hk
  have hConc : Concentrated (tapePresampleAt σ₁ α k)
      (presampleAtSupport σ₁ α t k S) := by
    rw [hMap, ← presampleAt_image_eq hlookup hk]
    exact Concentrated.map (State.measurable_fillAtTape σ₁ α t k)
      ((presampleAt_image_eq hlookup hk).symm ▸ hMeas) hconc
  have hCredit :
      (∫⁻ σ', presampleAtCredit α k ε₂ σ' ∂tapePresampleAt σ₁ α k) ≤ ε₁ := by
    rw [hMap, MeasureTheory.lintegral_map (measurable_presampleAtCredit α k hε₂)
      (State.measurable_fillAtTape σ₁ α t k)]
    simpa only [presampleAtCredit_update hk] using hInt
  have hExpected : (0 : ENNReal) +
      ∫⁻ σ', ((ε_now - ε₁) + presampleAtCredit α k ε₂ σ')
        ∂tapePresampleAt σ₁ α k ≤ ε_now := by
    have hProb : MeasureTheory.IsProbabilityMeasure (tapePresampleAt σ₁ α k) :=
      tapePresampleAt.isProbabilityMeasure hlookup hd
    rw [zero_add, MeasureTheory.lintegral_add_left measurable_const,
      MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
    calc
      (ε_now - ε₁) + ∫⁻ σ', presampleAtCredit α k ε₂ σ'
          ∂tapePresampleAt σ₁ α k ≤ (ε_now - ε₁) + ε₁ := by gcongr
      _ = ε_now := tsub_add_cancel_of_le hLe
  iapply glm'_erasable_step
  iexists (tapePresampleAt σ₁ α k), (presampleAtSupport σ₁ α t k S),
    0, (fun σ' => (ε_now - ε₁) + presampleAtCredit α k ε₂ σ')
  have hPgl := Pgl.of_concentrated hConc
  have hMeas' : MeasurableSet {σ' | σ' ∈ presampleAtSupport σ₁ α t k S} := hMeas
  isplitr
  · ipureintro; exact hErase
  isplitr
  · ipureintro; exact hMeas'
  isplitr
  · ipureintro; exact hExpected
  isplitr
  · ipureintro; exact hPgl
  iintro %σ' %hσ'
  rw [← presampleAt_image_eq hlookup hk] at hσ'
  obtain ⟨w, hw, rfl⟩ := hσ'
  simp only [presampleAtCredit_update hk]
  imod Hclose with -
  imod app_state_update_tape $$ Hσ Htape with ⟨Hσ', Htape'⟩
  ihave >Hε_rem := errInterp_supply_decrease $$ [$Hε_now $Herr]
  by_cases hlt : ε_now - ε₁ + ε₂ w < 1
  · imod errInterp_supply_increase hlt $$ Hε_rem with ⟨Hε_new, Hε₂_cr⟩
    ihave Hwp := Hcont $$ %w %hw Hε₂_cr Htape'
    isimp only [tglWp_unfold_step hv] at Hwp
    imod Hwp $$ %_ %(ε_now - ε₁ + ε₂ w) [$Hσ' $Hε_new] with HGlm
    imodintro
    iapply execStutter_free
    simp only [Std.ExtTreeMap.insert_eq_PartialMap_insert]
    iexact HGlm
  · push Not at hlt
    imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with -
    imodintro
    iapply execStutter_spend hlt

/-- Presample one chosen empty tape position without spending error credit. -/
theorem twp_presample {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {α : Loc} {t : Tape rT} {k : ℕ} {S : Set (Val rT)}
    (hk : t.presamples k = none) (hS : MeasurableSet S)
    (hconc : Concentrated t.dist S) (hd : t.dist ≠ 0) (hv : e.toVal? = none) : iprop%
    appTapesFrag α t ∗
      (∀ w, ⌜w ∈ S⌝ -∗ appTapesFrag α (t.fillAt k w) -∗ tglWp E e Φ) ⊢
      tglWp E e Φ := by
  iintro ⟨Htape, Hcont⟩
  iapply fupd_tglWp
  imod ErrorCredit.zero with Herr
  imodintro
  iapply (twp_presample_adv_comp (S := S) (k := k) (ε₂ := fun _ => 0)
    hk hS hconc hd measurable_const (by simp) hv)
  iframe
  iintro %w %hw - Htape'
  iapply Hcont $$ %w %hw Htape'

/-- Presample every hole of a tape from an i.i.d. stream of its family law. -/
theorem twp_presample_all {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {α : Loc} {t : Tape rT} [MeasureTheory.IsProbabilityMeasure t.dist]
    (hv : e.toVal? = none) : iprop%
    appTapesFrag α t ∗
      (∀ ω, appTapesFrag α (t.fillAll ω) -∗ tglWp E e Φ) ⊢ tglWp E e Φ := by
  iintro ⟨Htape, Hcont⟩
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  ihave %hlookup := app_state_lookup_tape $$ Hσ Htape
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  have hErase := ErasableExpr.tapePresampleAll hlookup
    (MeasureTheory.IsProbabilityMeasure.ne_zero t.dist)
  have hMeas := measurableSet_presampleAllSupport σ₁ α t
  have hMap : tapePresampleAll σ₁ α =
      (MeasureTheory.Measure.infinitePi fun _ : ℕ => t.dist).map fun ω =>
        σ₁.updateTapes (·.insert α (t.fillAll ω)) :=
    tapePresampleAll_eq_map hlookup
  have hConc : Concentrated (tapePresampleAll σ₁ α)
      (presampleAllSupport σ₁ α t) := by
    rw [hMap, ← presampleAll_range_eq hlookup, ← Set.image_univ]
    have himage : MeasurableSet
        ((fun ω => σ₁.updateTapes (·.insert α (t.fillAll ω))) '' Set.univ) := by
      rw [Set.image_univ, presampleAll_range_eq hlookup]
      exact hMeas
    exact Concentrated.map (State.measurable_fillAllTape σ₁ α t) himage
      Concentrated.univ
  have hExpected : (0 : ENNReal) + ∫⁻ _σ', ε_now ∂tapePresampleAll σ₁ α ≤ ε_now := by
    have hProb : MeasureTheory.IsProbabilityMeasure (tapePresampleAll σ₁ α) :=
      tapePresampleAll.isProbabilityMeasure hlookup
        (MeasureTheory.IsProbabilityMeasure.ne_zero t.dist)
    simp
  iapply glm'_erasable_step
  iexists (tapePresampleAll σ₁ α), (presampleAllSupport σ₁ α t), 0,
    (fun _ => ε_now)
  have hPgl := Pgl.of_concentrated hConc
  have hMeas' : MeasurableSet {σ' | σ' ∈ presampleAllSupport σ₁ α t} := hMeas
  isplitr
  · ipureintro; exact hErase
  isplitr
  · ipureintro; exact hMeas'
  isplitr
  · ipureintro; exact hExpected
  isplitr
  · ipureintro; exact hPgl
  iintro %σ' %hσ'
  rw [← presampleAll_range_eq hlookup] at hσ'
  obtain ⟨ω, rfl⟩ := hσ'
  imod Hclose with -
  imod app_state_update_tape $$ Hσ Htape with ⟨Hσ', Htape'⟩
  ihave Hwp := Hcont $$ %ω Htape'
  isimp only [tglWp_unfold_step hv] at Hwp
  imod Hwp $$ %_ %ε_now [$Hσ' $Hε_now] with HGlm
  imodintro
  iapply execStutter_free
  simp only [Std.ExtTreeMap.insert_eq_PartialMap_insert]
  iexact HGlm

/-- Presample every hole of a program tape while distributing expected error credit over the
filled tape. -/
theorem twp_presample_all_adv_comp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {α : Loc} {t : Tape rT} [MeasureTheory.IsProbabilityMeasure t.dist]
    {ε₁ : ENNReal} {ε₂ : Tape rT → ENNReal} (hε₂ : Measurable ε₂)
    (hInt : (∫⁻ ω, ε₂ (t.fillAll ω) ∂MeasureTheory.Measure.infinitePi fun _ : ℕ => t.dist) ≤ ε₁)
    (hv : e.toVal? = none) : iprop%
    ↯ε₁ ∗ appTapesFrag α t ∗
      (∀ ω, ↯(ε₂ (t.fillAll ω)) -∗ appTapesFrag α (t.fillAll ω) -∗ tglWp E e Φ) ⊢
      tglWp E e Φ := by
  iintro ⟨Herr, Htape, Hcont⟩
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  ihave %hlookup := app_state_lookup_tape $$ Hσ Htape
  ihave ⟨Hε_now, Herr, %hLe⟩ := errInterp_supply_bound $$ [$Hε_now $Herr]
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  have hErase := ErasableExpr.tapePresampleAll hlookup
    (MeasureTheory.IsProbabilityMeasure.ne_zero t.dist)
  have hMeas := measurableSet_presampleAllSupport σ₁ α t
  have hMap : tapePresampleAll σ₁ α =
      (MeasureTheory.Measure.infinitePi fun _ : ℕ => t.dist).map fun ω =>
        σ₁.updateTapes (·.insert α (t.fillAll ω)) :=
    tapePresampleAll_eq_map hlookup
  have hConc : Concentrated (tapePresampleAll σ₁ α) (presampleAllSupport σ₁ α t) := by
    rw [hMap, ← presampleAll_range_eq hlookup, ← Set.image_univ]
    have himage : MeasurableSet
        ((fun ω => σ₁.updateTapes (·.insert α (t.fillAll ω))) '' Set.univ) := by
      rw [Set.image_univ, presampleAll_range_eq hlookup]
      exact hMeas
    exact Concentrated.map (State.measurable_fillAllTape σ₁ α t) himage Concentrated.univ
  have hCredit : (∫⁻ σ', presampleAllCredit α ε₂ σ' ∂tapePresampleAll σ₁ α) ≤ ε₁ := by
    rw [hMap, MeasureTheory.lintegral_map (measurable_presampleAllCredit α hε₂)
      (State.measurable_fillAllTape σ₁ α t)]
    simpa only [presampleAllCredit_update] using hInt
  have hExpected : (0 : ENNReal) +
      ∫⁻ σ', ((ε_now - ε₁) + presampleAllCredit α ε₂ σ') ∂tapePresampleAll σ₁ α ≤ ε_now := by
    have hProb : MeasureTheory.IsProbabilityMeasure (tapePresampleAll σ₁ α) :=
      tapePresampleAll.isProbabilityMeasure hlookup
        (MeasureTheory.IsProbabilityMeasure.ne_zero t.dist)
    rw [zero_add, MeasureTheory.lintegral_add_left measurable_const,
      MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
    calc
      (ε_now - ε₁) + ∫⁻ σ', presampleAllCredit α ε₂ σ' ∂tapePresampleAll σ₁ α ≤
          (ε_now - ε₁) + ε₁ := by gcongr
      _ = ε_now := tsub_add_cancel_of_le hLe
  iapply glm'_erasable_step
  iexists (tapePresampleAll σ₁ α), (presampleAllSupport σ₁ α t), 0,
    (fun σ' => (ε_now - ε₁) + presampleAllCredit α ε₂ σ')
  have hPgl := Pgl.of_concentrated hConc
  have hMeas' : MeasurableSet {σ' | σ' ∈ presampleAllSupport σ₁ α t} := hMeas
  isplitr
  · ipureintro; exact hErase
  isplitr
  · ipureintro; exact hMeas'
  isplitr
  · ipureintro; exact hExpected
  isplitr
  · ipureintro; exact hPgl
  iintro %σ' %hσ'
  rw [← presampleAll_range_eq hlookup] at hσ'
  obtain ⟨ω, rfl⟩ := hσ'
  simp only [presampleAllCredit_update]
  imod Hclose with -
  imod app_state_update_tape $$ Hσ Htape with ⟨Hσ', Htape'⟩
  ihave >Hε_rem := errInterp_supply_decrease $$ [$Hε_now $Herr]
  by_cases hlt : ε_now - ε₁ + ε₂ (t.fillAll ω) < 1
  · imod errInterp_supply_increase hlt $$ Hε_rem with ⟨Hε_new, Hε₂_cr⟩
    ihave Hwp := Hcont $$ %ω Hε₂_cr Htape'
    isimp only [tglWp_unfold_step hv] at Hwp
    imod Hwp $$ %_ %(ε_now - ε₁ + ε₂ (t.fillAll ω)) [$Hσ' $Hε_new] with HGlm
    imodintro
    iapply execStutter_free
    simp only [Std.ExtTreeMap.insert_eq_PartialMap_insert]
    iexact HGlm
  · push Not at hlt
    imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with -
    imodintro
    iapply execStutter_spend hlt

end TotalEris
end ProbLang
