module

public import Mathlib.Probability.Independence.InfinitePi
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Metatheory

@[expose] public section

/-! # Presampling unified tapes

Presampling fills one hole, the first hole, or every hole of a tape from its own distribution.
-/

noncomputable section

namespace ProbLang

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

variable {X : Type} [MeasurableSpace X]

/-- A nonzero zero-or-probability measure is a probability measure. -/
theorem isProbabilityMeasure_of_ne_zero (μ : Measure X) [IsZeroOrProbabilityMeasure μ]
    (hμ : μ ≠ 0) : IsProbabilityMeasure μ := by
  constructor
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h
  · exact (hμ (measure_univ_eq_zero.mp h)).elim
  · exact h

/-! ## Infinite streams -/

section Stream

variable {ι : Type}

/-- Prepends a value to a stream. -/
def streamCons (a : ι) (ω : ℕ → ι) : ℕ → ι
  | 0 => a
  | k + 1 => ω k

/-- Splitting off and then restoring a stream's head changes nothing. -/
@[simp]
theorem streamCons_head_tail (ω : ℕ → ι) :
    streamCons (ω 0) (fun k => ω (k + 1)) = ω := by
  funext k
  cases k <;> rfl

variable [MeasurableSpace ι]

/-- Prepending to a stream is measurable in the head and tail. -/
@[fun_prop]
theorem measurable_streamCons :
    Measurable (fun p : ι × (ℕ → ι) => streamCons p.1 p.2) := by
  refine measurable_pi_iff.mpr fun k => ?_
  cases k
  · exact measurable_fst
  · exact (measurable_pi_apply _).comp measurable_snd

variable (μ : Measure ι) [IsProbabilityMeasure μ]

open Nat (succ succ_injective succ_ne_zero)
open ProbabilityTheory
open Set (range disjoint_singleton_left)

/-- The head and tail of an i.i.d. stream have the product of their original laws. -/
theorem infinitePi_map_head_tail :
    (infinitePi fun _ : ℕ => μ).map (fun ω => (ω 0, fun k => ω (k + 1))) =
      μ.prod (infinitePi fun _ : ℕ => μ) := by
  have hind := (iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ x => x)
    fun _ => measurable_id).indepFun_set {0} (range succ)
    (disjoint_singleton_left.mpr fun ⟨_, h⟩ => succ_ne_zero _ h)
    fun i => measurable_pi_apply i
  have h2 : IndepFun (fun ω : ℕ → ι => ω 0) (fun ω k => ω (k + 1))
      (infinitePi fun _ : ℕ => μ) :=
    hind.comp (φ := fun g : ({0} : Set ℕ) → ι => g ⟨0, rfl⟩)
      (ψ := fun (g : range succ → ι) k => g ⟨k + 1, k, rfl⟩)
      (measurable_pi_apply _) (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
  rw [h2.map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
      (measurable_pi_iff.mpr fun k => measurable_pi_apply (k + 1)).aemeasurable,
    infinitePi_map_eval, map_infinitePi_infinitePi_of_inj succ_injective]

/-- An i.i.d. stream integral splits into independent head and tail integrals. -/
theorem lintegral_infinitePi_head_tail (f : (ℕ → ι) → ENNReal) (hf : Measurable f) :
    ∫⁻ ω, f ω ∂(infinitePi fun _ : ℕ => μ) =
      ∫⁻ a, ∫⁻ ω, f (streamCons a ω) ∂(infinitePi fun _ : ℕ => μ) ∂μ := by
  have hm : Measurable (fun ω : ℕ → ι => (ω 0, fun k => ω (k + 1))) := by
    fun_prop
  have hg : Measurable (fun p : ι × (ℕ → ι) => f (streamCons p.1 p.2)) :=
    hf.comp measurable_streamCons
  rw [← lintegral_prod _ hg.aemeasurable, ← infinitePi_map_head_tail, lintegral_map hg hm]
  simp

end Stream

section Credit

variable {rT : Type}

/-! ## Expected-credit function for one-position presampling -/

/-- Read the credit assigned to the value stored at position `k` of tape `α`. -/
def presampleAtCredit (α : Loc) (k : ℕ) (ε₂ : Val rT → ENNReal) (σ : State rT) : ENNReal :=
  match σ.tapes[α]? with
  | none => 0
  | some t => match t.presamples k with
    | none => 0
    | some w => ε₂ w

/-- `presampleAtCredit` is measurable when its per-value credit is. -/
theorem measurable_presampleAtCredit [MeasurableSpace rT] (α : Loc) (k : ℕ) {ε₂ : Val rT → ENNReal}
    (hε₂ : Measurable ε₂) : Measurable (presampleAtCredit α k ε₂) := by
  unfold presampleAtCredit
  have hsome : Measurable (fun p : State rT × Tape rT =>
      match p.2.presamples k with | none => (0 : ENNReal) | some w => ε₂ w) := by
    have hinner := Option.measurable_elim_param_zero
      (α := State rT × Tape rT) (β := Val rT) (γ := ENNReal)
      (f := fun p : State rT × Tape rT => p.2.presamples k)
      ((Tape.measurable_presamples_apply k).comp measurable_snd)
      (hε₂.comp measurable_snd)
    convert hinner using 1
    funext p
    rcases hp : p.2.presamples k with _ | w <;> simp
  have h := Option.measurable_elim_param_zero
    (α := State rT) (β := Tape rT) (γ := ENNReal)
    (f := fun σ : State rT => σ.tapes[α]?)
    ((LocHeap.measurable_getElem? α).comp State.measurable_tapes) hsome
  convert h using 1
  funext σ
  rcases ht : σ.tapes[α]? with _ | t <;> simp

/-- On a state filled at an empty position, `presampleAtCredit` returns the assigned credit. -/
@[simp]
theorem presampleAtCredit_update {σ : State rT} {α : Loc} {k : ℕ} {t : Tape rT}
    {ε₂ : Val rT → ENNReal} {w : Val rT} (hk : t.presamples k = none) :
    presampleAtCredit α k ε₂ (σ.updateTapes (·.insert α (t.fillAt k w))) = ε₂ w := by
  simp [presampleAtCredit, State.upd_tape_some, Tape.fillAt, Presamples.fillAt_of_none hk]

/-! ## Expected-credit function for whole-stream presampling -/

/-- Read the credit assigned to the contents of tape `α`. -/
def presampleAllCredit (α : Loc) (ε₂ : Tape rT → ENNReal) (σ : State rT) : ENNReal :=
  match σ.tapes[α]? with
  | none => 0
  | some t => ε₂ t

/-- `presampleAllCredit` is measurable when its per-tape credit is. -/
theorem measurable_presampleAllCredit [MeasurableSpace rT] (α : Loc) {ε₂ : Tape rT → ENNReal}
    (hε₂ : Measurable ε₂) : Measurable (presampleAllCredit α ε₂) := by
  have h := Option.measurable_elim_param_zero (α := State rT) (β := Tape rT) (γ := ENNReal)
    (f := fun σ : State rT => σ.tapes[α]?)
    ((LocHeap.measurable_getElem? α).comp State.measurable_tapes) (hε₂.comp measurable_snd)
  convert h using 1
  funext σ
  rcases ht : σ.tapes[α]? with _ | t <;> simp [presampleAllCredit, ht]

/-- After writing tape `α`, `presampleAllCredit` returns the credit of the written tape. -/
@[simp]
theorem presampleAllCredit_update {σ : State rT} {α : Loc} {t : Tape rT}
    {ε₂ : Tape rT → ENNReal} :
    presampleAllCredit α ε₂ (σ.updateTapes (·.insert α t)) = ε₂ t := by
  simp [presampleAllCredit, State.upd_tape_some]

end Credit

variable {rT : Type} [MeasurableSpace rT]

/-- Updating tape `α` by filling position `k` is measurable in the value. -/
@[fun_prop]
theorem State.measurable_fillAtTape (σ : State rT) (α : Loc) (t : Tape rT) (k : ℕ) :
    Measurable fun w => σ.updateTapes (·.insert α (t.fillAt k w)) := by
  refine State.measurable_mk_param measurable_const ?_ measurable_const
  exact (Measurable.locHeap_insert α).comp
    (measurable_const.prodMk
      ((Tape.measurable_fillAt k).comp (measurable_const.prodMk measurable_id)))

/-- Updating tape `α` by filling its first hole is measurable in the value. -/
@[fun_prop]
theorem State.measurable_fillNextTape (σ : State rT) (α : Loc) (t : Tape rT) :
    Measurable fun w => σ.updateTapes (·.insert α (t.fillNext w)) := by
  by_cases h : ∃ k, t.presamples k = none
  · rw [show (fun w => σ.updateTapes (·.insert α (t.fillNext w))) =
        fun w => σ.updateTapes (·.insert α (t.fillAt (Nat.find h) w)) by
      funext w
      simp [Tape.fillNext, Tape.fillAt, Presamples.fillNext, Presamples.firstNone, h]]
    fun_prop
  · rw [show (fun w => σ.updateTapes (·.insert α (t.fillNext w))) =
        fun _ => σ.updateTapes (·.insert α t) by
      funext w
      simp [Tape.fillNext, Presamples.fillNext, Presamples.firstNone, h]]
    fun_prop

/-- Updating tape `α` by filling every hole is measurable in the filling stream. -/
@[fun_prop]
theorem State.measurable_fillAllTape (σ : State rT) (α : Loc) (t : Tape rT) :
    Measurable fun ω => σ.updateTapes (·.insert α (t.fillAll ω)) := by
  refine State.measurable_mk_param measurable_const ?_ measurable_const
  exact (Measurable.locHeap_insert α).comp
    (measurable_const.prodMk (Tape.measurable_fillAll.comp
      (measurable_const.prodMk measurable_id)))

variable [ProbLangDist rT]
variable {σ : State rT} {α : Loc} {k : ℕ}

/-- The distribution carried by a tape. -/
abbrev Tape.dist (t : Tape rT) : Measure (Val rT) :=
  ProbLangDist.dist t.name t.arg

/-- Fill position `k` of tape `α` from its family; a full position is a no-op. -/
def tapePresampleAt (σ : State rT) (α : Loc) (k : ℕ) : Measure (State rT) :=
  match σ.tapes[α]? with
  | none => 0
  | some t =>
      match t.presamples k with
      | some _ => dirac σ
      | none => t.dist.map fun w => σ.updateTapes (·.insert α (t.fillAt k w))

/-- Fill the first hole of tape `α` from its family; a full tape is a no-op. -/
def tapePresampleNext (σ : State rT) (α : Loc) : Measure (State rT) :=
  match σ.tapes[α]? with
  | none => 0
  | some t =>
      match Presamples.firstNone t.presamples with
      | none => dirac σ
      | some _ => t.dist.map fun w => σ.updateTapes (·.insert α (t.fillNext w))

/-- Fill every hole of tape `α` from an i.i.d. stream drawn from its family. -/
def tapePresampleAll (σ : State rT) (α : Loc) : Measure (State rT) :=
  match σ.tapes[α]? with
  | none => 0
  | some t =>
      (infinitePi fun _ : ℕ => t.dist).map fun ω =>
        σ.updateTapes (·.insert α (t.fillAll ω))

/-- Filling one fixed position is measurable in the starting state. -/
theorem tapePresampleAt.measurable (α : Loc) (k : ℕ) :
    Measurable (fun σ : State rT => tapePresampleAt σ α k) := by
  let someBranch : State rT × Tape rT → Measure (State rT) := fun p =>
    if p.2.presamples k = none then
      p.2.dist.map fun w => p.1.updateTapes (·.insert α (p.2.fillAt k w))
    else dirac p.1
  have hdist : Measurable (fun t : Tape rT => t.dist) := by
    have hnamed : Measurable (fun p : ℕ × Tape rT => ProbLangDist.dist p.1 p.2.arg) := by
      apply measurable_from_prod_countable_right
      intro n
      exact (ProbLangDist.dist n).measurable.comp Tape.measurable_arg
    exact hnamed.comp (Tape.measurable_name.prodMk measurable_id)
  have hfill : Measurable (fun p : (State rT × Tape rT) × Val rT =>
      p.1.1.updateTapes (·.insert α (p.1.2.fillAt k p.2))) := by
    refine State.measurable_mk_param
      (State.measurable_heap.comp (measurable_fst.comp measurable_fst)) ?_
      (State.measurable_rvs.comp (measurable_fst.comp measurable_fst))
    have htape : Measurable (fun p : (State rT × Tape rT) × Val rT =>
        p.1.2.fillAt k p.2) :=
      (Tape.measurable_fillAt k).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (Measurable.locHeap_insert α).comp
      ((State.measurable_tapes.comp (measurable_fst.comp measurable_fst)).prodMk htape)
  have hempty : Measurable (fun p : State rT × Tape rT =>
      p.2.dist.map fun w => p.1.updateTapes (·.insert α (p.2.fillAt k w))) := by
    have hk : Measurable (fun p : State rT × Tape rT => p.2.dist) :=
      hdist.comp measurable_snd
    have : IsFiniteKernel (Kernel.mk _ hk) :=
      ⟨1, ENNReal.one_lt_top, fun p => prob_le_one (μ := p.2.dist)⟩
    exact measurable_map_uncurry hfill hk
  have hsome : Measurable someBranch := by
    have hnone : MeasurableSet {p : State rT × Tape rT | p.2.presamples k = none} :=
      ((measurable_pi_apply k).comp
        (Tape.measurable_presamples.comp measurable_snd)) MeasurableSet.singleton_none
    exact hempty.ite hnone (measurable_dirac.comp measurable_fst)
  let g : (State rT × Option (Tape rT)) × Tape rT → Measure (State rT) := fun p =>
    someBranch (p.1.1, p.2)
  have hg : Measurable g :=
    hsome.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hleaf : Measurable (fun p : State rT × Option (Tape rT) =>
      Option.unwrapM (fun t => g (p, t)) p.2) :=
    Option.unwrapM.measurable_param measurable_snd hg
  have hproj : Measurable (fun σ : State rT => (σ, σ.tapes[α]?)) :=
    measurable_id.prodMk ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
  rw [show (fun σ : State rT => tapePresampleAt σ α k) =
      fun σ => Option.unwrapM (fun t => g ((σ, σ.tapes[α]?), t)) σ.tapes[α]? by
    funext σ
    rcases ht : σ.tapes[α]? with _ | t
    · simp [tapePresampleAt, Option.unwrapM, ht]
    · rcases hk : t.presamples k with _ | w <;>
        simp [tapePresampleAt, g, someBranch, Option.unwrapM, ht, hk]]
  exact hleaf.comp hproj

/-- Filling one position has total mass at most one. -/
theorem tapePresampleAt_univ_le_one : (tapePresampleAt σ α k) univ ≤ 1 := by
  rcases ht : σ.tapes[α]? with _ | t
  · simp [tapePresampleAt, ht]
  · rcases hk : t.presamples k with _ | w
    · simp only [tapePresampleAt, ht, hk]
      rw [map_apply
        (State.measurable_fillAtTape σ α t k) MeasurableSet.univ]
      simpa using prob_le_one (μ := t.dist)
    · simp [tapePresampleAt, ht, hk]

/-- Filling one position is a sub-probability measure. -/
instance tapePresampleAt.isSubProbabilityMeasure :
    IsSubProbabilityMeasure (tapePresampleAt σ α k) :=
  ⟨tapePresampleAt_univ_le_one⟩

/-- Presampling an empty position is the tape law mapped through `fillAt`. -/
theorem tapePresampleAt_eq_map {t : Tape rT} (ht : σ.tapes[α]? = some t)
    (hk : t.presamples k = none) :
    tapePresampleAt σ α k =
      t.dist.map fun w => σ.updateTapes (·.insert α (t.fillAt k w)) := by
  simp [tapePresampleAt, ht, hk]

/-- Presampling a full position leaves the state unchanged. -/
@[simp]
theorem tapePresampleAt_of_some {t : Tape rT} {w : Val rT}
    (ht : σ.tapes[α]? = some t) (hk : t.presamples k = some w) :
    tapePresampleAt σ α k = dirac σ := by
  simp [tapePresampleAt, ht, hk]

/-- Presampling a missing tape gives the zero measure. -/
@[simp]
theorem tapePresampleAt_of_none (h : σ.tapes[α]? = none) :
    tapePresampleAt σ α k = 0 := by
  simp [tapePresampleAt, h]

/-- Whole-stream presampling is the i.i.d. law mapped through `fillAll`. -/
theorem tapePresampleAll_eq_map {t : Tape rT} (ht : σ.tapes[α]? = some t) :
    tapePresampleAll σ α =
      (infinitePi fun _ : ℕ => t.dist).map fun ω =>
        σ.updateTapes (·.insert α (t.fillAll ω)) := by
  simp [tapePresampleAll, ht]

/-- A nonzero tape family makes a one-position presample a probability measure. -/
theorem tapePresampleAt.isProbabilityMeasure {t : Tape rT}
    (ht : σ.tapes[α]? = some t) (hd : t.dist ≠ 0) :
    IsProbabilityMeasure (tapePresampleAt σ α k) := by
  rcases hk : t.presamples k with _ | w
  · rw [tapePresampleAt_eq_map ht hk]
    let _ := isProbabilityMeasure_of_ne_zero t.dist hd
    infer_instance
  · rw [tapePresampleAt_of_some ht hk]
    infer_instance

/-- A nonzero tape family makes whole-stream presampling a probability measure. -/
theorem tapePresampleAll.isProbabilityMeasure {t : Tape rT}
    (ht : σ.tapes[α]? = some t) (hd : t.dist ≠ 0) :
    IsProbabilityMeasure (tapePresampleAll σ α) := by
  rw [tapePresampleAll_eq_map ht]
  let _ := isProbabilityMeasure_of_ne_zero t.dist hd
  infer_instance

/-- Integrating a one-position presample is integrating the tape law through `fillAt`. -/
theorem tapePresampleAt_lintegral {t : Tape rT} (ht : σ.tapes[α]? = some t)
    (hk : t.presamples k = none) (f : State rT → ENNReal) (hf : Measurable f) :
    ∫⁻ σ', f σ' ∂tapePresampleAt σ α k =
      ∫⁻ w, f (σ.updateTapes (·.insert α (t.fillAt k w))) ∂t.dist := by
  rw [tapePresampleAt_eq_map ht hk, lintegral_map hf (State.measurable_fillAtTape σ α t k)]

/-- Integrating a whole-stream presample is integrating the i.i.d. filling stream. -/
theorem tapePresampleAll_lintegral {t : Tape rT} (ht : σ.tapes[α]? = some t)
    (f : State rT → ENNReal) (hf : Measurable f) :
    ∫⁻ σ', f σ' ∂tapePresampleAll σ α =
      ∫⁻ ω, f (σ.updateTapes (·.insert α (t.fillAll ω)))
        ∂(infinitePi fun _ : ℕ => t.dist) := by
  rw [tapePresampleAll_eq_map ht,
    lintegral_map hf (State.measurable_fillAllTape σ α t)]

/-- An event holds almost surely after filling an empty position if it holds after every draw. -/
theorem tapePresampleAt_ae {t : Tape rT} (ht : σ.tapes[α]? = some t)
    (hk : t.presamples k = none) {P : State rT → Prop} (hP : MeasurableSet {σ' | P σ'})
    (hall : ∀ w, P (σ.updateTapes (·.insert α (t.fillAt k w)))) :
    ∀ᵐ σ' ∂tapePresampleAt σ α k, P σ' := by
  rw [tapePresampleAt_eq_map ht hk, ae_map_iff
    (State.measurable_fillAtTape σ α t k).aemeasurable hP]
  exact ae_of_all _ hall

/-- An event holds almost surely after filling every hole if it holds for every stream. -/
theorem tapePresampleAll_ae {t : Tape rT} (ht : σ.tapes[α]? = some t)
    {P : State rT → Prop} (hP : MeasurableSet {σ' | P σ'})
    (hall : ∀ ω, P (σ.updateTapes (·.insert α (t.fillAll ω)))) :
    ∀ᵐ σ' ∂tapePresampleAll σ α, P σ' := by
  rw [tapePresampleAll_eq_map ht, ae_map_iff
    (State.measurable_fillAllTape σ α t).aemeasurable hP]
  exact ae_of_all _ hall

end ProbLang
