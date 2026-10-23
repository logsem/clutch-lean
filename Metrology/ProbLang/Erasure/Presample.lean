module

public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Metatheory

@[expose] public section

/-! # Uniform tape presample

`tapePresample σ α` appends a uniform draw to tape `α` (Clutch `erasure.v`). -/

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT]

open MeasureTheory MeasureTheory.Measure
open Set ProbabilityTheory
open Measurable (of_discrete)

/-! ## The uniform index distribution -/

section

variable {N : Int} (hN : 0 < N)

/-- The totalising map `Int → [0, N)` that sends out-of-range values to `0`. -/
noncomputable def tapeIdxOf (n : Int) : { z : Int // 0 ≤ z ∧ z < N } :=
  if hz : 0 ≤ n ∧ n < N then ⟨n, hz⟩ else ⟨0, ⟨_root_.le_refl _, hN⟩⟩

/-- The uniform distribution on `[0, N)` as a subtype; `0` when `N ≤ 0`. -/
noncomputable def tapeIndexUniform (N : Int) : Measure { z : Int // 0 ≤ z ∧ z < N } :=
  if hN : 0 < N then
    (PMF.uniformOfFinset (Finset.Ico 0 N) (Finset.nonempty_Ico.mpr hN)).toMeasure.map (tapeIdxOf hN)
  else 0

variable [LawfulProbLangℝ rT]

/-- On `[0, N)`, `tapeIdxOf` is the identity. -/
@[simp] theorem tapeIdxOf_val {n : Int} (h0 : 0 ≤ n) (hn : n < N) :
    (tapeIdxOf hN n).val = n := by
  simp [tapeIdxOf, h0, hn]

/-- The uniform index distribution is the pushforward of the uniform distribution on `[0, N)`. -/
theorem tapeIndexUniform_eq_map :
    tapeIndexUniform N = (PMF.uniformOfFinset (Finset.Ico (0 : Int) N)
        (Finset.nonempty_Ico.mpr hN)).toMeasure.map (tapeIdxOf hN) :=
  dite_eq_left hN

include hN in
/-- The uniform index distribution has total mass one when `0 < N`. -/
theorem tapeIndexUniform_univ_eq_one :
    (tapeIndexUniform N) univ = 1 := by
  have : IsProbabilityMeasure
      (PMF.uniformOfFinset (Finset.Ico 0 N) (Finset.nonempty_Ico.mpr hN)).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  rw [tapeIndexUniform_eq_map hN, map_apply of_discrete .univ]
  simp only [preimage_univ, measure_univ]

/-- Integrating against the uniform index distribution is the average over `[0, N)`. -/
theorem lintegral_tapeIndexUniform
    (ψ : { z : Int // 0 ≤ z ∧ z < N } → ENNReal) :
    ∫⁻ x, ψ x ∂(tapeIndexUniform N) =
      ((N.toNat : ENNReal))⁻¹ * ∑ n ∈ Finset.Ico (0 : Int) N, ψ (tapeIdxOf hN n) := by
  have hcard : (Finset.Ico (0 : Int) N).card = N.toNat := by rw [Int.card_Ico]; omega
  rw [tapeIndexUniform_eq_map hN, lintegral_map of_discrete of_discrete,
      lintegral_countable',
      tsum_eq_sum (s := Finset.Ico (0 : Int) N) fun n hn => by
        rw [PMF.toMeasure_apply_singleton _ _ .of_discrete,
            PMF.uniformOfFinset_apply_of_notMem _ hn, mul_zero],
      Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [PMF.toMeasure_apply_singleton _ _ .of_discrete,
      PMF.uniformOfFinset_apply_of_mem _ hn, hcard, mul_comm]

/-- A bijection of `[0, N)` leaves `tapeIndexUniform N` invariant. -/
theorem tapeIndexUniform_map_bijOn (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    (tapeIndexUniform N).map (fun x => tapeIdxOf hN (f x.val)) = tapeIndexUniform N := by
  refine ext_of_lintegral _ fun ψ _ => ?_
  rw [lintegral_map of_discrete of_discrete, lintegral_tapeIndexUniform hN,
    lintegral_tapeIndexUniform hN,
    ← Finset.sum_Ico_comp_of_bijOn hdom hbij (fun m => ψ (tapeIdxOf hN m))]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [tapeIdxOf_val hN (Finset.mem_Ico.1 hn).1 (Finset.mem_Ico.1 hn).2]

end

/-- The uniform index distribution is s-finite. -/
instance tapeIndexUniform.instSFinite {N : Int} : SFinite (tapeIndexUniform N) := by
  unfold tapeIndexUniform
  split <;> infer_instance

section

variable [LawfulProbLangℝ rT]

/-- The uniform index distribution has total mass at most one. -/
theorem tapeIndexUniform_univ_le_one {N : Int} :
    (tapeIndexUniform N) univ ≤ 1 := by
  by_cases hN : 0 < N
  · exact (tapeIndexUniform_univ_eq_one hN).le
  · simp [tapeIndexUniform, hN]

/-- The uniform index distribution is a sub-probability measure. -/
instance tapeIndexUniform.isSubProbabilityMeasure (N : Int) :
    IsSubProbabilityMeasure (tapeIndexUniform N) :=
  ⟨tapeIndexUniform_univ_le_one⟩

end

/-! ## Presampling a tape -/

/-- Sample `n ∈ [0, N)` uniformly and append it to tape `α` (Clutch's `state_step σ α`);
`0` if the tape is absent. -/
noncomputable def tapePresample (σ : State rT) (α : Loc) : Measure (State rT) :=
  match σ.tapes[α]? with
  | none => 0
  | some ⟨N, bs⟩ =>
      (tapeIndexUniform N).bind (fun n =>
        dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))

section

variable {σ : State rT} {α : Loc}

/-- Presampling an allocated tape of positive bound has total mass one. -/
theorem tapePresample_univ_eq_one {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    (tapePresample σ α) univ = 1 := by
  obtain ⟨N, bs⟩ := t
  simp only [tapePresample, h]
  rw [bind_apply .univ of_discrete.aemeasurable]
  simp_rw [dirac_apply' _ .univ, indicator_univ,
    Pi.one_apply, lintegral_one]
  exact tapeIndexUniform_univ_eq_one hN

/-- Presampling has total mass at most one. -/
theorem tapePresample_univ_le_one :
    (tapePresample σ α) univ ≤ 1 := by
  cases hsome : σ.tapes[α]? with
  | none => simp [tapePresample, hsome]
  | some t =>
    obtain ⟨N, bs⟩ := t
    simp only [tapePresample, hsome]
    rw [bind_apply .univ of_discrete.aemeasurable]
    simpa using tapeIndexUniform_univ_le_one

/-- Presampling a fixed tape is measurable in the state. -/
theorem tapePresample.measurable :
    Measurable (fun σ : State rT => tapePresample σ α) := by
  -- `tapePresample σ α = leaf (σ, σ.tapes[α]?)`; `Option Tape` is countable, so check each
  -- branch: a map of the constant kernel `tapeIndexUniform N`.
  let leaf : State rT × Option Tape → Measure (State rT) := fun p =>
      match p.2 with
      | none => 0
      | some ⟨N, bs⟩ =>
        (tapeIndexUniform N).bind
          (fun n => dirac (p.1.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))
  have hleaf : Measurable leaf := by
    have hflat : Measurable (fun q : Option Tape × State rT => leaf (q.2, q.1)) := by
      apply measurable_from_prod_countable_right
      intro optTape
      show Measurable (fun σ : State rT => leaf (σ, optTape))
      cases optTape with
      | none => exact measurable_const
      | some t =>
        obtain ⟨N, bs⟩ := t
        show Measurable (fun σ : State rT =>
          (tapeIndexUniform N).bind
            (fun n => dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))))
        have hconv : (fun σ : State rT =>
            (tapeIndexUniform N).bind
              (fun n => dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))) =
            (fun σ : State rT =>
              (tapeIndexUniform N).map (fun n => σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))) := by
          funext σ; exact bind_dirac_eq_map _ of_discrete
        rw [hconv]
        have hval : Measurable (fun p : State rT × {z : Int // 0 ≤ z ∧ z < N} =>
              (⟨N, bs ++ [p.2]⟩ : Tape)) :=
          (of_discrete (f := fun n : {z : Int // 0 ≤ z ∧ z < N} =>
            (⟨N, bs ++ [n]⟩ : Tape))).comp measurable_snd
        have hh : Measurable (fun p : State rT × {z : Int // 0 ≤ z ∧ z < N} =>
              p.1.update_tapes (·.insert α ⟨N, bs ++ [p.2]⟩)) :=
          State.measurable_mk_param (State.measurable_heap.comp measurable_fst)
            ((Measurable.locHeap_insert α).comp
              ((State.measurable_tapes.comp measurable_fst).prodMk hval))
        have hk : Measurable (fun _ : State rT => tapeIndexUniform N) := measurable_const
        have hSF : IsSFiniteKernel
            (Kernel.mk (fun _ : State rT => tapeIndexUniform N) hk) :=
          inferInstanceAs (IsSFiniteKernel
              (Kernel.const (State rT) (tapeIndexUniform N)))
        exact @measurable_map_uncurry (State rT) {z : Int // 0 ≤ z ∧ z < N}
          (State rT) _ _ _ _ hh (fun _ => tapeIndexUniform N) hk hSF
    exact hflat.comp (measurable_snd.prodMk measurable_fst)
  have hproj : Measurable (fun σ : State rT => (σ, σ.tapes[α]?)) :=
    measurable_id.prodMk ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
  show Measurable (fun σ : State rT => leaf (σ, σ.tapes[α]?))
  exact hleaf.comp hproj

/-- Presampling is a sub-probability measure. -/
instance tapePresample.isSubProbabilityMeasure :
    IsSubProbabilityMeasure (tapePresample σ α) :=
  ⟨tapePresample_univ_le_one⟩

/-- Presampling onto a tape is the uniform index distribution pushed onto the extended tape. -/
theorem tapePresample_eq_map {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} (hσ : σ.tapes[α]? = some ⟨N, bs⟩) :
    tapePresample σ α =
      (tapeIndexUniform N).map (fun n => σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) := by
  simp only [tapePresample, hσ]
  rw [bind_dirac_eq_map _ of_discrete]

/-- Presampling then a measurable deterministic update is measurable in the configuration. -/
theorem tapePresample_bind_dirac_measurable
    {g : Cfg rT → State rT → Cfg rT}
    (hg : Measurable (fun p : Cfg rT × (State rT) => g p.1 p.2)) :
    Measurable (fun ρ : Cfg rT =>
      (tapePresample ρ.state α).bind (fun σ'' => dirac (g ρ σ''))) := by
  have hconv : (fun ρ : Cfg rT =>
        (tapePresample ρ.state α).bind (fun σ'' => dirac (g ρ σ''))) =
      (fun ρ : Cfg rT => (tapePresample ρ.state α).map (fun σ'' => g ρ σ'')) := by
    funext ρ
    exact bind_dirac_eq_map _ (hg.comp (measurable_const.prodMk measurable_id))
  rw [hconv]
  have hk : Measurable (fun ρ : Cfg rT => tapePresample ρ.state α) :=
    tapePresample.measurable.comp Cfg.measurable_state
  have hFin : IsFiniteKernel
      (Kernel.mk (fun ρ : Cfg rT => tapePresample ρ.state α) hk) :=
    ⟨1, ENNReal.one_lt_top, fun _ => tapePresample_univ_le_one⟩
  exact measurable_map_uncurry hg hk

/-! ## Tape persistence through a prim step -/

variable [inst : LawfulProbLangℝ rT]

include inst

/-- Every possible successor of a prim step keeps tape `α`, with the same bound. -/
theorem primStep_tape_persists_support
    {αloc : Loc} {e : Exp rT} {t : Tape} {ρ : Cfg rT}
    (h : σ.tapes[αloc]? = some t)
    (hρ : Possible ρ (primStep ⟨e, σ⟩)) :
    ∃ t' : Tape, ρ.state.tapes[αloc]? = some t' ∧ t'.bound = t.bound := by
  obtain ⟨e₂, σ₂⟩ := ρ
  obtain ⟨K, e₁', e₂', _hfill1, _hfill2, hhs⟩ := prim_step_imp hρ
  replace hhs := Possible.headStepSupport hhs
  cases hhs with
  | AllocS _ _ hσ' =>
    subst hσ'
    exact ⟨t, by simp [State.update_heap, h], rfl⟩
  | StoreS _ _ hσ' =>
    subst hσ'
    exact ⟨t, by simp [State.update_heap, h], rfl⟩
  | TapeS hℓ hσ' =>
    subst hσ' hℓ
    have hne : σ.tapes.fresh ≠ αloc := Std.ExtTreeMap.elem_fresh_ne h
    refine ⟨t, ?_, rfl⟩
    exact State.upd_diff_tape_tot hne.symm |>.trans h
  | @RandTapeS β _ _ _ _ _ _ _ hα' _hN _hv hσ' =>
    subst hσ'
    by_cases hαβ : αloc = β
    · subst hαβ
      rw [hα'] at h
      have ht := Option.some.inj h
      subst ht
      refine ⟨_, State.upd_tape_some _ _ _, rfl⟩
    · refine ⟨t, ?_, rfl⟩
      rw [show (σ.update_tapes fun x => x.insert β _).tapes[αloc]? = σ.tapes[αloc]?
          from State.upd_diff_tape_tot hαβ]
      exact h
  | RandTapeEmptyS _ _ _ _ _ hσ' =>
    subst hσ'
    exact ⟨t, h, rfl⟩
  | RandTapeOtherS _ _ _ _ _ hσ' =>
    subst hσ'
    exact ⟨t, h, rfl⟩
  | _ => exact ⟨t, h, rfl⟩

/-- Almost surely, a prim step keeps tape `α` with the same bound (discrete case). -/
theorem primStep_tape_persists [Countable rT]
    {e : Exp rT} {t : Tape}
    (h : σ.tapes[α]? = some t) :
    ∀ᵐ ρ ∂(primStep ⟨e, σ⟩),
      ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound := by
  refine ae_iff.mpr ?_
  rw [show {ρ : Cfg rT | ¬ ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound} =
        ⋃ ρ ∈ {ρ : Cfg rT | ¬ ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound},
            ({ρ} : Set (Cfg rT)) from by ext; simp]
  refine (measure_biUnion_null_iff (to_countable _)).mpr ?_
  intro ρ hρ
  by_contra hne
  rw [← ne_eq, ← pos_iff_ne_zero] at hne
  exact hρ (primStep_tape_persists_support h (possible_iff_pos.mpr hne))

end

end ProbLang
