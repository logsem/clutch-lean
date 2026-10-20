module

public import Metrology.ProbLang.Erasable
public import Metrology.ProbLang.Metatheory
public import Metrology.Couplings.Bridges.AddCoupl

@[expose] public section

/-! The uniform tape presample and how a prim step keeps tapes (Clutch `erasure.v`). -/

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure ProbLang.Measure

/-! ## Local uniform-presample distribution -/

/-- The uniform distribution on `[0, N)` as a subtype; `0` when `N ≤ 0`. -/
noncomputable def tapeIndexUniform (N : Int) : Measure { z : Int // 0 ≤ z ∧ z < N } :=
  if h : (Finset.Ico 0 N).Nonempty then
    (PMF.uniformOfFinset (Finset.Ico 0 N) h).toMeasure.map
      (fun z =>
        if hz : 0 ≤ z ∧ z < N then ⟨z, hz⟩
        else ⟨0, by
          rcases h with ⟨w, hw⟩
          simp [Finset.mem_Ico] at hw
          exact ⟨le_refl _, by omega⟩⟩)
  else 0

/-- The labels of the allocated tapes of `σ`. -/
def getActive (σ : State rT) : List Loc := σ.tapes.keys

omit [LawfulProbLangℝ rT] in
theorem getActive_mem_iff {σ : State rT} {α : Loc} :
    α ∈ getActive σ ↔ α ∈ σ.tapes := by
  unfold getActive
  exact Std.ExtTreeMap.mem_keys

/-- Sample `n ∈ [0, N)` uniformly and append it to tape `α` (Clutch's `state_step σ α`);
`0` if the tape is absent. -/
noncomputable def tapePresample (σ : State rT) (α : Loc) : Measure (State rT) :=
  match σ.tapes[α]? with
  | none => 0
  | some ⟨N, bs⟩ =>
      (tapeIndexUniform N).bind (fun n =>
        Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))

theorem tapeIndexUniform_univ_eq_one {N : Int} (hN : 0 < N) :
    (tapeIndexUniform N) Set.univ = 1 := by
  unfold tapeIndexUniform
  have hNonempty : (Finset.Ico 0 N).Nonempty := ⟨0, Finset.mem_Ico.mpr ⟨le_refl _, hN⟩⟩
  rw [dite_eq_left hNonempty]
  have : IsProbabilityMeasure
      (PMF.uniformOfFinset (Finset.Ico 0 N) hNonempty).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ]

/-- The clamping injection `Int → [0, N)` used by `tapeIndexUniform`. -/
noncomputable def tapeIdxOf {N : Int} (hN : 0 < N) (n : Int) : { z : Int // 0 ≤ z ∧ z < N } :=
  if hz : 0 ≤ n ∧ n < N then ⟨n, hz⟩ else ⟨0, ⟨_root_.le_refl _, hN⟩⟩

@[simp] theorem tapeIdxOf_val {N : Int} (hN : 0 < N) {n : Int} (h0 : 0 ≤ n) (hn : n < N) :
    (tapeIdxOf hN n).val = n := by
  simp [tapeIdxOf, h0, hn]

theorem tapeIndexUniform_eq_map {N : Int} (hN : 0 < N) :
    tapeIndexUniform N =
      (PMF.uniformOfFinset (Finset.Ico (0 : Int) N)
        (Finset.nonempty_Ico.mpr hN)).toMeasure.map (tapeIdxOf hN) := by
  unfold tapeIndexUniform tapeIdxOf
  rw [dite_eq_left ⟨0, Finset.mem_Ico.mpr ⟨_root_.le_refl _, hN⟩⟩]

theorem lintegral_tapeIndexUniform {N : Int} (hN : 0 < N)
    (ψ : { z : Int // 0 ≤ z ∧ z < N } → ENNReal) :
    ∫⁻ x, ψ x ∂(tapeIndexUniform N)
      = ((N.toNat : ENNReal))⁻¹ * ∑ n ∈ Finset.Ico (0 : Int) N, ψ (tapeIdxOf hN n) := by
  have hcard : (Finset.Ico (0 : Int) N).card = N.toNat := by rw [Int.card_Ico]; omega
  rw [tapeIndexUniform_eq_map hN, lintegral_map Measurable.of_discrete Measurable.of_discrete,
      lintegral_countable',
      tsum_eq_sum (s := Finset.Ico (0 : Int) N) fun n hn => by
        rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
            PMF.uniformOfFinset_apply_of_notMem _ hn, mul_zero],
      Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
      PMF.uniformOfFinset_apply_of_mem _ hn, hcard, mul_comm]

theorem tapePresample_univ_eq_one {σ : State rT} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    (tapePresample σ α) Set.univ = 1 := by
  obtain ⟨N, bs⟩ := t
  simp only [tapePresample, h]
  rw [Measure.bind_apply MeasurableSet.univ
        Measurable.of_discrete.aemeasurable]
  simp_rw [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ,
    Pi.one_apply, lintegral_one]
  exact tapeIndexUniform_univ_eq_one hN

instance tapeIndexUniform.instSFinite {N : Int} : SFinite (tapeIndexUniform N) := by
  unfold tapeIndexUniform
  split <;> infer_instance

theorem tapePresample.measurable {α : Loc} :
    Measurable (fun σ : State rT => tapePresample σ α) := by
  let leaf : State rT × Option Tape → Measure (State rT) :=
    fun p =>
      match p.2 with
      | none => 0
      | some ⟨N, bs⟩ =>
        (tapeIndexUniform N).bind
          (fun n => Measure.dirac (p.1.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))
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
            (fun n => Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))))
        have hconv : (fun σ : State rT =>
            (tapeIndexUniform N).bind
              (fun n => Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))))
            = (fun σ : State rT =>
              (tapeIndexUniform N).map
                (fun n => σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))) := by
          funext σ; exact Measure.bind_dirac_eq_map _ Measurable.of_discrete
        rw [hconv]
        have hval : Measurable
            (fun p : State rT × {z : Int // 0 ≤ z ∧ z < N} =>
              (⟨N, bs ++ [p.2]⟩ : Tape)) :=
          (Measurable.of_discrete (f := fun n : {z : Int // 0 ≤ z ∧ z < N} =>
            (⟨N, bs ++ [n]⟩ : Tape))).comp measurable_snd
        have hh : Measurable
            (fun p : State rT × {z : Int // 0 ≤ z ∧ z < N} =>
              p.1.update_tapes (·.insert α ⟨N, bs ++ [p.2]⟩)) :=
          State.measurable_mk_param (State.measurable_heap.comp measurable_fst)
            ((Measurable.locHeap_insert α).comp
              ((State.measurable_tapes.comp measurable_fst).prodMk hval))
        have hk : Measurable (fun _ : State rT => tapeIndexUniform N) := measurable_const
        have hSF : ProbabilityTheory.IsSFiniteKernel
            (ProbabilityTheory.Kernel.mk (fun _ : State rT => tapeIndexUniform N) hk) := by
          have : ProbabilityTheory.Kernel.mk (fun _ : State rT => tapeIndexUniform N) hk
              = ProbabilityTheory.Kernel.const (State rT) (tapeIndexUniform N) := rfl
          rw [this]; infer_instance
        exact @Measure.measurable_map_uncurry (State rT) {z : Int // 0 ≤ z ∧ z < N}
          (State rT) _ _ _ _ hh (fun _ => tapeIndexUniform N) hk hSF
    exact hflat.comp (measurable_snd.prodMk measurable_fst)
  have hproj : Measurable (fun σ : State rT => (σ, σ.tapes[α]?)) :=
    measurable_id.prodMk ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
  show Measurable (fun σ : State rT => leaf (σ, σ.tapes[α]?))
  exact hleaf.comp hproj

theorem tapeIndexUniform_univ_le_one {N : Int} :
    (tapeIndexUniform N) Set.univ ≤ 1 := by
  unfold tapeIndexUniform
  split
  next h =>
    have : IsProbabilityMeasure
        (PMF.uniformOfFinset (Finset.Ico 0 N) h).toMeasure :=
      PMF.toMeasure.isProbabilityMeasure _
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simp
  next => simp

theorem tapePresample_univ_le_one {σ : State rT} {α : Loc} :
    (tapePresample σ α) Set.univ ≤ 1 := by
  cases hsome : σ.tapes[α]? with
  | none => simp [tapePresample, hsome]
  | some t =>
    obtain ⟨N, bs⟩ := t
    simp only [tapePresample, hsome]
    rw [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable]
    simpa using tapeIndexUniform_univ_le_one

instance tapeIndexUniform.isSubProbabilityMeasure (N : Int) :
    IsSubProbabilityMeasure (tapeIndexUniform N) :=
  ⟨tapeIndexUniform_univ_le_one⟩

instance tapePresample.isSubProbabilityMeasure (σ : State rT) (α : Loc) :
    IsSubProbabilityMeasure (tapePresample σ α) :=
  ⟨tapePresample_univ_le_one⟩

theorem tapePresample_bind_dirac_measurable {α : Loc}
    {g : Cfg rT → State rT → Cfg rT}
    (hg : Measurable (fun p : Cfg rT × (State rT) => g p.1 p.2)) :
    Measurable (fun ρ : Cfg rT =>
      (tapePresample ρ.state α).bind (fun σ'' => Measure.dirac (g ρ σ''))) := by
  have hconv : (fun ρ : Cfg rT =>
        (tapePresample ρ.state α).bind (fun σ'' => Measure.dirac (g ρ σ'')))
      = (fun ρ : Cfg rT => (tapePresample ρ.state α).map (fun σ'' => g ρ σ'')) := by
    funext ρ
    exact Measure.bind_dirac_eq_map _ (hg.comp (measurable_const.prodMk measurable_id))
  rw [hconv]
  have hk : Measurable (fun ρ : Cfg rT => tapePresample ρ.state α) :=
    tapePresample.measurable.comp Cfg.measurable_state
  have hFin : ProbabilityTheory.IsFiniteKernel
      (ProbabilityTheory.Kernel.mk (fun ρ : Cfg rT => tapePresample ρ.state α) hk) :=
    ⟨1, ENNReal.one_lt_top, fun _ => tapePresample_univ_le_one⟩
  exact Measure.measurable_map_uncurry hg hk

/-! ## Bind-map distributivity -/

theorem Measure.bind_map_comm {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [DiscreteMeasurableSpace γ]
    (μ : Measure α) (k : α → Measure β) (f : β → γ) :
    (μ.bind k).map f = μ.bind (fun a => (k a).map f) := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply .of_discrete hS,
      Measure.bind_apply (by exact .of_discrete) Measurable.of_discrete.aemeasurable,
      Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
  simp_rw [Measure.map_apply .of_discrete hS]

theorem Measure.bind_map_comm' {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (k : α → Measure β) (f : β → γ)
    (hk : AEMeasurable k μ) (hf : Measurable f) :
    (μ.bind k).map f = μ.bind (fun a => (k a).map f) := by
  have hkmap : AEMeasurable (fun a => (k a).map f) μ :=
    (Measure.measurable_map f hf).comp_aemeasurable hk
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hf hS,
      Measure.bind_apply (hf hS) hk,
      Measure.bind_apply hS hkmap]
  simp_rw [Measure.map_apply hf hS]

theorem Measure.bind_map' {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {f : α → β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (g ∘ f) := by
  rw [Measure.bind, Measure.bind, Measure.map_map hg hf]

/-! ## Tape persistence through a prim step -/

theorem primStep_tape_persists_support
    {σ : State rT} {αloc : Loc} {e : Exp rT} {t : Tape} {ρ : Cfg rT}
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

theorem primStep_tape_persists [Countable rT] [MeasurableSingletonClass rT]
    {σ : State rT} {α : Loc} {e : Exp rT} {t : Tape}
    (h : σ.tapes[α]? = some t) :
    ∀ᵐ ρ ∂(primStep ⟨e, σ⟩),
      ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound := by
  refine MeasureTheory.ae_iff.mpr ?_
  rw [show {ρ : Cfg rT | ¬ ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound}
        = ⋃ ρ ∈ {ρ : Cfg rT | ¬ ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound},
            ({ρ} : Set (Cfg rT)) from by ext; simp]
  refine (measure_biUnion_null_iff (Set.to_countable _)).mpr ?_
  intro ρ hρ
  by_contra hne
  rw [← ne_eq, ← pos_iff_ne_zero] at hne
  exact hρ (primStep_tape_persists_support h (possible_iff_pos.mpr hne))

end ProbLang
