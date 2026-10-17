module

public import Metrology.ProbLang.Erasable
public import Metrology.ProbLang.Metatheory
public import Metrology.Couplings.Bridges.AddCoupl

@[expose] public section

/-!
# Erasure: presampling on tapes is invisible
-/

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure ProbLang.Measure

/-! ## Local uniform-presample distribution -/
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
  have hNonempty : (Finset.Ico 0 N).Nonempty := by
    refine ⟨0, Finset.mem_Ico.mpr ⟨le_refl _, hN⟩⟩
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
    exact hflat.comp ((measurable_snd).prodMk measurable_fst)
  have hproj : Measurable (fun σ : State rT => (σ, σ.tapes[α]?)) :=
    measurable_id.prodMk ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
  show Measurable (fun σ : State rT => leaf (σ, σ.tapes[α]?))
  exact hleaf.comp hproj

theorem tapeIndexUniform_univ_le_one {N : Int} :
    (tapeIndexUniform N) Set.univ ≤ 1 := by
  unfold tapeIndexUniform
  split
  · rename_i h
    have : IsProbabilityMeasure
        (PMF.uniformOfFinset (Finset.Ico 0 N) h).toMeasure :=
      PMF.toMeasure.isProbabilityMeasure _
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simp
  · simp

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
    exact State.upd_diff_tape_tot (hne.symm) |>.trans h
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
  refine (MeasureTheory.ae_iff).mpr ?_
  rw [show {ρ : Cfg rT | ¬ ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound}
        = ⋃ ρ ∈ {ρ : Cfg rT | ¬ ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound},
            ({ρ} : Set (Cfg rT)) from by ext; simp]
  refine (measure_biUnion_null_iff (Set.to_countable _)).mpr ?_
  intro ρ hρ
  by_contra hne
  rw [← ne_eq, ← pos_iff_ne_zero] at hne
  exact hρ (primStep_tape_persists_support h (possible_iff_pos.mpr hne))

/-! ## Structural properties of `tapePresample` -/

theorem tapePresample_ae
    {σ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} (h : σ.tapes[α]? = some ⟨N, bs⟩)
    {P : State rT → Prop} (hPm : MeasurableSet {σ' | P σ'})
    (hP : ∀ n, P (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))) :
    ∀ᵐ σ' ∂(tapePresample σ α), P σ' := by
  refine MeasureTheory.ae_iff.mpr ?_
  have hPc : MeasurableSet {σ' : State rT | ¬ P σ'} := hPm.compl
  simp only [tapePresample, h]
  rw [Measure.bind_apply hPc Measurable.of_discrete.aemeasurable]
  refine (lintegral_eq_zero_iff Measurable.of_discrete).mpr ?_
  refine MeasureTheory.ae_of_all _ fun n => ?_
  show (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))
        {a | ¬P a} = 0
  rw [Measure.dirac_apply' _ hPc, Set.indicator_of_notMem]
  simp only [Set.mem_ofPred_eq, not_not]
  exact hP n

theorem tapePresample_heap_eq
    {σ : State rT} {α : Loc} :
    ∀ᵐ σ' ∂(tapePresample σ α), σ'.heap = σ.heap := by
  cases hsome : σ.tapes[α]? with
  | none =>
    refine MeasureTheory.ae_iff.mpr ?_
    simp [tapePresample, hsome]
  | some t =>
    obtain ⟨N, bs⟩ := t
    exact tapePresample_ae hsome (by measurability) fun _ => by simp [State.update_tapes]

theorem tapePresample_tape_ne_ae
    {σ : State rT} {α α_lbl : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hne : α_lbl ≠ α) :
    ∀ᵐ σ' ∂(tapePresample σ α), σ'.tapes[α_lbl]? = σ.tapes[α_lbl]? := by
  obtain ⟨N, bs⟩ := t
  exact tapePresample_ae h (by measurability) fun _ => State.upd_diff_tape_tot hne

theorem tapePresample_bound_ae {σ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} (h : σ.tapes[α]? = some ⟨N, bs⟩) :
    ∀ᵐ σ' ∂tapePresample σ α, (σ'.tapes[α]?).map Tape.bound = some N := by
  have hmb : Measurable (fun σ' : State rT => (σ'.tapes[α]?).map Tape.bound) :=
    (Measurable.of_discrete (f := fun o : Option Tape => o.map Tape.bound)).comp
      ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
  exact tapePresample_ae h (hmb (measurableSet_singleton _)) fun _ => by simp [State.update_tapes]

theorem tapePresample_bind_pull_heap [Countable rT] [MeasurableSingletonClass rT]
    {σ : State rT} {α : Loc}
    (k : Std.ExtTreeMap Loc (Val rT) compare → State rT → Measure (Cfg rT)) :
    (tapePresample σ α).bind (fun σ' => k σ'.heap σ') =
      (tapePresample σ α).bind (fun σ' => k σ.heap σ') := by
  unfold tapePresample
  cases hsome : σ.tapes[α]? with
  | none =>
    show ((0 : Measure (State rT)).bind _) = _
    rw [Measure.bind_zero_left, Measure.bind_zero_left]
  | some t =>
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable,
        Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable]
    congr 1
    funext n'
    rw [Measure.dirac_bind (f := _) Measurable.of_discrete,
        Measure.dirac_bind (f := _) Measurable.of_discrete]
    show k (σ.update_tapes _).heap _ = k σ.heap _
    simp [State.update_tapes]

theorem tapePresample_update_heap_comm
    {σ : State rT} {α : Loc}
    (f : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare)
    (hf : Measurable f) :
    tapePresample (σ.update_heap f) α =
      (tapePresample σ α).map (·.update_heap f) := by
  have hmap : Measurable (fun σ' : State rT => σ'.update_heap f) :=
    State.measurable_iff.mpr ⟨hf.comp State.measurable_heap, State.measurable_tapes⟩
  unfold tapePresample
  have htapes : (σ.update_heap f).tapes[α]? = σ.tapes[α]? := by
    simp [State.update_heap]
  rw [htapes]
  cases hsome : σ.tapes[α]? with
  | none =>
    show (0 : Measure (State rT)) = _
    rw [Measure.map_zero]
  | some t =>
    obtain ⟨N, bs⟩ := t
    simp only
    have hker : AEMeasurable (fun n : {z : Int // 0 ≤ z ∧ z < N} =>
        (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) : Measure (State rT)))
        (tapeIndexUniform N) :=
      (measurable_dirac.comp Measurable.of_discrete).aemeasurable
    rw [Measure.bind_map_comm' _ _ _ hker hmap]
    congr 1
    funext n'
    rw [Measure.map_dirac (f := (·.update_heap f)) (σ.update_tapes (·.insert α ⟨N, bs ++ [n']⟩))]
    simp [State.update_tapes, State.update_heap]

theorem tapePresample_update_tapes_ne_comm
    {σ : State rT} {α β : Loc} {v : Tape} (hne : β ≠ α) :
    tapePresample (σ.update_tapes (·.insert β v)) α =
      (tapePresample σ α).map (·.update_tapes (·.insert β v)) := by
  have hins : Measurable (fun m : LocHeap Tape => m.insert β v) :=
    (Measurable.locHeap_insert β).comp (measurable_id.prodMk measurable_const)
  have hmap : Measurable (fun σ' : State rT => σ'.update_tapes (·.insert β v)) :=
    State.measurable_iff.mpr ⟨State.measurable_heap, hins.comp State.measurable_tapes⟩
  unfold tapePresample
  have htapes : (σ.update_tapes (·.insert β v)).tapes[α]? = σ.tapes[α]? :=
    State.upd_diff_tape_tot (Ne.symm hne)
  rw [htapes]
  cases hsome : σ.tapes[α]? with
  | none =>
    show (0 : Measure (State rT)) = _
    rw [Measure.map_zero]
  | some t =>
    obtain ⟨N, bs⟩ := t
    simp only
    have hker : AEMeasurable (fun n : {z : Int // 0 ≤ z ∧ z < N} =>
        (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) : Measure (State rT)))
        (tapeIndexUniform N) :=
      (measurable_dirac.comp Measurable.of_discrete).aemeasurable
    rw [Measure.bind_map_comm' _ _ _ hker hmap]
    congr 1
    funext n'
    rw [show Measure.dirac ((σ.update_tapes (·.insert β v)).update_tapes
            (·.insert α ⟨N, bs ++ [n']⟩))
        = (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n']⟩))).map
            (·.update_tapes (·.insert β v)) from by
      rw [Measure.map_dirac]; congr 1; exact State.upd_diff_tape_comm (Ne.symm hne)]

theorem tapePresample_lintegral
    {σ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }}
    (h : σ.tapes[α]? = some ⟨N, bs⟩) (f : State rT → ENNReal)
    (hf : Measurable f) :
    ∫⁻ σ', f σ' ∂tapePresample σ α
      = ∫⁻ n, f (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) ∂tapeIndexUniform N := by
  simp only [tapePresample, h]
  have hker : AEMeasurable (fun n : {z : Int // 0 ≤ z ∧ z < N} =>
      (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) : Measure (State rT)))
      (tapeIndexUniform N) :=
    (measurable_dirac.comp Measurable.of_discrete).aemeasurable
  rw [lintegral_bind hker hf.aemeasurable]
  simp_rw [lintegral_dirac]

theorem tapePresample_lintegral_update_heap
    {σ : State rT} {α : Loc}
    (g : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare)
    (hg : Measurable g)
    (f : State rT → ENNReal) (hf : Measurable f) :
    ∫⁻ σ', f (σ'.update_heap g) ∂tapePresample σ α
      = ∫⁻ τ, f τ ∂tapePresample (σ.update_heap g) α := by
  have hmap : Measurable (fun σ' : State rT => σ'.update_heap g) :=
    State.measurable_iff.mpr ⟨hg.comp State.measurable_heap, State.measurable_tapes⟩
  rw [tapePresample_update_heap_comm g hg,
      lintegral_map hf hmap]

theorem tapePresample_lintegral_update_tapes_ne
    {σ : State rT} {α β : Loc} {v : Tape} (hne : β ≠ α)
    (f : State rT → ENNReal) (hf : Measurable f) :
    ∫⁻ σ', f (σ'.update_tapes (·.insert β v)) ∂tapePresample σ α
      = ∫⁻ τ, f τ ∂tapePresample (σ.update_tapes (·.insert β v)) α := by
  have hins : Measurable (fun m : LocHeap Tape => m.insert β v) :=
    (Measurable.locHeap_insert β).comp (measurable_id.prodMk measurable_const)
  have hmap : Measurable (fun σ' : State rT => σ'.update_tapes (·.insert β v)) :=
    State.measurable_iff.mpr ⟨State.measurable_heap, hins.comp State.measurable_tapes⟩
  rw [tapePresample_update_tapes_ne_comm hne,
      lintegral_map hf hmap]

theorem Cfg.uniform_eq_bind {z : Int} {σ : State rT} (hz : 0 < z) :
    Cfg.uniform z σ =
      ((PMF.uniformOfFinset (Finset.Ico 0 z)
            (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
        (fun n => Measure.dirac (⟨.lit (.int n), σ⟩ : Cfg rT)) := by
  unfold Cfg.uniform Int.isPos
  rw [dite_eq_left hz]
  rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]

theorem tapePresample_bind_cfgUniform_comm
    {σ : State rT} {α : Loc} (z : Int) :
    (tapePresample σ α).bind (fun σ' => Cfg.uniform z σ') =
      (Cfg.uniform z σ).bind (fun ρ' =>
        (tapePresample ρ'.state α).bind
          (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg rT))) := by
  have hg2 : Measurable (fun p : Cfg rT × (State rT) => (⟨p.1.expr, p.2⟩ : Cfg rT)) := by
    refine Cfg.measurable_mk.comp (Measurable.prodMk ?_ ?_)
    · exact Cfg.measurable_expr.comp measurable_fst
    · exact measurable_snd
  have hk2 : Measurable (fun ρ' : Cfg rT =>
      (tapePresample ρ'.state α).bind
        (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg rT))) :=
    tapePresample_bind_dirac_measurable (g := fun ρ' σ'' => ⟨ρ'.expr, σ''⟩) hg2
  by_cases hz : 0 < z
  · have huniform_σ := Cfg.uniform_eq_bind (σ := σ) hz
    have hk_pmf : Measurable (fun σ' : State rT =>
        ((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
            (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT))) := by
      have hre : (fun σ' : State rT =>
          ((PMF.uniformOfFinset (Finset.Ico 0 z)
                (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
              (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT)))
          = (fun σ' : State rT => Cfg.uniform z σ') := by
        funext σ'; exact (Cfg.uniform_eq_bind (σ := σ') hz).symm
      rw [hre]
      exact Cfg.uniform.measurable.comp (measurable_const.prodMk measurable_id)
    have hLHS : (tapePresample σ α).bind (fun σ' => Cfg.uniform z σ') =
        (tapePresample σ α).bind (fun σ' =>
          ((PMF.uniformOfFinset (Finset.Ico 0 z)
                (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
              (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT))) := by
      congr 1; funext σ'; exact Cfg.uniform_eq_bind (σ := σ') hz
    rw [hLHS, huniform_σ]
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          hk2.aemeasurable]
    simp_rw [Measure.dirac_bind
              (f := fun ρ' : Cfg rT => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg rT)))
              hk2]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS hk_pmf.aemeasurable,
        Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    have hLlint : ∀ σ' : State rT,
        ((((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
                (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT))) S) =
        ∫⁻ n, (Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT)) S
          ∂((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure) := by
      intro σ'
      exact Measure.bind_apply hS Measurable.of_discrete.aemeasurable
    have hRlint : ∀ n : Int,
        ((tapePresample σ α).bind
            (fun σ'' => Measure.dirac (⟨.lit (.int n), σ''⟩ : Cfg rT))) S =
        ∫⁻ σ'', (Measure.dirac (⟨.lit (.int n), σ''⟩ : Cfg rT)) S
          ∂(tapePresample σ α) := by
      intro n
      exact Measure.bind_apply hS
        (Cfg.measurable_dirac_mk (fe := fun _ => .lit (.int n)) measurable_const
          measurable_id).aemeasurable
    simp_rw [hLlint, hRlint]
    have : IsFiniteMeasure (tapePresample σ α) :=
      ⟨lt_of_le_of_lt tapePresample_univ_le_one ENNReal.one_lt_top⟩
    have hcfgbuild : Measurable (fun p : State rT × Int =>
        (⟨.lit (.int p.2), p.1⟩ : Cfg rT)) :=
      Cfg.measurable_iff.mpr
        ⟨Exp.lit.measurable.comp (BaseLit.int.measurable.comp measurable_snd), measurable_fst⟩
    have hswapmeas : Measurable (Function.uncurry (fun (σ' : State rT) (n : Int) =>
        (Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT)) S)) := by
      show Measurable (fun p : State rT × Int =>
        (Measure.dirac (⟨.lit (.int p.2), p.1⟩ : Cfg rT)) S)
      exact ((Measure.measurable_coe hS).comp measurable_dirac).comp hcfgbuild
    exact lintegral_lintegral_swap
      (μ := tapePresample σ α)
      (ν := ((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure))
      (f := fun σ' n => (Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT)) S)
      hswapmeas.aemeasurable
  · have hCfg' : ∀ σ' : State rT,
        Cfg.uniform z σ' = Measure.dirac (⟨.lit (.int (-1)), σ'⟩ : Cfg rT) :=
      fun σ' => Cfg.uniform_nonpos_eq hz
    simp_rw [hCfg']
    rw [Measure.dirac_bind
          (f := fun ρ' : Cfg rT => (tapePresample ρ'.state α).bind
            (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg rT)))
          hk2]

/-! ## Core: presampling is invisible to `execN` at the expression level

Only the expression projection is invariant: presampling changes the final tape content.
Clutch's `prim_coupl_upd_tapes_dom` states the same thing on the `dmap (λ x, x.1)` projection. -/

omit [LawfulProbLangℝ rT] in
theorem State.update_tapes_insert_id {σ : State rT} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) :
    σ.update_tapes (·.insert α t) = σ :=
  State.update_tapes_no_change h

theorem tapeIndexUniform_lintegral_eq_cfg_uniform
    {N : Int} (hN : 0 < N) (σ : State rT)
    (f : Cfg rT → ENNReal) (hf : Measurable f) :
    ∫⁻ (a : { z : Int // 0 ≤ z ∧ z < N }),
        f ⟨.lit (.int ↑a), σ⟩ ∂tapeIndexUniform N
      = ∫⁻ (ρ : Cfg rT), f ρ ∂Cfg.uniform N σ := by
  unfold tapeIndexUniform Cfg.uniform Int.isPos
  have hNonempty : (Finset.Ico 0 N).Nonempty := ⟨0, Finset.mem_Ico.mpr ⟨le_refl _, hN⟩⟩
  rw [dite_eq_left hNonempty, dite_eq_left hN]
  simp only
  have hm_sub : Measurable (fun z : Int => if hz : 0 ≤ z ∧ z < N then
      (⟨z, hz⟩ : {z // 0 ≤ z ∧ z < N}) else ⟨0, ⟨le_refl _, by omega⟩⟩) :=
    Measurable.of_discrete
  have hm_cfg : Measurable (fun x : Int => (⟨Exp.lit (BaseLit.int x), σ⟩ : Cfg rT)) :=
    Measurable.of_discrete
  have hm_f_sub : Measurable (fun (a : {z // 0 ≤ z ∧ z < N}) => f ⟨.lit (.int ↑a), σ⟩) :=
    Measurable.of_discrete
  rw [lintegral_map hm_f_sub hm_sub, lintegral_map hf hm_cfg]
  apply lintegral_congr_ae
  rw [Filter.eventuallyEq_iff_exists_mem]
  use (PMF.uniformOfFinset (Finset.Ico 0 N) hNonempty).support
  constructor
  · rw [mem_ae_iff]
    rw [(PMF.uniformOfFinset (Finset.Ico 0 N) hNonempty).toMeasure_apply_eq_zero_iff
      MeasurableSet.of_discrete]
    exact disjoint_compl_right
  · intro a ha
    have hmem : a ∈ Finset.Ico 0 N := by
      rwa [PMF.mem_support_uniformOfFinset_iff] at ha
    have hab : 0 ≤ a ∧ a < N := Finset.mem_Ico.mp hmem
    simp [dite_eq_left hab]

/-! ## Case-closing helpers for `execN_tape_presample_expr_eq` -/

/-- The induction hypothesis of `execN_tape_presample_expr_eq`, under the evaluation context `K`. -/
abbrev ErasureIHFill (m : Nat) (K : Ectx rT) (S : Set (Exp rT)) (α : Loc) : Prop :=
  ∀ (e' : Exp rT) (σ' : State rT) (t' : Tape),
    σ'.tapes[α]? = some t' → 0 < t'.bound →
    ∫⁻ σ'', ((execN m ∘ K.fillCfg) ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S)
        ∂tapePresample σ' α
      = ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S)

theorem erasure_integrand_measurable {m : Nat} {K : Ectx rT} {S : Set (Exp rT)}
    (hS : MeasurableSet S) :
    Measurable (fun ρ : Cfg rT =>
      ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)) :=
  ((Measure.measurable_coe (Cfg.measurable_expr hS)).comp
    (execN_measurable m)).comp (Ectx.fillCfg.measurable K)

theorem erasure_det_close
    {m : Nat} {K : Ectx rT} {S : Set (Exp rT)} {σ : State rT} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α)
    (e_h e' : Exp rT)
    (hs : ∀ σ' : State rT, headStep (⟨e_h, σ'⟩ : Cfg rT) = Measure.dirac ⟨e', σ'⟩) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by
  simp_rw [hs, lintegral_dirac]
  exact ih_fill _ σ t h hN

theorem erasure_det_close_ae
    {m : Nat} {K : Ectx rT} {S : Set (Exp rT)} {σ : State rT} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α)
    (e_h e' : Exp rT)
    (hs_ae : ∀ᵐ σ' ∂(tapePresample σ α),
        headStep (⟨e_h, σ'⟩ : Cfg rT) = Measure.dirac ⟨e', σ'⟩)
    (hs_σ : headStep (⟨e_h, σ⟩ : Cfg rT) = Measure.dirac ⟨e', σ⟩) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by
  have : IsProbabilityMeasure (tapePresample σ α) :=
    ⟨tapePresample_univ_eq_one h hN⟩
  rw [hs_σ, lintegral_dirac]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S)
          ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hs_ae] with σ' hs
        rw [hs, lintegral_dirac]
    _ = ((execN m ∘ K.fillCfg) ⟨e', σ⟩) ((fun x => x.expr) ⁻¹' S) :=
          ih_fill _ σ t h hN

theorem erasure_uniform_close
    {m : Nat} {K : Ectx rT} {S : Set (Exp rT)} {σ : State rT} {α : Loc} {t : Tape}
    (hS : MeasurableSet S)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α)
    (e_h : Exp rT) (z_r : Int) (hz : 0 < z_r)
    (hstep_ae : ∀ᵐ σ' ∂(tapePresample σ α),
        headStep (⟨e_h, σ'⟩ : Cfg rT) = Cfg.uniform z_r σ')
    (hstep_σ : headStep (⟨e_h, σ⟩ : Cfg rT) = Cfg.uniform z_r σ) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by
  have : IsProbabilityMeasure (tapePresample σ α) :=
    ⟨tapePresample_univ_eq_one h hN⟩
  have hNonempty : (Finset.Ico (0 : Int) z_r).Nonempty := Finset.nonempty_Ico.mpr hz
  set pmf := PMF.uniformOfFinset (Finset.Ico (0 : Int) z_r) hNonempty
  have hunif : ∀ σ₀ : State rT, Cfg.uniform z_r σ₀ =
      pmf.toMeasure.map (fun n : Int => (⟨.lit (.int n), σ₀⟩ : Cfg rT)) := fun σ₀ => by
    unfold Cfg.uniform Int.isPos; rw [dite_eq_left hz]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂Cfg.uniform z_r σ' ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hstep_ae] with σ' hs; rw [hs]
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂Cfg.uniform z_r σ := by
        have hcfgbuild : Measurable (fun p : State rT × Int =>
            (⟨.lit (.int p.2), p.1⟩ : Cfg rT)) := by
          refine Cfg.measurable_mk.comp (Measurable.prodMk ?_ measurable_fst)
          exact Exp.lit.measurable.comp (BaseLit.int.measurable.comp measurable_snd)
        simp_rw [hunif,
          lintegral_map (erasure_integrand_measurable hS) Measurable.of_discrete]
        rw [lintegral_lintegral_swap (f := fun σ' n =>
              ((execN m ∘ K.fillCfg) ⟨.lit (.int n), σ'⟩) ((fun x => x.expr) ⁻¹' S))
            ((erasure_integrand_measurable hS).comp hcfgbuild).aemeasurable]
        congr 1; funext n; exact ih_fill _ σ t h hN
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by rw [hstep_σ]

theorem erasure_uniformReal_close
    {m : Nat} {K : Ectx rT} {S : Set (Exp rT)} {σ : State rT} {α : Loc} {t : Tape}
    (hS : MeasurableSet S)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α)
    (e_h : Exp rT)
    (hstep_ae : ∀ᵐ σ' ∂(tapePresample σ α),
        headStep (⟨e_h, σ'⟩ : Cfg rT) = Cfg.uniformReal σ')
    (hstep_σ : headStep (⟨e_h, σ⟩ : Cfg rT) = Cfg.uniformReal σ) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by
  have : IsProbabilityMeasure (tapePresample σ α) :=
    ⟨tapePresample_univ_eq_one h hN⟩
  have hunif : ∀ σ₀ : State rT, Cfg.uniformReal σ₀ =
      (LawfulProbLangℝ.unifUnit (T := rT)).map (fun r : rT => (⟨.lit (.real r), σ₀⟩ : Cfg rT)) :=
    fun _ => rfl
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂Cfg.uniformReal σ' ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hstep_ae] with σ' hs; rw [hs]
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂Cfg.uniformReal σ := by
        have hcfgbuild : Measurable (fun p : State rT × rT =>
            (⟨.lit (.real p.2), p.1⟩ : Cfg rT)) := by
          refine Cfg.measurable_mk.comp (Measurable.prodMk ?_ measurable_fst)
          exact Exp.lit.measurable.comp (BaseLit.real.measurable.comp measurable_snd)
        have hmap : ∀ σ₀ : State rT, Measurable (fun r : rT => (⟨.lit (.real r), σ₀⟩ : Cfg rT)) :=
          fun σ₀ => Cfg.measurable_iff.mpr
            ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
        simp_rw [hunif,
          lintegral_map (erasure_integrand_measurable hS) (hmap _)]
        rw [lintegral_lintegral_swap (f := fun σ' r =>
              ((execN m ∘ K.fillCfg) ⟨.lit (.real r), σ'⟩) ((fun x => x.expr) ⁻¹' S))
            ((erasure_integrand_measurable hS).comp hcfgbuild).aemeasurable]
        congr 1; funext r; exact ih_fill _ σ t h hN
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by rw [hstep_σ]

/-! ### Per-head-step case closers -/

theorem erasure_load_close
    {m : Nat} {K : Ectx rT} {S : Set (Exp rT)} {σ : State rT} {α ℓ : Loc} {t : Tape} {v : Val rT}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α)
    (hlookup : σ.heap[ℓ]? = some v) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.load (.lit (.loc ℓ)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.load (.lit (.loc ℓ)), σ⟩ := by
  have hload : ∀ (σ₀ : State rT), σ₀.heap = σ.heap →
      headStep (⟨.load (.lit (.loc ℓ)), σ₀⟩ : Cfg rT) = Measure.dirac ⟨.ofVal v, σ₀⟩ := by
    intro σ₀ hh
    change (match σ₀.heap[ℓ]? with
              | none => (0 : Measure (Cfg rT)) | some v => Measure.dirac ⟨.ofVal v, σ₀⟩) = _
    rw [hh, hlookup]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨.load (.lit (.loc ℓ)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ((execN m ∘ K.fillCfg) ⟨.ofVal v, σ'⟩)
                ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
        rw [hload σ' hheap, lintegral_dirac]
    _ = ((execN m ∘ K.fillCfg) ⟨.ofVal v, σ⟩) ((fun x => x.expr) ⁻¹' S) :=
        ih_fill _ σ t h hN
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.load (.lit (.loc ℓ)), σ⟩ := by
        rw [hload σ rfl, lintegral_dirac]

theorem erasure_alloc_close
    {m : Nat} {K : Ectx rT} {S : Set (Exp rT)} {σ : State rT} {α : Loc} {t : Tape} {ed : Exp rT}
    (hS : MeasurableSet S)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.alloc ed, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.alloc ed, σ⟩ := by
  have halloc : ∀ (σ₀ : State rT), σ₀.heap = σ.heap →
      headStep (⟨.alloc ed, σ₀⟩ : Cfg rT) =
        ed.asValM fun vd =>
          let ℓ := σ.heap.fresh
          Measure.dirac ⟨.lit (.loc ℓ), σ₀.update_heap fun hp => hp.insert ℓ vd⟩ := by
    intro σ₀ hh
    show Exp.asValM ed (fun vd => let ℓ := σ₀.heap.fresh; _) = _
    rw [hh]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨.alloc ed, σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂(ed.asValM fun vd => let ℓ := σ.heap.fresh;
                    Measure.dirac ⟨.lit (.loc ℓ), σ'.update_heap fun hp => hp.insert ℓ vd⟩)
                ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
        rw [halloc σ' hheap]
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.alloc ed, σ⟩ := by
        cases hcheck : ed.toVal? with
        | none =>
          simp only [Exp.asValM, hcheck, lintegral_zero_measure]
          rw [halloc σ rfl]; simp [Exp.asValM, hcheck, lintegral_zero_measure]
        | some vd =>
          simp only [Exp.asValM, hcheck]
          simp_rw [lintegral_dirac]
          set f_heap : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare :=
            (fun hp => hp.insert σ.heap.fresh vd)
          have htape_upd : (σ.update_heap f_heap).tapes[α]? = some t := by
            simp [State.update_heap, h]
          have hg_fheap : Measurable f_heap :=
            (Measurable.locHeap_insert σ.heap.fresh).comp (measurable_id.prodMk measurable_const)
          have hf_int : Measurable (fun τ : State rT =>
              ((execN m ∘ K.fillCfg) ⟨.lit (.loc σ.heap.fresh), τ⟩)
                ((fun x => x.expr) ⁻¹' S)) :=
            (erasure_integrand_measurable hS).comp
              (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
          rw [tapePresample_lintegral_update_heap (g := f_heap) hg_fheap
                (fun τ => ((execN m ∘ K.fillCfg) ⟨.lit (.loc σ.heap.fresh), τ⟩)
                  ((fun x => x.expr) ⁻¹' S)) hf_int,
              ih_fill _ (σ.update_heap f_heap) t htape_upd hN,
              halloc σ rfl]
          simp [Exp.asValM, hcheck, lintegral_dirac, f_heap]

theorem erasure_store_close
    {m : Nat} {K : Ectx rT} {S : Set (Exp rT)} {σ : State rT} {α ℓ : Loc} {t : Tape} {ev : Exp rT}
    (hS : MeasurableSet S)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ⟩ := by
  have hstore : ∀ (σ₀ : State rT), σ₀.heap = σ.heap →
      headStep (⟨.store (.lit (.loc ℓ)) ev, σ₀⟩ : Cfg rT) =
        ev.asValM fun v =>
          match σ.heap[ℓ]? with
          | none => (0 : Measure (Cfg rT))
          | some _ => Measure.dirac ⟨.lit .unit, σ₀.update_heap fun hp => hp.insert ℓ v⟩ := by
    intro σ₀ hh
    show Exp.asValM ev (fun v => match σ₀.heap[ℓ]? with | none => _ | some _ => _) = _
    rw [hh]
  have zero_branch : ∀ (_hz : ∀ (σ₀ : State rT), σ₀.heap = σ.heap →
      headStep (⟨.store (.lit (.loc ℓ)) ev, σ₀⟩ : Cfg rT) = 0),
      ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
        = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
            ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ⟩ := fun hz => by
    rw [hz σ rfl, lintegral_zero_measure]
    calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                  ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
        = ∫⁻ _, (0 : ENNReal) ∂tapePresample σ α := by
          refine lintegral_congr_ae ?_
          filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
          rw [hz σ' hheap]; exact lintegral_zero_measure _
      _ = 0 := lintegral_zero
  cases hcheck : ev.toVal? with
  | none =>
    exact zero_branch fun σ₀ hh => by
      rw [hstore σ₀ hh]; simp [Exp.asValM, hcheck]
  | some v =>
    cases hlook : σ.heap[ℓ]? with
    | none =>
      exact zero_branch fun σ₀ hh => by
        rw [hstore σ₀ hh]; simp [Exp.asValM, hcheck, hlook]
    | some w =>
      set f_heap : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare :=
        (fun hp => hp.insert ℓ v)
      calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                    ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
          = ∫⁻ σ', ((execN m ∘ K.fillCfg) ⟨.lit .unit, σ'.update_heap f_heap⟩)
                      ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
            refine lintegral_congr_ae ?_
            filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
            rw [hstore σ' hheap]
            simp only [Exp.asValM, hcheck, hlook, lintegral_dirac]
            simp only [f_heap]
        _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ⟩ := by
            have htape_upd : (σ.update_heap f_heap).tapes[α]? = some t := by
              simp [State.update_heap, h]
            have hg_fheap : Measurable f_heap :=
              (Measurable.locHeap_insert ℓ).comp (measurable_id.prodMk measurable_const)
            have hf_int : Measurable (fun τ : State rT =>
                ((execN m ∘ K.fillCfg) ⟨.lit .unit, τ⟩) ((fun x => x.expr) ⁻¹' S)) :=
              (erasure_integrand_measurable hS).comp
                (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
            rw [tapePresample_lintegral_update_heap (g := f_heap) hg_fheap
                  (fun τ => ((execN m ∘ K.fillCfg) ⟨.lit .unit, τ⟩)
                    ((fun x => x.expr) ⁻¹' S)) hf_int,
                ih_fill _ (σ.update_heap f_heap) t htape_upd hN,
                hstore σ rfl]
            simp [Exp.asValM, hcheck, hlook, lintegral_dirac, f_heap]

theorem erasure_tape_close
    {m : Nat} {K : Ectx rT} {S : Set (Exp rT)} {σ : State rT} {α : Loc} {t : Tape} {z : Int}
    (hS : MeasurableSet S)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.tape (.lit (.int z)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.tape (.lit (.int z)), σ⟩ := by
  have hne : σ.tapes.fresh ≠ α := Std.ExtTreeMap.elem_fresh_ne h
  have hfresh_eq : ∀ᵐ σ' ∂(tapePresample σ α), σ'.tapes.fresh = σ.tapes.fresh := by
    obtain ⟨N, bs⟩ := t
    exact tapePresample_ae h (by measurability) fun _ => State.fresh_loc_upd_some h
  have htape_rw : ∀ (σ₀ : State rT), σ₀.tapes.fresh = σ.tapes.fresh →
      headStep (⟨.tape (.lit (.int z)), σ₀⟩ : Cfg rT) =
        Measure.dirac ⟨.lit (.lbl σ.tapes.fresh),
          σ₀.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))⟩ := by
    intro σ₀ hfr; simp only [headStep, hfr]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨.tape (.lit (.int z)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ((execN m ∘ K.fillCfg)
            ⟨.lit (.lbl σ.tapes.fresh),
             σ'.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))⟩)
                  ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfresh_eq] with σ' hfr
        rw [htape_rw σ' hfr, lintegral_dirac]
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.tape (.lit (.int z)), σ⟩ := by
        have htape_upd :
            (σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))).tapes[α]?
              = some t := by
          rw [State.upd_diff_tape_tot (Ne.symm hne)]; exact h
        have hf_int : Measurable (fun τ : State rT =>
            ((execN m ∘ K.fillCfg) ⟨.lit (.lbl σ.tapes.fresh), τ⟩)
              ((fun x => x.expr) ⁻¹' S)) :=
          (erasure_integrand_measurable hS).comp
            (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
        rw [tapePresample_lintegral_update_tapes_ne hne
              (fun τ => ((execN m ∘ K.fillCfg) ⟨.lit (.lbl σ.tapes.fresh), τ⟩)
                ((fun x => x.expr) ⁻¹' S)) hf_int,
            ih_fill _ (σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z)))
              t htape_upd hN,
            htape_rw σ rfl, lintegral_dirac]

theorem erasure_zero_close
    {m : Nat} {K : Ectx rT} {S : Set (Exp rT)} {σ : State rT} {α : Loc} {t : Tape} {e_red : Exp rT}
    (h : σ.tapes[α]? = some t) (_hN : 0 < t.bound)
    (hzero : headStep ⟨e_red, σ⟩ = 0) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_red, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_red, σ⟩ := by
  have hzero_ae : ∀ᵐ σ' ∂(tapePresample σ α), headStep ⟨e_red, σ'⟩ = 0 := by
    obtain ⟨N, bs⟩ := t
    have hg : Measurable (fun σ' : State rT => headStep (⟨e_red, σ'⟩ : Cfg rT)) :=
      headStep.measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
    have hPm : MeasurableSet {σ' : State rT | headStep (⟨e_red, σ'⟩ : Cfg rT) = 0} := by
      have hset : {σ' : State rT | headStep (⟨e_red, σ'⟩ : Cfg rT) = 0}
          = (fun σ' => (headStep (⟨e_red, σ'⟩ : Cfg rT)) Set.univ) ⁻¹' {0} := by
        ext σ'; simp [Measure.measure_univ_eq_zero]
      rw [hset]
      exact ((Measure.measurable_coe MeasurableSet.univ).comp hg) (measurableSet_singleton 0)
    exact tapePresample_ae h hPm fun _ => State.head_step_dzero_upd_tapes h hzero
  rw [hzero, lintegral_zero_measure]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨e_red, σ'⟩ ∂tapePresample σ α
      = ∫⁻ _, (0 : ENNReal) ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hzero_ae] with σ' h0
        rw [h0, lintegral_zero_measure]
    _ = 0 := lintegral_zero

/-- Clutch `prim_coupl_upd_tapes_dom`, projected to expressions. `0 < t.bound` is needed:
otherwise `tapePresample σ α = 0`. -/
theorem execN_tape_presample_expr_eq
    {σ : State rT} {α : Loc} {e : Exp rT} {m : Nat} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresample σ α).bind (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩) := by
  unfold asExpr
  induction m generalizing e σ t with
  | zero =>
    show ((tapePresample σ α).bind (fun _ => (0 : Measure (Cfg rT)))).map (·.expr) =
         ((0 : Measure (Cfg rT))).map (·.expr)
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply Cfg.measurable_expr hS,
        Measure.map_apply Cfg.measurable_expr hS,
        Measure.bind_apply (Cfg.measurable_expr hS) measurable_const.aemeasurable]
    simp only [Measure.coe_zero, Pi.zero_apply, lintegral_zero]
  | succ m ih =>
    by_cases hv : e.isValue
    · have hstep : ∀ σ' : State rT,
          execN (m + 1) ⟨e, σ'⟩ = Measure.dirac ⟨e, σ'⟩ := fun σ' =>
        execN_succ_isValue (ρ := ⟨e, σ'⟩) hv m
      simp_rw [hstep]
      have hkdir : Measurable (fun σ' : State rT => Measure.dirac (⟨e, σ'⟩ : Cfg rT)) :=
        Cfg.measurable_dirac_mk (fe := fun _ => e) measurable_const measurable_id
      rw [Measure.bind_map_comm' _ _ _ hkdir.aemeasurable Cfg.measurable_expr]
      -- explicit kernel equality: `simp_rw` leaves metavariables here
      have hker : (fun σ' : State rT => Measure.map (·.expr) (Measure.dirac (⟨e, σ'⟩ : Cfg rT)))
          = (fun _ => Measure.dirac e) := by
        funext σ'
        rw [Measure.map_dirac (f := fun c : Cfg rT => c.expr) (⟨e, σ'⟩ : Cfg rT)]
      rw [hker, Measure.map_dirac (f := fun c : Cfg rT => c.expr) (⟨e, σ⟩ : Cfg rT)]
      refine Measure.ext fun S hS => ?_
      rw [Measure.bind_apply hS measurable_const.aemeasurable,
          lintegral_const, tapePresample_univ_eq_one h hN, mul_one]
    · have hstep : ∀ σ' : State rT,
          execN (m + 1) ⟨e, σ'⟩ = (primStep ⟨e, σ'⟩).bind (execN m) :=
        fun σ' => execN_succ_not_isValue (ρ := ⟨e, σ'⟩) hv m
      simp_rw [hstep]
      set K := e.decomp.1
      set e_red := e.decomp.2
      have hprim : ∀ σ' : State rT,
          primStep ⟨e, σ'⟩ = (headStep ⟨e_red, σ'⟩).map K.fillCfg := by
        intro σ'; simp only [primStep, e_red, K]
      have hg_exec : Measurable (execN m ∘ K.fillCfg) :=
        (execN_measurable m).comp (Ectx.fillCfg.measurable K)
      have hker_hs : Measurable (fun σ' : State rT => headStep (⟨e_red, σ'⟩ : Cfg rT)) :=
        headStep.measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
      have hbind_ker : Measurable (fun σ' : State rT =>
          (headStep (⟨e_red, σ'⟩ : Cfg rT)).bind (execN m ∘ K.fillCfg)) :=
        (Measure.measurable_join.comp (Measure.measurable_map _ hg_exec)).comp hker_hs
      simp_rw [hprim, Measure.bind_map' (Ectx.fillCfg.measurable K) (execN_measurable m)]
      refine Measure.ext fun S hS => ?_
      rw [Measure.map_apply Cfg.measurable_expr hS,
          Measure.map_apply Cfg.measurable_expr hS]
      rw [Measure.bind_apply (Cfg.measurable_expr hS) hbind_ker.aemeasurable]
      simp_rw [Measure.bind_apply (Cfg.measurable_expr hS) hg_exec.aemeasurable]
      have ih_pointwise : ∀ (e' : Exp rT) (σ' : State rT) (t' : Tape),
          σ'.tapes[α]? = some t' → 0 < t'.bound →
          ∫⁻ σ'', (execN m ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ' α
            = (execN m ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S) := by
        intro e' σ' t' ht' hN'
        have hih : ((tapePresample σ' α).bind (fun σ'' => execN m ⟨e', σ''⟩)).map (·.expr)
                  = (execN m ⟨e', σ'⟩).map (·.expr) := ih ht' hN'
        have hval : ((tapePresample σ' α).bind (fun σ'' => execN m ⟨e', σ''⟩)).map (·.expr) S
                  = (execN m ⟨e', σ'⟩).map (·.expr) S := by rw [hih]
        have hk_exec : Measurable (fun σ'' : State rT => execN m (⟨e', σ''⟩ : Cfg rT)) :=
          (execN_measurable m).comp
            (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
        rw [Measure.map_apply Cfg.measurable_expr hS,
            Measure.map_apply Cfg.measurable_expr hS,
            Measure.bind_apply (Cfg.measurable_expr hS) hk_exec.aemeasurable] at hval
        exact hval
      have ih_fill : ErasureIHFill m K S α := by
        intro e' σ' t' ht' hN'
        simp only [Function.comp]
        exact ih_pointwise (K.fill e') σ' t' ht' hN'
      have det_close_state_pres := fun e_h e' hs =>
        erasure_det_close (m := m) (K := K) (S := S) h hN ih_fill e_h e' hs
      have uniform_close := fun e_h z_r hz hstep_ae hstep_σ =>
        erasure_uniform_close (m := m) (K := K) (S := S) hS h hN ih_fill
          e_h z_r hz hstep_ae hstep_σ
      have uniformReal_close := fun e_h hstep_ae hstep_σ =>
        erasure_uniformReal_close (m := m) (K := K) (S := S) hS h hN ih_fill
          e_h hstep_ae hstep_σ
      rcases det_or_prob_or_zero e_red σ with hdet | hprob | hzero
      · clear_value e_red K
        cases hdet with
        | betaLam hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ (Exp.open' e1 e2) fun σ' => ?_
          exact Exp.isValM_some hv2
        | betaFix hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ (Exp.app (Exp.open' e1 (.fix e1)) e2) fun σ' => ?_
          exact Exp.isValM_some hv2
        | unop hv heval =>
          rename_i op e_u e'
          refine det_close_state_pres _ e' fun σ' => ?_
          show Exp.isValM e_u (ProbLang.Option.unwrapM _ (op.eval e_u)) = _
          rw [Exp.isValM_some hv, heval]; rfl
        | binop hv1 hv2 heval =>
          rename_i op e1 e2 e'
          refine det_close_state_pres _ e' fun σ' => ?_
          show Exp.isValM e1 (Exp.isValM e2 (ProbLang.Option.unwrapM _ (op.eval e1 e2))) = _
          rw [Exp.isValM_some hv2, Exp.isValM_some hv1, heval]; rfl
        | ifTrue =>
          rename_i et ef
          exact det_close_state_pres _ et fun _ => rfl
        | ifFalse =>
          rename_i et ef
          exact det_close_state_pres _ ef fun _ => rfl
        | fst hv1 hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ e1 fun σ' => ?_
          show Exp.isValM e1 (Exp.isValM e2 (Measure.dirac _)) = _
          rw [Exp.isValM_some hv2, Exp.isValM_some hv1]
        | snd hv1 hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ e2 fun σ' => ?_
          show Exp.isValM e1 (Exp.isValM e2 (Measure.dirac _)) = _
          rw [Exp.isValM_some hv2, Exp.isValM_some hv1]
        | caseL hv =>
          rename_i e_c el er
          refine det_close_state_pres _ (el.app e_c) fun σ' => ?_
          exact Exp.isValM_some hv
        | caseR hv =>
          rename_i e_c el er
          refine det_close_state_pres _ (er.app e_c) fun σ' => ?_
          exact Exp.isValM_some hv
        | scrutSuccess hv hmatch =>
          rename_i e_s p bindings
          refine det_close_state_pres _ (.inl bindings) fun σ' => ?_
          show Exp.isValM e_s (match Pat.tryMatch p e_s with | some b => _ | none => _) = _
          rw [Exp.isValM_some hv, hmatch]
        | scrutFailure hv hmatch =>
          rename_i e_s p
          refine det_close_state_pres _ (.inr (.lit .unit)) fun σ' => ?_
          show Exp.isValM e_s (match Pat.tryMatch p e_s with | some b => _ | none => _) = _
          rw [Exp.isValM_some hv, hmatch]
        | load hlook =>
          rename_i ℓ v
          exact erasure_load_close (v := v) h hN ih_fill hlook
        | alloc hv =>
          rename_i ed
          exact erasure_alloc_close (ed := ed) hS h hN ih_fill
        | store hv hsome =>
          rename_i ℓ ev
          exact erasure_store_close (ℓ := ℓ) (ev := ev) hS h hN ih_fill
        | tape =>
          rename_i z
          exact erasure_tape_close (z := z) hS h hN ih_fill
      · clear_value e_red K
        cases hprob with
        | randNoTape hz =>
          rename_i z_r
          exact uniform_close _ z_r hz
            (MeasureTheory.ae_of_all _ fun _ => rfl) rfl
        | @randTape z_r α_lbl _ N_b nn ns htapes hzN =>
          subst hzN
          by_cases hαeq : α = α_lbl
          · subst hαeq
            have ht_eq : t = ⟨z_r, nn :: ns⟩ := by
              rw [h] at htapes; exact Option.some.inj htapes
            subst ht_eq
            have hrhs : headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ⟩ =
                Measure.dirac ⟨.lit (.int nn),
                  σ.update_tapes (·.insert α ⟨z_r, ns⟩)⟩ := by
              simp [headStep, htapes]
            have hker_rand : Measurable (fun σ' : State rT =>
                headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩ : Cfg rT)) :=
              headStep.measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
            rw [hrhs, lintegral_dirac,
                tapePresample_lintegral h
                  (fun σ' => ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                    ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩)
                  ((Measure.measurable_lintegral (erasure_integrand_measurable hS)).comp
                    hker_rand)]
            have hstep_upd : ∀ n' : { z : Int // 0 ≤ z ∧ z < z_r },
                headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)),
                  σ.update_tapes (·.insert α ⟨z_r, (nn :: ns) ++ [↑n']⟩)⟩ =
                Measure.dirac ⟨.lit (.int ↑nn),
                  σ.update_tapes (·.insert α ⟨z_r, ns ++ [↑n']⟩)⟩ := by
              intro ⟨n', hn'⟩
              simp only [headStep, State.upd_tape_some, List.cons_append, ↓reduceIte]
              rw [State.update_tapes_twice]
            simp_rw [hstep_upd, lintegral_dirac]
            have htape_popped : (σ.update_tapes (·.insert α ⟨z_r, ns⟩)).tapes[α]? =
                some ⟨z_r, ns⟩ := State.upd_tape_some _ _ _
            convert
              ih_fill (.lit (.int ↑nn)) (σ.update_tapes (·.insert α ⟨z_r, ns⟩))
                ⟨z_r, ns⟩ htape_popped hN using 1
            rw [tapePresample_lintegral htape_popped
                  (fun σ'' => ((execN m ∘ K.fillCfg) ⟨.lit (.int ↑nn), σ''⟩)
                    ((fun x => x.expr) ⁻¹' S))
                  ((erasure_integrand_measurable hS).comp
                    (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id)))]
            simp_rw [State.update_tapes_twice]
          · have hstep_rw : ∀ (σ₀ : State rT), σ₀.tapes[α_lbl]? = some ⟨z_r, nn :: ns⟩ →
                headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ₀⟩ : Cfg rT) =
                  Measure.dirac ⟨.lit (.int nn),
                    σ₀.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)⟩ := by
              intro σ₀ ht'; simp [headStep, ht']
            have htapes_pres : ∀ᵐ σ' ∂(tapePresample σ α),
                σ'.tapes[α_lbl]? = some ⟨z_r, nn :: ns⟩ := by
              filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' heq
              exact heq.trans htapes
            calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                          ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ'⟩
                          ∂tapePresample σ α
                = ∫⁻ σ', ((execN m ∘ K.fillCfg)
                      ⟨.lit (.int nn), σ'.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)⟩)
                        ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
                  refine lintegral_congr_ae ?_
                  filter_upwards [htapes_pres] with σ' ht'
                  rw [hstep_rw σ' ht', lintegral_dirac]
              _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                    ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ⟩ := by
                  have htape_upd :
                      (σ.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)).tapes[α]?
                        = some t := by
                    rw [State.upd_diff_tape_tot hαeq]; exact h
                  rw [tapePresample_lintegral_update_tapes_ne (Ne.symm hαeq)
                        (fun τ =>
                          ((execN m ∘ K.fillCfg) ⟨.lit (.int nn), τ⟩)
                            ((fun x => x.expr) ⁻¹' S))
                        ((erasure_integrand_measurable hS).comp
                          (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))),
                      ih_fill _ (σ.update_tapes (·.insert α_lbl ⟨z_r, ns⟩))
                        t htape_upd hN,
                      hstep_rw σ htapes, lintegral_dirac]
        | @randTapeEmpty z_r α_lbl _ N_b hz htapes hzN =>
          subst hzN
          by_cases hαeq : α = α_lbl
          · subst hαeq
            have ht_eq : t = ⟨z_r, []⟩ := by
              rw [h] at htapes; exact Option.some.inj htapes
            subst ht_eq
            have hrhs : headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ⟩ =
                Cfg.uniform z_r σ := by simp [headStep, htapes]
            have hker_rand : Measurable (fun σ' : State rT =>
                headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩ : Cfg rT)) :=
              headStep.measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
            rw [hrhs, tapePresample_lintegral h
                  (fun σ' => ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                    ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩)
                  ((Measure.measurable_lintegral (erasure_integrand_measurable hS)).comp
                    hker_rand)]
            have hstep_upd : ∀ n' : { z : Int // 0 ≤ z ∧ z < z_r },
                headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)),
                  σ.update_tapes (·.insert α ⟨z_r, [n']⟩)⟩ =
                Measure.dirac ⟨.lit (.int ↑n'),
                  σ.update_tapes (·.insert α ⟨z_r, []⟩)⟩ := by
              intro ⟨n', hn'⟩
              simp only [headStep, State.upd_tape_some, ↓reduceIte]
              rw [State.update_tapes_twice]
            simp only [List.nil_append]
            simp_rw [hstep_upd, lintegral_dirac]
            rw [State.update_tapes_insert_id htapes]
            exact tapeIndexUniform_lintegral_eq_cfg_uniform hz σ
              (fun ρ => ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S))
              (erasure_integrand_measurable hS)
          · have hstep_σ : headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ⟩ : Cfg rT)
                = Cfg.uniform z_r σ := by simp [headStep, htapes]
            refine uniform_close _ z_r hz ?_ hstep_σ
            filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            simp [headStep, htape_eq.trans htapes]
        | @randTapeOther z_r α_lbl _ N_b L hz htapes hzN =>
          have hrand_uniform : ∀ (σ₀ : State rT) {M : Int} {ns : List _},
              σ₀.tapes[α_lbl]? = some ⟨M, ns⟩ → M ≠ z_r →
              headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ₀⟩ : Cfg rT)
                = Cfg.uniform z_r σ₀ := by
            intro σ₀ M ns ht hne
            show (match σ₀.tapes[α_lbl]? with | none => _ | some ⟨M, _⟩ => _) = _
            rw [ht]; simp only; rw [ite_eq_right hne]
          refine uniform_close _ z_r hz ?_ (hrand_uniform σ htapes (Ne.symm hzN))
          obtain ⟨N, bs⟩ := t
          by_cases hαeq : α = α_lbl
          · subst hαeq
            have hNN : N_b = N :=
              congrArg Tape.bound (Option.some.inj (htapes.symm.trans h))
            filter_upwards [tapePresample_bound_ae h] with σ' hb
            rcases hq : σ'.tapes[α]? with _ | ⟨M, L⟩
            · simp [hq] at hb
            · simp only [hq, Option.map_some, Option.some.injEq] at hb
              exact hrand_uniform _ hq (by omega)
          · filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            exact hrand_uniform _ (htape_eq.trans htapes) (Ne.symm hzN)
        | randNonpos hz =>
          rename_i z_r
          refine det_close_state_pres _ (.lit (.int (-1))) fun σ' => ?_
          show Cfg.uniform z_r σ' = _
          exact Cfg.uniform_nonpos_eq hz
        | @randTapeNonposEmpty z_r α_lbl _ N_b hz htapes hzN =>
          have hαne : α ≠ α_lbl := by
            intro heq; subst heq
            have ht_eq : t = ⟨N_b, []⟩ := by
              rw [htapes] at h; exact (Option.some.inj h).symm
            apply hz; rw [hzN]
            have : t.bound = N_b := by rw [ht_eq]
            exact this ▸ hN
          subst hzN
          have hstep : ∀ {σ' : State rT}, σ'.tapes[α_lbl]? = some ⟨z_r, []⟩ →
              headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ'⟩ : Cfg rT) =
                Measure.dirac ⟨.lit (.int (-1)), σ'⟩ := by
            intro σ' hσ'
            simp only [headStep, hσ', ↓reduceIte]
            exact Cfg.uniform_nonpos_eq hz
          refine erasure_det_close_ae h hN ih_fill _ (.lit (.int (-1))) ?_ ?_
          · filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαne)] with σ' htape_eq
            exact hstep (htape_eq.trans htapes)
          · exact hstep htapes
        | @randTapeNonposOther z_r α_lbl _ N_b L hz htapes hzN =>
          have hstep : ∀ {σ' : State rT}, σ'.tapes[α_lbl]? = some ⟨N_b, L⟩ →
              headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ'⟩ : Cfg rT) =
                Measure.dirac ⟨.lit (.int (-1)), σ'⟩ := by
            intro σ' hσ'
            simp only [headStep, hσ']
            rw [ite_eq_right (Ne.symm hzN)]
            exact Cfg.uniform_nonpos_eq hz
          refine erasure_det_close_ae h hN ih_fill _ (.lit (.int (-1))) ?_ (hstep htapes)
          by_cases hαeq : α = α_lbl
          · subst hαeq
            have ht_eq : t = ⟨N_b, L⟩ := by
              rw [htapes] at h; exact (Option.some.inj h).symm
            subst ht_eq
            filter_upwards [tapePresample_bound_ae h] with σ' hb
            rcases hq : σ'.tapes[α]? with _ | ⟨M, L'⟩
            · simp [hq] at hb
            · simp only [hq, Option.map_some, Option.some.injEq] at hb
              simp only [headStep, hq]
              rw [ite_eq_right (show ¬ M = z_r by omega)]
              exact Cfg.uniform_nonpos_eq hz
          · filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            exact hstep (htape_eq.trans htapes)
        | urand =>
          exact uniformReal_close Exp.urand (MeasureTheory.ae_of_all _ fun _ => rfl) rfl
      · exact erasure_zero_close (e_red := e_red) h hN hzero

/-! ## Iterated and limit variants -/

/-- `n`-fold presampling on tape `α`; the `Nat.rec` in Clutch's `erasure.v` tape batching. -/
noncomputable def tapePresampleIter (α : Loc) (σ : State rT) : Nat → Measure (State rT)
  | 0 => Measure.dirac σ
  | n + 1 => (tapePresampleIter α σ n).bind (fun σ' => tapePresample σ' α)

theorem tapePresampleIter_tape_bound_ae [Countable rT] [MeasurableSingletonClass rT]
    {σ : State rT} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (n : Nat) :
    ∀ᵐ σ' ∂(tapePresampleIter α σ n),
      ∃ t' : Tape, σ'.tapes[α]? = some t' ∧ t'.bound = t.bound := by
  induction n with
  | zero =>
    show ∀ᵐ σ' ∂(Measure.dirac σ), _
    rw [MeasureTheory.ae_iff, Measure.dirac_apply' _ MeasurableSet.of_discrete,
        Set.indicator_of_notMem]
    simp only [Set.mem_ofPred_eq, not_not]
    exact ⟨t, h, rfl⟩
  | succ k ihk =>
    rw [tapePresampleIter, MeasureTheory.ae_iff,
        Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
    refine (lintegral_eq_zero_iff Measurable.of_discrete).mpr ?_
    filter_upwards [ihk] with σ'' ⟨t'', ht'', hbound⟩
    show tapePresample σ'' α _ = 0
    obtain ⟨Nb, bs⟩ := t''
    refine MeasureTheory.ae_iff.mp (tapePresample_ae ht'' MeasurableSet.of_discrete fun n' => ?_)
    exact ⟨⟨Nb, bs ++ [n']⟩, by simp [State.update_tapes], hbound⟩

theorem execN_tapePresampleIter_expr_eq [Countable rT] [MeasurableSingletonClass rT]
    {σ : State rT} {α : Loc} {e : Exp rT} {m : Nat} {t : Tape} (n : Nat)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresampleIter α σ n).bind (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩) := by
  unfold asExpr
  induction n generalizing σ with
  | zero =>
    show ((Measure.dirac σ).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) = _
    rw [Measure.dirac_bind (f := _) Measurable.of_discrete]
  | succ k ih =>
    show ((((tapePresampleIter α σ k).bind (fun σ' => tapePresample σ' α)).bind
            (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr)) = _
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable,
        Measure.bind_map_comm]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    calc ∫⁻ σ₁, ((tapePresample σ₁ α).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) S
            ∂(tapePresampleIter α σ k)
        = ∫⁻ σ₁, (execN m ⟨e, σ₁⟩).map (·.expr) S ∂(tapePresampleIter α σ k) := by
          refine lintegral_congr_ae ?_
          filter_upwards [tapePresampleIter_tape_bound_ae h k]
            with σ₁ ⟨t', ht', hbound⟩
          have h_eq := execN_tape_presample_expr_eq (e := e) (m := m) ht' (hbound ▸ hN)
          unfold asExpr at h_eq
          rw [h_eq]
      _ = ((tapePresampleIter α σ k).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) S := by
          rw [Measure.map_apply Measurable.of_discrete hS,
              Measure.bind_apply (Measurable.of_discrete hS)
                Measurable.of_discrete.aemeasurable]
          simp_rw [Measure.map_apply Measurable.of_discrete hS]
      _ = (execN m ⟨e, σ⟩).map (·.expr) S := by
          rw [ih h, Measure.map_apply Measurable.of_discrete hS]

theorem execN_iterM_tape_presample_expr_eq [Countable rT] [MeasurableSingletonClass rT]
    {σ : State rT} {α : Loc} {e : Exp rT} {m : Nat} {t : Tape} (n : Nat)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr (((Nat.rec (motive := fun _ => Measure (State rT))
                (Measure.dirac σ)
                (fun _ μ => μ.bind (fun σ' => tapePresample σ' α))) n).bind
       (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩) := by
  have hiter_eq : (Nat.rec (motive := fun _ => Measure (State rT))
                    (Measure.dirac σ)
                    (fun _ μ => μ.bind (fun σ' => tapePresample σ' α))) n
                = tapePresampleIter α σ n := by
    induction n with
    | zero => rfl
    | succ k ih => show _ = (tapePresampleIter α σ k).bind _; rw [← ih]
  rw [hiter_eq]
  exact execN_tapePresampleIter_expr_eq n h hN

/-! ## `ErasableExpr`: erasability up to the expression projection

Clutch's `erasable` compares val-projected `exec`. `Erasable` compares full configurations,
which `tapePresample σ α` fails; `ErasableExpr` is the projected analogue it satisfies. -/
def ErasableExpr (μ : Measure (State rT)) (σ : State rT) : Prop :=
  ∀ (e : Exp rT) (m : Nat),
    asExpr (μ.bind (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩)

namespace ErasableExpr

theorem of_erasable {μ : Measure (State rT)} {σ : State rT} (h : Erasable μ σ) :
    ErasableExpr μ σ := by
  intro e m
  rw [h e m]

theorem mass {μ : Measure (State rT)} {σ : State rT} (h : ErasableExpr μ σ) :
    μ Set.univ = 1 := by
  have hv : IsVal (Exp.lit (rT := rT) .unit) := .lit
  have hstep : ∀ σ' : State rT,
      execN 1 ((⟨.lit .unit, σ'⟩ : Cfg rT)) = Measure.dirac (⟨.lit .unit, σ'⟩ : Cfg rT) :=
    fun σ' => execN_succ_isValue (ρ := ⟨.lit .unit, σ'⟩) hv.toIsValue 0
  have hexpr : ∀ ν : Measure (Cfg rT), asExpr ν Set.univ = ν Set.univ := fun ν => by
    rw [asExpr, Measure.map_apply Cfg.measurable_expr MeasurableSet.univ, Set.preimage_univ]
  have h1 := h (.lit .unit) 1
  have hboth := congrArg (fun ν => ν (Set.univ : Set (Exp rT))) h1
  simp only [hexpr] at hboth
  rw [hstep σ] at hboth
  rw [Measure.dirac_apply' _ .univ] at hboth
  simp at hboth
  rw [bind_apply .univ (Measurable.aemeasurable (by measurability))] at hboth
  simp_rw [hstep] at hboth
  simp_rw [Measure.dirac_apply' _ .univ] at hboth
  simp at hboth
  exact hboth

theorem isProbabilityMeasure {μ : Measure (State rT)} {σ : State rT} (h : ErasableExpr μ σ) :
    IsProbabilityMeasure μ :=
  ⟨h.mass⟩

theorem dret (σ : State rT) : ErasableExpr (Measure.dirac σ) σ :=
  of_erasable (Erasable.dret σ)

theorem tapePresample
    {σ : State rT} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    ErasableExpr (tapePresample σ α) σ :=
  fun _ _ => execN_tape_presample_expr_eq h hN

theorem dbind [Countable rT] [MeasurableSingletonClass rT]
    {μ₁ : Measure (State rT)} {μ₂ : State rT → Measure (State rT)} {σ : State rT}
    (h₁ : ErasableExpr μ₁ σ) (h₂ : ∀ σ', ErasableExpr (μ₂ σ') σ') :
    ErasableExpr (μ₁.bind μ₂) σ := by
  intro e m
  unfold asExpr
  rw [Measure.bind_bind
        Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable,
      Measure.bind_map_comm]
  have hker : (fun σ' : State rT =>
      Measure.map (·.expr : Cfg rT → Exp rT)
        ((μ₂ σ').bind (fun σ'' => execN m ⟨e, σ''⟩)))
      = (fun σ' : State rT =>
          Measure.map (·.expr) (execN m ⟨e, σ'⟩)) := by
    funext σ'
    have := h₂ σ' e m
    unfold asExpr at this
    exact this
  rw [hker, ← Measure.bind_map_comm]
  have := h₁ e m
  unfold asExpr at this
  exact this

theorem lim_exec
    {μ : Measure (State rT)} {σ : State rT} (h : ErasableExpr μ σ)
    (e : Exp rT) :
    asExpr (μ.bind (fun σ' => limExec ⟨e, σ'⟩)) =
      limExecV ⟨e, σ⟩ := by
  have hexpr : Measurable (·.expr : Cfg rT → Exp rT) := Cfg.measurable_expr
  have hmk : Measurable (fun σ' : State rT => (⟨e, σ'⟩ : Cfg rT)) := by fun_prop
  unfold asExpr limExecV asExpr
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hexpr hS,
      Measure.map_apply hexpr hS,
      Measure.bind_apply (hexpr hS)
        (show Measurable (fun σ' : State rT => limExec (⟨e, σ'⟩ : Cfg rT)) from
          limExec.measurable.comp hmk).aemeasurable]
  have hind : ∀ ρ : Cfg rT,
      limExec ρ ((·.expr) ⁻¹' S)
        = ∫⁻ x, (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(limExec ρ) := by
    intro ρ
    rw [lintegral_indicator_one (hexpr hS)]
  simp_rw [hind, lintegral_limExec']
  rw [lintegral_iSup
        (fun n => by
          have hrw : (fun σ' => ∫⁻ x,
                  (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(execN n ⟨e, σ'⟩))
                = (fun σ' => (execN n ⟨e, σ'⟩) ((·.expr) ⁻¹' S)) := by
            funext σ'; exact lintegral_indicator_one (hexpr hS)
          rw [hrw]
          exact (Measure.measurable_coe (hexpr hS)).comp ((execN_measurable n).comp hmk))
        (fun i j hij σ' =>
          lintegral_mono' (execN_mono hij ⟨e, σ'⟩) (le_refl _))]
  refine iSup_congr fun n => ?_
  have hn := h e n
  unfold asExpr at hn
  have hval : (μ.bind (fun σ' => execN n ⟨e, σ'⟩)).map (·.expr) S
            = (execN n ⟨e, σ⟩).map (·.expr) S := by
    rw [hn]
  rw [Measure.map_apply hexpr hS,
      Measure.map_apply hexpr hS,
      Measure.bind_apply (hexpr hS)
        (show Measurable (fun σ' : State rT => execN n (⟨e, σ'⟩ : Cfg rT)) from
          (execN_measurable n).comp hmk).aemeasurable] at hval
  rw [show (∫⁻ x, (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(execN n ⟨e, σ⟩))
        = (execN n ⟨e, σ⟩) ((·.expr) ⁻¹' S)
      from lintegral_indicator_one (hexpr hS)]
  simp_rw [show ∀ σ' : State rT,
        (∫⁻ x, (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(execN n ⟨e, σ'⟩))
          = (execN n ⟨e, σ'⟩) ((·.expr) ⁻¹' S)
      from fun σ' => lintegral_indicator_one (hexpr hS)]
  exact hval

end ErasableExpr

/-- Clutch `limprim_coupl_step_limprim` / `lim_exec_eq_erasure`, projected to expressions. -/
theorem limExec_tape_presample_expr_eq
    {σ : State rT} {α : Loc} {t : Tape} {e : Exp rT}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresample σ α).bind (fun σ' => limExec ⟨e, σ'⟩)) =
      limExecV ⟨e, σ⟩ :=
  (ErasableExpr.tapePresample h hN).lim_exec e

/-! ## Lifting wrappers

Micrometer-facing: transfer a lifting of `ErasableExpr` state distributions to the expression
projections of `execN`/`limExec`, as Clutch's val-projected `ARcoupl`. -/

section Lifting

open GradedLifting

variable {B : Type*} {L : GradedLifting.{0} B}

/-- A bijection of `[0, N)` leaves `tapeIndexUniform N` invariant. -/
theorem tapeIndexUniform_map_bijOn {N : Int} (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    (tapeIndexUniform N).map (fun x => tapeIdxOf hN (f x.val)) = tapeIndexUniform N := by
  refine Measure.ext_of_lintegral _ fun ψ _ => ?_
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete, lintegral_tapeIndexUniform hN,
    lintegral_tapeIndexUniform hN,
    ← Finset.sum_Ico_comp_of_bijOn hdom hbij (fun m => ψ (tapeIdxOf hN m))]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [tapeIdxOf_val hN (Finset.mem_Ico.1 hn).1 (Finset.mem_Ico.1 hn).2]

/-- Uniform presample coupling on the index type, along a bijection of `[0, N)`. -/
theorem tapeIndexUniform_codensity_bij [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [L.IsReflexive] {N : Int} (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    L.Rel 0 (fun p q ↦ ∃ n : Int, 0 ≤ n ∧ n < N ∧ p = tapeIdxOf hN n ∧ q = tapeIdxOf hN (f n))
      (tapeIndexUniform N) (tapeIndexUniform N) := by
  have h := rel_graph (L := L) (tapeIndexUniform N) (f := fun x => tapeIdxOf hN (f x.val))
    Measurable.of_discrete
  rw [tapeIndexUniform_map_bijOn hN f hdom hbij] at h
  exact h.mono le_rfl fun p q hp =>
    ⟨p.val, p.2.1, p.2.2, Subtype.ext (tapeIdxOf_val hN p.2.1 p.2.2).symm, hp.symm⟩

/-- Uniform presample coupling on the index type, along a bijection of `[0, N)`
(the `tv` instance of `tapeIndexUniform_codensity_bij`). -/
theorem tapeIndexUniform_addCoupl_bij {N : Int} (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    AddCoupl 0
      {p : { z : Int // 0 ≤ z ∧ z < N } × { z : Int // 0 ≤ z ∧ z < N } |
        ∃ n : Int, 0 ≤ n ∧ n < N ∧ p.1 = tapeIdxOf hN n ∧ p.2 = tapeIdxOf hN (f n)}
      (tapeIndexUniform N) (tapeIndexUniform N) :=
  (tapeIndexUniform_codensity_bij hN f hdom hbij).addCoupl

theorem tapePresample_eq_map {σ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} (hσ : σ.tapes[α]? = some ⟨N, bs⟩) :
    tapePresample σ α =
      (tapeIndexUniform N).map (fun n => σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) := by
  simp only [tapePresample, hσ]
  rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]

/-- Two same-bound tapes presample in lockstep along a bijection `f` on `[0, N)`. -/
theorem tapePresample_codensity_bij [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [L.IsReflexive] {σ σ' : State rT} {α α' : Loc} {N : Int}
    {bs bs' : List { z : Int // 0 ≤ z ∧ z < N }}
    (hσ : σ.tapes[α]? = some ⟨N, bs⟩) (hσ' : σ'.tapes[α']? = some ⟨N, bs'⟩)
    (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    L.Rel 0
      (fun τ τ' ↦ ∃ n : Int, 0 ≤ n ∧ n < N ∧
        τ = σ.update_tapes (·.insert α ⟨N, bs ++ [tapeIdxOf hN n]⟩) ∧
        τ' = σ'.update_tapes (·.insert α' ⟨N, bs' ++ [tapeIdxOf hN (f n)]⟩))
      (tapePresample σ α) (tapePresample σ' α') := by
  rw [tapePresample_eq_map hσ, tapePresample_eq_map hσ']
  refine (tapeIndexUniform_codensity_bij hN f hdom hbij).map ?_ Measurable.of_discrete
    Measurable.of_discrete
  rintro _ _ ⟨n, h0, hn, rfl, rfl⟩
  exact ⟨n, h0, hn, rfl, rfl⟩

/-- Two same-bound tapes presample in lockstep along a bijection `f` on `[0, N)`
(the `tv` instance of `tapePresample_codensity_bij`). -/
theorem tapePresample_addCoupl_bij {σ σ' : State rT} {α α' : Loc} {N : Int}
    {bs bs' : List { z : Int // 0 ≤ z ∧ z < N }}
    (hσ : σ.tapes[α]? = some ⟨N, bs⟩) (hσ' : σ'.tapes[α']? = some ⟨N, bs'⟩)
    (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    AddCoupl 0
      {p : State rT × State rT | ∃ n : Int, 0 ≤ n ∧ n < N ∧
        p.1 = σ.update_tapes (·.insert α ⟨N, bs ++ [tapeIdxOf hN n]⟩) ∧
        p.2 = σ'.update_tapes (·.insert α' ⟨N, bs' ++ [tapeIdxOf hN (f n)]⟩)}
      (tapePresample σ α) (tapePresample σ' α') :=
  (tapePresample_codensity_bij hσ hσ' hN f hdom hbij).addCoupl

/-- Running to the limit from a measure of states first runs `m` steps. -/
theorem bind_limExec_eq_pexecN (μ : Measure (State rT)) (e : Exp rT) (m : Nat) :
    μ.bind (fun σ => limExec ⟨e, σ⟩) = (μ.bind fun σ => pexecN m ⟨e, σ⟩).bind limExec := by
  have hpk : Measurable fun σ : State rT => pexecN m (⟨e, σ⟩ : Cfg rT) :=
    pexecN_measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  rw [Measure.bind_bind hpk.aemeasurable limExec.measurable.aemeasurable]
  exact congrArg _ (funext fun σ => limExec_pexecN m ⟨e, σ⟩)

/-- Clutch `ARcoupl_erasure_erasable_exp_rhs`, projected: the continuation's budget depends
on the RHS sample. -/
theorem lift_erasure_erasable_exp_rhs [AddCommMonoid B] [PartialOrder B] [IsOrderedAddMonoid B]
    [CanonicallyOrderedAdd B] [OrderTop B] {s : ENNReal →+o B} [L.IsLawful] [L.HasBind]
    [L.IsExpectationAdditive s] [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁ μ₁' : Measure (State rT)} {R : State rT → Cfg rT → Prop}
    {Φexp : Exp rT → Exp rT → Prop}
    {b b₁ : B} {ε₂ : ENNReal} {E₂ : Cfg rT → ENNReal} {n m : Nat}
    (hE₂meas : Measurable E₂)
    (hCoupl : L.Rel b₁ R μ₁ (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)) ≤ ε₂)
    (hEpsSum : b₁ + s ε₂ ≤ b)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R σ₂ ρ' →
        L.Rel (s (E₂ ρ')) Φexp (asExpr (execN n ⟨e₁, σ₂⟩)) (limExecV ρ')) :
    L.Rel b Φexp (asExpr (execN n ⟨e₁, σ₁⟩)) (limExecV ⟨e₁', σ₁'⟩) := by
  have hek : Measurable (fun σ : State rT => execN n (⟨e₁, σ⟩ : Cfg rT)) :=
    (execN_measurable n).comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  have := hErase₁.isProbabilityMeasure
  have := hErase₁'.isProbabilityMeasure
  refine IsLawful.mono ?_ ((add_le_add le_rfl (OrderHomClass.mono s hBoundSum)).trans hEpsSum)
    le_rfl
  rw [← hErase₁ e₁ n, ← hErase₁'.lim_exec e₁', bind_limExec_eq_pexecN _ _ m]
  unfold asExpr
  rw [Measure.bind_map_comm' _ _ _ hek.aemeasurable Cfg.measurable_expr,
      Measure.bind_map_comm' _ _ _ limExec.measurable.aemeasurable Cfg.measurable_expr]
  exact IsExpectationAdditive.bind_adv hCoupl hCont
    ((Measure.measurable_map _ Cfg.measurable_expr).comp hek)
    ((Measure.measurable_map _ Cfg.measurable_expr).comp limExec.measurable) hE₂meas

/-- Clutch `ARcoupl_erasure_erasable_exp_rhs`, projected: the continuation's slack depends
on the RHS sample (the `tv` instance of `lift_erasure_erasable_exp_rhs`). -/
theorem AddCoupl_erasure_erasable_exp_rhs [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁ μ₁' : Measure (State rT)} {R : Set ((State rT) × (Cfg rT))}
    {Φexp : Set ((Exp rT) × (Exp rT))}
    {ε ε₁ ε₂ : ENNReal} {E₂ : Cfg rT → ENNReal} {n m : Nat}
    (hE₂meas : Measurable E₂)
    (hCoupl : AddCoupl ε₁ R μ₁
        (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)) ≤ ε₂)
    (hEpsSum : ε₁ + ε₂ ≤ ε)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R (σ₂, ρ') →
        AddCoupl (E₂ ρ') Φexp
          (asExpr (execN n ⟨e₁, σ₂⟩))
          (limExecV ρ')) :
    AddCoupl ε Φexp
      (asExpr (execN n ⟨e₁, σ₁⟩))
      (limExecV ⟨e₁', σ₁'⟩) := by
  have := hErase₁.isProbabilityMeasure
  exact (lift_erasure_erasable_exp_rhs (L := GradedDivergence.tv.codensity)
    (s := OrderAddMonoidHom.id _) hE₂meas hCoupl.codensity hBoundSum hEpsSum hErase₁ hErase₁'
    fun σ₂ ρ' hR => (hCont σ₂ ρ' hR).codensity).addCoupl

/-- Clutch `ARcoupl_erasure_erasable`, projected to expressions. -/
theorem AddCoupl_erasure_erasable [Countable rT] [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁ μ₂ : Measure (State rT)} {R : Set ((State rT) × (State rT))}
    {Φexp : Set ((Exp rT) × (Exp rT))}
    {ε ε₁ ε₂ : ENNReal} {n : Nat}
    (hSum : ε₁ + ε₂ ≤ ε)
    (hCoupl : AddCoupl ε₁ R μ₁ μ₂)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₂ : ErasableExpr μ₂ σ₁')
    (hCont : ∀ σ₂ σ₂', R (σ₂, σ₂') →
        AddCoupl ε₂ Φexp
          (asExpr (execN n ⟨e₁, σ₂⟩))
          (limExecV ⟨e₁', σ₂'⟩)) :
    AddCoupl ε Φexp
      (asExpr (execN n ⟨e₁, σ₁⟩))
      (limExecV ⟨e₁', σ₁'⟩) := by
  have := hErase₂.isProbabilityMeasure
  have hd := Measure.bind_dirac_eq_map μ₂ (f := (⟨e₁', ·⟩ : State rT → Cfg rT)) .of_discrete
  refine AddCoupl_erasure_erasable_exp_rhs (m := 0) (E₂ := fun _ => ε₂)
    (R := {p | ∃ σ', p.2 = ⟨e₁', σ'⟩ ∧ R (p.1, σ')}) measurable_const ?_ (by simp [hd]) hSum
    hErase₁ hErase₂ fun σ₂ ρ ⟨σ₂', (h : ρ = _), hR⟩ => h ▸ hCont σ₂ σ₂' hR
  simpa [hd] using hCoupl.map id _ measurable_id .of_discrete fun h => ⟨_, rfl, h⟩

/-- Clutch `ARcoupl_erasure_erasable_exp_lhs`, projected: the continuation's slack depends
on the LHS sample. -/
theorem AddCoupl_erasure_erasable_exp_lhs [Countable rT] [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁' : Measure (State rT)} {R : Set ((Cfg rT) × (State rT))}
    {Φexp : Set ((Exp rT) × (Exp rT))}
    {ε ε₁ ε₂ : ENNReal} {E₂ : Cfg rT → ENNReal} {n : Nat}
    (hE₂meas : Measurable E₂)
    (hCoupl : AddCoupl ε₁ R (primStep ⟨e₁, σ₁⟩) μ₁')
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(primStep ⟨e₁, σ₁⟩) ≤ ε₂)
    (hEpsSum : ε₁ + ε₂ ≤ ε)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ ρ σ₂', R (ρ, σ₂') →
        AddCoupl (E₂ ρ) Φexp
          (asExpr (execN n ρ))
          (limExecV ⟨e₁', σ₂'⟩)) :
    AddCoupl ε Φexp
      (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n)))
      (limExecV ⟨e₁', σ₁'⟩) := by
  have hmassk : ∀ ρ : Cfg rT, asExpr (execN n ρ) Set.univ ≤ 1 :=
    fun _ => IsSubProbabilityMeasure.measure_univ_le_one
  rw [← hErase₁'.lim_exec e₁']
  unfold asExpr
  rw [Measure.bind_map_comm, Measure.bind_map_comm]
  exact (AddCoupl.bind_adv_lhs Measurable.of_discrete Measurable.of_discrete hE₂meas hmassk
    hBoundSum hCoupl fun {ρ σ₂'} hR => hCont ρ σ₂' hR).mono_grading hEpsSum

/-- Clutch `ARcoupl_erasure_erasable_exp_lhs_kanto`, projected: the leftover depends on both
samples. -/
theorem lift_erasure_erasable_exp_lhs_kanto [LT B] [Top B] [Zero B] [L.HasBind]
    [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁' : Measure (State rT)} {Φexp : Exp rT → Exp rT → Prop}
    {b : B} {R : Cfg rT → Cfg rT → B} {n m : Nat}
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hExp : L b R (primStep ⟨e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩)))
    (hCont : ∀ ρ ρ', R ρ ρ' < ⊤ →
        L.Rel (R ρ ρ') Φexp (asExpr (execN n ρ)) (limExecV ρ')) :
    L.Rel b Φexp
      (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n)))
      (limExecV ⟨e₁', σ₁'⟩) := by
  rw [← hErase₁'.lim_exec e₁', bind_limExec_eq_pexecN _ _ m]
  unfold asExpr
  rw [Measure.bind_map_comm' _ _ _ (execN_measurable n).aemeasurable Cfg.measurable_expr,
      Measure.bind_map_comm' _ _ _ limExec.measurable.aemeasurable Cfg.measurable_expr]
  exact HasBind.bind_fun hExp hCont
    ((Measure.measurable_map _ Cfg.measurable_expr).comp (execN_measurable n))
    ((Measure.measurable_map _ Cfg.measurable_expr).comp limExec.measurable)

/-- Clutch-dp `spec_coupl` erasure, projected: erasable distributions on both sides, coupled by a
lifting whose per-pair leftover is the continuation's budget. -/
theorem lift_erasure_erasable [LT B] [Top B] [Zero B] [L.HasBind] [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT} {μ₁ μ₁' : Measure (State rT)}
    {Φexp : Exp rT → Exp rT → Prop} {b : B} {R : State rT → Cfg rT → B} {n m : Nat}
    (hCoupl : L b R μ₁ (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hErase₁ : ErasableExpr μ₁ σ₁) (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R σ₂ ρ' < ⊤ →
      L.Rel (R σ₂ ρ') Φexp (asExpr (execN n ⟨e₁, σ₂⟩)) (limExecV ρ')) :
    L.Rel b Φexp (asExpr (execN n ⟨e₁, σ₁⟩)) (limExecV ⟨e₁', σ₁'⟩) := by
  have hek : Measurable (fun σ : State rT => execN n (⟨e₁, σ⟩ : Cfg rT)) :=
    (execN_measurable n).comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  rw [← hErase₁ e₁ n, ← hErase₁'.lim_exec e₁', bind_limExec_eq_pexecN _ _ m]
  unfold asExpr
  rw [Measure.bind_map_comm' _ _ _ hek.aemeasurable Cfg.measurable_expr,
      Measure.bind_map_comm' _ _ _ limExec.measurable.aemeasurable Cfg.measurable_expr]
  exact HasBind.bind_fun hCoupl hCont
    ((Measure.measurable_map _ Cfg.measurable_expr).comp hek)
    ((Measure.measurable_map _ Cfg.measurable_expr).comp limExec.measurable)

/-- Clutch `ARcoupl_erasure_erasable_exp_lhs_kanto`, projected: the slack depends on both
samples (the `tv` instance of `lift_erasure_erasable_exp_lhs_kanto`). -/
theorem AddCoupl_erasure_erasable_exp_lhs_kanto [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁' : Measure (State rT)} {Φexp : Set ((Exp rT) × (Exp rT))}
    {ε : ENNReal} {E₂ : Cfg rT → Cfg rT → ENNReal}
    {n m : Nat}
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hExp : ExpCoupl ε E₂ (primStep ⟨e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩)))
    (hCont : ∀ ρ ρ',
        AddCoupl (E₂ ρ ρ') Φexp
          (asExpr (execN n ρ))
          (limExecV ρ')) :
    AddCoupl ε Φexp
      (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n)))
      (limExecV ⟨e₁', σ₁'⟩) :=
  (lift_erasure_erasable_exp_lhs_kanto hErase₁'
    (expCoupl_iff_codensity_tv.1 hExp) fun ρ ρ' _ => (hCont ρ ρ').codensity).addCoupl

end Lifting

end ProbLang
