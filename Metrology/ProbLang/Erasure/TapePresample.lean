module

public import Metrology.ProbLang.Erasure.Presample

@[expose] public section

/-! # Properties of `tapePresample`

Presampling commutes with heap updates, other-tape updates and uniform draws;
`tapeIndexUniform_lintegral_eq_cfg_uniform` converts a presampled index into `Cfg.uniform`. -/

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure ProbLang.Measure

/-! ## Almost-sure facts about a presampled state -/

/-- An event holds a.s. after presampling if it holds after appending each possible value. -/
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

/-- Presampling leaves the heap unchanged a.s. -/
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

/-- Presampling `α` leaves every other tape `α_lbl` unchanged a.s. -/
theorem tapePresample_tape_ne_ae
    {σ : State rT} {α α_lbl : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hne : α_lbl ≠ α) :
    ∀ᵐ σ' ∂(tapePresample σ α), σ'.tapes[α_lbl]? = σ.tapes[α_lbl]? := by
  obtain ⟨N, bs⟩ := t
  exact tapePresample_ae h (by measurability) fun _ => State.upd_diff_tape_tot hne

/-- Presampling never changes the bound of the tape `α`. -/
theorem tapePresample_bound_ae {σ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} (h : σ.tapes[α]? = some ⟨N, bs⟩) :
    ∀ᵐ σ' ∂tapePresample σ α, (σ'.tapes[α]?).map Tape.bound = some N := by
  have hmb : Measurable (fun σ' : State rT => (σ'.tapes[α]?).map Tape.bound) :=
    (Measurable.of_discrete (f := fun o : Option Tape => o.map Tape.bound)).comp
      ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
  exact tapePresample_ae h (hmb (measurableSet_singleton _)) fun _ => by simp [State.update_tapes]

/-! ## Commutation with state updates -/

/-- Under a presample, a continuation may read the original heap instead of the presampled one. -/
theorem tapePresample_bind_pull_heap [Countable rT]
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

/-- Presampling commutes with any heap update. -/
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
    rw [Measure.bind_map_comm _ _ _ hmap hker]
    congr 1
    funext n'
    rw [Measure.map_dirac (f := (·.update_heap f)) (σ.update_tapes (·.insert α ⟨N, bs ++ [n']⟩))]
    simp [State.update_tapes, State.update_heap]

/-- Presampling `α` commutes with writing a different tape `β`. -/
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
    rw [Measure.bind_map_comm _ _ _ hmap hker]
    congr 1
    funext n'
    rw [show Measure.dirac ((σ.update_tapes (·.insert β v)).update_tapes
            (·.insert α ⟨N, bs ++ [n']⟩)) =
        (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n']⟩))).map
            (·.update_tapes (·.insert β v)) from by
      rw [Measure.map_dirac]; congr 1; exact State.upd_diff_tape_comm (Ne.symm hne)]

/-! ## Integrals against a presample -/

/-- Integrating against a presample is integrating over the appended index. -/
theorem tapePresample_lintegral
    {σ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }}
    (h : σ.tapes[α]? = some ⟨N, bs⟩) (f : State rT → ENNReal)
    (hf : Measurable f) :
    ∫⁻ σ', f σ' ∂tapePresample σ α =
      ∫⁻ n, f (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) ∂tapeIndexUniform N := by
  simp only [tapePresample, h]
  have hker : AEMeasurable (fun n : {z : Int // 0 ≤ z ∧ z < N} =>
      (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) : Measure (State rT)))
      (tapeIndexUniform N) :=
    (measurable_dirac.comp Measurable.of_discrete).aemeasurable
  rw [lintegral_bind hker hf.aemeasurable]
  simp_rw [lintegral_dirac]

/-- Updating the heap after presampling is presampling after updating the heap, as integrals. -/
theorem tapePresample_lintegral_update_heap
    {σ : State rT} {α : Loc}
    (g : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare)
    (hg : Measurable g)
    (f : State rT → ENNReal) (hf : Measurable f) :
    ∫⁻ σ', f (σ'.update_heap g) ∂tapePresample σ α =
      ∫⁻ τ, f τ ∂tapePresample (σ.update_heap g) α := by
  have hmap : Measurable (fun σ' : State rT => σ'.update_heap g) :=
    State.measurable_iff.mpr ⟨hg.comp State.measurable_heap, State.measurable_tapes⟩
  rw [tapePresample_update_heap_comm g hg,
      lintegral_map hf hmap]

/-- Writing a different tape `β` after presampling `α` is presampling after writing `β`, as
integrals. -/
theorem tapePresample_lintegral_update_tapes_ne
    {σ : State rT} {α β : Loc} {v : Tape} (hne : β ≠ α)
    (f : State rT → ENNReal) (hf : Measurable f) :
    ∫⁻ σ', f (σ'.update_tapes (·.insert β v)) ∂tapePresample σ α =
      ∫⁻ τ, f τ ∂tapePresample (σ.update_tapes (·.insert β v)) α := by
  have hins : Measurable (fun m : LocHeap Tape => m.insert β v) :=
    (Measurable.locHeap_insert β).comp (measurable_id.prodMk measurable_const)
  have hmap : Measurable (fun σ' : State rT => σ'.update_tapes (·.insert β v)) :=
    State.measurable_iff.mpr ⟨State.measurable_heap, hins.comp State.measurable_tapes⟩
  rw [tapePresample_update_tapes_ne_comm hne,
      lintegral_map hf hmap]

/-! ## Commutation with a uniform draw -/

/-- For `0 < z`, `Cfg.uniform z σ` draws a uniform integer in `[0, z)` and returns it as a
literal. -/
theorem Cfg.uniform_eq_bind {z : Int} {σ : State rT} (hz : 0 < z) :
    Cfg.uniform z σ =
      ((PMF.uniformOfFinset (Finset.Ico 0 z) (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
        (fun n => Measure.dirac (⟨.lit (.int n), σ⟩ : Cfg rT)) := by
  unfold Cfg.uniform Int.isPos
  rw [dite_eq_left hz, Measure.bind_dirac_eq_map _ Measurable.of_discrete]

/-- Presampling and a uniform draw `Cfg.uniform z` commute, since the draw ignores tapes. -/
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
        ((PMF.uniformOfFinset (Finset.Ico 0 z) (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
            (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT))) := by
      have hre : (fun σ' : State rT =>
          ((PMF.uniformOfFinset (Finset.Ico 0 z) (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
              (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT))) =
          (fun σ' : State rT => Cfg.uniform z σ') := by
        funext σ'; exact (Cfg.uniform_eq_bind (σ := σ') hz).symm
      rw [hre]
      exact Cfg.uniform.measurable.comp (measurable_const.prodMk measurable_id)
    have hLHS : (tapePresample σ α).bind (fun σ' => Cfg.uniform z σ') =
        (tapePresample σ α).bind (fun σ' =>
          ((PMF.uniformOfFinset (Finset.Ico 0 z) (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
              (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT))) := by
      congr 1; funext σ'; exact Cfg.uniform_eq_bind (σ := σ') hz
    rw [hLHS, huniform_σ, Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          hk2.aemeasurable]
    simp_rw [Measure.dirac_bind
              (f := fun ρ' : Cfg rT => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg rT)))
              hk2]
    -- Evaluate on a measurable `S`; both sides are a double integral, equal by Fubini.
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS hk_pmf.aemeasurable,
        Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    have hLlint : ∀ σ' : State rT,
        ((((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
                (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT))) S) =
        ∫⁻ n, (Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg rT)) S
          ∂((PMF.uniformOfFinset (Finset.Ico 0 z) (Finset.nonempty_Ico.mpr hz)).toMeasure) := by
      intro σ'
      exact Measure.bind_apply hS Measurable.of_discrete.aemeasurable
    have hRlint : ∀ n : Int,
        ((tapePresample σ α).bind (fun σ'' => Measure.dirac (⟨.lit (.int n), σ''⟩ : Cfg rT))) S =
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
      (ν := ((PMF.uniformOfFinset (Finset.Ico 0 z) (Finset.nonempty_Ico.mpr hz)).toMeasure))
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

/-! ## Change of variables: `tapeIndexUniform` vs `Cfg.uniform` -/

/-- Integrating over a presampled index equals integrating over `Cfg.uniform N σ`; this closes the
key erasure case. -/
theorem tapeIndexUniform_lintegral_eq_cfg_uniform
    {N : Int} (hN : 0 < N) (σ : State rT)
    (f : Cfg rT → ENNReal) (hf : Measurable f) :
    ∫⁻ (a : { z : Int // 0 ≤ z ∧ z < N }),
      f ⟨.lit (.int ↑a), σ⟩ ∂tapeIndexUniform N =
      ∫⁻ (ρ : Cfg rT), f ρ ∂Cfg.uniform N σ := by
  rw [tapeIndexUniform_eq_map hN]
  unfold Cfg.uniform Int.isPos
  have hNonempty : (Finset.Ico 0 N).Nonempty := Finset.nonempty_Ico.mpr hN
  rw [dite_eq_left hN]
  have hm_sub : Measurable (tapeIdxOf hN) := Measurable.of_discrete
  have hm_cfg : Measurable (fun x : Int => (⟨Exp.lit (BaseLit.int x), σ⟩ : Cfg rT)) :=
    Measurable.of_discrete
  have hm_f_sub : Measurable (fun (a : {z // 0 ≤ z ∧ z < N}) => f ⟨.lit (.int ↑a), σ⟩) :=
    Measurable.of_discrete
  rw [lintegral_map hm_f_sub hm_sub, lintegral_map hf hm_cfg]
  apply lintegral_congr_ae
  rw [Filter.eventuallyEq_iff_exists_mem]
  use (PMF.uniformOfFinset (Finset.Ico 0 N) hNonempty).support
  constructor
  · rw [mem_ae_iff, (PMF.uniformOfFinset (Finset.Ico 0 N) hNonempty).toMeasure_apply_eq_zero_iff
      MeasurableSet.of_discrete]
    exact disjoint_compl_right
  · intro a ha
    have hmem : a ∈ Finset.Ico 0 N := by
      rwa [PMF.mem_support_uniformOfFinset_iff] at ha
    have hab : 0 ≤ a ∧ a < N := Finset.mem_Ico.mp hmem
    simp [tapeIdxOf_val hN hab.1 hab.2]

end ProbLang
