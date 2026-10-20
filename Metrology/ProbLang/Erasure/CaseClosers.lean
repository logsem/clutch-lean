module

public import Metrology.ProbLang.Erasure.TapePresample

@[expose] public section

/-! # Head-step cases of erasure

Each lemma closes one head-step case of `execN_tape_presample_expr_eq`: presampling, then taking
the head step of `e_h` and running `m` more steps under `K`, equals taking the step without
presampling, measured on `S`. `ErasureIHFill` is the induction hypothesis in that form. -/

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure ProbLang.Measure

/-! ## Closers by step shape (Dirac, uniform int, uniform real) -/

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

/-- A deterministic head step that keeps the state commutes with presampling. -/
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

/-- Like `erasure_det_close`, with the head step deterministic only almost surely. -/
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

/-- A head step that samples `Cfg.uniform z_r` commutes with presampling. -/
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
        simp_rw [Cfg.uniform_eq_map_uniformOfFinset hz,
          lintegral_map (erasure_integrand_measurable hS) Measurable.of_discrete]
        rw [lintegral_lintegral_swap (f := fun σ' n =>
              ((execN m ∘ K.fillCfg) ⟨.lit (.int n), σ'⟩) ((fun x => x.expr) ⁻¹' S))
            ((erasure_integrand_measurable hS).comp hcfgbuild).aemeasurable]
        congr 1; funext n; exact ih_fill _ σ t h hN
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by rw [hstep_σ]

/-- A head step that samples `Cfg.uniformReal` commutes with presampling. -/
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

/-! ## Closers for heap and tape redexes (load, alloc, store, tape, stuck) -/

/-- A heap `load` commutes with presampling. -/
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

/-- A heap `alloc` commutes with presampling. Presampling keeps the heap, so the fresh location
is the same a.s.; the heap write commutes with presampling, and the IH applies at the written
state. -/
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

/-- A heap `store` commutes with presampling. Presampling keeps the heap, so the checked location
is the same a.s.; the heap write commutes with presampling, and the IH applies at the written
state. -/
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

/-- Allocating a fresh tape commutes with presampling another tape. Presampling an existing tape
keeps `tapes.fresh` (`fresh_loc_upd_some`), and the new tape is `≠ α`. -/
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

/-- A stuck head step (the zero measure) commutes with presampling. -/
theorem erasure_zero_close
    {m : Nat} {K : Ectx rT} {S : Set (Exp rT)} {σ : State rT} {α : Loc} {t : Tape} {e_red : Exp rT}
    (h : σ.tapes[α]? = some t)
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

end ProbLang
