module

public import Metrology.ProbLang.Erasure.TapePresample

@[expose] public section

/-! # One-step tape-presampling identities

The key identities move presampling through a read of the selected tape.
-/

noncomputable section

namespace ProbLang

open MeasureTheory MeasureTheory.Measure

/-- Two finite measure maps through a jointly measurable function commute. -/
theorem bind_map_swap {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X → Y → Z) (hf : Measurable fun p : X × Y => f p.1 p.2) :
    μ.bind (fun x => ν.map (f x)) =
      ν.bind (fun y => μ.map fun x => f x y) := by
  have hleft (x : X) : Measurable (f x) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hright (y : Y) : Measurable (fun x => f x y) :=
    hf.comp (measurable_id.prodMk measurable_const)
  have hKLeft : Measurable (fun x => ν.map (f x)) :=
    measurable_map_const_uncurry ν hf
  have hKRight : Measurable (fun y => μ.map fun x => f x y) :=
    measurable_map_const_uncurry μ (hf.comp (measurable_snd.prodMk measurable_fst))
  refine ext fun S hS => ?_
  rw [bind_apply hS hKLeft.aemeasurable, bind_apply hS hKRight.aemeasurable]
  simp_rw [← bind_dirac_eq_map ν (hleft _), ← bind_dirac_eq_map μ (hright _)]
  have hbindLeft (x : X) :
      (ν.bind fun y => dirac (f x y)) S = ∫⁻ y, (dirac (f x y)) S ∂ν :=
    bind_apply hS (measurable_dirac.comp (hleft x)).aemeasurable
  have hbindRight (y : Y) :
      (μ.bind fun x => dirac (f x y)) S = ∫⁻ x, (dirac (f x y)) S ∂μ :=
    bind_apply hS (measurable_dirac.comp (hright y)).aemeasurable
  simp_rw [hbindLeft, hbindRight]
  exact lintegral_lintegral_swap (f := fun x y => (dirac (f x y)) S)
    (((measurable_coe hS).comp measurable_dirac).comp hf).aemeasurable

variable {rT : Type} {σ : State rT} {α : Loc}

/-- Replaces one tape in a configuration without changing its expression. -/
def Cfg.updateTape (α : Loc) (t : Tape rT) (ρ : Cfg rT) : Cfg rT :=
  ⟨ρ.expr, ρ.state.updateTapes (·.insert α t)⟩

/-- Replacing a fixed tape in a configuration is measurable. -/
@[fun_prop]
theorem Cfg.updateTape.measurable [MeasurableSpace rT] (α : Loc) (t : Tape rT) :
    Measurable (Cfg.updateTape α t) :=
  Cfg.measurable_mapState (State.measurable_updateTapes_insert α t)

/-- A fresh draw commutes with replacing a fixed tape. -/
theorem Cfg.sample_map_updateTape [MeasurableSpace rT] [ProbLangDist rT]
    {n : ℕ} {v : Val rT} (t : Tape rT) :
    (Cfg.sample n v σ).map (Cfg.updateTape α t) =
      Cfg.sample n v (σ.updateTapes (·.insert α t)) :=
  Cfg.sample_map_state (State.measurable_updateTapes_insert α t)

/-- Replacing a tape commutes with changing the heap. -/
theorem State.updateTape_updateHeap (t : Tape rT)
    (f : LocHeap (Val rT) → LocHeap (Val rT)) :
    (σ.updateHeap f).updateTapes (·.insert α t) =
      (σ.updateTapes (·.insert α t)).updateHeap f :=
  rfl

/-- Replacing a tape commutes with changing the random-variable map. -/
theorem State.updateTape_updateRvs (t : Tape rT)
    (f : LocHeap (RvCell rT) → LocHeap (RvCell rT)) :
    (σ.updateRvs f).updateTapes (·.insert α t) =
      (σ.updateTapes (·.insert α t)).updateRvs f :=
  rfl

/-- Lifts one-position tape presampling from a configuration's state. -/
noncomputable def Cfg.tapePresampleAt [MeasurableSpace rT] [ProbLangDist rT]
    (α : Loc) (k : ℕ) (ρ : Cfg rT) : Measure (Cfg rT) :=
  (ProbLang.tapePresampleAt ρ.state α k).map fun σ => ⟨ρ.expr, σ⟩

/-- Lifted one-position tape presampling is measurable in the configuration. -/
theorem Cfg.tapePresampleAt.measurable [MeasurableSpace rT] [ProbLangDist rT]
    (α : Loc) (k : ℕ) : Measurable (Cfg.tapePresampleAt (rT := rT) α k) := by
  have hk : Measurable (fun ρ : Cfg rT => ProbLang.tapePresampleAt ρ.state α k) :=
    (ProbLang.tapePresampleAt.measurable α k).comp Cfg.measurable_state
  have : ProbabilityTheory.IsFiniteKernel (ProbabilityTheory.Kernel.mk _ hk) :=
    ⟨1, ENNReal.one_lt_top, fun ρ =>
      tapePresampleAt_univ_le_one (σ := ρ.state) (α := α) (k := k)⟩
  exact measurable_map_uncurry
    (Cfg.measurable_mk.comp ((Cfg.measurable_expr.comp measurable_fst).prodMk measurable_snd)) hk

/-- Fills every hole of a fixed tape in a configuration. -/
noncomputable def Cfg.tapePresampleAllOf [MeasurableSpace rT] [ProbLangDist rT]
    (α : Loc) (t : Tape rT) (ρ : Cfg rT) : Measure (Cfg rT) :=
  (infinitePi fun _ : ℕ => t.dist).map fun ω =>
    ⟨ρ.expr, ρ.state.updateTapes (·.insert α (t.fillAll ω))⟩

/-- Whole-stream filling of a fixed tape is measurable in the configuration. -/
theorem Cfg.tapePresampleAllOf.measurable [MeasurableSpace rT] [ProbLangDist rT]
    (α : Loc) (t : Tape rT) [IsProbabilityMeasure t.dist] :
    Measurable (Cfg.tapePresampleAllOf α t) := by
  have hf : Measurable (fun p : Cfg rT × (ℕ → Val rT) =>
      (⟨p.1.expr, p.1.state.updateTapes (·.insert α (t.fillAll p.2))⟩ : Cfg rT)) := by
    refine Cfg.measurable_mk.comp
      ((Cfg.measurable_expr.comp measurable_fst).prodMk ?_)
    refine State.measurable_mk_param
      (State.measurable_heap.comp (Cfg.measurable_state.comp measurable_fst)) ?_
      (State.measurable_rvs.comp (Cfg.measurable_state.comp measurable_fst))
    exact (Measurable.locHeap_insert α).comp
      ((State.measurable_tapes.comp (Cfg.measurable_state.comp measurable_fst)).prodMk
        (Tape.measurable_fillAll.comp (measurable_const.prodMk measurable_snd)))
  exact measurable_map_const_uncurry (infinitePi fun _ : ℕ => t.dist) hf

/-- Fixed-tape whole-stream filling agrees with state filling when that tape is allocated. -/
theorem Cfg.tapePresampleAllOf_eq [MeasurableSpace rT] [ProbLangDist rT]
    (t : Tape rT) (ρ : Cfg rT) (hρ : ρ.state.tapes[α]? = some t) :
    Cfg.tapePresampleAllOf α t ρ =
      (tapePresampleAll ρ.state α).map fun σ' => ⟨ρ.expr, σ'⟩ := by
  unfold Cfg.tapePresampleAllOf
  rw [tapePresampleAll_eq_map hρ]
  symm
  simpa [Function.comp_def] using
    (Measure.map_map
      (μ := infinitePi fun _ : ℕ => t.dist)
      (f := fun ω => ρ.state.updateTapes (·.insert α (t.fillAll ω)))
      (g := fun σ' => (⟨ρ.expr, σ'⟩ : Cfg rT))
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
      (State.measurable_fillAllTape ρ.state α t))

variable [MeasurableSpace rT] [LawfulProbLangℝ rT] [ProbLangDist rT]
  [ProbLangFFI rT] [ProbLangObs rT]

/-- A head step commutes with replacing tape `α` by `u`. -/
abbrev HeadStepFrames (α : Loc) (u : Tape rT) (e : Exp rT) (σ : State rT) : Prop :=
  headStep ⟨e, σ.updateTapes (·.insert α u)⟩ =
    (headStep ⟨e, σ⟩).map (Cfg.updateTape α u)

namespace HeadStepFrames

/-- Two corresponding deterministic steps establish framing. -/
theorem of_dirac {u : Tape rT} {e e' : Exp rT} {σ σ' : State rT}
    (h : headStep ⟨e, σ⟩ = dirac ⟨e', σ'⟩)
    (h' : headStep ⟨e, σ.updateTapes (·.insert α u)⟩ = dirac ⟨e', σ'.updateTapes (·.insert α u)⟩) :
    HeadStepFrames α u e σ := by
  unfold HeadStepFrames
  rw [h, h', map_dirac' (Cfg.updateTape.measurable α u)]
  rfl

/-- A state-independent deterministic step frames. -/
theorem of_forall {u : Tape rT} {e e' : Exp rT} {σ : State rT}
    (h : ∀ τ : State rT, headStep ⟨e, τ⟩ = dirac ⟨e', τ⟩) :
    HeadStepFrames α u e σ :=
  .of_dirac (h σ) (h _)

/-- Two corresponding fresh-sampling steps establish framing. -/
theorem of_sample {u : Tape rT} {e : Exp rT} {σ σ' : State rT}
    {n : ℕ} {v : Val rT} (h : headStep ⟨e, σ⟩ = Cfg.sample n v σ')
    (h' : headStep ⟨e, σ.updateTapes (·.insert α u)⟩ =
      Cfg.sample n v (σ'.updateTapes (·.insert α u))) :
    HeadStepFrames α u e σ := by
  unfold HeadStepFrames
  rw [h, h', Cfg.sample_map_updateTape]

end HeadStepFrames

/-- A deterministic head step other than a read of `α` frames over replacing `α`. -/
theorem headStep_updateTape_det {u t : Tape rT} {e : Exp rT}
    (ht : σ.tapes[α]? = some t)
    (hnot : ∀ n e', e ≠ .sample n e' (.lit (.lbl α)))
    (hd : DetHeadStepPred e σ) : HeadStepFrames α u e σ := by
  open _root_.Option in
    cases hd with
    | betaLam hv => exact .of_forall fun _ => Exp.isValM_some hv
    | betaFix hv => exact .of_forall fun _ => Exp.isValM_some hv
    | unop hv heval =>
      rename_i op e' e''
      refine .of_forall (e' := e'') fun τ => ?_
      show e'.isValM (Option.unwrapM _ (op.eval e')) = _
      rw [Exp.isValM_some hv, heval]
      rfl
    | binop hv₁ hv₂ heval =>
      rename_i op e₁ e₂ e'
      refine .of_forall (e' := e') fun τ => ?_
      show e₁.isValM (e₂.isValM (Option.unwrapM _ (op.eval e₁ e₂))) = _
      rw [Exp.isValM_some hv₂, Exp.isValM_some hv₁, heval]
      rfl
    | ifTrue => exact .of_forall fun _ => rfl
    | ifFalse => exact .of_forall fun _ => rfl
    | fst hv₁ hv₂ =>
      rename_i e₁ e₂
      refine .of_forall (e' := e₁) fun τ => ?_
      show e₁.isValM (e₂.isValM (dirac _)) = _
      rw [Exp.isValM_some hv₂, Exp.isValM_some hv₁]
    | snd hv₁ hv₂ =>
      rename_i e₁ e₂
      refine .of_forall (e' := e₂) fun τ => ?_
      show e₁.isValM (e₂.isValM (dirac _)) = _
      rw [Exp.isValM_some hv₂, Exp.isValM_some hv₁]
    | caseL hv => exact .of_forall fun _ => Exp.isValM_some hv
    | caseR hv => exact .of_forall fun _ => Exp.isValM_some hv
    | scrutSuccess hv hm =>
      rename_i e' p bindings
      refine .of_forall (e' := .inl bindings) fun τ => ?_
      show e'.isValM (match p.tryMatch e' with | some b => _ | none => _) = _
      rw [Exp.isValM_some hv, hm]
    | scrutFailure hv hm =>
      rename_i e' p
      refine .of_forall (e' := .inr (.lit .unit)) fun τ => ?_
      show e'.isValM (match p.tryMatch e' with | some b => _ | none => _) = _
      rw [Exp.isValM_some hv, hm]
    | load hlook =>
      rename_i ℓ v
      exact .of_dirac (e' := .ofVal v) (σ' := σ)
        (by simp [headStep, hlook])
        (by simp [headStep, State.updateTapes, hlook])
    | alloc hv =>
      rename_i ed v
      refine .of_dirac (e' := .lit (.loc σ.heap.fresh))
        (σ' := σ.updateHeap fun hp => hp.insert σ.heap.fresh v)
        (by simp [headStep, Exp.asValM, hv]) ?_
      simp [headStep, Exp.asValM, hv, State.updateTapes, State.updateHeap]
    | allocN hv hn =>
      rename_i n ev v
      refine .of_dirac (e' := .lit (.loc σ.heap.fresh))
        (σ' := σ.updateHeap fun hp => LocHeap.allocN hp v n.toNat)
        (by simp [headStep, Exp.asValM, hv, hn]) ?_
      simp [headStep, Exp.asValM, hv, hn, State.updateTapes, State.updateHeap]
    | store hv hsome =>
      rename_i ℓ ev v
      obtain ⟨w, hw⟩ := isSome_iff_exists.mp hsome
      refine .of_dirac (e' := .lit .unit)
        (σ' := σ.updateHeap fun hp => hp.insert ℓ v)
        (by simp [headStep, Exp.asValM, hv, hw]) ?_
      simp [headStep, Exp.asValM, hv, hw, State.updateTapes, State.updateHeap]
    | tape hv =>
      rename_i n et v
      have hne : σ.tapes.fresh ≠ α := Std.ExtTreeMap.elem_fresh_ne ht
      refine .of_dirac (e' := .lit (.lbl σ.tapes.fresh))
        (σ' := σ.updateTapes (·.insert σ.tapes.fresh (.empty n v)))
        (by simp [headStep, Exp.asValM, hv]) ?_
      simp only [headStep, Exp.asValM, hv]
      rw [show (σ.updateTapes (·.insert α u)).tapes.fresh = σ.tapes.fresh by
        simpa [State.updateTapes] using State.fresh_loc_upd_some (bs' := u) ht]
      congr 1
      congr 1
      exact State.upd_diff_tape_comm hne
    | sampleTape hv htape hfamily hhead =>
      rename_i n et v w β t'
      have hne : β ≠ α := by
        rintro rfl
        exact hnot n et rfl
      refine .of_dirac (e' := .ofVal w)
        (σ' := σ.updateTapes (·.insert β t'.shift))
        (headStep_sample_tape_some hv htape hfamily hhead) ?_
      have htape' : (σ.updateTapes (·.insert α u)).tapes[β]? = some t' := by
        rw [State.upd_diff_tape_tot hne, htape]
      rw [headStep_sample_tape_some hv htape' hfamily hhead]
      congr 1
      congr 1
      exact State.upd_diff_tape_comm hne
    | randvar hv =>
      rename_i n er v
      refine .of_dirac (e' := .lit (.lbl σ.rvs.fresh))
        (σ' := σ.updateRvs (·.insert σ.rvs.fresh (RvCell.fresh n v)))
        (by simp [headStep, Exp.asValM, hv, Cfg.randvar]) ?_
      simp [headStep, Exp.asValM, hv, Cfg.randvar, State.updateTapes, State.updateRvs]
    | ffi hv hr =>
      rename_i ef v out
      exact headStep_ffi_updateTapes ef σ α u

/-- A probabilistic head step other than a read of `α` frames over replacing `α`. -/
theorem headStep_updateTape_prob {u t : Tape rT} {e : Exp rT}
    (ht : σ.tapes[α]? = some t)
    (hnot : ∀ n e', e ≠ .sample n e' (.lit (.lbl α)))
    (hp : ProbHeadStepPred e σ) : HeadStepFrames α u e σ := by
  cases hp with
  | sample hv hd =>
    exact .of_sample (headStep_sample hv) (headStep_sample hv)
  | sampleTapeEmpty hv htape hfamily hhead hd =>
    rename_i n er v β t'
    have hne : β ≠ α := by
      rintro rfl
      exact hnot n er rfl
    have htape' : (σ.updateTapes (·.insert α u)).tapes[β]? = some t' := by
      rw [State.upd_diff_tape_tot hne, htape]
    refine .of_sample (σ' := σ.updateTapes (·.insert β t'.shift))
      (headStep_sample_tape_none hv htape hfamily hhead) ?_
    rw [headStep_sample_tape_none hv htape' hfamily hhead]
    congr 1
    exact State.upd_diff_tape_comm hne
  | sampleTapeOther hv htape hfamily hd =>
    rename_i n er v β t'
    have hne : β ≠ α := by
      rintro rfl
      exact hnot n er rfl
    have htape' : (σ.updateTapes (·.insert α u)).tapes[β]? = some t' := by
      rw [State.upd_diff_tape_tot hne, htape]
    exact .of_sample (headStep_sample_tape_other hv htape hfamily)
      (headStep_sample_tape_other hv htape' hfamily)
  | test hv hc hy =>
    rename_i k l er a c y
    unfold HeadStepFrames
    have hstep : headStep ⟨.test k (.lit (.lbl l)) er, σ⟩ = Cfg.test k a l σ := by
      simp [headStep, Exp.asValM, hv]
    have hstep' : headStep ⟨.test k (.lit (.lbl l)) er,
        σ.updateTapes (·.insert α u)⟩ =
        Cfg.test k a l (σ.updateTapes (·.insert α u)) := by
      simp [headStep, Exp.asValM, hv]
    rw [hstep, hstep']
    change Cfg.test k a l (σ.updateTapes (·.insert α u)) =
      (Cfg.test k a l σ).map fun ρ =>
        ⟨ρ.expr, ρ.state.updateTapes (·.insert α u)⟩
    exact (Cfg.test_map_state (State.measurable_updateTapes_insert α u) rfl (fun _ => rfl)).symm

/-- A stuck head step other than a read of `α` stays stuck after replacing `α`. -/
theorem headStep_updateTape_zero {u t : Tape rT} {e : Exp rT}
    (ht : σ.tapes[α]? = some t)
    (hnot : ∀ n e', e ≠ .sample n e' (.lit (.lbl α)))
    (hzero : headStep ⟨e, σ⟩ = 0) : HeadStepFrames α u e σ := by
  have hzero' : headStep ⟨e, σ.updateTapes (·.insert α u)⟩ = 0 := by
    revert hzero
    head_case
    all_goals try (intro hzero; exact absurd hzero Measure.dirac_ne_zero)
    all_goals try (intro _; dsimp only; simp only [*, ↓reduceIte, Exp.asValM]; done)
    all_goals intro hzero
    all_goals try dsimp only at hzero ⊢
    case unop.redex | binop.redex =>
      simp only [*, ↓reduceIte]
      unfold Option.unwrapM at hzero ⊢
      split <;> rename_i hopt
      · rw [hopt] at hzero
        exact absurd hzero Measure.dirac_ne_zero
      · rfl
    case load.segfault =>
      rename_i heq
      simp [State.updateTapes, heq]
    case sample.tape.unalloc =>
      simp_all [State.updateTapes, Std.ExtTreeMap.getElem?_insert]
      have hne' : α ≠ ‹Lbl› := Ne.symm hnot
      simp [hne']
    case sample.plain.redex =>
      rename_i heq
      simp only [heq]
      rw [Cfg.sample_eq_zero_iff] at hzero ⊢
      exact hzero
    case sample.tape.empty | sample.tape.mismatch =>
      have hne : ‹Lbl› ≠ α := by
        rintro rfl
        exact hnot _ _ rfl
      rw [State.upd_diff_tape_tot hne]
      simp only [*]
      simp only [true_and, ite_true, ite_false]
      rw [Cfg.sample_eq_zero_iff] at hzero ⊢
      exact hzero
    case test.redex =>
      rename_i hv
      simp only [hv]
      rw [Cfg.test_eq_zero_iff_of_rvs
        (show (σ.updateTapes fun x => x.insert α u).rvs = σ.rvs from rfl)]
      exact hzero
    case ffi.redex =>
      rename_i heq
      simp only [heq]
      exact Cfg.ffi_eq_zero_iff.mpr ((Cfg.ffi_eq_zero_iff (σ := σ)).mp hzero)
    case store.segfault =>
      rename_i hv _ heq
      simp only [State.updateTapes, hv, heq]
    case default =>
      split <;> first
        | rfl
        | (rename_i heq
           obtain ⟨rfl, -⟩ := Cfg.mk.inj heq
           exfalso
           solve_by_elim)
  unfold HeadStepFrames
  rw [hzero, hzero', Measure.map_zero]

/-- Any head step other than a read of `α` frames over replacing the allocated tape `α`. -/
theorem headStep_updateTape_frame [ProbLangDist.IsIntValued rT]
    {u t : Tape rT} {e : Exp rT} (ht : σ.tapes[α]? = some t)
    (hnot : ∀ n e', e ≠ .sample n e' (.lit (.lbl α))) :
    HeadStepFrames α u e σ := by
  rcases det_or_prob_or_zero e σ with hd | hp | hzero
  · exact headStep_updateTape_det ht hnot hd
  · exact headStep_updateTape_prob ht hnot hp
  · exact headStep_updateTape_zero ht hnot hzero

/-- A head step that does not read `α` keeps its tape unchanged almost surely. -/
theorem headStep_tape_persists_frame [ProbLangDist.IsIntValued rT]
    {t : Tape rT} {e : Exp rT} (ht : σ.tapes[α]? = some t)
    (hnot : ∀ n e', e ≠ .sample n e' (.lit (.lbl α))) :
    ∀ᵐ ρ ∂headStep ⟨e, σ⟩, ρ.state.tapes[α]? = some t := by
  have hsame : σ.updateTapes (·.insert α t) = σ :=
    State.updateTapes_no_change ht
  have hframe : headStep ⟨e, σ⟩ =
      (headStep ⟨e, σ⟩).map (Cfg.updateTape α t) := by
    simpa [HeadStepFrames, hsame] using
      headStep_updateTape_frame (u := t) ht hnot
  have hP : MeasurableSet {ρ : Cfg rT | ρ.state.tapes[α]? = some t} :=
    (((LocHeap.measurable_getElem? α).comp State.measurable_tapes).comp
      Cfg.measurable_state) (measurableSet_singleton _)
  rw [hframe]
  exact (ae_map_iff (Cfg.updateTape.measurable α t).aemeasurable hP).mpr
    (ae_of_all _ fun ρ => State.upd_tape_some ρ.state α t)

/-- One-position presampling commutes with a head step that does not read its tape. -/
theorem tapePresampleAt_bind_headStep_frame [ProbLangDist.IsIntValued rT]
    {t : Tape rT} {k : ℕ} {e : Exp rT} (ht : σ.tapes[α]? = some t)
    (hk : t.presamples k = none)
    (hnot : ∀ n e', e ≠ .sample n e' (.lit (.lbl α))) :
    (tapePresampleAt σ α k).bind (fun σ' => headStep ⟨e, σ'⟩) =
      (headStep ⟨e, σ⟩).bind (Cfg.tapePresampleAt α k) := by
  let H : Measure (Cfg rT) := headStep ⟨e, σ⟩
  let F : Val rT → Cfg rT → Cfg rT := fun x ρ =>
    Cfg.updateTape α (t.fillAt k x) ρ
  have hF : Measurable (fun p : Val rT × Cfg rT => F p.1 p.2) := by
    refine Cfg.measurable_mk.comp ((Cfg.measurable_expr.comp measurable_snd).prodMk ?_)
    refine State.measurable_mk_param
      (State.measurable_heap.comp (Cfg.measurable_state.comp measurable_snd)) ?_
      (State.measurable_rvs.comp (Cfg.measurable_state.comp measurable_snd))
    have htape : Measurable (fun p : Val rT × Cfg rT => t.fillAt k p.1) :=
      (Tape.measurable_fillAt k).comp (measurable_const.prodMk measurable_fst)
    exact (Measurable.locHeap_insert α).comp
      ((State.measurable_tapes.comp (Cfg.measurable_state.comp measurable_snd)).prodMk htape)
  have hH : Measurable (fun σ' : State rT => headStep ⟨e, σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  rw [tapePresampleAt_eq_map ht hk,
    Measure.bind_map (State.measurable_fillAtTape σ α t k).aemeasurable
      hH.aemeasurable]
  have hframe (x : Val rT) :
      headStep ⟨e, σ.updateTapes (·.insert α (t.fillAt k x))⟩ =
        H.map (F x) := by
    simpa [H, F, HeadStepFrames] using
      headStep_updateTape_frame (u := t.fillAt k x) ht hnot
  simp_rw [hframe]
  have hsame : σ.updateTapes (·.insert α t) = σ :=
    State.updateTapes_no_change ht
  have hframeSelf : H = H.map (Cfg.updateTape α t) := by
    simpa [H, HeadStepFrames, hsame] using
      headStep_updateTape_frame (u := t) ht hnot
  have hpersist : ∀ᵐ ρ ∂H, ρ.state.tapes[α]? = some t := by
    have hP : MeasurableSet {ρ : Cfg rT | ρ.state.tapes[α]? = some t} :=
      (((LocHeap.measurable_getElem? α).comp State.measurable_tapes).comp
        Cfg.measurable_state) (measurableSet_singleton _)
    rw [hframeSelf]
    exact (ae_map_iff (Cfg.updateTape.measurable α t).aemeasurable hP).mpr
      (ae_of_all _ fun ρ => State.upd_tape_some ρ.state α t)
  have hright : H.bind (Cfg.tapePresampleAt α k) =
      H.bind (fun ρ => t.dist.map fun x => F x ρ) := by
    exact bind_congr_right (hpersist.mono fun ρ hρ => by
      unfold Cfg.tapePresampleAt F
      rw [tapePresampleAt_eq_map hρ hk,
        Measure.map_map (μ := t.dist)
          (f := fun w => ρ.state.updateTapes (·.insert α (t.fillAt k w)))
          (g := fun σ' => (⟨ρ.expr, σ'⟩ : Cfg rT))
          (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
          (State.measurable_fillAtTape ρ.state α t k)]
      rfl)
  rw [hright]
  let _ : IsFiniteMeasure H :=
    ⟨lt_of_le_of_lt (headStep_univ_le_one ⟨e, σ⟩) ENNReal.one_lt_top⟩
  exact bind_map_swap t.dist H F hF

/-- Whole-stream presampling commutes with a head step that does not read its tape. -/
theorem tapePresampleAll_bind_headStep_frame [ProbLangDist.IsIntValued rT]
    {t : Tape rT} {e : Exp rT} [IsProbabilityMeasure t.dist]
    (ht : σ.tapes[α]? = some t)
    (hnot : ∀ n e', e ≠ .sample n e' (.lit (.lbl α))) :
    (tapePresampleAll σ α).bind (fun σ' => headStep ⟨e, σ'⟩) =
      (headStep ⟨e, σ⟩).bind (Cfg.tapePresampleAllOf α t) := by
  let Ω : Measure (ℕ → Val rT) := infinitePi fun _ : ℕ => t.dist
  let H : Measure (Cfg rT) := headStep ⟨e, σ⟩
  let F : (ℕ → Val rT) → Cfg rT → Cfg rT := fun ω ρ =>
    Cfg.updateTape α (t.fillAll ω) ρ
  have hF : Measurable (fun p : (ℕ → Val rT) × Cfg rT => F p.1 p.2) := by
    refine Cfg.measurable_mk.comp ((Cfg.measurable_expr.comp measurable_snd).prodMk ?_)
    refine State.measurable_mk_param
      (State.measurable_heap.comp (Cfg.measurable_state.comp measurable_snd)) ?_
      (State.measurable_rvs.comp (Cfg.measurable_state.comp measurable_snd))
    exact (Measurable.locHeap_insert α).comp
      ((State.measurable_tapes.comp (Cfg.measurable_state.comp measurable_snd)).prodMk
        (Tape.measurable_fillAll.comp (measurable_const.prodMk measurable_fst)))
  have hH : Measurable (fun σ' : State rT => headStep ⟨e, σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  rw [tapePresampleAll_eq_map ht,
    Measure.bind_map (State.measurable_fillAllTape σ α t).aemeasurable
      hH.aemeasurable]
  have hframe (ω : ℕ → Val rT) :
      headStep ⟨e, σ.updateTapes (·.insert α (t.fillAll ω))⟩ =
        H.map (F ω) := by
    simpa [H, F, HeadStepFrames] using
      headStep_updateTape_frame (u := t.fillAll ω) ht hnot
  simp_rw [hframe]
  change Ω.bind (fun ω => H.map (F ω)) =
    H.bind (Cfg.tapePresampleAllOf α t)
  change Ω.bind (fun ω => H.map (F ω)) =
    H.bind (fun ρ => Ω.map fun ω => F ω ρ)
  let _ : IsFiniteMeasure H :=
    ⟨lt_of_le_of_lt (headStep_univ_le_one ⟨e, σ⟩) ENNReal.one_lt_top⟩
  exact bind_map_swap Ω H F hF

/-- Filling position zero before a matching tape read is the same as drawing freshly. -/
theorem tapePresampleAt_zero_bind_headStep {n : ℕ} {e : Exp rT} {v : Val rT}
    {t : Tape rT} (hv : e.toVal? = some v) (ht : σ.tapes[α]? = some t)
    (hfamily : t.name = n ∧ t.arg = v) (hhead : t.head? = none) :
    (tapePresampleAt σ α 0).bind
      (fun σ' => headStep ⟨.sample n e (.lit (.lbl α)), σ'⟩) =
      headStep ⟨.sample n e (.lit (.lbl α)), σ⟩ := by
  have hfill := State.measurable_fillAtTape σ α t 0
  have hnone : t.presamples 0 = none := hhead
  have hkernel : Measurable (fun σ' : State rT =>
      headStep ⟨.sample n e (.lit (.lbl α)), σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  have hstep : ∀ w : Val rT,
      headStep ⟨.sample n e (.lit (.lbl α)),
          σ.updateTapes (·.insert α (t.fillAt 0 w))⟩ =
        dirac ⟨.ofVal w, σ.updateTapes (·.insert α t.shift)⟩ := by
    intro w
    have hfilled : (t.fillAt 0 w).head? = some w := by
      simp [Tape.head?, Tape.fillAt, Presamples.fillAt, hnone]
    rw [headStep_sample_tape_some (t := t.fillAt 0 w) hv
      (State.upd_tape_some _ _ _) hfamily hfilled]
    · simp [Tape.shift_fillAt_zero, State.updateTapes_twice]
  rw [tapePresampleAt_eq_map ht hhead,
    Measure.bind_map (m := t.dist) (f := fun w =>
      σ.updateTapes (·.insert α (t.fillAt 0 w))) hfill.aemeasurable hkernel.aemeasurable]
  simp_rw [hstep]
  rw [bind_dirac_eq_map]
  · rw [headStep_sample_tape_none hv ht hfamily hhead]
    simp [Cfg.sample, Tape.dist, hfamily.1, hfamily.2]
  · fun_prop

/-- Filling a later position moves one position closer after a matching tape read. -/
theorem tapePresampleAt_succ_bind_headStep {n : ℕ} {e : Exp rT} {v : Val rT}
    {t : Tape rT} {k : ℕ} (hv : e.toVal? = some v)
    (ht : σ.tapes[α]? = some t) (hfamily : t.name = n ∧ t.arg = v)
    (hk : t.presamples (k + 1) = none) :
    (tapePresampleAt σ α (k + 1)).bind
        (fun σ' => headStep ⟨.sample n e (.lit (.lbl α)), σ'⟩) =
      (headStep ⟨.sample n e (.lit (.lbl α)), σ⟩).bind
        (Cfg.tapePresampleAt α k) := by
  have hfill := State.measurable_fillAtTape σ α t (k + 1)
  have hkernel : Measurable (fun σ' : State rT =>
      headStep ⟨.sample n e (.lit (.lbl α)), σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  have htshift : (σ.updateTapes (·.insert α t.shift)).tapes[α]? = some t.shift :=
    State.upd_tape_some _ _ _
  have hkshift : t.shift.presamples k = none := hk
  rcases hhead : t.head? with _ | w
  · have hstep : ∀ x : Val rT,
        headStep ⟨.sample n e (.lit (.lbl α)),
            σ.updateTapes (·.insert α (t.fillAt (k + 1) x))⟩ =
          Cfg.sample n v
            (σ.updateTapes (·.insert α (t.shift.fillAt k x))) := by
      intro x
      have hnone : t.presamples 0 = none := hhead
      have hhead' : (t.fillAt (k + 1) x).head? = none := by
        simp [Tape.head?, Tape.fillAt, Presamples.fillAt, hnone]
      rw [headStep_sample_tape_none (t := t.fillAt (k + 1) x) hv
        (State.upd_tape_some _ _ _) hfamily hhead']
      simp [Tape.shift_fillAt_succ, State.updateTapes_twice]
    rw [tapePresampleAt_eq_map ht hk,
      Measure.bind_map (m := t.dist) (f := fun x =>
        σ.updateTapes (·.insert α (t.fillAt (k + 1) x)))
        hfill.aemeasurable hkernel.aemeasurable]
    simp_rw [hstep]
    rw [headStep_sample_tape_none hv ht hfamily hhead]
    unfold Cfg.sample Cfg.tapePresampleAt
    have hdist : ProbLangDist.dist n v = t.dist := by
      simp [Tape.dist, hfamily.1, hfamily.2]
    rw [hdist]
    rw [Measure.bind_map]
    · simp_rw [tapePresampleAt_eq_map htshift hkshift]
      have hshiftDist : t.shift.dist = t.dist := rfl
      simp_rw [hshiftDist]
      let out : Val rT → Val rT → Cfg rT := fun x y =>
        ⟨.ofVal y, σ.updateTapes (·.insert α (t.shift.fillAt k x))⟩
      have hinner := State.measurable_fillAtTape
        (σ.updateTapes (·.insert α t.shift)) α t.shift k
      have hcollapse (y : Val rT) :
          (t.dist.map fun x =>
            (σ.updateTapes (·.insert α t.shift)).updateTapes
              (·.insert α (t.shift.fillAt k x))).map
              (fun σ' => (⟨.ofVal y, σ'⟩ : Cfg rT)) =
            t.dist.map fun x => out x y := by
        rw [Measure.map_map (μ := t.dist)
          (f := fun x =>
            (σ.updateTapes (·.insert α t.shift)).updateTapes
              (·.insert α (t.shift.fillAt k x)))
          (g := fun σ' => (⟨.ofVal y, σ'⟩ : Cfg rT))
          (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id)) hinner]
        congr 1
        funext x
        simp [out, State.updateTapes_twice]
      simp_rw [hcollapse]
      change t.dist.bind (fun x => t.dist.map (out x)) =
        t.dist.bind (fun y => t.dist.map fun x => out x y)
      have hleft (x : Val rT) : Measurable (out x) := by
        fun_prop
      have hright (y : Val rT) : Measurable (fun x => out x y) := by
        fun_prop
      have hout : Measurable (fun p : Val rT × Val rT => out p.1 p.2) := by
        dsimp only [out]
        exact Cfg.measurable_mk.comp
          ((Exp.ofVal.measurable.comp measurable_snd).prodMk
            ((State.measurable_fillAtTape σ α t.shift k).comp measurable_fst))
      simp_rw [← bind_dirac_eq_map t.dist (hleft _),
        ← bind_dirac_eq_map t.dist (hright _)]
      have hKLeft : Measurable (fun x =>
          t.dist.bind fun y => dirac (out x y)) := by
        rw [show (fun x => t.dist.bind fun y => dirac (out x y)) = fun x => t.dist.map (out x) by
          funext x
          exact bind_dirac_eq_map t.dist (hleft x)]
        exact measurable_map_const_uncurry t.dist hout
      have hKRight : Measurable (fun y =>
          t.dist.bind fun x => dirac (out x y)) := by
        rw [show (fun y => t.dist.bind fun x => dirac (out x y)) =
            fun y => t.dist.map (fun x => out x y) by
          funext y
          exact bind_dirac_eq_map t.dist (hright y)]
        exact measurable_map_const_uncurry t.dist
          (hout.comp (measurable_snd.prodMk measurable_fst))
      refine ext fun S hS => ?_
      rw [bind_apply hS hKLeft.aemeasurable, bind_apply hS hKRight.aemeasurable]
      have hbindLeft (x : Val rT) :
          (t.dist.bind fun y => dirac (out x y)) S =
            ∫⁻ y, (dirac (out x y)) S ∂t.dist :=
        bind_apply hS (measurable_dirac.comp (hleft x)).aemeasurable
      have hbindRight (y : Val rT) :
          (t.dist.bind fun x => dirac (out x y)) S =
            ∫⁻ x, (dirac (out x y)) S ∂t.dist :=
        bind_apply hS (measurable_dirac.comp (hright y)).aemeasurable
      simp_rw [hbindLeft, hbindRight]
      exact lintegral_lintegral_swap (μ := t.dist) (ν := t.dist)
        (f := fun x y => (dirac (out x y)) S)
        (((measurable_coe hS).comp measurable_dirac).comp hout).aemeasurable
    · fun_prop
    · exact (Cfg.tapePresampleAt.measurable α k).aemeasurable
  · have hhead' : ∀ x : Val rT, (t.fillAt (k + 1) x).head? = some w := by
      intro x
      have hsome : t.presamples 0 = some w := hhead
      simp [Tape.head?, Tape.fillAt, Presamples.fillAt, hsome]
    have hstep : ∀ x : Val rT,
        headStep ⟨.sample n e (.lit (.lbl α)),
            σ.updateTapes (·.insert α (t.fillAt (k + 1) x))⟩ =
          dirac ⟨.ofVal w,
            σ.updateTapes (·.insert α (t.shift.fillAt k x))⟩ := by
      intro x
      rw [headStep_sample_tape_some (t := t.fillAt (k + 1) x) hv
        (State.upd_tape_some _ _ _) hfamily (hhead' x)]
      simp [Tape.shift_fillAt_succ, State.updateTapes_twice]
    rw [tapePresampleAt_eq_map ht hk,
      Measure.bind_map (m := t.dist) (f := fun x =>
        σ.updateTapes (·.insert α (t.fillAt (k + 1) x)))
        hfill.aemeasurable hkernel.aemeasurable]
    simp_rw [hstep]
    rw [bind_dirac_eq_map t.dist (by fun_prop),
      headStep_sample_tape_some hv ht hfamily hhead,
      dirac_bind (Cfg.tapePresampleAt.measurable α k)]
    unfold Cfg.tapePresampleAt
    rw [tapePresampleAt_eq_map htshift hkshift]
    let inner : Val rT → State rT := fun x =>
      (σ.updateTapes (·.insert α t.shift)).updateTapes
        (·.insert α (t.shift.fillAt k x))
    let outer : State rT → Cfg rT := fun σ' => ⟨.ofVal w, σ'⟩
    have hinner : Measurable inner := by
      exact State.measurable_fillAtTape
        (σ.updateTapes (·.insert α t.shift)) α t.shift k
    have houter : Measurable outer := by
      fun_prop
    calc
      t.dist.map (fun x =>
          (⟨.ofVal w, σ.updateTapes (·.insert α (t.shift.fillAt k x))⟩ : Cfg rT)) =
          t.dist.map (outer ∘ inner) := by
            congr 1
            funext x
            simp [inner, outer, State.updateTapes_twice]
      _ = (t.dist.map inner).map outer :=
        (Measure.map_map (μ := t.dist) (f := inner) (g := outer) houter hinner).symm

/-- Filling every hole before a matching read is the read followed by filling the shifted tape. -/
theorem tapePresampleAll_bind_headStep {n : ℕ} {e : Exp rT} {v : Val rT}
    {t : Tape rT} [IsProbabilityMeasure t.dist]
    (hv : e.toVal? = some v) (ht : σ.tapes[α]? = some t)
    (hfamily : t.name = n ∧ t.arg = v) :
    (tapePresampleAll σ α).bind
        (fun σ' => headStep ⟨.sample n e (.lit (.lbl α)), σ'⟩) =
      (headStep ⟨.sample n e (.lit (.lbl α)), σ⟩).bind
        (Cfg.tapePresampleAllOf α t.shift) := by
  let Ω : Measure (ℕ → Val rT) := infinitePi fun _ : ℕ => t.dist
  let _ : IsProbabilityMeasure t.shift.dist := by
    change IsProbabilityMeasure t.dist
    infer_instance
  have htailMeas : Measurable (fun ω : ℕ → Val rT => fun k => ω (k + 1)) :=
    Measurable.of_eval fun k => measurable_pi_apply (k + 1)
  have hheadTailMeas : Measurable (fun ω : ℕ → Val rT =>
      (ω 0, fun k => ω (k + 1))) :=
    (measurable_pi_apply 0).prodMk htailMeas
  have hfill := State.measurable_fillAllTape σ α t
  have hkernel : Measurable (fun σ' : State rT =>
      headStep ⟨.sample n e (.lit (.lbl α)), σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  rw [tapePresampleAll_eq_map ht,
    Measure.bind_map (m := Ω)
      (f := fun ω => σ.updateTapes (·.insert α (t.fillAll ω)))
      hfill.aemeasurable hkernel.aemeasurable]
  rcases hhead : t.head? with _ | w
  · let out : Val rT → (ℕ → Val rT) → Cfg rT := fun y ω =>
      ⟨.ofVal y, σ.updateTapes (·.insert α (t.shift.fillAll ω))⟩
    have hout : Measurable (fun p : Val rT × (ℕ → Val rT) => out p.1 p.2) :=
      Cfg.measurable_mk.comp
        ((Exp.ofVal.measurable.comp measurable_fst).prodMk
          ((State.measurable_fillAllTape σ α t.shift).comp measurable_snd))
    have hstep (ω : ℕ → Val rT) :
        headStep ⟨.sample n e (.lit (.lbl α)),
            σ.updateTapes (·.insert α (t.fillAll ω))⟩ =
          dirac (out (ω 0) (fun k => ω (k + 1))) := by
      have hfilled : (t.fillAll ω).head? = some (ω 0) := by
        have hhead' : t.presamples 0 = none := hhead
        simp [Tape.head?, Tape.fillAll, Presamples.fillAll, hhead']
      rw [headStep_sample_tape_some (t := t.fillAll ω) hv
        (State.upd_tape_some _ _ _) hfamily hfilled]
      simp [out, Tape.shift_fillAll, State.updateTapes_twice]
    simp_rw [hstep]
    have hdraw : Measurable (fun ω : ℕ → Val rT =>
        out (ω 0) (fun k => ω (k + 1))) := by
      exact hout.comp hheadTailMeas
    have hcollapse : Ω.bind (fun ω =>
        dirac (out (ω 0) (fun k => ω (k + 1)))) =
        Ω.map (fun ω => out (ω 0) (fun k => ω (k + 1))) :=
      bind_dirac_eq_map Ω hdraw
    rw [hcollapse]
    rw [headStep_sample_tape_none hv ht hfamily hhead]
    unfold Cfg.sample
    rw [Measure.bind_map (by fun_prop) (Cfg.tapePresampleAllOf.measurable α t.shift).aemeasurable]
    unfold Cfg.tapePresampleAllOf
    have hdist : ProbLangDist.dist n v = t.dist := by
      simp [Tape.dist, hfamily.1, hfamily.2]
    rw [hdist]
    simp_rw [show t.shift.dist = t.dist from rfl, State.updateTapes_twice]
    change Ω.map (fun ω => out (ω 0) (fun k => ω (k + 1))) =
      t.dist.bind fun y => Ω.map fun ω => out y ω
    have hheadtail :
        Ω.map (fun ω => (ω 0, fun k => ω (k + 1))) = t.dist.prod Ω := by
      exact infinitePi_map_head_tail (μ := t.dist)
    calc
      Ω.map (fun ω => out (ω 0) (fun k => ω (k + 1))) =
          (Ω.map fun ω => (ω 0, fun k => ω (k + 1))).map
            (fun p => out p.1 p.2) := by
              rw [Measure.map_map hout hheadTailMeas]
              rfl
      _ = (t.dist.prod Ω).map (fun p => out p.1 p.2) := by rw [hheadtail]
      _ = t.dist.bind (fun y => Ω.map fun ω => out y ω) := by
        have hmk : Measurable (fun p : Val rT × (ℕ → Val rT) =>
            (p.1, p.2)) := measurable_id
        have hpair : Measurable (fun y : Val rT => Ω.map (Prod.mk y)) :=
          measurable_map_const_uncurry Ω hmk
        have hmap (y : Val rT) :
            (Ω.map (Prod.mk y)).map (fun p => out p.1 p.2) =
              Ω.map (out y) := by
          simpa [Function.comp_def] using
            (Measure.map_map
              (μ := Ω) (f := Prod.mk y) (g := fun p => out p.1 p.2)
              hout (measurable_const.prodMk measurable_id))
        rw [Measure.prod_eq_of_sfinite,
          Measure.map_bind hpair.aemeasurable hout.aemeasurable]
        simp_rw [hmap]
  · let out : (ℕ → Val rT) → Cfg rT := fun ω =>
      ⟨.ofVal w, σ.updateTapes (·.insert α (t.shift.fillAll ω))⟩
    have hout : Measurable out := by
      exact Cfg.measurable_mk.comp
        (measurable_const.prodMk (State.measurable_fillAllTape σ α t.shift))
    have hstep (ω : ℕ → Val rT) :
        headStep ⟨.sample n e (.lit (.lbl α)),
            σ.updateTapes (·.insert α (t.fillAll ω))⟩ =
          dirac (out fun k => ω (k + 1)) := by
      have hfilled : (t.fillAll ω).head? = some w := by
        have hhead' : t.presamples 0 = some w := hhead
        simp [Tape.head?, Tape.fillAll, Presamples.fillAll, hhead']
      rw [headStep_sample_tape_some (t := t.fillAll ω) hv
        (State.upd_tape_some _ _ _) hfamily hfilled]
      simp [out, Tape.shift_fillAll, State.updateTapes_twice]
    simp_rw [hstep]
    have hdraw : Measurable (fun ω : ℕ → Val rT => out fun k => ω (k + 1)) := by
      exact hout.comp htailMeas
    have hcollapse : Ω.bind (fun ω => dirac (out fun k => ω (k + 1))) =
        Ω.map (fun ω => out fun k => ω (k + 1)) :=
      bind_dirac_eq_map Ω hdraw
    rw [hcollapse, headStep_sample_tape_some hv ht hfamily hhead,
      dirac_bind (Cfg.tapePresampleAllOf.measurable α t.shift)]
    unfold Cfg.tapePresampleAllOf
    simp_rw [show t.shift.dist = t.dist from rfl, State.updateTapes_twice]
    have htail : Ω.map (fun ω k => ω (k + 1)) = Ω := by
      exact map_infinitePi_infinitePi_of_inj Nat.succ_injective
    calc
      Ω.map (fun ω => out fun k => ω (k + 1)) =
          (Ω.map fun ω k => ω (k + 1)).map out := by
            rw [Measure.map_map hout htailMeas]
            rfl
      _ = Ω.map out := by rw [htail]
      _ = _ := rfl

/-- Presampling commutes with a tape-backed draw from a different family. -/
theorem tapePresampleAt_bind_headStep_other {n : ℕ} {e : Exp rT} {v : Val rT}
    {t : Tape rT} {k : ℕ} (hv : e.toVal? = some v)
    (ht : σ.tapes[α]? = some t) (hk : t.presamples k = none)
    (hfamily : ¬(t.name = n ∧ t.arg = v)) :
    (tapePresampleAt σ α k).bind
        (fun σ' => headStep ⟨.sample n e (.lit (.lbl α)), σ'⟩) =
      (headStep ⟨.sample n e (.lit (.lbl α)), σ⟩).bind
        (Cfg.tapePresampleAt α k) := by
  have hfill := State.measurable_fillAtTape σ α t k
  have hkernel : Measurable (fun σ' : State rT =>
      headStep ⟨.sample n e (.lit (.lbl α)), σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  have hstep : ∀ x : Val rT,
      headStep ⟨.sample n e (.lit (.lbl α)),
          σ.updateTapes (·.insert α (t.fillAt k x))⟩ =
        Cfg.sample n v (σ.updateTapes (·.insert α (t.fillAt k x))) := by
    intro x
    exact headStep_sample_tape_other hv (State.upd_tape_some _ _ _) hfamily
  rw [tapePresampleAt_eq_map ht hk,
    Measure.bind_map (m := t.dist) (f := fun x =>
      σ.updateTapes (·.insert α (t.fillAt k x)))
      hfill.aemeasurable hkernel.aemeasurable]
  simp_rw [hstep]
  rw [headStep_sample_tape_other hv ht hfamily]
  unfold Cfg.sample
  rw [Measure.bind_map]
  · have hcfg (y : Val rT) :
        Cfg.tapePresampleAt α k (⟨.ofVal y, σ⟩ : Cfg rT) =
          (t.dist.map fun x => σ.updateTapes (·.insert α (t.fillAt k x))).map
            fun σ' => (⟨.ofVal y, σ'⟩ : Cfg rT) := by
      unfold Cfg.tapePresampleAt
      rw [tapePresampleAt_eq_map ht hk]
    simp_rw [hcfg]
    let out : Val rT → Val rT → Cfg rT := fun x y =>
      ⟨.ofVal y, σ.updateTapes (·.insert α (t.fillAt k x))⟩
    have hinner := State.measurable_fillAtTape σ α t k
    have hcollapse (y : Val rT) :
        (t.dist.map fun x => σ.updateTapes (·.insert α (t.fillAt k x))).map
            (fun σ' => (⟨.ofVal y, σ'⟩ : Cfg rT)) =
          t.dist.map fun x => out x y := by
      rw [Measure.map_map (μ := t.dist)
        (f := fun x => σ.updateTapes (·.insert α (t.fillAt k x)))
        (g := fun σ' => (⟨.ofVal y, σ'⟩ : Cfg rT))
        (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id)) hinner]
      rfl
    simp_rw [hcollapse]
    have hout : Measurable (fun p : Val rT × Val rT => out p.1 p.2) :=
      Cfg.measurable_mk.comp
        ((Exp.ofVal.measurable.comp measurable_snd).prodMk (hfill.comp measurable_fst))
    exact bind_map_swap t.dist (ProbLangDist.dist n v) out hout
  · fun_prop
  · exact (Cfg.tapePresampleAt.measurable α k).aemeasurable

/-- Whole-stream presampling commutes with a tape-backed draw from another family. -/
theorem tapePresampleAll_bind_headStep_other {n : ℕ} {e : Exp rT}
    {v : Val rT} {t : Tape rT} [IsProbabilityMeasure t.dist]
    (hv : e.toVal? = some v) (ht : σ.tapes[α]? = some t)
    (hfamily : ¬(t.name = n ∧ t.arg = v)) :
    (tapePresampleAll σ α).bind
        (fun σ' => headStep ⟨.sample n e (.lit (.lbl α)), σ'⟩) =
      (headStep ⟨.sample n e (.lit (.lbl α)), σ⟩).bind
        (Cfg.tapePresampleAllOf α t) := by
  let Ω : Measure (ℕ → Val rT) := infinitePi fun _ : ℕ => t.dist
  have hfill := State.measurable_fillAllTape σ α t
  have hkernel : Measurable (fun σ' : State rT =>
      headStep ⟨.sample n e (.lit (.lbl α)), σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  have hstep : ∀ ω : ℕ → Val rT,
      headStep ⟨.sample n e (.lit (.lbl α)),
          σ.updateTapes (·.insert α (t.fillAll ω))⟩ =
        Cfg.sample n v (σ.updateTapes (·.insert α (t.fillAll ω))) := by
    intro ω
    exact headStep_sample_tape_other hv (State.upd_tape_some _ _ _) hfamily
  rw [tapePresampleAll_eq_map ht,
    Measure.bind_map (m := Ω)
      (f := fun ω => σ.updateTapes (·.insert α (t.fillAll ω)))
      hfill.aemeasurable hkernel.aemeasurable]
  simp_rw [hstep]
  rw [headStep_sample_tape_other hv ht hfamily]
  unfold Cfg.sample
  rw [Measure.bind_map (by fun_prop) (Cfg.tapePresampleAllOf.measurable α t).aemeasurable]
  unfold Cfg.tapePresampleAllOf
  let out : (ℕ → Val rT) → Val rT → Cfg rT := fun ω y =>
    ⟨.ofVal y, σ.updateTapes (·.insert α (t.fillAll ω))⟩
  have hout : Measurable (fun p : (ℕ → Val rT) × Val rT => out p.1 p.2) :=
    Cfg.measurable_mk.comp
      ((Exp.ofVal.measurable.comp measurable_snd).prodMk (hfill.comp measurable_fst))
  change Ω.bind (fun ω => (ProbLangDist.dist n v).map (out ω)) =
    (ProbLangDist.dist n v).bind fun y => Ω.map fun ω => out ω y
  exact bind_map_swap Ω (ProbLangDist.dist n v) out hout

end ProbLang
