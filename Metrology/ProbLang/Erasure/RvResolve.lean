module

public import Metrology.ProbLang.Erasure.ErasableExpr

/-! # Resolving a random variable is erasable

Drawing the value of a random variable from its posterior before a run leaves the run's result
distribution unchanged (`ErasableExpr.rvResolve`). -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory

namespace ProbLang

variable {rT : Type} {l : Lbl} {c : RvCell rT} {σ : State rT}

/-! ## Replacing one random variable -/

/-- The state with the random variable at `l` replaced by `c`. -/
def State.setRv (l : Lbl) (c : RvCell rT) (σ : State rT) : State rT :=
  σ.updateRvs (·.insert l c)

/-- The configuration with the random variable at `l` replaced by `c`. -/
def Cfg.setRv (l : Lbl) (c : RvCell rT) (ρ : Cfg rT) : Cfg rT :=
  ⟨ρ.expr, ρ.state.setRv l c⟩

section SetRv

@[simp]
theorem State.heap_setRv : (σ.setRv l c).heap = σ.heap :=
  rfl

@[simp]
theorem State.tapes_setRv : (σ.setRv l c).tapes = σ.tapes :=
  rfl

@[simp]
theorem State.setRv_updateHeap (f : LocHeap (Val rT) → LocHeap (Val rT)) :
    (σ.setRv l c).updateHeap f = (σ.updateHeap f).setRv l c :=
  rfl

@[simp]
theorem State.setRv_updateTapes (f : LocHeap (Tape rT) → LocHeap (Tape rT)) :
    (σ.setRv l c).updateTapes f = (σ.updateTapes f).setRv l c :=
  rfl

@[simp]
theorem Cfg.setRv_mk (e : Exp rT) : Cfg.setRv l c ⟨e, σ⟩ = ⟨e, σ.setRv l c⟩ :=
  rfl

/-- Reading the replaced random variable returns the replacement. -/
@[simp]
theorem State.rvs_setRv_self : (σ.setRv l c).rvs[l]? = some c := by
  simp [State.setRv, State.updateRvs]

/-- Replacing one random variable leaves the others alone. -/
theorem State.rvs_setRv_ne {l' : Lbl} (hne : l' ≠ l) : (σ.setRv l c).rvs[l']? = σ.rvs[l']? := by
  simp [State.setRv, State.updateRvs, Std.ExtTreeMap.getElem?_insert, Ne.symm hne]

/-- Replacing a random variable twice keeps the last replacement. -/
@[simp]
theorem State.setRv_setRv (c' : RvCell rT) : (σ.setRv l c).setRv l c' = σ.setRv l c' := by
  unfold State.setRv State.updateRvs
  congr 1
  refine Std.ExtTreeMap.ext_getElem? fun k => ?_
  by_cases hk : l = k <;> simp [Std.ExtTreeMap.getElem?_insert, hk]

/-- Replacing a random variable by itself changes nothing. -/
theorem State.setRv_of_getElem? (h : σ.rvs[l]? = some c) : σ.setRv l c = σ := by
  unfold State.setRv State.updateRvs
  congr 1
  refine Std.ExtTreeMap.ext_getElem? fun k => ?_
  by_cases hk : l = k
  · subst hk
    simp [h]
  · simp [Std.ExtTreeMap.getElem?_insert, hk]

/-- Writing the random variable at `l' ≠ l` commutes with replacing the one at `l`. -/
theorem State.setRv_insert_comm {l' : Lbl} (hne : l' ≠ l) (c' : RvCell rT) :
    (σ.setRv l c).updateRvs (·.insert l' c') = (σ.updateRvs (·.insert l' c')).setRv l c := by
  unfold State.setRv State.updateRvs
  congr 1
  refine Std.ExtTreeMap.ext_getElem? fun k => ?_
  simp only [Std.ExtTreeMap.getElem?_insert]
  by_cases hl'k : l' = k
  · subst hl'k
    simp [Ne.symm hne]
  · by_cases hlk : l = k
    · subst hlk
      simp [hl'k]
    · simp [hl'k, hlk]

end SetRv

variable [MeasurableSpace rT]

section Measurability

theorem State.measurable_setRv : Measurable (State.setRv (rT := rT) l c) := by
  show Measurable fun σ : State rT => State.mk σ.heap σ.tapes (σ.rvs.insert l c)
  exact State.measurable_mk_param State.measurable_heap State.measurable_tapes
    ((Measurable.locHeap_insert l).comp (State.measurable_rvs.prodMk measurable_const))

theorem Cfg.measurable_setRv : Measurable (Cfg.setRv (rT := rT) l c) :=
  Cfg.measurable_iff.mpr ⟨Cfg.measurable_expr, State.measurable_setRv.comp Cfg.measurable_state⟩

@[simp]
theorem Cfg.map_dirac_setRv (ρ : Cfg rT) : (dirac ρ).map (Cfg.setRv l c) = dirac (ρ.setRv l c) :=
  map_dirac' Cfg.measurable_setRv ρ

/-- Replacing a random variable is jointly measurable in the state and the replacement. -/
theorem State.measurable_setRv_uncurry :
    Measurable (fun q : State rT × RvCell rT => q.1.setRv l q.2) := by
  show Measurable fun q : State rT × RvCell rT =>
    State.mk q.1.heap q.1.tapes (q.1.rvs.insert l q.2)
  exact State.measurable_mk_param (State.measurable_heap.comp measurable_fst)
    (State.measurable_tapes.comp measurable_fst)
    ((Measurable.locHeap_insert l).comp ((State.measurable_rvs.comp measurable_fst).prodMk
      measurable_snd))

/-- Replacing a random variable of a fixed state is measurable in the replacement. -/
theorem State.measurable_setRv_right (σ : State rT) :
    Measurable (fun c' : RvCell rT => σ.setRv l c') :=
  State.measurable_setRv_uncurry.comp (measurable_const.prodMk measurable_id)

/-- Placing a state under a fixed expression is measurable. -/
theorem Cfg.measurable_mk_right (e : Exp rT) : Measurable (Cfg.mk e : State rT → Cfg rT) :=
  Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩

/-- Replacing a random variable is jointly measurable in the replacement and the
configuration. -/
theorem Cfg.measurable_setRv_uncurry :
    Measurable (fun q : RvCell rT × Cfg rT => Cfg.setRv l q.1 q.2) :=
  Cfg.measurable_iff.mpr ⟨(Cfg.measurable_expr.comp measurable_snd :
      Measurable fun q : RvCell rT × Cfg rT => q.2.expr),
    State.measurable_setRv_uncurry.comp ((Cfg.measurable_state.comp measurable_snd).prodMk
      measurable_fst)⟩

/-- The configuration a test of the random variable at `l` reaches is measurable in the
outcome. -/
theorem measurable_testOut (σ : State rT) :
    Measurable (fun p : Int × RvCell rT => (⟨.lit (.int p.1), σ.setRv l p.2⟩ : Cfg rT)) :=
  Cfg.measurable_iff.mpr ⟨Exp.lit.measurable.comp (BaseLit.int.measurable.comp measurable_fst),
    State.measurable_setRv_uncurry.comp (measurable_const.prodMk measurable_snd)⟩

/-- The random variables allocated at `l`, as a measurable set of configurations. -/
theorem measurableSet_rv_mem :
    MeasurableSet {ρ : Cfg rT | ∃ c, ρ.state.rvs[l]? = some c} := by
  have h : {ρ : Cfg rT | ∃ c, ρ.state.rvs[l]? = some c} =
      (fun ρ : Cfg rT => ρ.state.rvs[l]?) ⁻¹' {none}ᶜ := by
    ext ρ
    exact Option.ne_none_iff_exists'.symm
  rw [h]
  exact ((LocHeap.measurable_getElem? l).comp (State.measurable_rvs.comp Cfg.measurable_state))
    MeasurableSet.singleton_none.compl

end Measurability

/-! ## Head steps that do not test the replaced random variable -/

section Frame

theorem Cfg.uniform_setRv (z : Int) :
    Cfg.uniform z (σ.setRv l c) = (Cfg.uniform z σ).map (Cfg.setRv l c) := by
  unfold Cfg.uniform
  split
  · rw [map_map Cfg.measurable_setRv .of_discrete]
    rfl
  · rw [Cfg.map_dirac_setRv]
    rfl

theorem Cfg.ffi_setRv [ProbLangFFI rT] (v : Val rT) :
    Cfg.ffi v (σ.setRv l c) = (Cfg.ffi v σ).map (Cfg.setRv l c) := by
  unfold Cfg.ffi
  rw [State.heap_setRv]
  cases ProbLangFFI.ffi (v, σ.heap) <;> simp [Option.unwrapM, Cfg.ofFFI]

theorem Cfg.sample_setRv [ProbLangDist rT] (n : ℕ) (v : Val rT) :
    Cfg.sample n v (σ.setRv l c) = (Cfg.sample n v σ).map (Cfg.setRv l c) := by
  have hg : Measurable (fun w : Val rT => (⟨.ofVal w, σ⟩ : Cfg rT)) :=
    Cfg.measurable_iff.mpr ⟨Exp.ofVal.measurable, measurable_const⟩
  unfold Cfg.sample
  rw [map_map Cfg.measurable_setRv hg]
  rfl

theorem Cfg.randvar_setRv {c₀ : RvCell rT} (hl : σ.rvs[l]? = some c₀) (n : ℕ) (v : Val rT) :
    Cfg.randvar n v (σ.setRv l c) = (Cfg.randvar n v σ).map (Cfg.setRv l c) := by
  have hfresh : (σ.setRv l c).rvs.fresh = σ.rvs.fresh := Std.ExtTreeMap.fresh_insert_of_mem σ.rvs hl
  unfold Cfg.randvar
  rw [Cfg.map_dirac_setRv, hfresh]
  simp only [Cfg.setRv_mk]
  rw [State.setRv_insert_comm (Std.ExtTreeMap.elem_fresh_ne hl)]

theorem Cfg.test_setRv [ProbLangDist rT] [ProbLangObs rT] {l' : Lbl} (hne : l' ≠ l) (k : ℕ)
    (a : Val rT) : Cfg.test k a l' (σ.setRv l c) = (Cfg.test k a l' σ).map (Cfg.setRv l c) := by
  unfold Cfg.test
  rw [State.rvs_setRv_ne hne]
  rcases hc : σ.rvs[l']? with _ | c'
  · simp
  · have hH : Measurable (fun p : Int × RvCell rT =>
        (⟨.lit (.int p.1), σ.updateRvs (·.insert l' p.2)⟩ : Cfg rT)) := by
      refine Cfg.measurable_iff.mpr ⟨Exp.lit.measurable.comp (BaseLit.int.measurable.comp
        measurable_fst), ?_⟩
      show Measurable (fun p : Int × RvCell rT =>
        State.mk σ.heap σ.tapes (σ.rvs.insert l' p.2))
      exact State.measurable_mk_param measurable_const measurable_const
        ((Measurable.locHeap_insert l').comp (measurable_const.prodMk measurable_snd))
    simp only
    rw [map_map Cfg.measurable_setRv hH]
    congr 1
    funext p
    simp only [Function.comp, Cfg.setRv_mk]
    rw [State.setRv_insert_comm hne]

end Frame

section HeadFrame

variable [LawfulProbLangℝ rT]

theorem Cfg.uniformReal_setRv :
    Cfg.uniformReal (σ.setRv l c) = (Cfg.uniformReal σ).map (Cfg.setRv l c) := by
  have hg : Measurable (fun r : rT => (⟨.lit (.real r), σ⟩ : Cfg rT)) :=
    Cfg.measurable_iff.mpr ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
  unfold Cfg.uniformReal
  rw [map_map Cfg.measurable_setRv hg]
  rfl

variable [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]

/-- A head step that does not test the random variable at `l` commutes with replacing it. -/
theorem headStep_setRv {c₀ : RvCell rT} (hl : σ.rvs[l]? = some c₀) {e : Exp rT}
    (he : ∀ k a, e ≠ .test k (.lit (.lbl l)) a) :
    headStep ⟨e, σ.setRv l c⟩ = (headStep ⟨e, σ⟩).map (Cfg.setRv l c) := by
  cases e with
  | bvar | fvar | lit | lam | fix | pair | inl | inr | fail => simp [headStep]
  | app e1 e2 => cases e1 <;> simp [headStep, Exp.isValM_map]
  | unop op e => simp [headStep, Exp.isValM_map, Option.unwrapM_map]
  | binop op e1 e2 => simp [headStep, Exp.isValM_map, Option.unwrapM_map]
  | cond ec et ef =>
    cases ec <;> try simp [headStep]
    case lit b =>
      cases b <;> try simp
      case bool b => cases b <;> simp
  | fst e => cases e <;> simp [headStep, Exp.isValM_map]
  | snd e => cases e <;> simp [headStep, Exp.isValM_map]
  | case ec el er => cases ec <;> simp [headStep, Exp.isValM_map]
  | alloc ed => rcases hv : ed.toVal? with _ | v <;> simp [headStep, hv]
  | load e =>
    cases e <;> try simp [headStep]
    case lit b =>
      cases b <;> try simp
      case loc ℓ => cases σ.heap[ℓ]? <;> simp
  | store e1 e2 =>
    cases e1 <;> try simp [headStep]
    case lit b =>
      cases b <;> try simp
      case loc ℓ =>
        rcases hv : e2.toVal? with _ | v
        · simp
        · cases σ.heap[ℓ]? <;> simp
  | tape n e => rcases hv : e.toVal? with _ | v <;> simp [headStep, hv]
  | ffi e => rcases hv : e.toVal? with _ | v <;> simp [headStep, hv, Cfg.ffi_setRv]
  | sample n e et =>
    cases et <;> try simp [headStep]
    case lit b =>
      cases b <;> try simp
      case unit =>
        rcases hv : e.toVal? with _ | v <;>
          simp [Cfg.sample_setRv]
      case lbl α =>
        rcases hv : e.toVal? with _ | v
        · simp
        ·
          rcases ht : σ.tapes[α]? with _ | t
          · simp
          · by_cases hfamily : t.name = n ∧ t.arg = v
            · rcases hhead : t.head? with _ | w
              · simp [hfamily, hhead, Cfg.sample_setRv]
              · simp [hfamily, hhead]
            · simp [hfamily, Cfg.sample_setRv]
  | scrut e p =>
    simp only [headStep, Exp.isValM_map]
    cases Pat.tryMatch p e <;> simp
  | allocN en ev =>
    cases en <;> try simp [headStep]
    case lit b =>
      cases b <;> try simp
      case int n =>
        rcases hv : ev.toVal? with _ | v
        · simp
        · by_cases hn : 0 < n <;> simp [hn]
  | randvar n e => rcases hv : e.toVal? with _ | v <;> simp [headStep, hv, Cfg.randvar_setRv hl]
  | test k ec ea =>
    cases ec <;> try simp [headStep]
    case lit b =>
      cases b <;> try simp
      case lbl l' =>
        have hne : l' ≠ l := fun h => he k ea (h ▸ rfl)
        rcases hv : ea.toVal? with _ | v <;> simp [Cfg.test_setRv hne]

end HeadFrame

/-! ## Swapping two independent draws -/

/-- Drawing from `μ` then from `ν` is drawing from `ν` then from `μ`. -/
theorem Measure.bind_map_swap {α β γ : Type _} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] {f : α → β → γ}
    (hf : Measurable (Function.uncurry f)) :
    μ.bind (fun a => ν.map (f a)) = ν.bind (fun b => μ.map (f · b)) := by
  have hfa : ∀ a, Measurable (f a) := fun a => hf.comp (measurable_const.prodMk measurable_id)
  have hfb : ∀ b, Measurable (f · b) := fun b => hf.comp (measurable_id.prodMk measurable_const)
  have hk : Measurable (fun a => ν.map (f a)) := measurable_map_const_uncurry ν hf
  have hk' : Measurable (fun b => μ.map (f · b)) :=
    measurable_map_const_uncurry μ (h := fun q : β × α => f q.2 q.1)
      (hf.comp (measurable_snd.prodMk measurable_fst))
  ext s hs
  rw [bind_apply hs hk.aemeasurable, bind_apply hs hk'.aemeasurable]
  simp_rw [map_apply (hfa _) hs, map_apply (hfb _) hs,
    ← lintegral_indicator_one (hfa _ hs), ← lintegral_indicator_one (hfb _ hs)]
  exact lintegral_lintegral_swap ((measurable_one.indicator hs).comp hf).aemeasurable

/-! ## Resolving a random variable -/

section Resolve

variable [ProbLangDist rT] [ProbLangObs rT]

/-- Resolve the random variable at `l`: draw its value from its posterior (the identity when `l`
holds no random variable). -/
def rvResolve (l : Lbl) (σ : State rT) : Measure (State rT) :=
  match σ.rvs[l]? with
  | none => dirac σ
  | some c => (c.resolve ProbLangDist.dist).map fun c' => σ.setRv l c'

/-- `rvResolve` in a configuration: resolve in its state, keep its expression. -/
def rvResolveCfg (l : Lbl) (ρ : Cfg rT) : Measure (Cfg rT) :=
  (rvResolve l ρ.state).map (Cfg.mk ρ.expr)

theorem rvResolve_of_getElem? (h : σ.rvs[l]? = some c) :
    rvResolve l σ = (c.resolve ProbLangDist.dist).map fun c' => σ.setRv l c' := by
  simp [rvResolve, h]

instance isProbabilityMeasure_rvResolve : IsProbabilityMeasure (rvResolve l σ) := by
  unfold rvResolve
  split <;> infer_instance

instance isProbabilityMeasure_rvResolveCfg (ρ : Cfg rT) : IsProbabilityMeasure (rvResolveCfg l ρ) :=
  by unfold rvResolveCfg; infer_instance

theorem measurable_rvResolve : Measurable (rvResolve (rT := rT) l) := by
  have : IsFiniteKernel (Kernel.mk (fun q : State rT × RvCell rT => q.2.resolve ProbLangDist.dist)
      (RvCell.measurable_resolve.comp measurable_snd)) :=
    ⟨1, ENNReal.one_lt_top, fun q => by rw [Kernel.coe_mk]; exact prob_le_one⟩
  have hsome : Measurable (fun q : State rT × RvCell rT =>
      (q.2.resolve ProbLangDist.dist).map fun c' => q.1.setRv l c') :=
    measurable_map_uncurry
      (State.measurable_setRv_uncurry.comp ((measurable_fst.comp measurable_fst).prodMk
        measurable_snd)) (RvCell.measurable_resolve.comp measurable_snd)
  have hrw : rvResolve (rT := rT) l = fun σ =>
      Option.casesOn (motive := fun _ => Measure (State rT)) σ.rvs[l]? (dirac σ) fun c =>
        ((σ, c).2.resolve ProbLangDist.dist).map fun c' => (σ, c).1.setRv l c' := by
    funext σ
    unfold rvResolve
    cases σ.rvs[l]? <;> rfl
  rw [hrw]
  exact Option.measurable_elim_param ((LocHeap.measurable_getElem? l).comp State.measurable_rvs)
    measurable_dirac hsome

theorem measurable_rvResolveCfg : Measurable (rvResolveCfg (rT := rT) l) := by
  have : IsFiniteKernel (Kernel.mk (fun ρ : Cfg rT => rvResolve l ρ.state)
      (measurable_rvResolve.comp Cfg.measurable_state)) :=
    ⟨1, ENNReal.one_lt_top, fun ρ => by rw [Kernel.coe_mk]; exact prob_le_one⟩
  exact measurable_map_uncurry (h := fun q : Cfg rT × State rT => Cfg.mk q.1.expr q.2)
    (Cfg.measurable_iff.mpr ⟨(Cfg.measurable_expr.comp measurable_fst :
      Measurable fun q : Cfg rT × State rT => q.1.expr), measurable_snd⟩)
    (measurable_rvResolve.comp Cfg.measurable_state)

/-- A test of an allocated random variable, as a pushforward of the test of its cell. -/
theorem Cfg.test_eq_map_testCell {k : ℕ} {a : Val rT} {c : RvCell rT} (h : σ.rvs[l]? = some c) :
    Cfg.test k a l σ =
      (c.testCell ProbLangDist.dist k a).map fun p => ⟨.lit (.int p.1), σ.setRv l p.2⟩ := by
  simp only [Cfg.test, h]
  rfl

/-- A test of a resolved random variable reads the observation off its value. -/
theorem Cfg.test_resolveTo {k : ℕ}
    {a x : Val rT} {c : RvCell rT} (h : σ.rvs[l]? = some (c.resolveTo x)) :
    Cfg.test k a l σ = dirac ⟨.lit (.int (ProbLangObs.obs k (a, x))),
      σ.setRv l ((c.resolveTo x).observe k a (ProbLangObs.obs k (a, x)))⟩ := by
  rw [Cfg.test_eq_map_testCell h, RvCell.testCell, RvCell.post_resolveTo,
    map_dirac' (RvCell.measurable_testOutcome _ k a), map_dirac' (measurable_testOut σ)]

/-- Resolving a random variable with no observations draws its value from its prior. -/
theorem rvResolve_fresh {n : ℕ} {v : Val rT} [IsProbabilityMeasure (ProbLangDist.dist n v)]
    (h : σ.rvs[l]? = some (RvCell.fresh n v)) :
    rvResolve l σ =
      (ProbLangDist.dist n v).map fun x => σ.setRv l ((RvCell.fresh n v).resolveTo x) := by
  rw [rvResolve_of_getElem? h, RvCell.resolve, RvCell.post_fresh,
    ite_eq_right (IsProbabilityMeasure.ne_zero _), map_map (State.measurable_setRv_right σ)
      (RvCell.measurable_resolveTo _)]
  rfl

end Resolve

/-! ## Resolving commutes with a head step -/

section Commute

variable [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
  {c₀ : RvCell rT} (e : Exp rT)

instance isFiniteMeasure_headStep (ρ : Cfg rT) : IsFiniteMeasure (headStep ρ) :=
  ⟨(headStep_univ_le_one ρ).trans_lt ENNReal.one_lt_top⟩

theorem measurable_headStep_state :
    Measurable (fun τ : State rT => headStep ⟨e, τ⟩) :=
  headStep.measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)

theorem measurable_primStep_state :
    Measurable (fun τ : State rT => primStep ⟨e, τ⟩) :=
  primStep.measurable.comp (Cfg.measurable_mk_right e)

/-- A prim step, as the head step of the redex under its context. -/
theorem primStep_eq_map_decomp (τ : State rT) :
    primStep ⟨e, τ⟩ = (headStep ⟨e.decomp.2, τ⟩).map e.decomp.1.fillCfg :=
  rfl

section

variable (hl : σ.rvs[l]? = some c₀)

include hl

/-- A head step that does not test the random variable at `l` keeps it. -/
theorem headStep_eq_map_setRv_self {e : Exp rT}
    (he : ∀ k a, e ≠ .test k (.lit (.lbl l)) a) :
    headStep ⟨e, σ⟩ = (headStep ⟨e, σ⟩).map (Cfg.setRv l c₀) := by
  conv_lhs => rw [← State.setRv_of_getElem? hl]
  exact headStep_setRv hl he

/-- Resolving the random variable at `l` commutes with a head step. -/
theorem rvResolve_bind_headStep :
    (rvResolve l σ).bind (fun τ => headStep ⟨e, τ⟩) = (headStep ⟨e, σ⟩).bind (rvResolveCfg l) := by
  have hL : (rvResolve l σ).bind (fun τ => headStep ⟨e, τ⟩) =
      (c₀.resolve ProbLangDist.dist).bind fun c' => headStep ⟨e, σ.setRv l c'⟩ := by
    rw [rvResolve_of_getElem? hl, bind_map (State.measurable_setRv_right σ).aemeasurable
      (measurable_headStep_state e).aemeasurable]
  rw [hL]
  by_cases ht : ∃ k a, e = .test k (.lit (.lbl l)) a
  · -- testing the random variable itself: Bayes
    obtain ⟨k, a, rfl⟩ := ht
    rcases hv : a.toVal? with _ | v
    · simp [headStep, hv]
    · have hstep : ∀ τ : State rT, headStep ⟨.test k (.lit (.lbl l)) a, τ⟩ = Cfg.test k v l τ :=
        fun τ => by simp [headStep, hv]
      set G : Int × RvCell rT → Cfg rT := fun p => ⟨.lit (.int p.1), σ.setRv l p.2⟩ with hG_def
      have hG : Measurable G := measurable_testOut σ
      have hT := RvCell.measurable_testCell (D := ProbLangDist.dist (rT := rT)) k v
      have hk : Measurable (fun p : Int × RvCell rT => p.2.resolve ProbLangDist.dist) :=
        RvCell.measurable_resolve.comp measurable_snd
      have : IsFiniteKernel (Kernel.mk _ hk) :=
        ⟨1, ENNReal.one_lt_top, fun p => by rw [Kernel.coe_mk]; exact prob_le_one⟩
      have hpair : Measurable (fun p : Int × RvCell rT =>
          (p.2.resolve ProbLangDist.dist).map (p.1, ·)) :=
        measurable_map_uncurry (h := fun q : (Int × RvCell rT) × RvCell rT => (q.1.1, q.2))
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd) hk
      -- resolving first, then testing
      have hleft : ((c₀.resolve ProbLangDist.dist).bind fun c' =>
          headStep ⟨.test k (.lit (.lbl l)) a, σ.setRv l c'⟩) =
          ((c₀.resolve ProbLangDist.dist).bind (RvCell.testCell ProbLangDist.dist k v)).map G := by
        rw [map_bind hT.aemeasurable hG.aemeasurable]
        refine bind_congr_right (ae_of_all _ fun c' => ?_)
        dsimp only
        rw [hstep, Cfg.test_eq_map_testCell State.rvs_setRv_self]
        refine congrArg (fun f => map f (c'.testCell ProbLangDist.dist k v)) ?_
        funext p
        simp only [hG_def, State.setRv_setRv]
      -- testing first, then resolving
      have hright : (headStep ⟨.test k (.lit (.lbl l)) a, σ⟩).bind (rvResolveCfg l) =
          ((c₀.testCell ProbLangDist.dist k v).bind fun p =>
            (p.2.resolve ProbLangDist.dist).map (p.1, ·)).map G := by
        rw [hstep, Cfg.test_eq_map_testCell hl, bind_map hG.aemeasurable
          measurable_rvResolveCfg.aemeasurable, map_bind hpair.aemeasurable hG.aemeasurable]
        refine bind_congr_right (ae_of_all _ fun p => ?_)
        dsimp only [rvResolveCfg, hG_def]
        rw [rvResolve_of_getElem? State.rvs_setRv_self,
          map_map (Cfg.measurable_mk_right _) (State.measurable_setRv_right _),
          map_map hG measurable_prodMk_left]
        refine congrArg (fun f => map f (p.2.resolve ProbLangDist.dist)) ?_
        funext c'
        simp only [hG_def, Function.comp, State.setRv_setRv]
      rw [hleft, hright, RvCell.resolve_bind_testCell]
  · -- any other step does not read the random variable, so the two draws are independent
    push Not at ht
    have hleft : ((c₀.resolve ProbLangDist.dist).bind fun c' => headStep ⟨e, σ.setRv l c'⟩) =
        (c₀.resolve ProbLangDist.dist).bind fun c' => (headStep ⟨e, σ⟩).map (Cfg.setRv l c') :=
      bind_congr_right (ae_of_all _ fun c' => headStep_setRv hl ht)
    have hright : (headStep ⟨e, σ⟩).bind (rvResolveCfg l) =
        (headStep ⟨e, σ⟩).bind fun ρ => (c₀.resolve ProbLangDist.dist).map (Cfg.setRv l · ρ) := by
      conv_lhs => rw [headStep_eq_map_setRv_self hl ht]
      rw [Measure.bind_map Cfg.measurable_setRv.aemeasurable measurable_rvResolveCfg.aemeasurable]
      refine bind_congr_right (ae_of_all _ fun ρ => ?_)
      dsimp only [rvResolveCfg, Cfg.setRv]
      rw [rvResolve_of_getElem? State.rvs_setRv_self,
        map_map (Cfg.measurable_mk_right _) (State.measurable_setRv_right _)]
      refine congrArg (fun f => map f (c₀.resolve ProbLangDist.dist)) ?_
      funext c'
      simp only [Function.comp, State.setRv_setRv]
    rw [hleft, hright]
    exact Measure.bind_map_swap (f := fun c' ρ => Cfg.setRv l c' ρ) _ _ Cfg.measurable_setRv_uncurry

/-- A head step keeps the random variable at `l` allocated. -/
theorem headStep_ae_rv_mem :
    ∀ᵐ ρ ∂headStep ⟨e, σ⟩, ∃ c, ρ.state.rvs[l]? = some c := by
  by_cases ht : ∃ k a, e = .test k (.lit (.lbl l)) a
  · obtain ⟨k, a, rfl⟩ := ht
    rcases hv : a.toVal? with _ | v
    · simp [headStep, hv]
    · have hstep : headStep ⟨.test k (.lit (.lbl l)) a, σ⟩ = Cfg.test k v l σ := by
        simp [headStep, hv]
      rw [hstep, Cfg.test_eq_map_testCell hl]
      exact (ae_map_iff (measurable_testOut σ).aemeasurable measurableSet_rv_mem).mpr
        (ae_of_all _ fun p => ⟨p.2, State.rvs_setRv_self⟩)
  · push Not at ht
    rw [headStep_eq_map_setRv_self hl ht]
    exact (ae_map_iff Cfg.measurable_setRv.aemeasurable measurableSet_rv_mem).mpr
      (ae_of_all _ fun _ => ⟨c₀, State.rvs_setRv_self⟩)

/-- Resolving the random variable at `l` commutes with a prim step. -/
theorem rvResolve_bind_primStep :
    (rvResolve l σ).bind (fun τ => primStep ⟨e, τ⟩) = (primStep ⟨e, σ⟩).bind (rvResolveCfg l) := by
  have hfill := Ectx.fillCfg.measurable e.decomp.1
  simp only [primStep_eq_map_decomp]
  rw [← map_bind (measurable_headStep_state _).aemeasurable hfill.aemeasurable,
    rvResolve_bind_headStep _ hl, map_bind measurable_rvResolveCfg.aemeasurable
      hfill.aemeasurable, bind_map hfill.aemeasurable measurable_rvResolveCfg.aemeasurable]
  refine bind_congr_right (ae_of_all _ fun ρ => ?_)
  dsimp only [rvResolveCfg]
  rw [map_map hfill (Cfg.measurable_mk_right _)]
  rfl

/-- A prim step keeps the random variable at `l` allocated. -/
theorem primStep_ae_rv_mem :
    ∀ᵐ ρ ∂primStep ⟨e, σ⟩, ∃ c, ρ.state.rvs[l]? = some c := by
  rw [primStep_eq_map_decomp]
  exact (ae_map_iff (Ectx.fillCfg.measurable _).aemeasurable measurableSet_rv_mem).mpr
    (headStep_ae_rv_mem _ hl)

end

/-- Resolving an allocated random variable commutes with running a program for `m` steps. -/
theorem rvResolve_bind_execN (m : ℕ) : ∀ (e : Exp rT) (σ : State rT), (∃ c, σ.rvs[l]? = some c) →
    (rvResolve l σ).bind (fun τ => execN m ⟨e, τ⟩) = (execN m ⟨e, σ⟩).bind (rvResolveCfg l) := by
  induction m with
  | zero => intro e σ _; simp [execN]
  | succ m ih =>
    intro e σ ⟨c₀, hl⟩
    by_cases hv : e.isValue
    · have h1 : ∀ τ : State rT, execN (m + 1) ⟨e, τ⟩ = dirac ⟨e, τ⟩ :=
        fun τ => execN_succ_isValue hv m
      simp only [h1]
      rw [bind_dirac_eq_map _ (Cfg.measurable_mk_right e), dirac_bind measurable_rvResolveCfg]
      rfl
    · have h1 : ∀ τ : State rT, execN (m + 1) ⟨e, τ⟩ = (primStep ⟨e, τ⟩).bind (execN m) :=
        fun τ => execN_succ_not_isValue hv m
      simp only [h1]
      rw [← bind_bind (measurable_primStep_state e).aemeasurable
          (execN_measurable m).aemeasurable, rvResolve_bind_primStep e hl,
        bind_bind measurable_rvResolveCfg.aemeasurable (execN_measurable m).aemeasurable,
        bind_bind (execN_measurable m).aemeasurable measurable_rvResolveCfg.aemeasurable]
      refine bind_congr_right ?_
      filter_upwards [primStep_ae_rv_mem e hl] with ρ hρ
      dsimp only [rvResolveCfg]
      rw [Measure.bind_map (Cfg.measurable_mk_right _).aemeasurable
        (execN_measurable m).aemeasurable]
      exact ih ρ.expr ρ.state hρ

end Commute

/-! ## Erasure -/

section Erasure

variable [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] {l : Lbl}
  {σ : State rT}

/-- Drawing the value of an allocated random variable from its posterior before a run leaves the
distribution of every bounded run's result unchanged. -/
theorem ErasableExpr.rvResolve (hl : ∃ c, σ.rvs[l]? = some c) :
    ErasableExpr (ProbLang.rvResolve l σ) σ := by
  intro e m
  rw [rvResolve_bind_execN m e σ hl, asExpr, asExpr, Measure.map_bind
    measurable_rvResolveCfg.aemeasurable Cfg.measurable_expr.aemeasurable,
    ← bind_dirac_eq_map _ Cfg.measurable_expr]
  refine bind_congr_right (ae_of_all _ fun ρ => ?_)
  dsimp only [rvResolveCfg]
  rw [map_map Cfg.measurable_expr (Cfg.measurable_mk_right _),
    show Cfg.expr ∘ Cfg.mk ρ.expr = fun _ : State rT => ρ.expr from rfl, Measure.map_const,
    measure_univ, one_smul]

/-- A run from a state with an unobserved random variable has the result distribution of drawing
its value from the prior first and running from the state where it is resolved to that value. -/
theorem asExpr_execN_eq_bind_prior {n : ℕ} {v : Val rT}
    [IsProbabilityMeasure (ProbLangDist.dist n v)] (h : σ.rvs[l]? = some (RvCell.fresh n v))
    (e : Exp rT) (m : ℕ) :
    asExpr (execN m ⟨e, σ⟩) = (ProbLangDist.dist n v).bind fun x =>
      asExpr (execN m ⟨e, σ.setRv l ((RvCell.fresh n v).resolveTo x)⟩) := by
  have hres : Measurable fun x : Val rT => σ.setRv l ((RvCell.fresh n v).resolveTo x) :=
    (State.measurable_setRv_right σ).comp (RvCell.measurable_resolveTo _)
  have hk : Measurable fun τ : State rT => execN m (⟨e, τ⟩ : Cfg rT) :=
    (execN_measurable m).comp (Cfg.measurable_mk_right e)
  have hk' : Measurable fun τ : State rT => asExpr (execN m (⟨e, τ⟩ : Cfg rT)) :=
    asExpr.measurable.comp hk
  rw [← ErasableExpr.rvResolve ⟨_, h⟩ e m, rvResolve_fresh h, asExpr_bind _ _ hk,
    bind_map hres.aemeasurable hk'.aemeasurable]

/-- Erasure of random variables, for the limit of the run. -/
theorem limExecV_rvResolve (hl : ∃ c, σ.rvs[l]? = some c) (e : Exp rT) :
    asExpr ((ProbLang.rvResolve l σ).bind fun σ' => limExec ⟨e, σ'⟩) = limExecV ⟨e, σ⟩ :=
  (ErasableExpr.rvResolve hl).lim_exec e

end Erasure

end ProbLang
