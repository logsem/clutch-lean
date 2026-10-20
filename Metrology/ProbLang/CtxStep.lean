module

public meta import Metrology.Meta.Discrete
public import Metrology.ProbLang.Measure
public import Metrology.Couplings.SubProbability
public import Metrology.ProbLang.HeadStep
public import Metrology.ProbLang.Discrete

@[expose] public section

/-! # Primitive step

The step of `Cfg` that decomposes into an evaluation context and a head step, and its basic laws. -/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

variable {rT : Type _}

/-- Plugs the expression of a configuration into the context `K`. -/
@[simp] def Ectx.fillCfg [LawfulProbLangℝ rT] (K : Ectx rT) (ρ : Cfg rT) : Cfg rT :=
  ⟨K.fill ρ.expr, ρ.state⟩

theorem Ectx.fillCfg_comp [LawfulProbLangℝ rT] (K1 K2 : Ectx rT) :
    (K1.comp K2).fillCfg = K1.fillCfg ∘ K2.fillCfg := by
  funext ⟨e, σ⟩; simp [Ectx.fill_comp]

@[simp]
theorem Ectx.fillCfg_empty [LawfulProbLangℝ rT] : Ectx.fillCfg ([] : Ectx rT) = id := by
  funext ⟨e, σ⟩; simp [Ectx.fillCfg, Ectx.fill]

theorem Ectx.fillCfg_injective [LawfulProbLangℝ rT] (K : Ectx rT) :
    Function.Injective K.fillCfg := by
  rintro ⟨e1, σ1⟩ ⟨e2, σ2⟩ h
  simpa [Cfg.mk.injEq, Ectx.fill_injective K |>.eq_iff] using h

@[fun_prop]
theorem Ectx.fillCfg.measurable [LawfulProbLangℝ rT] (K : Ectx rT) :
    Measurable K.fillCfg := by
  rw [Cfg.measurable_iff]
  exact ⟨Exp.Ectx_fill.measurable.comp (measurable_const.prodMk Cfg.measurable_expr),
    Cfg.measurable_state⟩

theorem EctxItem.fillItem.measurableEmbedding [LawfulProbLangℝ rT] (Ki : EctxItem rT) :
    MeasurableEmbedding Ki.fillItem := by
  cases Ki with
  | appL v2 => exact Exp.app.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)
  | appR e1 => exact Exp.app.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | unop op => exact Exp.unop.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | binopL op v2 =>
      exact Exp.binop.measurableEmbedding.comp
        (MeasurableEmbedding.prodMk_left _ (measurableEmbedding_prod_mk_right _))
  | binopR op e1 =>
      exact Exp.binop.measurableEmbedding.comp
        (MeasurableEmbedding.prodMk_left _ (measurableEmbedding_prodMk_left _))
  | condC e1 e2 =>
      exact Exp.cond.measurableEmbedding.comp (measurableEmbedding_prod_mk_right (e1, e2))
  | pairL v2 => exact Exp.pair.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)
  | pairR e1 => exact Exp.pair.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | fst => exact Exp.fst.measurableEmbedding
  | snd => exact Exp.snd.measurableEmbedding
  | inl => exact Exp.inl.measurableEmbedding
  | inr => exact Exp.inr.measurableEmbedding
  | case e1 e2 =>
      exact Exp.case.measurableEmbedding.comp (measurableEmbedding_prod_mk_right (e1, e2))
  | alloc => exact Exp.alloc.measurableEmbedding
  | load => exact Exp.load.measurableEmbedding
  | storeL v2 => exact Exp.store.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)
  | storeR e1 => exact Exp.store.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | tape => exact Exp.tape.measurableEmbedding
  | randL v2 => exact Exp.rand.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)
  | randR e1 => exact Exp.rand.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | scrut p => exact Exp.scrut.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)

theorem Ectx.fill.measurableEmbedding [LawfulProbLangℝ rT] (K : Ectx rT) :
    MeasurableEmbedding K.fill := by
  induction K with
  | nil => exact MeasurableEmbedding.id
  | cons Ki K ih => exact ih.comp (EctxItem.fillItem.measurableEmbedding Ki)

/-- A configuration is a pair of expression and state. -/
def Cfg.measurableEquivProd [LawfulProbLangℝ rT] : Cfg rT ≃ᵐ Exp rT × State rT where
  toFun ρ := (ρ.expr, ρ.state)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := Cfg.measurable_expr.prodMk Cfg.measurable_state
  measurable_invFun := Cfg.measurable_mk

theorem Ectx.fillCfg.measurableEmbedding [LawfulProbLangℝ rT] (K : Ectx rT) :
    MeasurableEmbedding K.fillCfg := by
  have h : K.fillCfg
      = Cfg.measurableEquivProd.symm ∘ Prod.map K.fill id ∘ Cfg.measurableEquivProd := by
    funext ρ; rfl
  rw [h]
  exact (Cfg.measurableEquivProd.symm.measurableEmbedding.comp
    ((Ectx.fill.measurableEmbedding K).prodMap MeasurableEmbedding.id)).comp
    Cfg.measurableEquivProd.measurableEmbedding

/-- Needed by `glm'_bind`, whose transported support predicate is `K.fillCfg '' {R}`. -/
theorem Ectx.measurableSet_fillCfg_image [LawfulProbLangℝ rT] (K : Ectx rT)
    {S : Set (Cfg rT)} (hS : MeasurableSet S) : MeasurableSet (K.fillCfg '' S) :=
  (Ectx.fillCfg.measurableEmbedding K).measurableSet_image' hS

/-- Plugs the expression of a configuration into the context item `K`. -/
@[simp] def EctxItem.fillItemCfg [LawfulProbLangℝ rT] (K : EctxItem rT) (ρ : Cfg rT) : Cfg rT :=
  ⟨K.fillItem ρ.expr, ρ.state⟩

theorem EctxItem.fillItemCfg_injective [LawfulProbLangℝ rT] (K : EctxItem rT) :
    Function.Injective K.fillItemCfg := by
  rintro ⟨e1, σ1⟩ ⟨e2, σ2⟩ ha
  simp only [EctxItem.fillItemCfg, Cfg.mk.injEq] at ha
  have _ := @Ectx.fillItem_injective rT K e1 e2
  grind

/-- One step of the primitive semantics: decompose into a context and a redex, take a head step. -/
def primStep [LawfulProbLangℝ rT] (cfg : Cfg rT) : Measure (Cfg rT) :=
  let (K, e') := cfg.expr.decomp
  (headStep ⟨e', cfg.state⟩).map K.fillCfg

@[fun_prop]
theorem primStep.measurable [LawfulProbLangℝ rT] :
    Measurable (primStep : Cfg rT → Measure (Cfg rT)) := by
  have hk : Measurable fun cfg : Cfg rT => headStep ⟨cfg.expr.decomp.2, cfg.state⟩ :=
    headStep.measurable.comp (by measurability)
  have hh : Measurable fun p : Cfg rT × Cfg rT => p.1.expr.decomp.1.fillCfg p.2 := by
    rw [Cfg.measurable_iff]
    exact ⟨Exp.Ectx_fill.measurable.comp ((by measurability : Measurable _).prodMk
      (by measurability)), by measurability⟩
  have : IsFiniteKernel (Kernel.mk _ hk) :=
    ⟨1, ENNReal.one_lt_top, fun _ => headStep_univ_le_one _⟩
  exact Measure.measurable_map_uncurry hh hk

/-- `primStep` as a kernel. -/
def primStepKernel [LawfulProbLangℝ rT] : Kernel (Cfg rT) (Cfg rT) where
  measurable' := primStep.measurable
  toFun := primStep

/-- Some configuration is reached with positive probability (discrete form of `Reducible`). -/
@[discrete]
abbrev Discrete.Reducible [LawfulProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  ∃ ρ : Cfg rT, 0 < primStep ⟨e, σ⟩ {ρ}

/-- The expression can take a step. -/
abbrev Reducible [LawfulProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  primStep ⟨e, σ⟩ ≠ 0

/-- The converse is `Reducible.toDiscrete`. -/
@[discrete]
theorem Discrete.Reducible.toReducible [LawfulProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (h : Discrete.Reducible e σ) : _root_.ProbLang.Reducible e σ := by
  obtain ⟨ρ, hρ⟩ := h
  intro hz
  rw [hz] at hρ
  simp at hρ

/-! ## Values can't step -/

theorem val_stuck [LawfulProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (h : primStep ⟨e, σ⟩ ≠ 0) : ¬e.isValue := by
  simp only [primStep] at h
  set d := e.decomp with hd
  rw [← Exp.decomp_fill hd.symm]
  refine Ectx.fill_noVal (val_head_stuck (σ := σ) fun hz => ?_)
  rw [hz] at h; simp at h

theorem primStep_univ_le_one [LawfulProbLangℝ rT] (ρ : Cfg rT) : (primStep ρ) Set.univ ≤ 1 := by
  obtain ⟨e, σ⟩ := ρ
  simp only [primStep]
  have Hmeas : Measurable e.decomp.1.fillCfg := by measurability
  rw [Measure.map_apply Hmeas MeasurableSet.univ]
  simpa using headStep_univ_le_one ⟨e.decomp.2, σ⟩

/-- One step of the primitive semantics has mass at most one. -/
instance primStep.isSubProbabilityMeasure [LawfulProbLangℝ rT] (ρ : Cfg rT) :
    IsSubProbabilityMeasure (primStep ρ) :=
  ⟨primStep_univ_le_one ρ⟩

theorem prim_step_mass [LawfulProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (hred : Reducible e σ) : IsProbabilityMeasure (primStep ⟨e, σ⟩) := by
  have hhs : headStep ⟨e.decomp.2, σ⟩ ≠ 0 := fun h => hred (by simp [primStep, h])
  have := head_step_mass hhs
  simp only [primStep]
  infer_instance

/-! ## Bridge: headStep ↔ primStep -/

/-- Without local closedness a value-shaped but non-closed subterm (e.g. a non-closed
`lam`) could still be focused. -/
theorem Exp.decompItem_none_of_lc_headReducible [LawfulProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (he : e.IsLocallyClosed) (hred : headStep ⟨e, σ⟩ ≠ 0) : e.decompItem = none := by
  cases H : e.decompItem with
  | none => rfl
  | some redex =>
    obtain ⟨K, e'⟩ := redex
    obtain ⟨hfill, hne⟩ := Exp.decompItem_fill H
    exfalso
    have he' : e'.IsLocallyClosed := EctxItem.fillItem_isLocallyClosed (hfill ▸ he)
    exact hne (Exp.isValue_iff_isValueR.mpr ⟨head_ctx_step_val (hfill ▸ hred), Exp.lc_imp_lcb he'⟩)

/-- With no context to peel off, `primStep` is `headStep`. The hypothesis is weaker than local
closedness: the branches of an `if` need not be closed. -/
theorem primStep_eq_headStep [LawfulProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (hdec : e.decompItem = none) :
    primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  suffices hd : e.decomp = ([], e) by simp [primStep, hd]
  unfold Exp.decomp; rw [hdec]

theorem reducible_of_headReducible [LawfulProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (he : e.IsLocallyClosed)
    (h : HeadReducible e σ) : Reducible e σ := by
  unfold Reducible
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible he h)]
  exact h

/-! ## Context fill interaction with primStep -/

theorem primStep_fill [LawfulProbLangℝ rT] {K : Ectx rT} {e : Exp rT} {σ : State rT}
    (hv : ¬e.isValue) :
    primStep ⟨K.fill e, σ⟩ = (primStep ⟨e, σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  simp only [primStep]
  set d := e.decomp with hd
  obtain ⟨K', e''⟩ := d
  simp only [Exp.decomp_fill_comp hv hd.symm]
  rw [Measure.map_map (by measurability) (by measurability)]
  congr 1
  funext ⟨e', σ'⟩
  simp [Function.comp, Ectx.fill_append]

theorem primStep_fillItem [LawfulProbLangℝ rT]
    (Ki : EctxItem rT) {e : Exp rT} {σ : State rT} (hv : ¬e.isValue) :
    primStep ⟨Ki.fillItem e, σ⟩ =
      (primStep ⟨e, σ⟩).map (fun ρ => ⟨Ki.fillItem ρ.expr, ρ.state⟩) := by
  have : Ki.fillItem e = Ectx.fill [Ki] e := by simp [Ectx.fill, List.foldl, flip]
  rw [this, primStep_fill hv]; congr 1

-- TODO: This generalized to continuous, though really I imagine it can't be used in any
-- continuous way. I won't mark it as discrete, but I'd guess this should really be changed to be
-- primStep_fill
theorem primStep_fill_singleton [LawfulProbLangℝ rT] {K : Ectx rT} {e1 e2 : Exp rT}
    {σ1 σ2 : State rT} (hv : ¬e1.isValue) :
    primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} = primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rw [primStep_fill hv, Measure.map_apply (by measurability) (measurableSet_singleton _)]
  congr 1
  ext ⟨e', σ'⟩
  simp [(Ectx.fill_injective K).eq_iff]

theorem primStep_fill_pos [LawfulProbLangℝ rT] {K : Ectx rT} {e : Exp rT} {σ : State rT}
    (h : primStep ⟨e, σ⟩ ≠ 0) : primStep ⟨K.fill e, σ⟩ ≠ 0 := by
  by_cases hk : e.isValue
  · exact val_stuck h hk |>.elim
  · rw [primStep_fill hk]
    have hm : Measurable (fun ρ : Cfg rT ↦ (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT)) := by measurability
    refine fun H => h ?_
    refine Measure.measure_univ_eq_zero.mp ?_
    have := H ▸ Measure.map_apply hm .univ
    simpa using this.symm

theorem primStep_fill_inv [LawfulProbLangℝ rT] {K : Ectx rT} {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (hv : ¬e1.isValue) (h : 0 < primStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩}) :
    ∃ e2', e2 = K.fill e2' ∧ 0 < primStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} := by
  rw [primStep_fill hv] at h
  obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ :=
    map_singleton_pos (by measurability) (Ectx.fillCfg_injective K) h
  simp [Cfg.mk.injEq] at heq
  exact ⟨e2', heq.1.symm, heq.2 ▸ hpos⟩

/-! ## Reducible: fill interaction -/

theorem Reducible.fill [LawfulProbLangℝ rT] (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hred : Reducible e σ) : Reducible (K.fill e) σ :=
  primStep_fill_pos hred

theorem Reducible.of_fill [LawfulProbLangℝ rT] (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hv : ¬e.isValue) (hred : Reducible (K.fill e) σ) : Reducible e σ := by
  unfold Reducible at hred ⊢
  rw [primStep_fill hv] at hred
  exact fun h0 => hred (by rw [h0]; simp)

theorem Reducible.of_head_fill [LawfulProbLangℝ rT] (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (he : e.IsLocallyClosed)
    (hred : HeadReducible e σ) : Reducible (K.fill e) σ :=
  (reducible_of_headReducible he hred).fill K

/-! ## Irreducible: contrapositives -/

theorem irreducible_fill [LawfulProbLangℝ rT] (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hv : ¬e.isValue) (hirr : ¬ Reducible e σ) : ¬ Reducible (K.fill e) σ :=
  fun hr => hirr (hr.of_fill K hv)

theorem irreducible_fill_inv [LawfulProbLangℝ rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hirr : ¬ Reducible (K.fill e) σ) : ¬ Reducible e σ :=
  fun hred => hirr (hred.fill K)

theorem Reducible.headStep_zero [LawfulProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (he : e.IsLocallyClosed) (hirr : ¬ Reducible e σ) :
    headStep ⟨e, σ⟩ = 0 := by
  by_contra h; exact hirr <| reducible_of_headReducible he h

/-! ## Context decomposition -/

theorem head_ctx_step_val_ectx [LawfulProbLangℝ rT] (K : Ectx rT) (e : Exp rT) (σ : State rT)
    (hstep : HeadReducible (K.fill e) σ) : e.isValueR ∨ K = [] := by
  rcases List.eq_nil_or_concat' K with rfl | ⟨K'', Ki, rfl⟩
  · exact .inr rfl
  · simp only [Ectx.fill_snoc] at hstep
    exact .inl (Ectx.fill_isValueR (head_ctx_step_val hstep))

theorem step_by_val [LawfulProbLangℝ rT] (K' K_redex : Ectx rT) (e1' e1_redex : Exp rT)
    (σ : State rT)
    (hfill : K'.fill e1' = K_redex.fill e1_redex)
    (hv : ¬e1'.isValueR)
    (hstep : HeadReducible e1_redex σ) :
    ∃ K'' : Ectx rT, K_redex = K'.comp K'' := by
  induction K' using List.reverseRecOn generalizing K_redex e1_redex with
  | nil => exact ⟨K_redex, (List.append_nil K_redex).symm⟩
  | append_singleton K'_rest Ki' ih =>
    simp only [Ectx.fill_snoc] at hfill
    rcases List.eq_nil_or_concat' K_redex with rfl | ⟨K_redex_rest, Ki_redex, rfl⟩
    · simp only [Ectx.fill, List.foldl_nil] at hfill
      subst hfill
      exact absurd (Ectx.fill_isValueR (head_ctx_step_val hstep)) hv
    · simp only [Ectx.fill_snoc] at hfill ⊢
      have hKi := EctxItem.fillItem_noVal_inj
        (Ectx.fill_noVal (Exp.not_isValue_of_not_isValueR hv))
        (Ectx.fill_noVal (val_head_stuck hstep)) hfill
      subst hKi
      obtain ⟨K'', hK''⟩ := ih K_redex_rest e1_redex (Ectx.fillItem_injective hfill) hstep
      exact ⟨K'', by rw [hK'']; simp [Ectx.comp, List.append_assoc]⟩

theorem not_headReducible_iff [LawfulProbLangℝ rT] {e : Exp rT} {σ : State rT} :
    (¬ HeadReducible e σ) ↔ (headStep ⟨e, σ⟩ = 0) := by
  push Not
  rfl

theorem head_redex_unique [LawfulProbLangℝ rT] (K K' : Ectx rT) (e e' : Exp rT) (σ : State rT)
    (hfill : K.fill e = K'.fill e') (hred : HeadReducible e σ) (hred' : HeadReducible e' σ) :
    -- FIXME: Make this just be K = K'
    K = K'.comp [] ∧ e = e' := by
  obtain ⟨K'', rfl⟩ := step_by_val K K' e e' σ hfill (val_head_stuck_R hred) hred'
  rw [← Ectx.fill_comp] at hfill
  have he := Ectx.fill_injective _ hfill
  rcases @head_ctx_step_val_ectx rT _ K'' e' σ (he ▸ hred) with hval | rfl
  · exact absurd hval (val_head_stuck_R hred')
  · simp [Ectx.fill] at he
    exact ⟨rfl, he⟩

/-! ## primStep characterization -/

/-- Unlike `prim_step_iff`, needs no local closedness. -/
theorem prim_step_imp [LawfulProbLangℝ rT]
    {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : Possible (⟨e2, σ2⟩ : Cfg rT) (primStep ⟨e1, σ1⟩)) :
    ∃ (K : Ectx rT) (e1' e2' : Exp rT),
      K.fill e1' = e1 ∧
      K.fill e2' = e2 ∧
      Possible (⟨e2', σ2⟩ : Cfg rT) (headStep ⟨e1', σ1⟩) := by
  rw [possible_iff_pos] at h
  simp only [primStep] at h
  set d := e1.decomp with hd; obtain ⟨K, e1'⟩ := d
  obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ :=
    map_singleton_pos (by measurability) (Ectx.fillCfg_injective K) h
  simp [Ectx.fillCfg, Cfg.mk.injEq] at heq
  exact ⟨K, e1', e2', Exp.decomp_fill hd.symm, heq.1, possible_iff_pos.mpr (heq.2 ▸ hpos)⟩

theorem prim_step_iff [LawfulProbLangℝ rT]
    {e1 e2 : Exp rT} {σ1 σ2 : State rT} (he1 : e1.IsLocallyClosed) :
    Possible (⟨e2, σ2⟩ : Cfg rT) (primStep ⟨e1, σ1⟩) ↔
    ∃ (K : Ectx rT) (e1' e2' : Exp rT),
      K.fill e1' = e1 ∧
      K.fill e2' = e2 ∧
      Possible (⟨e2', σ2⟩ : Cfg rT) (headStep ⟨e1', σ1⟩) := by
  refine ⟨prim_step_imp, ?_⟩
  rintro ⟨K, e1', e2', rfl, rfl, hhs⟩
  rw [possible_iff_pos] at hhs ⊢
  have hred : HeadReducible e1' σ1 := fun h0 => by simp [h0] at hhs
  rw [← primStep_fill_singleton (val_head_stuck hred),
    primStep_eq_headStep
      (Exp.decompItem_none_of_lc_headReducible (Ectx.fill_isLocallyClosed he1) hred)]
  exact hhs

/-! ## subRedexesAreValues -/

/-- Every non-value subterm of `e` is under the empty context. -/
def subRedexesAreValues [LawfulProbLangℝ rT] (e : Exp rT) : Prop :=
  ∀ (K : Ectx rT) (e' : Exp rT), e = K.fill e' → ¬e'.isValue → K = []

theorem ectxi_language_subRedexesAreValues [LawfulProbLangℝ rT] {e : Exp rT}
    (h : ∀ (Ki : EctxItem rT) (e' : Exp rT), e = Ki.fillItem e' → e'.isValue) :
    subRedexesAreValues e := by
  intro K e' hfill hv
  rcases List.eq_nil_or_concat' K with rfl | ⟨K'', Ki, rfl⟩
  · rfl
  · simp only [Ectx.fill_snoc] at hfill
    exact absurd (Ectx.fill_isValue (h Ki _ hfill)) hv

/-! ## notStuck_discrete / stuck_discrete -/

/-- The expression is a value or can step. -/
def notStuck [LawfulProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  e.isValue ∨ Reducible e σ

theorem NotStuck.of_fill [LawfulProbLangℝ rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (h : notStuck (K.fill e) σ) : notStuck e σ := by
  rcases h with hv | hred
  · exact .inl (Ectx.fill_isValue hv)
  · exact if hv : e.isValue then .inl hv
    else .inr (hred.of_fill K hv)

/-- The expression is neither a value nor reducible. -/
def stuck [LawfulProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  ¬ e.isValue ∧ ¬ Reducible e σ

theorem stuck_iff_not_notStuck [LawfulProbLangℝ rT] {e : Exp rT} {σ : State rT} :
    stuck e σ ↔ ¬ notStuck e σ := by simp [stuck, notStuck]

theorem Stuck.fill [LawfulProbLangℝ rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (h : stuck e σ) : stuck (K.fill e) σ :=
  ⟨fun hv => h.1 (Ectx.fill_isValue hv),
   fun hred => h.2 (hred.of_fill K h.1)⟩

theorem measurableSet_primStep_support [LawfulProbLangℝ rT] (e : Exp rT) (σ : State rT) :
    MeasurableSet {ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}} := by
  have : IsFiniteMeasure (primStep ⟨e, σ⟩) :=
    ⟨lt_of_le_of_lt (primStep_univ_le_one _) ENNReal.one_lt_top⟩
  have hc : {ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}}.Countable := by
    simpa only [id_eq, Set.ofPred_eq_eq_singleton] using
      Measure.countable_meas_level_set_pos (μ := primStep ⟨e, σ⟩) measurable_id
  exact hc.measurableSet

theorem measurableSet_possible_support [LawfulProbLangℝ rT] :
    MeasurableSet
      {ρ | (fun σ₁ ρ ↦ Possible ρ (primStep (rT := rT) { expr := e₁, state := σ₁ })) σ₁ ρ} := by
  have hset :
      {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)} = {ρ | 0 < primStep ⟨e₁, σ₁⟩ {ρ}} :=
    Set.ext fun ρ => possible_iff_pos
  rw [hset]
  exact measurableSet_primStep_support e₁ σ₁

/-- `urand` is the only diffuse head step. -/
theorem primStep_atomic [LawfulProbLangℝ rT] (e : Exp rT) (σ : State rT)
    (hne : e.decomp.2 ≠ .urand) :
    IsAtomicSupport (primStep ⟨e, σ⟩) := by
  have hmeas : Measurable e.decomp.1.fillCfg := by measurability
  have hinj : Function.Injective e.decomp.1.fillCfg := Ectx.fillCfg_injective _
  have hsingle : ∀ ρ' : Cfg rT,
      (primStep ⟨e, σ⟩) {e.decomp.1.fillCfg ρ'} = (headStep ⟨e.decomp.2, σ⟩) {ρ'} := by
    intro ρ'
    show ((headStep ⟨e.decomp.2, σ⟩).map e.decomp.1.fillCfg) {e.decomp.1.fillCfg ρ'} = _
    rw [Measure.map_apply hmeas (measurableSet_singleton _)]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  have hcomeas : MeasurableSet {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} := by
    have heq : {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0}
        = {ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}}ᶜ := by
      ext ρ; simp [pos_iff_ne_zero]
    rw [heq]; exact (measurableSet_primStep_support e σ).compl
  unfold IsAtomicSupport
  show ((headStep ⟨e.decomp.2, σ⟩).map e.decomp.1.fillCfg)
      {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} = 0
  rw [Measure.map_apply hmeas hcomeas]
  have hpre : e.decomp.1.fillCfg ⁻¹' {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0}
      = {ρ' : Cfg rT | (headStep ⟨e.decomp.2, σ⟩) {ρ'} = 0} := by
    ext ρ'; simp only [Set.mem_preimage, Set.mem_ofPred_eq, hsingle ρ']
  rw [hpre]
  exact headStep_atomic e.decomp.2 σ hne

/-- Discharges `e.decomp.2 ≠ .urand` at a concrete redex by computing `decompItem`. -/
macro "no_urand" : tactic =>
  `(tactic| first
    | (rw [Exp.decomp_snd_fill (by first | (intro ⟨w⟩; nomatch w) | nofun)
          (by first | rfl | (simp [Exp.decompItem, Exp.toVal?_ofVal]; done))]
       intro h; cases h)
    | (rw [Exp.decomp_snd_of_decompItem_none
          (by first | rfl | (simp [Exp.decompItem, Exp.toVal?_ofVal]; done))]
       intro h; cases h)
    | (intro h; cases h))

@[discrete]
theorem Reducible.toDiscrete [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} (hne : e.decomp.2 ≠ .urand)
    (h : _root_.ProbLang.Reducible e σ) : Discrete.Reducible e σ := by
  by_contra hcon
  refine h ?_
  have hall : ∀ ρ : Cfg rT, (primStep ⟨e, σ⟩) {ρ} = 0 := fun ρ => by
    by_contra hρ
    exact hcon ⟨ρ, pos_iff_ne_zero.mpr hρ⟩
  have huniv : {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} = Set.univ := by
    ext ρ; simpa using hall ρ
  have := primStep_atomic e σ hne
  unfold IsAtomicSupport at this
  rw [huniv] at this
  exact MeasureTheory.Measure.measure_univ_eq_zero.mp this

@[discrete]
theorem HeadReducible.of_headStepSupport [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    {e e' : Exp rT} {σ σ' : State rT} (h : HeadStepSupport (⟨e, σ⟩ : Cfg rT) ⟨e', σ'⟩)
    (hu : e ≠ .urand := by nofun) : HeadReducible e σ := fun hz => by
  simpa [hz] using h.pos hu

@[discrete]
theorem Discrete.Reducible.of_headStepSupport [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    {e e' : Exp rT} {σ σ' : State rT} (h : HeadStepSupport (⟨e, σ⟩ : Cfg rT) ⟨e', σ'⟩)
    (hlc : e.IsLocallyClosed) (hne : e.decomp.2 ≠ .urand := by no_urand)
    (hu : e ≠ .urand := by nofun) :
    Discrete.Reducible e σ :=
  Reducible.toDiscrete hne (reducible_of_headReducible hlc (HeadReducible.of_headStepSupport h hu))

@[discrete]
theorem HeadStepSupport.of_primStep_fill [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    {K : Ectx rT} {e e₀ e₂' : Exp rT} {σ σ₀ σ₂' : State rT}
    (hwit : HeadStepSupport (⟨e, σ⟩ : Cfg rT) ⟨e₀, σ₀⟩) (hlc : e.IsLocallyClosed)
    (hstep : 0 < primStep (⟨K.fill e, σ⟩ : Cfg rT) {⟨e₂', σ₂'⟩})
    (hv : ¬ e.isValue := by intro ⟨w⟩; nomatch w) (hu : e ≠ .urand := by nofun) :
    ∃ e', e₂' = K.fill e' ∧ HeadStepSupport (⟨e, σ⟩ : Cfg rT) ⟨e', σ₂'⟩ := by
  obtain ⟨e', rfl, hstep'⟩ := primStep_fill_inv hv hstep
  refine ⟨e', rfl, Possible.headStepSupport (possible_iff_pos.mpr ?_)⟩
  rwa [primStep_eq_headStep
    (Exp.decompItem_none_of_lc_headReducible hlc (HeadReducible.of_headStepSupport hwit hu))]
    at hstep'

@[discrete]
theorem Discrete.Reducible.of_headStepSupport_fill [LawfulProbLangℝ rT]
    [MeasurableSingletonClass rT] {e e' : Exp rT} {σ σ' : State rT} (K : Ectx rT)
    (h : HeadStepSupport (⟨e, σ⟩ : Cfg rT) ⟨e', σ'⟩) (hlc : e.IsLocallyClosed)
    (hne : e.decomp.2 ≠ .urand := by no_urand) (hu : e ≠ .urand := by nofun)
    (hneK : (K.fill e).decomp.2 ≠ .urand := by no_urand) :
    Discrete.Reducible (K.fill e) σ :=
  Reducible.toDiscrete hneK
    ((Discrete.Reducible.of_headStepSupport h hlc hne hu).toReducible.fill K)

end ProbLang
end
