module

public meta import Metrology.Meta.Discrete
public import Metrology.ProbLang.Measure
public import Metrology.Couplings.SubProbability
public import Metrology.ProbLang.HeadStep
public import Metrology.ProbLang.Discrete

@[expose] public section

/-! # Primitive step

The full step `primStep`: decompose into a context and a head redex, head-step, plug back. -/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure Set

namespace ProbLang

open Ectx EctxItem Cfg Exp
open List (eq_nil_or_concat' foldl foldl_nil reverseRecOn append_nil append_assoc)

variable {rT : Type _} (K : Ectx rT)

/-! ## Plugging configurations into contexts -/

/-- Plugs the expression of a configuration into the context `K`. -/
@[simp] def Ectx.fillCfg (ρ : Cfg rT) : Cfg rT :=
  ⟨K.fill ρ.expr, ρ.state⟩

/-- Plugs the expression of a configuration into the context item `K`. -/
@[simp] def EctxItem.fillItemCfg (K : EctxItem rT) (ρ : Cfg rT) : Cfg rT :=
  ⟨K.fillItem ρ.expr, ρ.state⟩

/-- Plugging into the empty context is the identity. -/
@[simp]
theorem Ectx.fillCfg_empty : fillCfg ([] : Ectx rT) = id := by
  funext ⟨e, σ⟩; simp [fillCfg, fill]

/-- `K.fillCfg` is injective. -/
theorem Ectx.fillCfg_injective : Function.Injective K.fillCfg := by
  rintro ⟨e1, σ1⟩ ⟨e2, σ2⟩ h
  simpa [mk.injEq, fill_injective K |>.eq_iff] using h

variable [MeasurableSpace rT]

/-- `K.fillCfg` is measurable. -/
@[fun_prop]
theorem Ectx.fillCfg.measurable : Measurable K.fillCfg := by
  rw [measurable_iff]
  exact ⟨Exp.Ectx_fill.measurable.comp (measurable_const.prodMk measurable_expr),
    measurable_state⟩

variable [LawfulProbLangℝ rT] {e e' e1 e2 : Exp rT} {σ σ' σ1 σ2 : State rT}

/-! ## The primitive step -/

/-- The full step: decompose `e = K[e']`, head-step `e'`, and plug the result back into `K`. -/
def primStep (cfg : Cfg rT) : Measure (Cfg rT) :=
  let (K, e') := cfg.expr.decomp
  (headStep ⟨e', cfg.state⟩).map K.fillCfg

/-- The expression can take a step: `primStep` has nonzero mass. -/
abbrev Reducible (e : Exp rT) (σ : State rT) : Prop :=
  primStep ⟨e, σ⟩ ≠ 0

-- `@[discrete]` marks the point-mass (singleton) formulations. They hold for any `rT` but say
-- nothing about diffuse steps such as `urand`, so the linter keeps them out of continuous proofs.
/-- Some configuration is reached with positive probability (discrete form of `Reducible`). -/
@[discrete]
abbrev Discrete.Reducible (e : Exp rT) (σ : State rT) : Prop :=
  ∃ ρ : Cfg rT, 0 < primStep ⟨e, σ⟩ {ρ}

/-- A discretely reducible expression is reducible. -/
@[discrete]
theorem Discrete.Reducible.toReducible
    (h : Discrete.Reducible e σ) : ProbLang.Reducible e σ := by
  obtain ⟨ρ, hρ⟩ := h
  intro hz
  rw [hz] at hρ
  simp at hρ

/-! ## Measurability of `fillCfg` and `primStep` -/

/-- `Ki.fillItem` is a measurable embedding. -/
theorem EctxItem.fillItem.measurableEmbedding (Ki : EctxItem rT) :
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
  | allocNL v2 => exact Exp.allocN.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)
  | allocNR e1 => exact Exp.allocN.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | tape => exact Exp.tape.measurableEmbedding
  | randL v2 => exact Exp.rand.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)
  | randR e1 => exact Exp.rand.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | scrut p => exact Exp.scrut.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)

/-- `K.fill` is a measurable embedding. -/
theorem Ectx.fill.measurableEmbedding : MeasurableEmbedding K.fill := by
  induction K with
  | nil => exact MeasurableEmbedding.id
  | cons Ki K ih => exact ih.comp (fillItem.measurableEmbedding Ki)

/-- `Cfg` is measurably equivalent to the product `Exp × State`. -/
def Cfg.measurableEquivProd : Cfg rT ≃ᵐ Exp rT × State rT where
  toFun ρ := (ρ.expr, ρ.state)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_expr.prodMk measurable_state
  measurable_invFun := measurable_mk

/-- `K.fillCfg` is a measurable embedding. -/
theorem Ectx.fillCfg.measurableEmbedding : MeasurableEmbedding K.fillCfg := by
  have h : K.fillCfg = measurableEquivProd.symm ∘ Prod.map K.fill id ∘ measurableEquivProd := by
    funext ρ; rfl
  rw [h]
  exact (measurableEquivProd.symm.measurableEmbedding.comp
    ((fill.measurableEmbedding K).prodMap MeasurableEmbedding.id)).comp
    measurableEquivProd.measurableEmbedding

/-- The image of a measurable set under `K.fillCfg` is measurable. -/
theorem Ectx.measurableSet_fillCfg_image
    {S : Set (Cfg rT)} (hS : MeasurableSet S) : MeasurableSet (K.fillCfg '' S) :=
  (fillCfg.measurableEmbedding K).measurableSet_image' hS

/-- `primStep` is a measurable function of the configuration. -/
@[fun_prop]
theorem primStep.measurable : Measurable (primStep : Cfg rT → Measure (Cfg rT)) := by
  have hk : Measurable fun cfg : Cfg rT => headStep ⟨cfg.expr.decomp.2, cfg.state⟩ :=
    headStep.measurable.comp (by measurability)
  have hh : Measurable fun p : Cfg rT × Cfg rT => p.1.expr.decomp.1.fillCfg p.2 := by
    rw [measurable_iff]
    exact ⟨Exp.Ectx_fill.measurable.comp ((by measurability : Measurable _).prodMk
      (by measurability)), by measurability⟩
  have : IsFiniteKernel (Kernel.mk _ hk) := ⟨1, ENNReal.one_lt_top, fun _ => headStep_univ_le_one _⟩
  exact measurable_map_uncurry hh hk

/-! ## Values do not step; mass of a step -/

/-- Only non-values step. -/
theorem val_stuck (h : primStep ⟨e, σ⟩ ≠ 0) : ¬e.isValue := by
  simp only [primStep] at h
  set d := e.decomp with hd
  rw [← Exp.decomp_fill hd.symm]
  refine fill_noVal (val_head_stuck (σ := σ) fun hz => ?_)
  rw [hz] at h; simp at h

/-- The total mass of `primStep ρ` is at most one. -/
theorem primStep_univ_le_one (ρ : Cfg rT) : (primStep ρ) univ ≤ 1 := by
  obtain ⟨e, σ⟩ := ρ
  simp only [primStep]
  have Hmeas : Measurable e.decomp.1.fillCfg := by measurability
  rw [map_apply Hmeas MeasurableSet.univ]
  simpa using headStep_univ_le_one ⟨e.decomp.2, σ⟩

/-- One step of the primitive semantics has mass at most one. -/
instance primStep.isSubProbabilityMeasure (ρ : Cfg rT) : IsSubProbabilityMeasure (primStep ρ) where
  measure_univ_le_one := primStep_univ_le_one ρ

/-- A reducible configuration steps with total mass one. -/
theorem prim_step_mass (hred : Reducible e σ) : IsProbabilityMeasure (primStep ⟨e, σ⟩) := by
  have hhs : headStep ⟨e.decomp.2, σ⟩ ≠ 0 := fun h => hred (by simp [primStep, h])
  have := head_step_mass hhs
  simp only [primStep]
  infer_instance

/-! ## Bridge: `headStep` ↔ `primStep` -/

/-- A locally closed head redex has no frame for `decompItem` to peel. -/
theorem Exp.decompItem_none_of_lc_headReducible
    (he : e.IsLocallyClosed) (hred : headStep ⟨e, σ⟩ ≠ 0) : e.decompItem = none := by
  cases H : e.decompItem with
  | none => rfl
  | some redex =>
    obtain ⟨K, e'⟩ := redex
    obtain ⟨hfill, hne⟩ := Exp.decompItem_fill H
    exfalso
    have he' : e'.IsLocallyClosed := fillItem_isLocallyClosed (hfill ▸ he)
    exact hne (Exp.isValue_iff_isValueR.mpr ⟨head_ctx_step_val (hfill ▸ hred), Exp.lc_imp_lcb he'⟩)

/-- If `decompItem` finds no frame, `primStep` is `headStep`. -/
theorem primStep_eq_headStep (hdec : e.decompItem = none) : primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  suffices hd : e.decomp = ([], e) by simp [primStep, hd]
  unfold Exp.decomp; rw [hdec]

/-- A locally closed head-reducible expression is reducible. -/
theorem reducible_of_headReducible
    (he : e.IsLocallyClosed)
    (h : HeadReducible e σ) : Reducible e σ := by
  unfold Reducible
  rw [primStep_eq_headStep (decompItem_none_of_lc_headReducible he h)]
  exact h

/-! ## The context lemma: `primStep` under `K.fill` -/

section

variable {K}

/-- Stepping `K[e]` is stepping `e` and wrapping the result in `K`. -/
theorem primStep_fill
    (hv : ¬e.isValue) :
    primStep ⟨K.fill e, σ⟩ = (primStep ⟨e, σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  simp only [primStep]
  set d := e.decomp with hd
  obtain ⟨K', e''⟩ := d
  -- `e` is not a value, so `decomp (K[e]) = (K' ++ K, e'')`: both sides push the same head step.
  simp only [Exp.decomp_fill_comp hv hd.symm]
  rw [map_map (by measurability) (by measurability)]
  congr 1
  funext ⟨e', σ'⟩
  simp [Function.comp, fill_append]

/-- Stepping `Ki[e]` is stepping `e` and wrapping the result in `Ki`. -/
theorem primStep_fillItem
    (Ki : EctxItem rT) (hv : ¬e.isValue) :
    primStep ⟨Ki.fillItem e, σ⟩ =
      (primStep ⟨e, σ⟩).map (fun ρ => ⟨Ki.fillItem ρ.expr, ρ.state⟩) := by
  have : Ki.fillItem e = fill [Ki] e := by simp [fill, foldl, flip]
  rw [this, primStep_fill hv]; congr 1

/-- Filling a context preserves the mass of each successor configuration. -/
theorem primStep_fill_singleton
    (hv : ¬e1.isValue) :
    primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} = primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rw [primStep_fill hv, map_apply (by measurability) (measurableSet_singleton _)]
  congr 1
  ext ⟨e', σ'⟩
  simp [(fill_injective K).eq_iff]

/-- A reducible `e` stays reducible under any context. -/
theorem primStep_fill_pos (h : primStep ⟨e, σ⟩ ≠ 0) : primStep ⟨K.fill e, σ⟩ ≠ 0 := by
  by_cases hk : e.isValue
  · exact val_stuck h hk |>.elim
  · rw [primStep_fill hk]
    have hm : Measurable (fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT)) := by measurability
    refine fun H => h ?_
    refine measure_univ_eq_zero.mp ?_
    have := H ▸ map_apply hm .univ
    simpa using this.symm

/-- A step of `K[e1]` comes from a step of `e1` wrapped in `K`. -/
theorem primStep_fill_inv
    (hv : ¬e1.isValue) (h : 0 < primStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩}) :
    ∃ e2', e2 = K.fill e2' ∧ 0 < primStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} := by
  rw [primStep_fill hv] at h
  obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ := map_singleton_pos (by measurability) (fillCfg_injective K) h
  simp only [fillCfg, mk.injEq] at heq
  exact ⟨e2', heq.1.symm, heq.2 ▸ hpos⟩

end

/-! ## Reducibility under contexts -/

/-- A reducible expression stays reducible under a context. -/
theorem Reducible.fill (hred : Reducible e σ) : Reducible (K.fill e) σ :=
  primStep_fill_pos hred

/-! ## Uniqueness of the redex -/

/-- If `K[e]` is a head redex, then either `K` is empty or `e` is value-shaped. -/
theorem head_ctx_step_val_ectx (e : Exp rT) (σ : State rT)
    (hstep : HeadReducible (K.fill e) σ) : e.isValueR ∨ K = [] := by
  rcases eq_nil_or_concat' K with rfl | ⟨K'', Ki, rfl⟩
  · exact .inr rfl
  · simp only [fill_snoc] at hstep
    exact .inl (fill_isValueR (head_ctx_step_val hstep))

/-- If `K'[e1'] = K_redex[e1_redex]` with `e1'` not a value and `e1_redex` a head redex, then
`K_redex` extends `K'`. -/
theorem step_by_val (K' K_redex : Ectx rT) (e1' e1_redex : Exp rT)
    (σ : State rT)
    (hfill : K'.fill e1' = K_redex.fill e1_redex)
    (hv : ¬e1'.isValueR)
    (hstep : HeadReducible e1_redex σ) :
    ∃ K'' : Ectx rT, K_redex = K'.comp K'' := by
  induction K' using reverseRecOn generalizing K_redex e1_redex with
  | nil => exact ⟨K_redex, (append_nil K_redex).symm⟩
  | append_singleton K'_rest Ki' ih =>
    simp only [fill_snoc] at hfill
    rcases eq_nil_or_concat' K_redex with rfl | ⟨K_redex_rest, Ki_redex, rfl⟩
    · simp only [fill, foldl_nil] at hfill
      subst hfill
      exact absurd (fill_isValueR (head_ctx_step_val hstep)) hv
    · simp only [fill_snoc] at hfill ⊢
      have hKi := fillItem_noVal_inj (fill_noVal (Exp.not_isValue_of_not_isValueR hv))
        (fill_noVal (val_head_stuck hstep)) hfill
      subst hKi
      obtain ⟨K'', hK''⟩ := ih K_redex_rest e1_redex (fillItem_injective hfill) hstep
      exact ⟨K'', by rw [hK'']; simp [comp, append_assoc]⟩

/-- An expression decomposes into a context around a head redex in at most one way. -/
theorem head_redex_unique (K K' : Ectx rT) (e e' : Exp rT) (σ : State rT)
    (hfill : K.fill e = K'.fill e') (hred : HeadReducible e σ) (hred' : HeadReducible e' σ) :
    K = K' ∧ e = e' := by
  obtain ⟨K'', rfl⟩ := step_by_val K K' e e' σ hfill (val_head_stuck_R hred) hred'
  rw [← fill_comp] at hfill
  have he := fill_injective _ hfill
  rcases head_ctx_step_val_ectx K'' e' σ (he ▸ hred) with hval | rfl
  · exact absurd hval (val_head_stuck_R hred')
  · simp [fill] at he
    exact ⟨by simp [comp], he⟩

/-! ## Positive-probability steps are head steps in a context -/

/-- Every possible full step is a head step inside a context. -/
theorem prim_step_imp
    (h : Possible ⟨e2, σ2⟩ (primStep ⟨e1, σ1⟩)) :
    ∃ (K : Ectx rT) (e1' e2' : Exp rT),
      K.fill e1' = e1 ∧
      K.fill e2' = e2 ∧
      Possible ⟨e2', σ2⟩ (headStep ⟨e1', σ1⟩) := by
  rw [possible_iff_pos] at h
  simp only [primStep] at h
  set d := e1.decomp with hd
  obtain ⟨K, e1'⟩ := d
  obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ := map_singleton_pos (by measurability) (fillCfg_injective K) h
  simp only [fillCfg, mk.injEq] at heq
  exact ⟨K, e1', e2', Exp.decomp_fill hd.symm, heq.1, possible_iff_pos.mpr (heq.2 ▸ hpos)⟩

/-- The possible full steps of a locally closed expression are its head steps inside a context. -/
theorem prim_step_iff (he1 : e1.IsLocallyClosed) :
    Possible ⟨e2, σ2⟩ (primStep ⟨e1, σ1⟩) ↔ ∃ (K : Ectx rT) (e1' e2' : Exp rT),
      K.fill e1' = e1 ∧
      K.fill e2' = e2 ∧
      Possible ⟨e2', σ2⟩ (headStep ⟨e1', σ1⟩) := by
  refine ⟨prim_step_imp, ?_⟩
  rintro ⟨K, e1', e2', rfl, rfl, hhs⟩
  rw [possible_iff_pos] at hhs ⊢
  have hred : HeadReducible e1' σ1 := fun h0 => by simp [h0] at hhs
  rw [← primStep_fill_singleton (val_head_stuck hred),
    primStep_eq_headStep (decompItem_none_of_lc_headReducible (fill_isLocallyClosed he1) hred)]
  exact hhs

/-! ## Atomicity and the discrete bridge -/

/-- The atoms of `primStep ⟨e, σ⟩` form a measurable set. -/
theorem measurableSet_primStep_support (e : Exp rT) (σ : State rT) :
    MeasurableSet {ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}} := by
  have hc : {ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}}.Countable := by
    simpa only [id_eq, ofPred_eq_eq_singleton] using countable_meas_level_set_pos measurable_id
  exact hc.measurableSet

/-- The possible successors of a step form a measurable set. -/
theorem measurableSet_possible_support {e₁ : Exp rT} {σ₁ : State rT} :
    MeasurableSet {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)} := by
  have hset : {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)} = {ρ | 0 < primStep ⟨e₁, σ₁⟩ {ρ}} :=
    ext fun ρ => possible_iff_pos
  rw [hset]
  exact measurableSet_primStep_support e₁ σ₁

/-- Away from `urand` redexes, the step measure has atomic support. -/
theorem primStep_atomic (e : Exp rT) (σ : State rT)
    (hne : e.decomp.2 ≠ .urand) :
    IsAtomicSupport (primStep ⟨e, σ⟩) := by
  have hmeas : Measurable e.decomp.1.fillCfg := by measurability
  have hinj : Function.Injective e.decomp.1.fillCfg := fillCfg_injective _
  have hsingle : ∀ ρ' : Cfg rT,
      (primStep ⟨e, σ⟩) {e.decomp.1.fillCfg ρ'} = (headStep ⟨e.decomp.2, σ⟩) {ρ'} := by
    intro ρ'
    show ((headStep ⟨e.decomp.2, σ⟩).map e.decomp.1.fillCfg) {e.decomp.1.fillCfg ρ'} = _
    rw [map_apply hmeas (measurableSet_singleton _)]
    congr 1
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  have hcomeas : MeasurableSet {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} := by
    have heq : {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} =
        {ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}}ᶜ := by
      ext ρ; simp [pos_iff_ne_zero]
    rw [heq]; exact (measurableSet_primStep_support e σ).compl
  -- `fillCfg` is injective, so `primStep`'s null-singleton set pulls back to `headStep`'s.
  unfold IsAtomicSupport
  show ((headStep ⟨e.decomp.2, σ⟩).map e.decomp.1.fillCfg)
      {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} = 0
  rw [map_apply hmeas hcomeas]
  have hpre : e.decomp.1.fillCfg ⁻¹' {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} =
      {ρ' : Cfg rT | (headStep ⟨e.decomp.2, σ⟩) {ρ'} = 0} := by
    ext ρ'; simp only [mem_preimage, mem_ofPred_eq, hsingle ρ']
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

/-- A reducible expression away from `urand` is discretely reducible. -/
@[discrete]
theorem Reducible.toDiscrete
    (hne : e.decomp.2 ≠ .urand)
    (h : ProbLang.Reducible e σ) : Discrete.Reducible e σ := by
  by_contra hcon
  refine h ?_
  have hall : ∀ ρ : Cfg rT, (primStep ⟨e, σ⟩) {ρ} = 0 := fun ρ => by
    by_contra hρ
    exact hcon ⟨ρ, pos_iff_ne_zero.mpr hρ⟩
  have huniv : {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} = univ := by
    ext ρ; simpa using hall ρ
  have := primStep_atomic e σ hne
  unfold IsAtomicSupport at this
  rw [huniv] at this
  exact measure_univ_eq_zero.mp this

/-- A head step in the support makes the expression head reducible. -/
@[discrete]
theorem HeadReducible.of_headStepSupport
    (h : HeadStepSupport ⟨e, σ⟩ ⟨e', σ'⟩)
    (hu : e ≠ .urand := by nofun) : HeadReducible e σ := fun hz => by
  simpa [hz] using h.pos hu

/-- A head step in the support makes a locally closed expression discretely reducible. -/
@[discrete]
theorem Discrete.Reducible.of_headStepSupport
    (h : HeadStepSupport ⟨e, σ⟩ ⟨e', σ'⟩)
    (hlc : e.IsLocallyClosed) (hne : e.decomp.2 ≠ .urand := by no_urand)
    (hu : e ≠ .urand := by nofun) :
    Discrete.Reducible e σ :=
  Reducible.toDiscrete hne (reducible_of_headReducible hlc (HeadReducible.of_headStepSupport h hu))

/-- A step of `K[e]` in the support comes from a head step of `e`. -/
@[discrete]
theorem HeadStepSupport.of_primStep_fill
    {K : Ectx rT} {e e₀ e₂' : Exp rT} {σ σ₀ σ₂' : State rT}
    (hwit : HeadStepSupport ⟨e, σ⟩ ⟨e₀, σ₀⟩) (hlc : e.IsLocallyClosed)
    (hstep : 0 < primStep ⟨K.fill e, σ⟩ {⟨e₂', σ₂'⟩})
    (hv : ¬ e.isValue := by intro ⟨w⟩; nomatch w) (hu : e ≠ .urand := by nofun) :
    ∃ e', e₂' = K.fill e' ∧ HeadStepSupport ⟨e, σ⟩ ⟨e', σ₂'⟩ := by
  obtain ⟨e', rfl, hstep'⟩ := primStep_fill_inv hv hstep
  refine ⟨e', rfl, Possible.headStepSupport (possible_iff_pos.mpr ?_)⟩
  rwa [primStep_eq_headStep
    (decompItem_none_of_lc_headReducible hlc (HeadReducible.of_headStepSupport hwit hu))]
    at hstep'

/-- A head step of `e` in the support makes `K[e]` discretely reducible. -/
@[discrete]
theorem Discrete.Reducible.of_headStepSupport_fill
    (h : HeadStepSupport ⟨e, σ⟩ ⟨e', σ'⟩) (hlc : e.IsLocallyClosed)
    (hne : e.decomp.2 ≠ .urand := by no_urand) (hu : e ≠ .urand := by nofun)
    (hneK : (K.fill e).decomp.2 ≠ .urand := by no_urand) :
    Discrete.Reducible (K.fill e) σ :=
  Reducible.toDiscrete hneK
    ((Discrete.Reducible.of_headStepSupport h hlc hne hu).toReducible.fill K)

end ProbLang
end
