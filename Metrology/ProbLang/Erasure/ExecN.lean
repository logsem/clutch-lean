module

public import Metrology.ProbLang.Erasure.CaseClosers

@[expose] public section

/-! # Presampling invariance of `execN`

Presampling a tape leaves the final-expression distribution of `execN m` unchanged. -/

open Option (some map_some)

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure
open Cfg Exp State Ectx Pat
open List (cons_append nil_append)
open ProbLang.Option (unwrapM)

/-! ## The two `rand` cases that read the presampled tape itself -/

variable {m : Nat} {σ : State rT} {α : Loc}

/-- A `rand` step on the non-empty tape `α` commutes with presampling. -/
theorem erasure_rand_tape_pop_close {K : Ectx rT} {S : Set (Exp rT)} {z_r : Int}
    {nn : { z : Int // 0 ≤ z ∧ z < z_r }} {ns : List { z : Int // 0 ≤ z ∧ z < z_r }}
    (hS : MeasurableSet S) (h : σ.tapes[α]? = some ⟨z_r, nn :: ns⟩) (hN : 0 < z_r)
    (ih_fill : ErasureIHFill m K S α) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
      ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩ ∂tapePresample σ α =
      ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
      ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ⟩ := by
  -- presampling appends to the tape's end, so the popped head `nn` is unchanged
  have hrhs : headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ⟩ =
      dirac ⟨.lit (.int nn), σ.update_tapes (·.insert α ⟨z_r, ns⟩)⟩ := by
    simp [headStep, h]
  have hker_rand : Measurable (fun σ' : State rT =>
      headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩) :=
    headStep.measurable.comp (measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  rw [hrhs, lintegral_dirac,
    tapePresample_lintegral h (fun σ' => ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
      ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩)
      ((measurable_lintegral (erasure_integrand_measurable hS)).comp hker_rand)]
  have hstep_upd : ∀ n' : { z : Int // 0 ≤ z ∧ z < z_r },
      headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)),
        σ.update_tapes (·.insert α ⟨z_r, (nn :: ns) ++ [↑n']⟩)⟩ =
      dirac ⟨.lit (.int ↑nn), σ.update_tapes (·.insert α ⟨z_r, ns ++ [↑n']⟩)⟩ := by
    intro ⟨n', hn'⟩
    simp only [headStep, upd_tape_some, cons_append, ↓reduceIte]
    rw [update_tapes_twice]
  simp_rw [hstep_upd, lintegral_dirac]
  have htape_popped :
      (σ.update_tapes (·.insert α ⟨z_r, ns⟩)).tapes[α]? = some ⟨z_r, ns⟩ := upd_tape_some _ _ _
  -- after the pop, the state is the presample of the popped tape ⟨z_r, ns⟩; apply the IH there
  convert
    ih_fill (.lit (.int ↑nn)) (σ.update_tapes (·.insert α ⟨z_r, ns⟩)) ⟨z_r, ns⟩ htape_popped hN
    using 1
  rw [tapePresample_lintegral htape_popped
    (fun σ'' => ((execN m ∘ K.fillCfg) ⟨.lit (.int ↑nn), σ''⟩) ((fun x => x.expr) ⁻¹' S))
    ((erasure_integrand_measurable hS).comp
      (measurable_mk.comp (measurable_const.prodMk measurable_id)))]
  simp_rw [update_tapes_twice]

/-- A `rand` step on the empty tape `α` commutes with presampling (the key case). -/
theorem erasure_rand_presampled_close {K : Ectx rT} {S : Set (Exp rT)} {z_r : Int}
    (hS : MeasurableSet S) (hz : 0 < z_r) (h : σ.tapes[α]? = some ⟨z_r, []⟩) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
      ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩ ∂tapePresample σ α =
      ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
      ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ⟩ := by
  -- the popped presampled index is uniform, which matches `Cfg.uniform z_r σ` by
  -- `tapeIndexUniform_lintegral_eq_cfg_uniform`
  have hrhs : headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ⟩ = uniform z_r σ := by
    simp [headStep, h]
  have hker_rand : Measurable (fun σ' : State rT =>
      headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩) :=
    headStep.measurable.comp (measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  rw [hrhs, tapePresample_lintegral h
    (fun σ' => ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
      ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩)
    ((measurable_lintegral (erasure_integrand_measurable hS)).comp hker_rand)]
  have hstep_upd : ∀ n' : { z : Int // 0 ≤ z ∧ z < z_r },
      headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)),
        σ.update_tapes (·.insert α ⟨z_r, [n']⟩)⟩ =
      dirac ⟨.lit (.int ↑n'), σ.update_tapes (·.insert α ⟨z_r, []⟩)⟩ := by
    intro ⟨n', hn'⟩
    simp only [headStep, upd_tape_some, ↓reduceIte]
    rw [update_tapes_twice]
  simp only [nil_append]
  simp_rw [hstep_upd, lintegral_dirac]
  rw [update_tapes_no_change h]
  exact tapeIndexUniform_lintegral_eq_cfg_uniform hz σ
    (fun ρ => ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S))
    (erasure_integrand_measurable hS)

/-! ## Main theorem -/

/-- Presampling tape `α` before running `m` steps leaves the distribution of the final expression
unchanged (Clutch `prim_coupl_upd_tapes_dom`, projected). -/
theorem execN_tapePresample_expr_eq {e : Exp rT} {t : Tape} (h : σ.tapes[α]? = some t)
    (hN : 0 < t.bound) :
    asExpr ((tapePresample σ α).bind (fun σ' => execN m ⟨e, σ'⟩)) = asExpr (execN m ⟨e, σ⟩) := by
  -- `0 < t.bound` is needed: otherwise `tapePresample σ α = 0`
  unfold asExpr
  -- induction on fuel; the step case splits on value / head-step kind (`det_or_prob_or_zero`)
  induction m generalizing e σ t with
  | zero =>
    show ((tapePresample σ α).bind (fun _ => (0 : Measure (Cfg rT)))).map (·.expr) =
         ((0 : Measure (Cfg rT))).map (·.expr)
    refine ext fun S hS => ?_
    rw [map_apply measurable_expr hS,
        map_apply measurable_expr hS,
        bind_apply (measurable_expr hS) measurable_const.aemeasurable]
    simp only [coe_zero, Pi.zero_apply, lintegral_zero]
  | succ m ih =>
    by_cases hv : e.isValue
    · -- a value stops immediately, so only the total mass of `tapePresample` (one) matters
      have hstep : ∀ σ' : State rT, execN (m + 1) ⟨e, σ'⟩ = dirac ⟨e, σ'⟩ := fun σ' =>
        execN_succ_isValue hv m
      simp_rw [hstep]
      have hkdir : Measurable (fun σ' : State rT => dirac (⟨e, σ'⟩ : Cfg rT)) :=
        measurable_dirac_mk measurable_const measurable_id
      rw [bind_map_comm _ _ _ measurable_expr hkdir.aemeasurable]
      -- explicit kernel equality: `simp_rw` leaves metavariables here
      have hker : (fun σ' : State rT => map (·.expr) (dirac (⟨e, σ'⟩ : Cfg rT))) =
          (fun _ => dirac e) := by
        funext σ'
        rw [map_dirac (⟨e, σ'⟩ : Cfg rT)]
      rw [hker, map_dirac (⟨e, σ⟩ : Cfg rT)]
      refine ext fun S hS => ?_
      rw [bind_apply hS measurable_const.aemeasurable,
          lintegral_const, tapePresample_univ_eq_one h hN, mul_one]
    · -- not a value: unfold one step `K[e_red]`, then show each head step commutes with presampling
      have hstep : ∀ σ' : State rT,
          execN (m + 1) ⟨e, σ'⟩ = (primStep ⟨e, σ'⟩).bind (execN m) :=
        fun σ' => execN_succ_not_isValue hv m
      simp_rw [hstep]
      set K := e.decomp.1
      set e_red := e.decomp.2
      have hprim : ∀ σ' : State rT,
          primStep ⟨e, σ'⟩ = (headStep ⟨e_red, σ'⟩).map K.fillCfg := by
        intro σ'; simp only [primStep, e_red, K]
      have hg_exec : Measurable (execN m ∘ K.fillCfg) :=
        (execN_measurable m).comp (fillCfg.measurable K)
      have hker_hs : Measurable (fun σ' : State rT => headStep ⟨e_red, σ'⟩) :=
        headStep.measurable.comp (measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
      have hbind_ker : Measurable (fun σ' : State rT =>
          (headStep ⟨e_red, σ'⟩).bind (execN m ∘ K.fillCfg)) :=
        (measurable_join.comp (measurable_map _ hg_exec)).comp hker_hs
      simp_rw [hprim, Measure.bind_map (fillCfg.measurable K) (execN_measurable m)]
      refine ext fun S hS => ?_
      rw [map_apply measurable_expr hS,
          map_apply measurable_expr hS,
          bind_apply (measurable_expr hS) hbind_ker.aemeasurable]
      simp_rw [bind_apply (measurable_expr hS) hg_exec.aemeasurable]
      -- the IH, evaluated on `S` and pushed under `K`
      have ih_pointwise : ∀ e' (σ' : State rT) t', σ'.tapes[α]? = some t' → 0 < t'.bound →
          ∫⁻ σ'', (execN m ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ' α =
            (execN m ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S) := by
        intro e' σ' t' ht' hN'
        have hih : ((tapePresample σ' α).bind (fun σ'' => execN m ⟨e', σ''⟩)).map (·.expr) =
            (execN m ⟨e', σ'⟩).map (·.expr) := ih ht' hN'
        have hval : ((tapePresample σ' α).bind (fun σ'' => execN m ⟨e', σ''⟩)).map (·.expr) S =
            (execN m ⟨e', σ'⟩).map (·.expr) S := by rw [hih]
        have hk_exec : Measurable (fun σ'' : State rT => execN m (⟨e', σ''⟩ : Cfg rT)) :=
          (execN_measurable m).comp (measurable_mk.comp (measurable_const.prodMk measurable_id))
        rw [map_apply measurable_expr hS, map_apply measurable_expr hS,
          bind_apply (measurable_expr hS) hk_exec.aemeasurable] at hval
        exact hval
      have ih_fill : ErasureIHFill m K S α := by
        intro e' σ' t' ht' hN'
        simp only [Function.comp]
        exact ih_pointwise (K.fill e') σ' t' ht' hN'
      have det_close_state_pres := erasure_det_close h hN ih_fill
      have uniform_close := erasure_uniform_close hS h hN ih_fill
      have uniformReal_close := erasure_uniformReal_close hS h hN ih_fill
      rcases det_or_prob_or_zero e_red σ with hdet | hprob | hzero
      · clear_value e_red K
        cases hdet with
        -- deterministic, state-independent redexes: `erasure_det_close`
        | betaLam hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ (open' e1 e2) fun σ' => ?_
          exact isValM_some hv2
        | betaFix hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ (app (open' e1 (.fix e1)) e2) fun σ' => ?_
          exact isValM_some hv2
        | unop hv heval =>
          rename_i op e_u e'
          refine det_close_state_pres _ e' fun σ' => ?_
          show isValM e_u (unwrapM _ (op.eval e_u)) = _
          rw [isValM_some hv, heval]; rfl
        | binop hv1 hv2 heval =>
          rename_i op e1 e2 e'
          refine det_close_state_pres _ e' fun σ' => ?_
          show isValM e1 (isValM e2 (unwrapM _ (op.eval e1 e2))) = _
          rw [isValM_some hv2, isValM_some hv1, heval]; rfl
        | ifTrue =>
          rename_i et ef
          exact det_close_state_pres _ et fun _ => rfl
        | ifFalse =>
          rename_i et ef
          exact det_close_state_pres _ ef fun _ => rfl
        | fst hv1 hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ e1 fun σ' => ?_
          show isValM e1 (isValM e2 (dirac _)) = _
          rw [isValM_some hv2, isValM_some hv1]
        | snd hv1 hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ e2 fun σ' => ?_
          show isValM e1 (isValM e2 (dirac _)) = _
          rw [isValM_some hv2, isValM_some hv1]
        | caseL hv =>
          rename_i e_c el er
          refine det_close_state_pres _ (el.app e_c) fun σ' => ?_
          exact isValM_some hv
        | caseR hv =>
          rename_i e_c el er
          refine det_close_state_pres _ (er.app e_c) fun σ' => ?_
          exact isValM_some hv
        | scrutSuccess hv hmatch =>
          rename_i e_s p bindings
          refine det_close_state_pres _ (.inl bindings) fun σ' => ?_
          show isValM e_s (match tryMatch p e_s with | some b => _ | none => _) = _
          rw [isValM_some hv, hmatch]
        | scrutFailure hv hmatch =>
          rename_i e_s p
          refine det_close_state_pres _ (.inr (.lit .unit)) fun σ' => ?_
          show isValM e_s (match tryMatch p e_s with | some b => _ | none => _) = _
          rw [isValM_some hv, hmatch]
        -- heap/tape allocation and access: commute with presampling
        | load hlook =>
          rename_i ℓ v
          exact erasure_load_close h hN ih_fill hlook
        | alloc hv =>
          rename_i ed
          exact erasure_alloc_close hS h hN ih_fill
        | store hv hsome =>
          rename_i ℓ ev
          exact erasure_store_close hS h hN ih_fill
        | tape =>
          rename_i z
          exact erasure_tape_close hS h hN ih_fill
      · clear_value e_red K
        cases hprob with
        | randNoTape hz =>
          rename_i z_r
          exact uniform_close _ z_r hz (ae_of_all _ fun _ => rfl) rfl
        | @randTape z_r α_lbl _ N_b nn ns htapes hzN =>
          subst hzN
          by_cases hαeq : α = α_lbl
          · subst hαeq
            -- the popped head is unchanged by appending
            obtain rfl : t = ⟨z_r, nn :: ns⟩ := some.inj (h.symm.trans htapes)
            exact erasure_rand_tape_pop_close hS h hN ih_fill
          · -- a different tape α_lbl ≠ α: the same pop from every presampled state
            have hstep_rw : ∀ σ₀ : State rT, σ₀.tapes[α_lbl]? = some ⟨z_r, nn :: ns⟩ →
                headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ₀⟩ =
                dirac ⟨.lit (.int nn), σ₀.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)⟩ := by
              intro σ₀ ht'
              simp [headStep, ht']
            have htapes_pres :
                ∀ᵐ σ' ∂(tapePresample σ α), σ'.tapes[α_lbl]? = some ⟨z_r, nn :: ns⟩ := by
              filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' heq
              exact heq.trans htapes
            calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                  ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ'⟩ ∂tapePresample σ α
              _ = ∫⁻ σ', ((execN m ∘ K.fillCfg)
                    ⟨.lit (.int nn), σ'.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)⟩)
                  ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
                refine lintegral_congr_ae ?_
                filter_upwards [htapes_pres] with σ' ht'
                rw [hstep_rw σ' ht', lintegral_dirac]
              _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                  ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ⟩ := by
                have htape_upd :
                    (σ.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)).tapes[α]? = some t := by
                  rw [upd_diff_tape_tot hαeq]
                  exact h
                rw [tapePresample_lintegral_update_tapes_ne (Ne.symm hαeq)
                    (fun τ => ((execN m ∘ K.fillCfg) ⟨.lit (.int nn), τ⟩) ((fun x => x.expr) ⁻¹' S))
                    ((erasure_integrand_measurable hS).comp
                      (measurable_mk.comp (measurable_const.prodMk measurable_id))),
                  ih_fill _ (σ.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)) t htape_upd hN,
                  hstep_rw σ htapes, lintegral_dirac]
        | @randTapeEmpty z_r α_lbl _ N_b hz htapes hzN =>
          subst hzN
          by_cases hαeq : α = α_lbl
          · subst hαeq
            -- KEY CASE: `rand` on the empty presampled tape `α`
            obtain rfl : t = ⟨z_r, []⟩ := some.inj (h.symm.trans htapes)
            exact erasure_rand_presampled_close hS hz h
          · -- a different tape α_lbl ≠ α: the same uniform step from every presampled state
            have hstep_σ :
                headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ⟩ = uniform z_r σ := by
              simp [headStep, htapes]
            refine uniform_close _ z_r hz ?_ hstep_σ
            filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            simp [headStep, htape_eq.trans htapes]
        | @randTapeOther z_r α_lbl _ N_b L hz htapes hzN =>
          -- bound mismatch: the same uniform step from every presampled state
          have hrand_uniform : ∀ (σ₀ : State rT) {M : Int} {ns : List _},
              σ₀.tapes[α_lbl]? = some ⟨M, ns⟩ → M ≠ z_r →
              headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ₀⟩ = uniform z_r σ₀ := by
            intro σ₀ M ns ht hne
            show (match σ₀.tapes[α_lbl]? with | none => _ | some ⟨M, _⟩ => _) = _
            rw [ht]
            simp only
            rw [ite_eq_right hne]
          refine uniform_close _ z_r hz ?_ (hrand_uniform σ htapes hzN.symm)
          obtain ⟨N, bs⟩ := t
          by_cases hαeq : α = α_lbl
          · subst hαeq
            have hNN : N_b = N := congrArg Tape.bound (some.inj (htapes.symm.trans h))
            filter_upwards [tapePresample_bound_ae h] with σ' hb
            rcases hq : σ'.tapes[α]? with _ | ⟨M, L⟩
            · simp [hq] at hb
            · simp only [hq, map_some, some.injEq] at hb
              exact hrand_uniform _ hq (by omega)
          · filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            exact hrand_uniform _ (htape_eq.trans htapes) hzN.symm
        | randNonpos hz =>
          rename_i z_r
          refine det_close_state_pres _ (.lit (.int (-1))) fun σ' => ?_
          show uniform z_r σ' = _
          exact uniform_nonpos_eq hz
        | @randTapeNonposEmpty z_r α_lbl _ N_b hz htapes hzN =>
          -- α_lbl ≠ α: tape α has bound > 0, this one has bound z ≤ 0
          have hαne : α ≠ α_lbl := by
            intro heq
            subst heq
            have ht_eq : t = ⟨N_b, []⟩ := by
              rw [htapes] at h; exact (some.inj h).symm
            apply hz
            rw [hzN]
            have : t.bound = N_b := by rw [ht_eq]
            exact this ▸ hN
          subst hzN
          have hstep : ∀ {σ' : State rT}, σ'.tapes[α_lbl]? = some ⟨z_r, []⟩ →
              headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ'⟩ =
                dirac ⟨.lit (.int (-1)), σ'⟩ := by
            intro σ' hσ'
            simp only [headStep, hσ', ↓reduceIte]
            exact uniform_nonpos_eq hz
          refine erasure_det_close_ae h hN ih_fill _ (.lit (.int (-1))) ?_ ?_
          · filter_upwards [tapePresample_tape_ne_ae h hαne.symm] with σ' htape_eq
            exact hstep (htape_eq.trans htapes)
          · exact hstep htapes
        | @randTapeNonposOther z_r α_lbl _ N_b L hz htapes hzN =>
          have hstep : ∀ {σ' : State rT}, σ'.tapes[α_lbl]? = some ⟨N_b, L⟩ →
              headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ'⟩ =
                dirac ⟨.lit (.int (-1)), σ'⟩ := by
            intro σ' hσ'
            simp only [headStep, hσ']
            rw [ite_eq_right hzN.symm]
            exact uniform_nonpos_eq hz
          refine erasure_det_close_ae h hN ih_fill _ (.lit (.int (-1))) ?_ (hstep htapes)
          by_cases hαeq : α = α_lbl
          · subst hαeq
            have ht_eq : t = ⟨N_b, L⟩ := by
              rw [htapes] at h; exact (some.inj h).symm
            subst ht_eq
            filter_upwards [tapePresample_bound_ae h] with σ' hb
            rcases hq : σ'.tapes[α]? with _ | ⟨M, L'⟩
            · simp [hq] at hb
            · simp only [hq, map_some, some.injEq] at hb
              simp only [headStep, hq]
              rw [ite_eq_right (show ¬ M = z_r by omega)]
              exact uniform_nonpos_eq hz
          · filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            exact hstep (htape_eq.trans htapes)
        | urand =>
          exact uniformReal_close urand (ae_of_all _ fun _ => rfl) rfl
      · exact erasure_zero_close h hzero

end ProbLang
