module

public import Metrology.ProbLang.Erasure.CaseClosers

@[expose] public section

/-! Presampling on a tape is invisible to `execN` at the expression level. -/

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure ProbLang.Measure

/-- Presampling tape `α` before running `m` steps leaves the distribution of the final expression
unchanged (Clutch `prim_coupl_upd_tapes_dom`, projected). `0 < t.bound` is needed: otherwise
`tapePresample σ α = 0`. -/
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
      rw [Measure.bind_map_comm _ _ _ Cfg.measurable_expr hkdir.aemeasurable]
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
      simp_rw [hprim, Measure.bind_map (Ectx.fillCfg.measurable K) (execN_measurable m)]
      refine Measure.ext fun S hS => ?_
      rw [Measure.map_apply Cfg.measurable_expr hS,
          Measure.map_apply Cfg.measurable_expr hS,
          Measure.bind_apply (Cfg.measurable_expr hS) hbind_ker.aemeasurable]
      simp_rw [Measure.bind_apply (Cfg.measurable_expr hS) hg_exec.aemeasurable]
      -- the IH, evaluated on `S` and pushed under `K`
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
        -- deterministic, state-independent redexes: `erasure_det_close`
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
        -- heap/tape allocation and access: commute with presampling
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
            -- rand on tape `α`, non-empty: the popped head is unchanged by appending
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
          · -- other tape: the same pop from every presampled state
            have hstep_rw : ∀ (σ₀ : State rT), σ₀.tapes[α_lbl]? = some ⟨z_r, nn :: ns⟩ →
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
            -- KEY CASE: rand on the empty tape `α` pops exactly the presampled value
            -- (`State.update_tapes_no_change` + `tapeIndexUniform_lintegral_eq_cfg_uniform`)
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
            rw [State.update_tapes_no_change htapes]
            exact tapeIndexUniform_lintegral_eq_cfg_uniform hz σ
              (fun ρ => ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S))
              (erasure_integrand_measurable hS)
          · -- other tape: the same uniform step from every presampled state
            have hstep_σ : headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ⟩ : Cfg rT)
                = Cfg.uniform z_r σ := by simp [headStep, htapes]
            refine uniform_close _ z_r hz ?_ hstep_σ
            filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            simp [headStep, htape_eq.trans htapes]
        | @randTapeOther z_r α_lbl _ N_b L hz htapes hzN =>
          -- bound mismatch: the same uniform step from every presampled state
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

end ProbLang
