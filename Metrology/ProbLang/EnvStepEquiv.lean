module

public import Metrology.ProbLang.EnvStep
public import Metrology.ProbLang.BigStepEquiv
public import Metrology.ProbLang.Syntax.LocallyClosed

@[expose] public section

/-! # The environment machine agrees with the big-step semantics

`envBig` is the measure semantics of the environment machine `envStep`; `envBig_map_rb` says
that reading its results back gives `bigStep` of the read-back configuration (discrete only). -/

noncomputable section
open MeasureTheory Measure Function

namespace ProbLang

variable {rT : Type}

/-! ## Substitution of environments -/

namespace Exp

theorem lcb_succ (e : Exp rT) (k : Nat) (h : lcb k e = true) : lcb (k + 1) e = true := by
  induction e generalizing k with
  | bvar j => simp only [lcb, decide_eq_true_eq] at h ⊢; omega
  | lam e ih | fix e ih => exact ih _ h
  | _ => simp_all [lcb]

theorem lcb_mono {k m : Nat} {e : Exp rT} (h : lcb k e = true) (hkm : k ≤ m) :
    lcb m e = true := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact lcb_succ e m ih

@[simp] theorem substEnv_nil (k : Nat) (e : Exp rT) : e.substEnv k [] = e := by
  induction e generalizing k with
  | bvar j => simp [substEnv]
  | _ => simp_all [substEnv]

/-- Substituting locally-closed values for the indices `k, …, k + |vs| - 1` of a term
whose indices are below `k + |vs|` leaves indices below `k`. -/
theorem lcb_substEnv {k : Nat} {vs : List (Exp rT)} {e : Exp rT}
    (he : lcb (k + vs.length) e = true) (hvs : ∀ v ∈ vs, lcb 0 v = true) :
    lcb k (e.substEnv k vs) = true := by
  induction e generalizing k with
  | bvar j =>
    simp only [lcb, decide_eq_true_eq] at he
    simp only [substEnv]
    split
    · rename_i hkj
      have hlt : j - k < vs.length := by omega
      rw [List.getElem?_eq_getElem hlt, Option.getD_some]
      exact lcb_mono (hvs _ (List.getElem_mem hlt)) (Nat.zero_le _)
    · simp only [lcb, decide_eq_true_eq]; omega
  | lam e ih | fix e ih =>
    simp only [lcb, substEnv] at he ⊢
    exact ih (by rwa [show k + 1 + vs.length = k + vs.length + 1 by omega])
  | _ => simp_all [lcb, substEnv]

/-- Opening the outer binder of a substituted body extends the substitution. -/
theorem openRec_substEnv {k : Nat} {v : Exp rT} {vs : List (Exp rT)} (e : Exp rT)
    (hvs : ∀ u ∈ vs, u.IsLocallyClosed) :
    openRec k v (e.substEnv (k + 1) vs) = e.substEnv k (v :: vs) := by
  induction e generalizing k with
  | bvar j =>
    simp only [substEnv]
    by_cases hj : k + 1 ≤ j
    · rw [ite_eq_left hj, ite_eq_left (by omega)]
      obtain ⟨i, rfl⟩ : ∃ i, j = k + 1 + i := ⟨j - (k + 1), by omega⟩
      rw [show k + 1 + i - k = i + 1 by omega, show k + 1 + i - (k + 1) = i by omega,
        List.getElem?_cons_succ]
      cases hi : vs[i]? with
      | none => simp [openRec]; omega
      | some u => exact (open_lc k v u (hvs u (List.mem_of_getElem? hi))).symm
    · rw [ite_eq_right hj]
      by_cases hkj : k = j
      · subst hkj; simp [openRec]
      · rw [ite_eq_right (by omega)]; simp [openRec, hkj]
  | lam e ih | fix e ih => simp only [substEnv, openRec]; rw [ih]
  | _ => simp_all [substEnv, openRec]

end Exp

/-! ## Well-formed runtime values -/

mutual
/-- A runtime value is well formed when every closure body is scoped by its environment. -/
def RVal.WF : RVal rT → Prop
  | .lit _ => True
  | .clo env body => Exp.lcb (env.length + 1) body = true ∧ RVal.WFEnv env
  | .fixClo env body => Exp.lcb (env.length + 1) body = true ∧ RVal.WFEnv env
  | .pair v1 v2 => v1.WF ∧ v2.WF
  | .inl v => v.WF
  | .inr v => v.WF

/-- Every entry of the environment is well formed. -/
def RVal.WFEnv : List (RVal rT) → Prop
  | [] => True
  | v :: vs => v.WF ∧ RVal.WFEnv vs
end

theorem RVal.rbEnv_eq_map (env : List (RVal rT)) : RVal.rbEnv env = env.map RVal.rb := by
  induction env with
  | nil => rfl
  | cons v vs ih => simp [RVal.rbEnv, ih]

@[simp] theorem RVal.length_rbEnv (env : List (RVal rT)) :
    (RVal.rbEnv env).length = env.length := by
  simp [RVal.rbEnv_eq_map]

theorem RVal.wfEnv_iff (env : List (RVal rT)) : RVal.WFEnv env ↔ ∀ v ∈ env, v.WF := by
  induction env with
  | nil => simp [RVal.WFEnv]
  | cons v vs ih => simp [RVal.WFEnv, ih]

theorem RVal.WFEnv.getElem? {env : List (RVal rT)} (h : RVal.WFEnv env) {j : Nat} {v : RVal rT}
    (hj : env[j]? = some v) : v.WF :=
  (RVal.wfEnv_iff env).mp h v (List.mem_of_getElem? hj)

theorem RVal.rbEnv_getElem? (env : List (RVal rT)) (j : Nat) :
    (RVal.rbEnv env)[j]? = env[j]?.map RVal.rb := by
  simp [RVal.rbEnv_eq_map]

mutual
theorem RVal.WF.isValue : ∀ {v : RVal rT}, v.WF → v.rb.isValue
  | .lit _, _ => ⟨.lit⟩
  | .clo env body, ⟨hb, henv⟩ => by
    refine Exp.isValue_iff_isValueR.mpr ⟨trivial, ?_⟩
    simp only [RVal.rb, Exp.lcb]
    exact Exp.lcb_substEnv (by simpa [Nat.add_comm] using hb) (RVal.WFEnv.lcb (env := env) henv)
  | .fixClo env body, ⟨hb, henv⟩ => by
    refine Exp.isValue_iff_isValueR.mpr ⟨trivial, ?_⟩
    simp only [RVal.rb, Exp.lcb]
    exact Exp.lcb_substEnv (by simpa [Nat.add_comm] using hb) (RVal.WFEnv.lcb (env := env) henv)
  | .pair v1 v2, ⟨h1, h2⟩ => by
    obtain ⟨w1⟩ := RVal.WF.isValue (v := v1) h1
    obtain ⟨w2⟩ := RVal.WF.isValue (v := v2) h2
    exact ⟨.pair w1 w2⟩
  | .inl v, h => by obtain ⟨w⟩ := RVal.WF.isValue (v := v) h; exact ⟨.inl w⟩
  | .inr v, h => by obtain ⟨w⟩ := RVal.WF.isValue (v := v) h; exact ⟨.inr w⟩

theorem RVal.WFEnv.lcb : ∀ {env : List (RVal rT)}, RVal.WFEnv env →
    ∀ u ∈ RVal.rbEnv env, Exp.lcb 0 u = true
  | [], _ => by simp [RVal.rbEnv]
  | v :: vs, ⟨hv, hvs⟩ => by
    simp only [RVal.rbEnv, List.mem_cons, forall_eq_or_imp]
    exact ⟨(Exp.isValue_iff_isValueR.mp (RVal.WF.isValue (v := v) hv)).2,
      RVal.WFEnv.lcb (env := vs) hvs⟩
end

theorem RVal.WFEnv.lc {env : List (RVal rT)} (h : RVal.WFEnv env) :
    ∀ u ∈ RVal.rbEnv env, u.IsLocallyClosed :=
  fun u hu => Exp.lcb_imp_lc (h.lcb u hu)

theorem RVal.WF.lc {v : RVal rT} (h : v.WF) : v.rb.IsLocallyClosed :=
  Exp.lcb_imp_lc (Exp.isValue_iff_isValueR.mp h.isValue).2

/-- The read-back value, as a `Val`. -/
def RVal.WF.toVal {v : RVal rT} (h : v.WF) : Val rT :=
  ⟨v.rb, IsVal.ofIsValue h.isValue, h.lc⟩

theorem RVal.ofExp_spec {e : Exp rT} (he : e.isValue) :
    (RVal.ofExp e).rb = e ∧ (RVal.ofExp e).WF := by
  obtain ⟨w⟩ := he
  induction w with
  | lit => exact ⟨rfl, trivial⟩
  | lam h | fix h =>
    refine ⟨by simp [RVal.ofExp, RVal.rb, RVal.rbEnv], ?_, trivial⟩
    simpa [Exp.lcb] using Exp.lc_imp_lcb h
  | pair _ _ ih1 ih2 => exact ⟨by simp [RVal.ofExp, RVal.rb, ih1.1, ih2.1], ih1.2, ih2.2⟩
  | inl _ ih => exact ⟨by simp [RVal.ofExp, RVal.rb, ih.1], ih.2⟩
  | inr _ ih => exact ⟨by simp [RVal.ofExp, RVal.rb, ih.1], ih.2⟩

theorem Pat.tryMatchR_spec [MeasurableSpace rT] [LawfulProbLangℝ rT] (p : Pat rT) {v : RVal rT}
    (hv : v.WF) :
    (p.tryMatchR v).map RVal.rb = p.tryMatch v.rb ∧ ∀ b, p.tryMatchR v = some b → b.WF := by
  induction p generalizing v with
  | wildcard => simp_all [Pat.tryMatchR, Pat.tryMatch]
  | lit l =>
    cases v <;> simp [Pat.tryMatchR, Pat.tryMatch, RVal.rb]
    intro _; trivial
  | pair p1 p2 ih1 ih2 =>
    cases v with
    | pair v1 v2 =>
      obtain ⟨h1, h2⟩ := hv
      obtain ⟨e1, w1⟩ := ih1 h1
      obtain ⟨e2, w2⟩ := ih2 h2
      simp only [Pat.tryMatchR, Pat.tryMatch, RVal.rb, ← e1, ← e2]
      cases hb1 : p1.tryMatchR v1 with
      | none => simp
      | some b1 =>
        cases hb2 : p2.tryMatchR v2 with
        | none => simp
        | some b2 =>
          simp only [Option.bind_eq_bind, Option.map_some, Option.bind_some, Option.pure_def,
            RVal.rb, Option.some.injEq, forall_eq', RVal.WF, true_and]
          exact ⟨w1 b1 hb1, w2 b2 hb2⟩
    | _ => simp [Pat.tryMatchR, Pat.tryMatch, RVal.rb]
  | inl p ih =>
    cases v with
    | inl v => exact ih hv
    | _ => simp [Pat.tryMatchR, Pat.tryMatch, RVal.rb]
  | inr p ih =>
    cases v with
    | inr v => exact ih hv
    | _ => simp [Pat.tryMatchR, Pat.tryMatch, RVal.rb]

/-- Well-formed frames: each subterm still to be evaluated is scoped by its environment. -/
def Frame.WF : Frame rT → Prop
  | .pairR env e1 | .appR env e1 | .binopR _ env e1 | .storeR env e1 | .randR env e1 =>
    Exp.lcb env.length e1 = true ∧ RVal.WFEnv env
  | .pairL v2 | .appL v2 | .applyTo v2 | .binopL _ v2 | .storeL v2 | .randL v2 => v2.WF
  | .cond env e1 e2 | .case env e1 e2 =>
    Exp.lcb env.length e1 = true ∧ Exp.lcb env.length e2 = true ∧ RVal.WFEnv env
  | .inl | .inr | .unop _ | .fst | .snd | .scrut _ | .alloc | .load | .tape => True

/-- Well-formed configurations. -/
def EnvCfg.WF : EnvCfg rT → Prop
  | .eval env e _ => Exp.lcb env.length e = true ∧ RVal.WFEnv env
  | .apply f v _ => f.WF ∧ v.WF
  | .resume f v _ => f.WF ∧ v.WF

/-! ## `Measure.bind` on discrete spaces, continuity in both arguments -/

section BindLemmas

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]

theorem map_bind_disc {γ : Type _} [MeasurableSpace γ] [DiscreteMeasurableSpace β]
    {μ : Measure α} {f : α → Measure β} {g : β → γ} (hf : Measurable f) :
    (μ.bind f).map g = μ.bind fun a => (f a).map g := by
  have hg : Measurable g := .of_discrete
  have hfg : Measurable fun a => (f a).map g := (measurable_map _ hg).comp hf
  ext s hs
  rw [map_apply hg hs, bind_apply (hg hs) hf.aemeasurable, bind_apply hs hfg.aemeasurable]
  simp_rw [map_apply hg hs]

variable [DiscreteMeasurableSpace α]

theorem bind_mono_disc {μ ν : Measure α} {f g : α → Measure β} (hμ : μ ≤ ν)
    (hfg : ∀ a, f a ≤ g a) : μ.bind f ≤ ν.bind g := by
  refine le_iff.mpr fun s hs => ?_
  rw [bind_apply hs Measurable.of_discrete.aemeasurable,
    bind_apply hs Measurable.of_discrete.aemeasurable]
  exact lintegral_mono' hμ fun a => hfg a s

theorem bind_mono_ae_disc {μ : Measure α} {f g : α → Measure β} (hfg : ∀ᵐ a ∂μ, f a ≤ g a) :
    μ.bind f ≤ μ.bind g := by
  refine le_iff.mpr fun s hs => ?_
  rw [bind_apply hs Measurable.of_discrete.aemeasurable,
    bind_apply hs Measurable.of_discrete.aemeasurable]
  exact lintegral_mono_ae (hfg.mono fun a h => h s)

/-- `bind` is continuous along monotone sequences in both arguments. -/
theorem bind_iSup_iSup_le {μ : ℕ → Measure α} (hμ : Monotone μ) {f : ℕ → α → Measure β}
    (hf : Monotone f) : (⨆ n, μ n).bind (fun a => ⨆ n, f n a) ≤ ⨆ n, (μ n).bind (f n) := by
  have hbind : Monotone fun n => (μ n).bind (f n) :=
    fun _ _ h => bind_mono_disc (hμ h) fun a => hf h a
  refine le_iff.mpr fun s hs => ?_
  rw [bind_apply hs Measurable.of_discrete.aemeasurable,
    iSup_apply_of_monotone hbind hs]
  simp_rw [iSup_apply_of_monotone (fun _ _ h => hf h _) hs]
  rw [lintegral_iSup (fun _ => Measurable.of_discrete) (fun _ _ h a => hf h a s)]
  refine iSup_le fun n => ?_
  rw [lintegral_iSup_of_monotone hμ Measurable.of_discrete]
  refine iSup_le fun m => le_iSup_of_le (max n m) ?_
  rw [bind_apply hs Measurable.of_discrete.aemeasurable]
  exact lintegral_mono' (hμ (le_max_right _ _)) fun a => hf (le_max_left _ _) a s

variable [DiscreteMeasurableSpace β]

/-- An almost-everywhere property of a `bind`'s continuations holds for the `bind`. -/
theorem ae_bind_disc {μ : Measure α} {f : α → Measure β} {p : β → Prop}
    (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂(f a), p b) : ∀ᵐ b ∂(μ.bind f), p b := by
  rw [ae_iff, bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  exact (lintegral_eq_zero_iff Measurable.of_discrete).mpr (h.mono fun a ha => ae_iff.mp ha)

end BindLemmas

/-! ## The measure semantics of the machine -/

instance : MeasurableSpace (RCfg rT) := ⊤

instance : DiscreteMeasurableSpace (RCfg rT) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

theorem RVal.rb_clo_open {env : Env rT} {body : Exp rT} {v : RVal rT} (henv : RVal.WFEnv env) :
    (body.substEnv 1 (RVal.rbEnv env)).open' v.rb = body.substEnv 0 (RVal.rbEnv (v :: env)) := by
  simp only [Exp.open', RVal.rbEnv]
  exact Exp.openRec_substEnv body henv.lc

/-- A well-formed frame reads back to an evaluation-context item. -/
theorem Frame.exists_item {f : Frame rT} (hf : f.WF) :
    ∃ Ki : EctxItem rT, ∀ x, f.fill x = Ki.fillItem x := by
  cases f with
  | pairR env e1 => exact ⟨.pairR _, fun _ => rfl⟩
  | pairL v2 => exact ⟨.pairL (RVal.WF.toVal (v := v2) hf), fun _ => rfl⟩
  | inl => exact ⟨.inl, fun _ => rfl⟩
  | inr => exact ⟨.inr, fun _ => rfl⟩
  | appR env e1 => exact ⟨.appR _, fun _ => rfl⟩
  | appL v2 => exact ⟨.appL (RVal.WF.toVal (v := v2) hf), fun _ => rfl⟩
  | applyTo v => exact ⟨.appL (RVal.WF.toVal (v := v) hf), fun _ => rfl⟩
  | unop op => exact ⟨.unop op, fun _ => rfl⟩
  | binopR op env e1 => exact ⟨.binopR op _, fun _ => rfl⟩
  | binopL op v2 => exact ⟨.binopL op (RVal.WF.toVal (v := v2) hf), fun _ => rfl⟩
  | cond env et ef => exact ⟨.condC _ _, fun _ => rfl⟩
  | fst => exact ⟨.fst, fun _ => rfl⟩
  | snd => exact ⟨.snd, fun _ => rfl⟩
  | case env el er => exact ⟨.case _ _, fun _ => rfl⟩
  | scrut p => exact ⟨.scrut p, fun _ => rfl⟩
  | alloc => exact ⟨.alloc, fun _ => rfl⟩
  | load => exact ⟨.load, fun _ => rfl⟩
  | storeR env e1 => exact ⟨.storeR _, fun _ => rfl⟩
  | storeL v2 => exact ⟨.storeL (RVal.WF.toVal (v := v2) hf), fun _ => rfl⟩
  | tape => exact ⟨.tape, fun _ => rfl⟩
  | randR env e1 => exact ⟨.randR _, fun _ => rfl⟩
  | randL v2 => exact ⟨.randL (RVal.WF.toVal (v := v2) hf), fun _ => rfl⟩

theorem dirac_bind_rcfg (r : RCfg rT) (f : RCfg rT → Measure (RCfg rT)) :
    (dirac r).bind f = f r :=
  dirac_bind Measurable.of_discrete r

variable [MeasurableSpace rT]

/-- The integer sampled by `Cfg.uniform`. -/
def intUniform (z : Int) : Measure Int :=
  match ProbLang.Int.isPos z with
  | some ⟨z, h⟩ => (PMF.uniformOfFinset (.Ico 0 z) (Finset.nonempty_Ico.mpr h)).toMeasure
  | none => dirac (-1)

theorem RCfg.measurable_rb : Measurable (RCfg.rb (rT := rT)) := .of_discrete

theorem intUniform_map (z : Int) (σ : State rT) :
    (intUniform z).map (fun n => (⟨.lit (.int n), σ⟩ : Cfg rT)) = Cfg.uniform z σ := by
  unfold intUniform Cfg.uniform
  cases Int.isPos z with
  | some z' => rfl
  | none => exact map_dirac' Measurable.of_discrete _

theorem map_iSup_le_of {μ : ℕ → Measure (RCfg rT)} (hμ : Monotone μ) {ν : Measure (Cfg rT)}
    (h : ∀ n, (μ n).map RCfg.rb ≤ ν) : (⨆ n, μ n).map RCfg.rb ≤ ν := by
  refine le_iff.mpr fun s hs => ?_
  rw [map_apply RCfg.measurable_rb hs,
    iSup_apply_of_monotone hμ (RCfg.measurable_rb hs)]
  exact iSup_le fun n => by
    rw [← map_apply RCfg.measurable_rb hs]; exact le_iff.mp (h n) s hs

variable [LawfulProbLangℝ rT]

/-- A machine step read as a measure, with recursive calls handled by `X`. -/
def Step.interp (X : EnvCfg rT → Measure (RCfg rT)) : Step rT → Measure (RCfg rT)
  | .ret v σ => dirac ⟨v, σ⟩
  | .eval env e σ => X (.eval env e σ)
  | .evalThen env e σ f => (X (.eval env e σ)).bind fun r => X (.resume f r.val r.state)
  | .apply f v σ => X (.apply f v σ)
  | .stuck _ => 0
  | .uniform z σ => (intUniform z).map fun n => ⟨.lit (.int n), σ⟩
  | .uniformReal σ => (LawfulProbLangℝ.unifUnit (T := rT)).map fun r => ⟨.lit (.real r), σ⟩

/-- One unfolding of the machine's measure semantics. -/
def envΦ (X : EnvCfg rT → Measure (RCfg rT)) (c : EnvCfg rT) : Measure (RCfg rT) :=
  (envStep c).interp X

theorem envΦ_mono : Monotone (envΦ (rT := rT)) := by
  intro X Y h c
  unfold envΦ
  generalize envStep c = s
  cases s with
  | evalThen => exact bind_mono_disc (h _) fun _ => h _
  | eval | apply => exact h _
  | _ => exact le_rfl

/-- The measure semantics of the environment machine: the Kleene sup of `envΦ`. -/
def envBig : EnvCfg rT → Measure (RCfg rT) := ⨆ n, envΦ^[n] ⊥

theorem envIter_mono : Monotone fun n => envΦ^[n] (⊥ : EnvCfg rT → Measure (RCfg rT)) :=
  Monotone.monotone_iterate_of_le_map envΦ_mono bot_le

theorem envΦ_iSup_le {X : ℕ → EnvCfg rT → Measure (RCfg rT)} (hX : Monotone X) :
    envΦ (⨆ n, X n) ≤ ⨆ n, envΦ (X n) := by
  intro c
  rw [iSup_apply]
  unfold envΦ
  generalize envStep c = s
  cases s with
  | evalThen =>
    simp only [Step.interp, iSup_apply]
    exact bind_iSup_iSup_le (fun _ _ h => hX h _) (fun _ _ h _ => hX h _)
  | eval | apply => simp only [Step.interp, iSup_apply]; exact le_rfl
  | _ => exact le_iSup_of_le 0 le_rfl

/-- `envBig` is a fixed point of `envΦ`. -/
theorem envBig_unfold : envBig (rT := rT) = envΦ envBig := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    cases n with
    | zero => exact bot_le
    | succ n =>
      rw [iterate_succ_apply']
      exact envΦ_mono (le_iSup (fun n => envΦ^[n] ⊥) n)
  · refine (envΦ_iSup_le envIter_mono).trans (iSup_le fun n => ?_)
    rw [← iterate_succ_apply' envΦ n]
    exact le_iSup (fun n => envΦ^[n] ⊥) (n + 1)

theorem envBig_apply (c : EnvCfg rT) : envBig c = (envStep c).interp envBig :=
  congrFun envBig_unfold c

/-! ## Results that do not need countability -/

/-- A step whose results and calls are all well formed. -/
def Step.Good : Step rT → Prop
  | .ret v _ => v.WF
  | .eval env e σ => (EnvCfg.eval env e σ).WF
  | .evalThen env e σ f => (EnvCfg.eval env e σ).WF ∧ f.WF
  | .apply f v _ => f.WF ∧ v.WF
  | _ => True

theorem envStep_good {c : EnvCfg rT} (hc : c.WF) : (envStep c).Good := by
  cases c with
  | eval env e σ =>
    obtain ⟨he, henv⟩ := hc
    cases e
    case bvar j =>
      simp only [envStep, evalK, stepOps]
      split
      · rename_i v hj; exact henv.getElem? hj
      · trivial
    all_goals simp_all [envStep, evalK, stepOps, Step.Good, EnvCfg.WF, Frame.WF, Exp.lcb,
      RVal.WF]
  | apply f v σ =>
    obtain ⟨hf, hv⟩ := hc
    cases f <;> simp_all [envStep, applyK, stepOps, Step.Good, EnvCfg.WF, Frame.WF, RVal.WF,
      RVal.WFEnv, Nat.add_comm]
  | resume f v σ =>
    obtain ⟨hf, hv⟩ := hc
    cases f <;> simp only [envStep, resumeK, stepOps] <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;>
      simp_all [Step.Good, EnvCfg.WF, Frame.WF, RVal.WF]
    all_goals first
      | exact (RVal.ofExp_spec (UnOp.eval_isValue ‹_›)).2
      | exact (RVal.ofExp_spec (BinOp.eval_isValue ‹_›)).2
      | exact (Pat.tryMatchR_spec _ hv).2 _ ‹_›
      | exact (RVal.ofExp_spec (Val.isValue _)).2

theorem Step.map_interp_uniform (z : Int) (σ : State rT) (X : EnvCfg rT → Measure (RCfg rT)) :
    ((Step.uniform z σ).interp X).map RCfg.rb = Cfg.uniform z σ := by
  simp only [Step.interp]
  rw [map_map RCfg.measurable_rb Measurable.of_discrete, ← intUniform_map]
  rfl

theorem envBig_eval_bvar {env : Env rT} {j : Nat} {σ : State rT} {u : Exp rT}
    (hc : (EnvCfg.eval env (.bvar j) σ).WF) (hu : (Exp.bvar j).substEnv 0 (RVal.rbEnv env) = u) :
    ∃ v : RVal rT, v.WF ∧ v.rb = u ∧ envBig (.eval env (.bvar j) σ) = dirac ⟨v, σ⟩ := by
  obtain ⟨he, henv⟩ := hc
  simp only [Exp.lcb, decide_eq_true_eq] at he
  obtain ⟨v, hj⟩ : ∃ v, env[j]? = some v := ⟨env[j], List.getElem?_eq_getElem he⟩
  refine ⟨v, henv.getElem? hj, ?_, ?_⟩
  · simpa [Exp.substEnv, RVal.rbEnv_getElem?, hj] using hu
  · rw [envBig_apply]; simp [envStep, evalK, stepOps, hj, Step.interp]

/-- Evaluating an expression that reads back to a value returns that value at once. -/
theorem envBig_eval_val : ∀ {u : Exp rT} (_ : IsVal u) {env : Env rT} {e : Exp rT}
    {σ : State rT}, (EnvCfg.eval env e σ).WF → e.substEnv 0 (RVal.rbEnv env) = u →
    ∃ v : RVal rT, v.WF ∧ v.rb = u ∧ envBig (.eval env e σ) = dirac ⟨v, σ⟩ := by
  intro u w
  induction w with
  | @lit b =>
    intro env e σ hc hu
    cases e with
    | bvar j => exact envBig_eval_bvar hc hu
    | lit b' =>
      simp only [Exp.substEnv] at hu
      exact ⟨.lit b', trivial, by simp [RVal.rb, hu], by rw [envBig_apply]; rfl⟩
    | _ => simp [Exp.substEnv] at hu
  | lam _ =>
    intro env e σ hc hu
    cases e with
    | bvar j => exact envBig_eval_bvar hc hu
    | lam body =>
      exact ⟨.clo env body, ⟨by simpa [Exp.lcb] using hc.1, hc.2⟩,
        by simpa [RVal.rb, Exp.substEnv] using hu, by rw [envBig_apply]; rfl⟩
    | _ => simp [Exp.substEnv] at hu
  | fix _ =>
    intro env e σ hc hu
    cases e with
    | bvar j => exact envBig_eval_bvar hc hu
    | fix body =>
      exact ⟨.fixClo env body, ⟨by simpa [Exp.lcb] using hc.1, hc.2⟩,
        by simpa [RVal.rb, Exp.substEnv] using hu, by rw [envBig_apply]; rfl⟩
    | _ => simp [Exp.substEnv] at hu
  | pair _ _ ih1 ih2 =>
    intro env e σ hc hu
    cases e with
    | bvar j => exact envBig_eval_bvar hc hu
    | pair e1 e2 =>
      simp only [Exp.substEnv, Exp.pair.injEq] at hu
      simp only [EnvCfg.WF, Exp.lcb, Bool.and_eq_true] at hc
      obtain ⟨v2, hv2, hr2, hE2⟩ := ih2 (σ := σ) ⟨hc.1.2, hc.2⟩ hu.2
      obtain ⟨v1, hv1, hr1, hE1⟩ := ih1 (σ := σ) ⟨hc.1.1, hc.2⟩ hu.1
      refine ⟨.pair v1 v2, ⟨hv1, hv2⟩, by simp [RVal.rb, hr1, hr2], ?_⟩
      rw [envBig_apply]
      simp only [envStep, evalK, stepOps, Step.interp]
      rw [hE2, dirac_bind_rcfg, envBig_apply]
      simp only [envStep, resumeK, stepOps, Step.interp]
      rw [hE1, dirac_bind_rcfg, envBig_apply]
      rfl
    | _ => simp [Exp.substEnv] at hu
  | inl _ ih =>
    intro env e σ hc hu
    cases e with
    | bvar j => exact envBig_eval_bvar hc hu
    | inl e1 =>
      simp only [Exp.substEnv, Exp.inl.injEq] at hu
      obtain ⟨v1, hv1, hr1, hE1⟩ := ih (e := e1) (σ := σ) ⟨by simpa [Exp.lcb] using hc.1, hc.2⟩ hu
      refine ⟨.inl v1, hv1, by simp [RVal.rb, hr1], ?_⟩
      rw [envBig_apply]
      simp only [envStep, evalK, stepOps, Step.interp]
      rw [hE1, dirac_bind_rcfg, envBig_apply]
      rfl
    | _ => simp [Exp.substEnv] at hu
  | inr _ ih =>
    intro env e σ hc hu
    cases e with
    | bvar j => exact envBig_eval_bvar hc hu
    | inr e1 =>
      simp only [Exp.substEnv, Exp.inr.injEq] at hu
      obtain ⟨v1, hv1, hr1, hE1⟩ := ih (e := e1) (σ := σ) ⟨by simpa [Exp.lcb] using hc.1, hc.2⟩ hu
      refine ⟨.inr v1, hv1, by simp [RVal.rb, hr1], ?_⟩
      rw [envBig_apply]
      simp only [envStep, evalK, stepOps, Step.interp]
      rw [hE1, dirac_bind_rcfg, envBig_apply]
      rfl
    | _ => simp [Exp.substEnv] at hu

/-- Every configuration that reads back to a value returns that value at once. -/
theorem envBig_val {c : EnvCfg rT} (hc : c.WF) (hv : c.rb.expr.isValue) :
    (envBig c).map RCfg.rb = dirac c.rb := by
  cases c with
  | eval env e σ =>
    obtain ⟨w⟩ := hv
    obtain ⟨v, _, hr, hE⟩ := envBig_eval_val w hc rfl
    rw [hE, map_dirac' RCfg.measurable_rb]
    simp [RCfg.rb, EnvCfg.rb, hr]
  | apply f v σ => obtain ⟨w⟩ := hv; cases w
  | resume f v σ =>
    obtain ⟨hf, hvw⟩ := hc
    obtain ⟨w⟩ := hv
    cases f <;> simp only [EnvCfg.rb, Frame.fill] at w
    case pairR env e1 =>
      cases w with
      | pair w1 _ =>
        obtain ⟨v1, _, hr1, hE1⟩ := envBig_eval_val w1 (σ := σ) hf rfl
        rw [envBig_apply]
        simp only [envStep, resumeK, stepOps, Step.interp]
        rw [hE1, dirac_bind_rcfg, envBig_apply]
        simp only [envStep, resumeK, stepOps, Step.interp]
        rw [map_dirac' RCfg.measurable_rb]
        simp [RCfg.rb, EnvCfg.rb, Frame.fill, RVal.rb, hr1]
    case pairL | inl | inr =>
      rw [envBig_apply]
      simp only [envStep, resumeK, stepOps, Step.interp]
      rw [map_dirac' RCfg.measurable_rb]
      rfl
    all_goals cases w

/-- The smallest read-back result of the machine over all configurations reading back
to `ρ`. -/
def Yb (ρ : Cfg rT) : Measure (Cfg rT) :=
  ⨅ (c : EnvCfg rT) (_ : c.WF ∧ c.rb = ρ), (envBig c).map RCfg.rb

theorem Yb_le' {c : EnvCfg rT} {ρ : Cfg rT} (hc : c.WF) (hρ : c.rb = ρ) :
    Yb ρ ≤ (envBig c).map RCfg.rb :=
  iInf₂_le c ⟨hc, hρ⟩

theorem Yb_le {c : EnvCfg rT} (hc : c.WF) : Yb c.rb ≤ (envBig c).map RCfg.rb :=
  Yb_le' hc rfl

theorem Yb_retVal : RetVal (Yb (rT := rT)) := by
  intro e σ he
  have hspec := RVal.ofExp_spec he
  apply le_antisymm
  · have hc : (EnvCfg.eval [RVal.ofExp e] (.bvar 0) σ).WF :=
      ⟨by simp [Exp.lcb], hspec.2, trivial⟩
    have hrb : (EnvCfg.eval [RVal.ofExp e] (.bvar 0) σ).rb = ⟨e, σ⟩ := by
      simp [EnvCfg.rb, Exp.substEnv, RVal.rbEnv, hspec.1]
    refine (iInf₂_le _ ⟨hc, hrb⟩).trans ?_
    rw [envBig_val hc (by rw [hrb]; exact he), hrb]
  · refine le_iInf₂ fun c ⟨hc, hρ⟩ => ?_
    rw [envBig_val hc (by rw [hρ]; exact he), hρ]

theorem envBig_appL_eq (v w : RVal rT) (σ : State rT) :
    envBig (.resume (.appL v) w σ) = envBig (.resume (.applyTo v) w σ) := by
  rw [envBig_apply, envBig_apply (.resume (.applyTo v) w σ)]; rfl

/-- Two ways of evaluating `e` and applying the result to `v` agree. -/
theorem envBig_appR_eq (env : Env rT) (e : Exp rT) (v : RVal rT) (σ : State rT) :
    envBig (.resume (.appR env e) v σ) = (Step.evalThen env e σ (.applyTo v)).interp envBig := by
  rw [envBig_apply]
  simp only [envStep, resumeK, stepOps, Step.interp, envBig_appL_eq]

section Discrete

variable [Countable rT]

/-! ## Well-formedness is preserved -/

/-- `X` returns well-formed values on well-formed configurations. -/
def Pres (X : EnvCfg rT → Measure (RCfg rT)) : Prop :=
  ∀ c, c.WF → ∀ᵐ r ∂(X c), r.val.WF

theorem Step.interp_wf {X : EnvCfg rT → Measure (RCfg rT)} (hX : Pres X) {s : Step rT}
    (hs : s.Good) : ∀ᵐ r ∂(s.interp X), r.val.WF := by
  cases s with
  | ret v σ => exact (ae_dirac_iff MeasurableSet.of_discrete).mpr hs
  | eval env e σ => exact hX _ hs
  | evalThen env e σ f =>
    exact ae_bind_disc ((hX _ hs.1).mono fun r hr => hX _ ⟨hs.2, hr⟩)
  | apply f v σ => exact hX _ hs
  | stuck => simp [Step.interp]
  | uniform z σ =>
    exact (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
      (ae_of_all _ fun _ => trivial)
  | uniformReal σ =>
    exact (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
      (ae_of_all _ fun _ => trivial)

theorem envΦ_pres {X : EnvCfg rT → Measure (RCfg rT)} (hX : Pres X) : Pres (envΦ X) :=
  fun _ hc => Step.interp_wf hX (envStep_good hc)

theorem envIter_pres (n : ℕ) : Pres (envΦ^[n] (⊥ : EnvCfg rT → Measure (RCfg rT))) := by
  induction n with
  | zero =>
    intro c _
    simp only [ae_iff]
    rfl
  | succ n ih => rw [iterate_succ_apply']; exact envΦ_pres ih

theorem envBig_pres : Pres (envBig (rT := rT)) := by
  intro c hc
  rw [ae_iff, envBig, iSup_apply,
    iSup_apply_of_monotone (fun _ _ h => envIter_mono h c) MeasurableSet.of_discrete]
  exact ENNReal.iSup_eq_zero.mpr fun n => ae_iff.mp (envIter_pres n c hc)

/-! ## Bounding one step by read-back evaluations -/

/-- What one step becomes after readback, when calls are evaluated by `Z`. -/
def Step.bnd (Z : Cfg rT → Measure (Cfg rT)) : Step rT → Measure (Cfg rT)
  | .ret v σ => dirac ⟨v.rb, σ⟩
  | .eval env e σ => Z (EnvCfg.eval env e σ).rb
  | .evalThen env e σ f =>
    (Z (EnvCfg.eval env e σ).rb).bind fun ρ => Z ⟨f.fill ρ.expr, ρ.state⟩
  | .apply f v σ => Z (EnvCfg.apply f v σ).rb
  | .stuck _ => 0
  | .uniform z σ => Cfg.uniform z σ
  | .uniformReal σ => Cfg.uniformReal σ

theorem bind_map_disc {μ : Measure (RCfg rT)} {g : RCfg rT → Cfg rT}
    {k : Cfg rT → Measure (Cfg rT)} : (μ.map g).bind k = μ.bind (k ∘ g) := by
  rw [Measure.bind, Measure.bind, map_map Measurable.of_discrete Measurable.of_discrete]

theorem Step.map_interp_uniformReal (σ : State rT) (X : EnvCfg rT → Measure (RCfg rT)) :
    ((Step.uniformReal σ).interp X).map RCfg.rb = Cfg.uniformReal σ := by
  simp only [Step.interp]
  rw [map_map RCfg.measurable_rb Measurable.of_discrete]
  rfl

/-- If `X` is bounded by `Z` after readback, so is one interpreted step. -/
theorem Step.map_interp_le {X : EnvCfg rT → Measure (RCfg rT)} {Z : Cfg rT → Measure (Cfg rT)}
    (hX : Pres X) (hXZ : ∀ c, c.WF → (X c).map RCfg.rb ≤ Z c.rb) {s : Step rT} (hs : s.Good) :
    (s.interp X).map RCfg.rb ≤ s.bnd Z := by
  cases s with
  | ret v σ => simp only [Step.interp, Step.bnd, map_dirac' RCfg.measurable_rb]; rfl
  | eval env e σ => exact hXZ _ hs
  | evalThen env e σ f =>
    simp only [Step.interp, Step.bnd]
    rw [map_bind_disc Measurable.of_discrete]
    calc (X (.eval env e σ)).bind (fun r => (X (.resume f r.val r.state)).map RCfg.rb)
        ≤ (X (.eval env e σ)).bind ((fun ρ => Z ⟨f.fill ρ.expr, ρ.state⟩) ∘ RCfg.rb) :=
          bind_mono_ae_disc ((hX _ hs.1).mono fun r hr => hXZ (.resume f r.val r.state) ⟨hs.2, hr⟩)
      _ = ((X (.eval env e σ)).map RCfg.rb).bind fun ρ => Z ⟨f.fill ρ.expr, ρ.state⟩ :=
          bind_map_disc.symm
      _ ≤ _ := bind_mono_disc (hXZ _ hs.1) fun _ => le_rfl
  | apply f v σ => exact hXZ _ hs
  | stuck => simp [Step.interp, Step.bnd]
  | uniform z σ => exact (Step.map_interp_uniform z σ X).le
  | uniformReal σ => exact (Step.map_interp_uniformReal σ X).le

/-- If `Z` is bounded by `X` after readback on well-formed configurations, so is one
interpreted step. -/
theorem Step.bnd_le_map_interp {X : EnvCfg rT → Measure (RCfg rT)}
    {Z : Cfg rT → Measure (Cfg rT)} (hX : Pres X)
    (hZX : ∀ c, c.WF → Z c.rb ≤ (X c).map RCfg.rb) {s : Step rT} (hs : s.Good) :
    s.bnd Z ≤ (s.interp X).map RCfg.rb := by
  cases s with
  | ret v σ => simp only [Step.interp, Step.bnd, map_dirac' RCfg.measurable_rb]; rfl
  | eval env e σ => exact hZX _ hs
  | evalThen env e σ f =>
    simp only [Step.interp, Step.bnd]
    rw [map_bind_disc Measurable.of_discrete]
    calc (Z (EnvCfg.eval env e σ).rb).bind (fun ρ => Z ⟨f.fill ρ.expr, ρ.state⟩)
        ≤ ((X (.eval env e σ)).map RCfg.rb).bind fun ρ => Z ⟨f.fill ρ.expr, ρ.state⟩ :=
          bind_mono_disc (hZX _ hs.1) fun _ => le_rfl
      _ = (X (.eval env e σ)).bind ((fun ρ => Z ⟨f.fill ρ.expr, ρ.state⟩) ∘ RCfg.rb) :=
          bind_map_disc
      _ ≤ _ := bind_mono_ae_disc
          ((hX _ hs.1).mono fun r hr => hZX (.resume f r.val r.state) ⟨hs.2, hr⟩)
  | apply f v σ => exact hZX _ hs
  | stuck => simp [Step.interp, Step.bnd]
  | uniform z σ => exact (Step.map_interp_uniform z σ X).ge
  | uniformReal σ => exact (Step.map_interp_uniformReal σ X).ge

/-! ## Head configurations -/

/-- Configurations whose step is a head step: leaves of `eval`, applications of non-`fix`
values, and frames with all their subterms evaluated, except those that continue with an
application (`appL`, `applyTo`, `case`). -/
def EnvCfg.IsHead : EnvCfg rT → Prop
  | .eval _ e _ =>
    match e with
    | .bvar _ | .fvar _ | .fail | .lit _ | .lam _ | .fix _ | .urand => True
    | _ => False
  | .apply f _ _ =>
    match f with
    | .fixClo .. => False
    | _ => True
  | .resume f _ _ =>
    match f with
    | .pairR .. | .appR .. | .binopR .. | .storeR .. | .randR .. | .appL _ | .applyTo _
    | .case .. => False
    | _ => True

theorem RetVal.bind_rb {Z : Cfg rT → Measure (Cfg rT)} (hZ : RetVal Z) {v : RVal rT}
    (hv : v.WF) (σ : State rT) (f : Cfg rT → Measure (Cfg rT)) :
    (Z ⟨v.rb, σ⟩).bind f = f ⟨v.rb, σ⟩ :=
  hZ.bind_eq hv.isValue f

/-- At a head configuration, one unfolding of `bigStepF` is the machine's step read back. -/
theorem bigStepF_eq_bnd {Z : Cfg rT → Measure (Cfg rT)} (hZ : RetVal Z) {c : EnvCfg rT}
    (hc : c.WF) (hhead : c.IsHead) : bigStepF measureOps Z c.rb = (envStep c).bnd Z := by
  cases c with
  | eval env e σ =>
    obtain ⟨he, henv⟩ := hc
    cases e <;> simp only [EnvCfg.IsHead] at hhead
    case bvar j =>
      simp only [Exp.lcb, decide_eq_true_eq] at he
      obtain ⟨v, hj⟩ : ∃ v, env[j]? = some v := ⟨env[j], List.getElem?_eq_getElem he⟩
      have hv := henv.getElem? hj
      simp only [EnvCfg.rb, Exp.substEnv, Nat.zero_le, ite_true, Nat.sub_zero,
        RVal.rbEnv_getElem?, hj, Option.map_some, Option.getD_some, envStep, evalK, stepOps,
        Step.bnd]
      exact bigStepF_val hZ σ hv.isValue
    case lam body =>
      have hv : (RVal.clo env body).WF := ⟨by simpa [Exp.lcb] using he, henv⟩
      exact bigStepF_val hZ σ hv.isValue
    case fix body =>
      have hv : (RVal.fixClo env body).WF := ⟨by simpa [Exp.lcb] using he, henv⟩
      exact bigStepF_val hZ σ hv.isValue
    all_goals rfl
  | apply f v σ =>
    obtain ⟨hf, hv⟩ := hc
    simp only [EnvCfg.rb, bigStepF, measureOps]
    rw [hZ.bind_rb hv, hZ.bind_rb hf]
    cases f <;> simp only [EnvCfg.IsHead] at hhead
    case clo env body =>
      simp only [RVal.rb, envStep, applyK, stepOps, Step.bnd, EnvCfg.rb]
      rw [RVal.rb_clo_open hf.2]
    all_goals simp [RVal.rb, envStep, applyK, stepOps, Step.bnd]
  | resume f v σ =>
    obtain ⟨hf, hv⟩ := hc
    cases f <;> simp only [EnvCfg.IsHead] at hhead <;>
      simp only [EnvCfg.rb, Frame.fill, bigStepF, measureOps, envStep, resumeK, stepOps] <;>
      (try rw [hZ.bind_rb hf]) <;> rw [hZ.bind_rb hv] <;> dsimp only
    case unop op =>
      cases h : op.eval v.rb with
      | none => simp [Step.bnd]
      | some r => simp [Step.bnd, (RVal.ofExp_spec (UnOp.eval_isValue h)).1]
    case binopL op v2 =>
      cases h : op.eval v.rb v2.rb with
      | none => simp [Step.bnd]
      | some r => simp [Step.bnd, (RVal.ofExp_spec (BinOp.eval_isValue h)).1]
    case scrut p =>
      rw [← (Pat.tryMatchR_spec p hv).1]
      cases p.tryMatchR v <;> simp [Step.bnd, RVal.rb]
    case alloc => cases v.rb.toVal? <;> simp [Step.bnd, RVal.rb]
    case load =>
      cases v with
      | lit b =>
        cases b with
        | loc ℓ =>
          cases h : σ.heap[ℓ]? with
          | none => simp [RVal.rb, h, Step.bnd]
          | some w =>
            simp [RVal.rb, h, Step.bnd, (RVal.ofExp_spec (Val.isValue w)).1, Exp.ofVal]
        | _ => simp [RVal.rb, Step.bnd]
      | _ => simp [RVal.rb, Step.bnd]
    case storeL v2 =>
      cases v with
      | lit b =>
        cases b with
        | loc ℓ =>
          cases v2.rb.toVal? with
          | none => simp [RVal.rb, Step.bnd]
          | some w => cases h : σ.heap[ℓ]? <;> simp [h, RVal.rb, Step.bnd]
        | _ => simp [RVal.rb, Step.bnd]
      | _ => simp [RVal.rb, Step.bnd]
    case randL v2 =>
      cases v with
      | lit b =>
        cases b with
        | int z =>
          cases v2 with
          | lit b2 =>
            cases b2 with
            | unit => rfl
            | lbl α =>
              simp only [RVal.rb]
              cases σ.tapes[α]? with
              | none => simp [Step.bnd]
              | some t =>
                obtain ⟨bound, ns⟩ := t
                simp only
                split
                · cases ns <;> simp [Step.bnd, RVal.rb]
                · rfl
            | _ => simp [RVal.rb, Step.bnd]
          | _ => simp [RVal.rb, Step.bnd]
        | _ => simp [RVal.rb, Step.bnd]
      | _ => simp [RVal.rb, Step.bnd]
    case cond env et ef =>
      cases v with
      | lit b =>
        cases b with
        | bool b => cases b <;> simp [RVal.rb, Step.bnd, EnvCfg.rb]
        | _ => simp [RVal.rb, Step.bnd]
      | _ => simp [RVal.rb, Step.bnd]
    case tape =>
      cases v with
      | lit b => cases b <;> simp [RVal.rb, Step.bnd]
      | _ => simp [RVal.rb, Step.bnd]
    all_goals (cases v <;> simp [RVal.rb, Step.bnd])

/-! ## `envBig ≤ bigStep` after readback -/

theorem bigStep_frame {f : Frame rT} (hf : f.WF) (e : Exp rT) (σ : State rT) :
    bigStep ⟨f.fill e, σ⟩ = (bigStep ⟨e, σ⟩).bind fun ρ => bigStep ⟨f.fill ρ.expr, ρ.state⟩ := by
  obtain ⟨Ki, hKi⟩ := Frame.exists_item hf
  simp only [hKi]
  exact bigStep_fillItem Ki e σ

theorem bnd_evalThen_bigStep {env : Env rT} {e : Exp rT} {σ : State rT} {f : Frame rT}
    (hf : f.WF) :
    (Step.evalThen env e σ f).bnd bigStep = bigStep ⟨f.fill (e.substEnv 0 (RVal.rbEnv env)), σ⟩ :=
  (bigStep_frame hf _ σ).symm

theorem bigStep_eq_F (ρ : Cfg rT) : bigStep ρ = bigStepF measureOps bigStep ρ :=
  congrFun bigStep_unfold ρ

/-- The machine's step, read back and evaluated by `bigStep`, is `bigStep` itself. -/
theorem envStep_bnd_bigStep {c : EnvCfg rT} (hc : c.WF) :
    (envStep c).bnd bigStep = bigStep c.rb := by
  by_cases hhead : c.IsHead
  · rw [← bigStepF_eq_bnd bigStep_retVal hc hhead, ← bigStep_eq_F]
  cases c with
  | eval env e σ =>
    obtain ⟨he, henv⟩ := hc
    cases e <;> simp only [EnvCfg.IsHead, not_true_eq_false] at hhead <;>
      simp only [Exp.lcb, Bool.and_eq_true] at he <;>
      simp only [envStep, evalK, stepOps] <;>
      rw [bnd_evalThen_bigStep (by simp_all [Frame.WF])] <;> rfl
  | apply f v σ =>
    obtain ⟨hf, hv⟩ := hc
    cases f <;> simp only [EnvCfg.IsHead, not_true_eq_false, not_false_eq_true] at hhead
    case fixClo env body =>
      simp only [envStep, applyK, stepOps]
      rw [bnd_evalThen_bigStep (f := .applyTo v) hv]
      simp only [EnvCfg.rb, Frame.fill]
      rw [← RVal.rb_clo_open (v := .fixClo env body) hf.2]
      conv_rhs => rw [bigStep_eq_F]
      simp only [bigStepF, measureOps]
      rw [bigStep_retVal.bind_rb hv, bigStep_retVal.bind_rb (v := .fixClo env body) hf]
      rfl
  | resume f v σ =>
    obtain ⟨hf, hv⟩ := hc
    cases f <;> simp only [EnvCfg.IsHead, not_true_eq_false, not_false_eq_true] at hhead
    case appL v2 | applyTo v2 => rfl
    case case env el er =>
      simp only [EnvCfg.rb, Frame.fill]
      rw [bigStep_eq_F ⟨.case _ _ _, σ⟩]
      simp only [bigStepF, measureOps]
      rw [bigStep_retVal.bind_rb hv]
      dsimp only
      cases v with
      | inl v | inr v =>
        simp only [envStep, resumeK, stepOps, RVal.rb]
        exact bnd_evalThen_bigStep (f := .applyTo v) hv
      | _ => simp [envStep, resumeK, stepOps, RVal.rb, Step.bnd]
    all_goals
      simp only [envStep, resumeK, stepOps]
      rw [bnd_evalThen_bigStep (by simpa [Frame.WF] using hv)]
      rfl

theorem envIter_le (n : ℕ) :
    ∀ c : EnvCfg rT, c.WF → ((envΦ^[n] ⊥) c).map RCfg.rb ≤ bigStep c.rb := by
  induction n with
  | zero =>
    intro c _
    rw [Function.iterate_zero_apply, Pi.bot_apply, show (⊥ : Measure (RCfg rT)) = 0 from rfl,
      Measure.map_zero]
    exact Measure.zero_le _
  | succ n ih =>
    intro c hc
    rw [iterate_succ_apply', envΦ, ← envStep_bnd_bigStep hc]
    exact Step.map_interp_le (envIter_pres n) ih (envStep_good hc)

/-- The read-back of `envBig` is bounded by `bigStep`. -/
theorem envBig_le {c : EnvCfg rT} (hc : c.WF) : (envBig c).map RCfg.rb ≤ bigStep c.rb := by
  rw [envBig, iSup_apply]
  exact map_iSup_le_of (fun _ _ h => envIter_mono h c) fun n => envIter_le n c hc

/-! ## `bigStep ≤ envBig` after readback -/

theorem Yb_onlyVal' {c : EnvCfg rT} {ρ : Cfg rT} (hc : c.WF) (hρ : c.rb = ρ) :
    ∀ᵐ ρ' ∂(Yb ρ), ρ'.expr.isValue :=
  ae_mono (Yb_le' hc hρ) <|
    (ae_map_iff RCfg.measurable_rb.aemeasurable MeasurableSet.of_discrete).mpr
      ((envBig_pres c hc).mono fun _ hr => hr.isValue)

/-- The bind step of `bigStepF` at one frame, when the hole's results are values almost surely. -/
theorem bigStepF_fillItem_loc {R : Cfg rT → Measure (Cfg rT)} (hV : RetVal R) (Ki : EctxItem rT)
    (e : Exp rT) (σ : State rT) (hC : ∀ᵐ c ∂(R ⟨e, σ⟩), c.expr.isValue) :
    bigStepF measureOps R ⟨Ki.fillItem e, σ⟩ =
      (R ⟨e, σ⟩).bind fun c => bigStepF measureOps R ⟨Ki.fillItem c.expr, c.state⟩ := by
  cases Ki <;> simp only [EctxItem.fillItem, bigStepF, measureOps, Exp.ofVal] <;>
    (try rw [hV.bind_eq (Val.isValue _)]) <;>
    refine bind_congr_right (hC.mono fun ⟨v, σ'⟩ hv => ?_) <;> dsimp only <;>
    (try rw [hV.bind_eq (Val.isValue _)]) <;> rw [hV.bind_eq hv]

/-- The claim of the lower bound at one configuration. -/
def ClaimGe (c : EnvCfg rT) : Prop := bigStepF measureOps Yb c.rb ≤ (envBig c).map RCfg.rb

theorem claimGe_head {c : EnvCfg rT} (hc : c.WF) (hhead : c.IsHead) : ClaimGe c := by
  unfold ClaimGe
  rw [bigStepF_eq_bnd Yb_retVal hc hhead, envBig_apply]
  exact Step.bnd_le_map_interp envBig_pres (fun _ hc => Yb_le hc) (envStep_good hc)

/-- Evaluating a subterm and resuming a frame: reduce to the claim at the frame. -/
theorem claimGe_chain {env : Env rT} {e : Exp rT} {σ : State rT} {f : Frame rT}
    (he : (EnvCfg.eval env e σ).WF) (hf : f.WF)
    (hres : ∀ v σ', v.WF → ClaimGe (.resume f v σ')) :
    bigStepF measureOps Yb ⟨f.fill (e.substEnv 0 (RVal.rbEnv env)), σ⟩ ≤
      ((Step.evalThen env e σ f).interp envBig).map RCfg.rb := by
  obtain ⟨Ki, hKi⟩ := Frame.exists_item hf
  have hC : ∀ᵐ c ∂(Yb ⟨e.substEnv 0 (RVal.rbEnv env), σ⟩), c.expr.isValue :=
    Yb_onlyVal' he rfl
  have hYle : Yb ⟨e.substEnv 0 (RVal.rbEnv env), σ⟩ ≤ (envBig (.eval env e σ)).map RCfg.rb :=
    Yb_le' he rfl
  rw [hKi, bigStepF_fillItem_loc Yb_retVal Ki (e.substEnv 0 (RVal.rbEnv env)) σ hC]
  simp only [Step.interp]
  rw [map_bind_disc Measurable.of_discrete]
  calc (Yb ⟨e.substEnv 0 (RVal.rbEnv env), σ⟩).bind
        (fun c => bigStepF measureOps Yb ⟨Ki.fillItem c.expr, c.state⟩)
      ≤ ((envBig (.eval env e σ)).map RCfg.rb).bind
          (fun c => bigStepF measureOps Yb ⟨Ki.fillItem c.expr, c.state⟩) :=
        bind_mono_disc hYle fun _ => le_rfl
    _ = (envBig (.eval env e σ)).bind
          ((fun c => bigStepF measureOps Yb ⟨Ki.fillItem c.expr, c.state⟩) ∘ RCfg.rb) :=
        bind_map_disc
    _ ≤ _ := bind_mono_ae_disc ((envBig_pres _ he).mono fun r hr => by
          have := hres r.val r.state hr
          simp only [ClaimGe, EnvCfg.rb, hKi] at this
          exact this)

theorem claimGe_apply {f v : RVal rT} {σ : State rT} (hc : (EnvCfg.apply f v σ).WF) :
    ClaimGe (.apply f v σ) := by
  cases f
  case fixClo env body =>
    obtain ⟨hf, hv⟩ := hc
    unfold ClaimGe
    simp only [EnvCfg.rb, bigStepF, measureOps]
    rw [Yb_retVal.bind_rb hv, Yb_retVal.bind_rb (v := .fixClo env body) hf]
    simp only [RVal.rb]
    rw [show (body.substEnv 1 (RVal.rbEnv env)).open' (.fix (body.substEnv 1 (RVal.rbEnv env))) =
      body.substEnv 0 (RVal.rbEnv (.fixClo env body :: env)) from
        RVal.rb_clo_open (v := .fixClo env body) hf.2, envBig_apply]
    simp only [envStep, applyK, stepOps]
    rw [← envBig_appR_eq]
    exact Yb_le (c := .resume (.appR (.fixClo env body :: env) body) v σ)
      ⟨⟨by simpa [Nat.add_comm] using hf.1, hf, hf.2⟩, hv⟩
  all_goals exact claimGe_head hc trivial

theorem claimGe_resume_value {f : Frame rT} {v : RVal rT} {σ : State rT}
    (hc : (EnvCfg.resume f v σ).WF)
    (hf : ∀ env e, f ≠ .pairR env e ∧ f ≠ .appR env e ∧ (∀ op, f ≠ .binopR op env e) ∧
      f ≠ .storeR env e ∧ f ≠ .randR env e) :
    ClaimGe (.resume f v σ) := by
  obtain ⟨hfw, hv⟩ := hc
  cases f
  case appL v2 | applyTo v2 =>
    have := claimGe_apply (σ := σ) ⟨hv, hfw⟩
    unfold ClaimGe at this ⊢
    rw [envBig_apply]; exact this
  case case env el er =>
    unfold ClaimGe
    simp only [EnvCfg.rb, Frame.fill, bigStepF, measureOps]
    rw [Yb_retVal.bind_rb hv]
    dsimp only
    cases v with
    | inl v =>
      simp only [RVal.rb]
      rw [envBig_apply]
      simp only [envStep, resumeK, stepOps]
      rw [← envBig_appR_eq]
      exact Yb_le (c := .resume (.appR env el) v σ) ⟨⟨hfw.1, hfw.2.2⟩, hv⟩
    | inr v =>
      simp only [RVal.rb]
      rw [envBig_apply]
      simp only [envStep, resumeK, stepOps]
      rw [← envBig_appR_eq]
      exact Yb_le (c := .resume (.appR env er) v σ) ⟨⟨hfw.2.1, hfw.2.2⟩, hv⟩
    | _ => simp only [RVal.rb]; exact Measure.zero_le _
  case pairR env e => exact absurd rfl (hf env e).1
  case appR env e => exact absurd rfl (hf env e).2.1
  case binopR op env e => exact absurd rfl ((hf env e).2.2.1 op)
  case storeR env e => exact absurd rfl (hf env e).2.2.2.1
  case randR env e => exact absurd rfl (hf env e).2.2.2.2
  all_goals exact claimGe_head ⟨hfw, hv⟩ trivial

theorem claimGe_resume {f : Frame rT} {v : RVal rT} {σ : State rT}
    (hc : (EnvCfg.resume f v σ).WF) : ClaimGe (.resume f v σ) := by
  obtain ⟨hfw, hv⟩ := hc
  cases f
  case pairR env e1 | appR env e1 | binopR op env e1 | storeR env e1 | randR env e1 =>
    unfold ClaimGe
    rw [envBig_apply]
    simp only [envStep, resumeK, stepOps]
    refine le_of_eq_of_le ?_
      (claimGe_chain hfw hv fun w σ' hw => claimGe_resume_value ⟨hv, hw⟩ (by simp))
    rfl
  all_goals exact claimGe_resume_value ⟨hfw, hv⟩ (by simp)

theorem claimGe_eval {env : Env rT} {e : Exp rT} {σ : State rT}
    (hc : (EnvCfg.eval env e σ).WF) : ClaimGe (.eval env e σ) := by
  by_cases hhead : (EnvCfg.eval env e σ).IsHead
  · exact claimGe_head hc hhead
  obtain ⟨he, henv⟩ := hc
  unfold ClaimGe
  rw [envBig_apply]
  cases e <;> simp only [EnvCfg.IsHead, not_true_eq_false] at hhead <;>
    simp only [Exp.lcb, Bool.and_eq_true] at he <;>
    simp only [envStep, evalK, stepOps] <;>
    exact le_of_eq_of_le (by rfl) (claimGe_chain (by simp_all [EnvCfg.WF]) (by simp_all [Frame.WF])
      fun w σ' hw => claimGe_resume ⟨by simp_all [Frame.WF], hw⟩)

/-- `ClaimGe` holds on every well-formed configuration. -/
theorem claim_ge {c : EnvCfg rT} (hc : c.WF) : ClaimGe c := by
  cases c with
  | eval => exact claimGe_eval hc
  | apply => exact claimGe_apply hc
  | resume => exact claimGe_resume hc

/-- `bigStep` is bounded by `Yb`. -/
theorem bigStep_le_Yb : bigStep (rT := rT) ≤ Yb :=
  OrderHom.lfp_le _ fun _ => le_iInf₂ fun _ ⟨hc, hρ⟩ => hρ ▸ claim_ge hc

/-! ## The main theorem -/

/-- On a well-formed configuration, the environment machine's results, read back, are
distributed exactly as `bigStep` of the read-back configuration. -/
theorem envBig_map_rb {c : EnvCfg rT} (hc : c.WF) : (envBig c).map RCfg.rb = bigStep c.rb :=
  le_antisymm (envBig_le hc) ((bigStep_le_Yb c.rb).trans (Yb_le hc))

/-- For a closed program, the environment machine agrees with the big-step semantics, and so
with the reduction semantics. -/
theorem envBig_eval_closed {e : Exp rT} (he : e.IsLocallyClosed) (σ : State rT) :
    (envBig (.eval [] e σ)).map RCfg.rb = limExec ⟨e, σ⟩ := by
  rw [envBig_map_rb (c := .eval [] e σ) ⟨Exp.lc_imp_lcb he, trivial⟩, ← bigStep_eq_limExec]
  simp [EnvCfg.rb, RVal.rbEnv]

end Discrete

end ProbLang
