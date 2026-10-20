module

public import Metrology.ProbLang.CtxStep
import Metrology.ProbLang.Syntax.Notation
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

/-! # Deterministic steps

`PureStep`, `PureExec` and `DetStep`: steps with a single outcome, closed under contexts. -/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

/-- `n`-fold composition of the relation `r`. -/
def nsteps (r : α → α → Prop) : ℕ → α → α → Prop
  | 0,   a, b => a = b
  | n+1, a, b => ∃ c, r a c ∧ nsteps r n c b

/-- `Measure.map_dirac` without `MeasurableSingletonClass`, which general `rT` lacks. -/
theorem map_dirac' {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) (a : α) : (dirac a).map f = dirac (f a) := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.dirac_apply' _ (hf hs), Measure.dirac_apply' _ hs]
  rfl

/-- `e1` steps to `e2` deterministically in every state. -/
structure PureStep (e1 e2 : Exp rT) : Prop where
  safe : ∀ σ, Reducible e1 σ
  det  : ∀ σ, primStep ⟨e1, σ⟩ = dirac ⟨e2, σ⟩

/-- Under `φ`, `e1` reaches `e2` in `n` pure steps. -/
class PureExec (φ : outParam Prop) (n : outParam ℕ) (e1 e2 : Exp rT) : Prop where
  pure_exec : φ → nsteps PureStep n e1 e2

/-- `PureStep` for a head redex. -/
structure PureHeadStep (e1 e2 : Exp rT) : Prop where
  safe : ∀ σ : State rT, HeadReducible e1 σ
  det  : ∀ σ : State rT, headStep ⟨e1, σ⟩ = dirac ⟨e2, σ⟩
  dec  : e1.decompItem = none

theorem PureHeadStep.toPureStep {e1 e2 : Exp rT} (h : PureHeadStep e1 e2) :
    PureStep e1 e2 :=
  ⟨fun σ => by rw [Reducible, primStep_eq_headStep h.dec]; exact h.safe σ,
   fun σ => primStep_eq_headStep h.dec ▸ h.det σ⟩

theorem PureStep.fill (K : Ectx rT) {e1 e2 : Exp rT} (h : PureStep e1 e2) :
    PureStep (K.fill e1) (K.fill e2) := by
  refine ⟨fun σ => (h.safe σ).fill K, fun σ => ?_⟩
  rw [primStep_fill (val_stuck (h.safe σ)), h.det σ]
  exact map_dirac' (Ectx.fillCfg.measurable K) _

theorem PureStep.fill_nsteps (K : Ectx rT) {n : ℕ} {e1 e2 : Exp rT}
    (h : nsteps PureStep n e1 e2) :
    nsteps PureStep n (K.fill e1) (K.fill e2) := by
  induction n generalizing e1 e2 with
  | zero => exact congrArg K.fill (show e1 = e2 from h)
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    exact ⟨K.fill c, hstep.fill K, ih hrest⟩

theorem PureExec.fill (K : Ectx rT) {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    [h : PureExec φ n e1 e2] : PureExec φ n (K.fill e1) (K.fill e2) where
  pure_exec hφ := PureStep.fill_nsteps K (h.pure_exec hφ)

theorem PureExec.reducible {σ : State rT} {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    (hφ : φ) [h : PureExec φ (n + 1) e1 e2] :
    Reducible e1 σ := by
  obtain ⟨_, hstep, _⟩ := h.pure_exec hφ
  exact hstep.safe σ

theorem PureExec.not_val {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    (hφ : φ) [h : PureExec φ (n + 1) e1 e2] :
    ¬e1.isValue := by
  obtain ⟨_, hstep, _⟩ := h.pure_exec hφ
  exact val_stuck (hstep.safe default)

theorem rtc_pure_step_val {n : ℕ} {v : Val rT} {e : Exp rT}
    (h : nsteps PureStep n v.1 e) :
    e.toVal? = some v := by
  cases n with
  | zero =>
    obtain rfl : v.1 = e := h
    exact Exp.toVal?_ofVal v
  | succ n =>
    obtain ⟨_, hstep, -⟩ := h
    exact absurd v.2.toIsValue (val_stuck (hstep.safe default))

theorem PureHeadStep.of_det (e1 e2 : Exp rT)
    (hdec : e1.decompItem = none)
    (hdet : ∀ σ, headStep ⟨e1, σ⟩ = dirac ⟨e2, σ⟩) :
    PureHeadStep e1 e2 := by
  refine ⟨fun σ => ?_, hdet, hdec⟩
  unfold HeadReducible; rw [hdet σ]; simp

/-- A head step from `cfg1` that deterministically gives `cfg2`. -/
structure DetHeadStep (cfg1 cfg2 : Cfg rT) : Prop where
  safe : HeadReducible cfg1.expr cfg1.state
  det  : headStep cfg1 = dirac cfg2
  dec  : cfg1.expr.decompItem = none

theorem DetHeadStep.pos {cfg1 cfg2 : Cfg rT} (h : DetHeadStep cfg1 cfg2) :
    0 < headStep cfg1 {cfg2} := by rw [h.det]; simp

theorem DetHeadStep.of_det (cfg1 cfg2 : Cfg rT)
    (hdec : cfg1.expr.decompItem = none)
    (hdet : headStep cfg1 = dirac cfg2) : DetHeadStep cfg1 cfg2 where
  safe := by obtain ⟨e1, σ1⟩ := cfg1; unfold HeadReducible; rw [hdet]; simp
  det  := hdet
  dec  := hdec

theorem PureHeadStep.toDetHeadStep {e1 e2 : Exp rT} (h : PureHeadStep e1 e2) (σ : State rT) :
    DetHeadStep ⟨e1, σ⟩ ⟨e2, σ⟩ :=
  ⟨h.safe σ, h.det σ, h.dec⟩

/-- A step from `cfg1` that deterministically gives `cfg2`. -/
structure DetStep (cfg1 cfg2 : Cfg rT) : Prop where
  safe : Reducible cfg1.expr cfg1.state
  det  : primStep cfg1 = dirac cfg2

theorem DetStep.pos {cfg1 cfg2 : Cfg rT} (h : DetStep cfg1 cfg2) :
    0 < primStep cfg1 {cfg2} := by rw [h.det]; simp

theorem DetHeadStep.toDetStep {cfg1 cfg2 : Cfg rT} (h : DetHeadStep cfg1 cfg2) :
    DetStep cfg1 cfg2 where
  safe := by obtain ⟨e1, σ1⟩ := cfg1; rw [Reducible, primStep_eq_headStep h.dec]; exact h.safe
  det := by obtain ⟨e1, σ1⟩ := cfg1; rw [primStep_eq_headStep h.dec]; exact h.det

/-- `cfg1` reaches `cfg2` in `n` deterministic steps. -/
class DetExec (n : ℕ) (cfg1 cfg2 : Cfg rT) : Prop where
  det_exec : nsteps DetStep n cfg1 cfg2

theorem DetExec.succ {cfg1 cfg2 cfg3 : Cfg rT} {n : ℕ}
    (hstep : DetStep cfg1 cfg2) [hrest : DetExec n cfg2 cfg3] :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

theorem PureHeadStep.app_lam {body v : Exp rT}
    (hlam : (Exp.lam body).IsLocallyClosed) (hv : IsVal v) :
    PureHeadStep (.app (.lam body) v) (Exp.open' body v) :=
  .of_det _ _ (by
    obtain ⟨_, h1⟩ := Exp.toVal?_eq_some_of_isValue (⟨hv⟩ : v.isValue)
    obtain ⟨_, h2⟩ := Exp.toVal?_eq_some_of_isValue (⟨.lam hlam⟩ : (Exp.lam body).isValue)
    simp [Exp.decompItem, h1, h2]) fun _ => by simp [headStep, Exp.isValM_some' hv]

instance pureExec_app_lam {body v : Exp rT} :
    PureExec (v.isValue ∧ (Exp.lam body).IsLocallyClosed) 1
      (.app (.lam body) v) (Exp.open' body v) where
  pure_exec h := ⟨_, (PureHeadStep.app_lam h.2 h.1.some).toPureStep, rfl⟩

theorem PureHeadStep.cond_true (et ef : Exp rT) :
    PureHeadStep (.cond pl(#(.bool true)) et ef) et :=
  .of_det _ _ rfl fun _ => by simp [headStep]

theorem PureHeadStep.cond_false (et ef : Exp rT) :
    PureHeadStep (.cond pl(#(.bool false)) et ef) ef :=
  .of_det _ _ rfl fun _ => by simp [headStep]

instance pureExec_cond_true {et ef : Exp rT} :
    PureExec True 1 (.cond pl(#(.bool true)) et ef) et where
  pure_exec _ := ⟨_, (PureHeadStep.cond_true et ef).toPureStep, rfl⟩

instance pureExec_cond_false {et ef : Exp rT} :
    PureExec True 1 (.cond pl(#(.bool false)) et ef) ef where
  pure_exec _ := ⟨_, (PureHeadStep.cond_false et ef).toPureStep, rfl⟩

theorem PureHeadStep.fst_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) :
    PureHeadStep (.fst (.pair e1 e2)) e1 :=
  .of_det _ _
    (by
      obtain ⟨_, h⟩ := Exp.toVal?_eq_some_of_isValue (⟨.pair h1 h2⟩ : (Exp.pair e1 e2).isValue)
      simp [Exp.decompItem, h])
    fun _ => by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2]

theorem PureHeadStep.snd_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) :
    PureHeadStep (.snd (.pair e1 e2)) e2 :=
  .of_det _ _
    (by
      obtain ⟨_, h⟩ := Exp.toVal?_eq_some_of_isValue (⟨.pair h1 h2⟩ : (Exp.pair e1 e2).isValue)
      simp [Exp.decompItem, h])
    fun _ => by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2]

instance pureExec_fst_pair {e1 e2 : Exp rT} :
    PureExec (e1.isValue ∧ e2.isValue) 1 (.fst (.pair e1 e2)) e1 where
  pure_exec h := ⟨_, (PureHeadStep.fst_pair h.1.some h.2.some).toPureStep, rfl⟩

instance pureExec_snd_pair {e1 e2 : Exp rT} :
    PureExec (e1.isValue ∧ e2.isValue) 1 (.snd (.pair e1 e2)) e2 where
  pure_exec h := ⟨_, (PureHeadStep.snd_pair h.1.some h.2.some).toPureStep, rfl⟩

theorem PureHeadStep.case_inl {v el er : Exp rT} (hv : IsVal v) :
    PureHeadStep (.case (.inl v) el er) (el.app v) :=
  .of_det _ _
    (by
      obtain ⟨_, h⟩ := Exp.toVal?_eq_some_of_isValue (⟨.inl hv⟩ : (Exp.inl v).isValue)
      simp [Exp.decompItem, h])
    fun _ => by simp [headStep, Exp.isValM_some' hv]

theorem PureHeadStep.case_inr {v el er : Exp rT} (hv : IsVal v) :
    PureHeadStep (.case (.inr v) el er) (er.app v) :=
  .of_det _ _
    (by
      obtain ⟨_, h⟩ := Exp.toVal?_eq_some_of_isValue (⟨.inr hv⟩ : (Exp.inr v).isValue)
      simp [Exp.decompItem, h])
    fun _ => by simp [headStep, Exp.isValM_some' hv]

instance pureExec_case_inl {v el er : Exp rT} :
    PureExec v.isValue 1 (.case (.inl v) el er) (el.app v) where
  pure_exec hv := ⟨_, (PureHeadStep.case_inl hv.some).toPureStep, rfl⟩

instance pureExec_case_inr {v el er : Exp rT} :
    PureExec v.isValue 1 (.case (.inr v) el er) (er.app v) where
  pure_exec hv := ⟨_, (PureHeadStep.case_inr hv.some).toPureStep, rfl⟩

theorem PureHeadStep.binop {op : BinOp} {e1 e2 r : Exp rT}
    (h1 : IsVal e1) (h2 : IsVal e2) (heval : op.eval e1 e2 = some r) :
    PureHeadStep (.binop op e1 e2) r :=
  .of_det _ _ (by
    obtain ⟨_, h1'⟩ := Exp.toVal?_eq_some_of_isValue (⟨h1⟩ : e1.isValue)
    obtain ⟨_, h2'⟩ := Exp.toVal?_eq_some_of_isValue (⟨h2⟩ : e2.isValue)
    simp [Exp.decompItem, h1', h2']) fun _ => by
    simp [headStep, Option.unwrapM, Exp.isValM_some' h1, Exp.isValM_some' h2, heval]

instance pureExec_binop {op : BinOp} {e1 e2 r : Exp rT} :
    PureExec (e1.isValue ∧ e2.isValue ∧ op.eval e1 e2 = some r) 1
      (.binop op e1 e2) r where
  pure_exec h := ⟨_, (PureHeadStep.binop h.1.some h.2.1.some h.2.2).toPureStep, rfl⟩

theorem PureHeadStep.unop {op : UnOp} {e r : Exp rT}
    (hv : IsVal e) (heval : op.eval e = some r) :
    PureHeadStep (.unop op e) r :=
  .of_det _ _
    (by
      obtain ⟨_, h⟩ := Exp.toVal?_eq_some_of_isValue (⟨hv⟩ : e.isValue)
      simp [Exp.decompItem, h])
    fun _ => by simp [headStep, Option.unwrapM, Exp.isValM_some' hv, heval]

instance pureExec_unop {op : UnOp} {e r : Exp rT} :
    PureExec (e.isValue ∧ op.eval e = some r) 1 (.unop op e) r where
  pure_exec h := ⟨_, (PureHeadStep.unop h.1.some h.2).toPureStep, rfl⟩

theorem PureHeadStep.app_fix {body v : Exp rT}
    (hfix : (Exp.fix body).IsLocallyClosed) (hv : IsVal v) :
    PureHeadStep (.app (.fix body) v) (Exp.app (Exp.open' body (.fix body)) v) :=
  .of_det _ _ (by
    obtain ⟨_, h1⟩ := Exp.toVal?_eq_some_of_isValue (⟨hv⟩ : v.isValue)
    obtain ⟨_, h2⟩ := Exp.toVal?_eq_some_of_isValue (⟨.fix hfix⟩ : (Exp.fix body).isValue)
    simp [Exp.decompItem, h1, h2]) fun _ => by simp [headStep, Exp.isValM_some' hv]

instance pureExec_app_fix {body v : Exp rT} :
    PureExec (v.isValue ∧ (Exp.fix body).IsLocallyClosed) 1
      (.app (.fix body) v) (Exp.app (Exp.open' body (.fix body)) v) where
  pure_exec h := ⟨_, (PureHeadStep.app_fix h.2 h.1.some).toPureStep, rfl⟩

theorem PureHeadStep.scrut_some {v : Exp rT} {p : Pat rT} {b : Exp rT}
    (hv : IsVal v) (hmatch : Pat.tryMatch p v = some b) :
    PureHeadStep (.scrut v p) (.inl b) :=
  .of_det _ _
    (by
      obtain ⟨_, h⟩ := Exp.toVal?_eq_some_of_isValue (⟨hv⟩ : v.isValue)
      simp [Exp.decompItem, h])
    fun _ => by simp [headStep, Exp.isValM_some' hv, hmatch]

theorem PureHeadStep.scrut_none {v : Exp rT} {p : Pat rT}
    (hv : IsVal v) (hmatch : Pat.tryMatch p v = none) :
    PureHeadStep (.scrut v p) (.inr pl(#(.unit))) :=
  .of_det _ _
    (by
      obtain ⟨_, h⟩ := Exp.toVal?_eq_some_of_isValue (⟨hv⟩ : v.isValue)
      simp [Exp.decompItem, h])
    fun _ => by simp [headStep, Exp.isValM_some' hv, hmatch]

instance pureExec_scrut_some {v : Exp rT} {p : Pat rT} {b : Exp rT} :
    PureExec (v.isValue ∧ Pat.tryMatch p v = some b) 1 (.scrut v p) (.inl b) where
  pure_exec h := ⟨_, (PureHeadStep.scrut_some h.1.some h.2).toPureStep, rfl⟩

instance pureExec_scrut_none {v : Exp rT} {p : Pat rT} :
    PureExec (v.isValue ∧ Pat.tryMatch p v = none) 1 (.scrut v p) (.inr pl(#(.unit))) where
  pure_exec h := ⟨_, (PureHeadStep.scrut_none h.1.some h.2).toPureStep, rfl⟩

theorem DetHeadStep.fst_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) (σ : State rT) :
    DetHeadStep ⟨.fst (.pair e1 e2), σ⟩ ⟨e1, σ⟩ :=
  (PureHeadStep.fst_pair h1 h2).toDetHeadStep σ

theorem DetHeadStep.snd_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) (σ : State rT) :
    DetHeadStep ⟨.snd (.pair e1 e2), σ⟩ ⟨e2, σ⟩ :=
  (PureHeadStep.snd_pair h1 h2).toDetHeadStep σ

theorem DetHeadStep.cond_true (et ef : Exp rT) (σ : State rT) :
    DetHeadStep ⟨.cond pl(#(.bool true)) et ef, σ⟩ ⟨et, σ⟩ :=
  (PureHeadStep.cond_true et ef).toDetHeadStep σ

theorem DetHeadStep.cond_false (et ef : Exp rT) (σ : State rT) :
    DetHeadStep ⟨.cond pl(#(.bool false)) et ef, σ⟩ ⟨ef, σ⟩ :=
  (PureHeadStep.cond_false et ef).toDetHeadStep σ

theorem DetHeadStep.app_lam {body v : Exp rT}
    (hlam : (Exp.lam body).IsLocallyClosed) (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.app (.lam body) v, σ⟩ ⟨Exp.open' body v, σ⟩ :=
  (PureHeadStep.app_lam hlam hv).toDetHeadStep σ

theorem DetHeadStep.app_fix {body v : Exp rT}
    (hfix : (Exp.fix body).IsLocallyClosed) (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.app (.fix body) v, σ⟩
      ⟨Exp.app (Exp.open' body (.fix body)) v, σ⟩ :=
  (PureHeadStep.app_fix hfix hv).toDetHeadStep σ

theorem DetHeadStep.unop {op : UnOp} {e result : Exp rT}
    (hv : IsVal e)
    (heval : UnOp.eval op e = some result) (σ : State rT) :
    DetHeadStep ⟨.unop op e, σ⟩ ⟨result, σ⟩ :=
  (PureHeadStep.unop hv heval).toDetHeadStep σ

theorem DetHeadStep.binop {op : BinOp} {e1 e2 result : Exp rT}
    (h1 : IsVal e1) (h2 : IsVal e2)
    (heval : BinOp.eval op e1 e2 = some result) (σ : State rT) :
    DetHeadStep ⟨.binop op e1 e2, σ⟩ ⟨result, σ⟩ :=
  (PureHeadStep.binop h1 h2 heval).toDetHeadStep σ

theorem DetHeadStep.case_inl {v el er : Exp rT} (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.case (.inl v) el er, σ⟩ ⟨el.app v, σ⟩ :=
  (PureHeadStep.case_inl hv).toDetHeadStep σ

theorem DetHeadStep.case_inr {v el er : Exp rT} (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.case (.inr v) el er, σ⟩ ⟨er.app v, σ⟩ :=
  (PureHeadStep.case_inr hv).toDetHeadStep σ

theorem DetHeadStep.alloc {v : Exp rT} (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.alloc v, σ⟩
      ⟨pl(#(.loc σ.heap.fresh)), σ.update_heap (·.insert σ.heap.fresh ⟨v, hv, hv.lc⟩)⟩ := by
  obtain ⟨w, hw⟩ := hv.check?_some
  exact .of_det _ _
    (by
      obtain ⟨_, hd⟩ := Exp.toVal?_eq_some_of_isValue (⟨hv⟩ : v.isValue)
      simp [Exp.decompItem, hd])
    (by simp [headStep, Exp.asValM, Exp.toVal?, hw, IsVal.subsingleton hv w])

theorem DetHeadStep.load {ℓ : Loc} {v : Val rT} (σ : State rT) (hlookup : σ.heap[ℓ]? = some v) :
    DetHeadStep ⟨pl(!#(.loc ℓ)), σ⟩ ⟨.ofVal v, σ⟩ :=
  .of_det _ _ rfl (by simp [headStep, hlookup])

theorem DetHeadStep.store {ℓ : Loc} {e : Exp rT} {v_old v_new : Val rT}
    (σ : State rT)
    (hlookup : σ.heap[ℓ]? = some v_old)
    (hnew : e.toVal? = some v_new) :
    DetHeadStep ⟨.store pl(#(.loc ℓ)) e, σ⟩ ⟨pl(#(.unit)), σ.update_heap (·.insert ℓ v_new)⟩ :=
  .of_det _ _
    (by obtain ⟨_, hd⟩ := Exp.toVal?_eq_some_of_isValue (e := (Exp.lit (.loc ℓ) : Exp rT)) ⟨.lit⟩
        simp [Exp.decompItem, hnew, hd])
    (by simp [headStep, Exp.asValM, hnew, hlookup])

theorem DetStep.fill (K : Ectx rT) {cfg1 cfg2 : Cfg rT} (h : DetStep cfg1 cfg2) :
    DetStep ⟨K.fill cfg1.expr, cfg1.state⟩ ⟨K.fill cfg2.expr, cfg2.state⟩ where
  safe := h.safe.fill K
  det := by
    obtain ⟨e1, σ1⟩ := cfg1
    rw [primStep_fill (val_stuck h.safe), h.det]
    exact map_dirac' (Ectx.fillCfg.measurable K) _

theorem DetExec.refl (cfg : Cfg rT) : DetExec 0 cfg cfg where
  det_exec := rfl

theorem DetExec.cons {cfg1 cfg2 cfg3 : Cfg rT} {n : ℕ}
    (hstep : DetStep cfg1 cfg2) (hrest : DetExec n cfg2 cfg3) :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

/-! ## `PureSteps`: the reflexive-transitive closure of `PureStep`

Pure computations (e.g. the list recursions of `Metrology/Code/Switching.lean`) are proved once as
`PureSteps` by induction, then used by `wp_pure_steps` and `step_pure_steps`. -/

/-- `e1` reaches `e2` in some number of pure steps. -/
def PureSteps (e1 e2 : Exp rT) : Prop := ∃ n, nsteps PureStep n e1 e2

namespace PureSteps

theorem refl (e : Exp rT) : PureSteps e e := ⟨0, rfl⟩

theorem single {e1 e2 : Exp rT} (h : PureStep e1 e2) : PureSteps e1 e2 := ⟨1, e2, h, rfl⟩

theorem trans {e1 e2 e3 : Exp rT} (h1 : PureSteps e1 e2) (h2 : PureSteps e2 e3) :
    PureSteps e1 e3 := by
  obtain ⟨n, h1⟩ := h1
  obtain ⟨m, h2⟩ := h2
  induction n generalizing e1 with
  | zero => exact ⟨m, (show e1 = e2 from h1) ▸ h2⟩
  | succ n ih =>
    obtain ⟨c, hc, hrest⟩ := h1
    obtain ⟨k, hk⟩ := ih hrest
    exact ⟨k + 1, c, hc, hk⟩

theorem fill (K : Ectx rT) {e1 e2 : Exp rT} :
    PureSteps e1 e2 → PureSteps (K.fill e1) (K.fill e2)
  | ⟨n, h⟩ => ⟨n, PureStep.fill_nsteps K h⟩

theorem of_pureExec {φ : Prop} {n : ℕ} {e1 e2 : Exp rT} [h : PureExec φ n e1 e2]
    (hφ : φ) : PureSteps e1 e2 := ⟨n, h.pure_exec hφ⟩

/-- A `PureSteps` fact as an unconditional `PureExec`, for the `PureExec`-shaped rules. -/
theorem pureExec {e1 e2 : Exp rT} (h : PureSteps e1 e2) :
    PureExec True h.choose e1 e2 := ⟨fun _ => h.choose_spec⟩

end PureSteps

end ProbLang
end

