module

public import Metrology.ProbLang.CtxStep
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Deterministic steps

Dirac steps: `PureStep` (state-independent) with `PureExec`, and `DetStep` (one configuration). -/

noncomputable section
open MeasureTheory Measure
open ProbLang.Exp
open ProbLang.Pat (tryMatch)
open ProbLang.Option (unwrapM)

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT] {e1 e2 : Exp rT} {n : ℕ} (K : Ectx rT)

/-! ## Pure steps -/

/-- `n`-fold composition of the relation `r`. -/
def nsteps {α : Type _} (r : α → α → Prop) : ℕ → α → α → Prop
  | 0,   a, b => a = b
  | n+1, a, b => ∃ c, r a c ∧ nsteps r n c b

/-- `e1` steps to `e2` deterministically in every state. -/
structure PureStep (e1 e2 : Exp rT) : Prop where
  /-- `e1` is reducible in every state. -/
  safe : ∀ σ, Reducible e1 σ
  /-- `e1` steps to `e2` with probability one, in every state. -/
  det : ∀ σ, primStep ⟨e1, σ⟩ = dirac ⟨e2, σ⟩

/-- Under `φ`, `e1` reaches `e2` in `n` pure steps; instance search outputs `φ` and `n`. -/
class PureExec (φ : outParam Prop) (n : outParam ℕ) (e1 e2 : Exp rT) : Prop where
  /-- The side condition `φ` gives `n` pure steps from `e1` to `e2`. -/
  pure_exec : φ → nsteps PureStep n e1 e2

/-- `PureStep` for a head redex. -/
structure PureHeadStep (e1 e2 : Exp rT) : Prop where
  /-- `e1` is head reducible in every state. -/
  safe : ∀ σ : State rT, HeadReducible e1 σ
  /-- `e1` head-steps to `e2` with probability one, in every state. -/
  det : ∀ σ : State rT, headStep ⟨e1, σ⟩ = dirac ⟨e2, σ⟩
  /-- `e1` is its own redex (no context frame), so `primStep = headStep`. -/
  dec : e1.decompItem = none

/-- A pure head step is a pure step. -/
theorem PureHeadStep.toPureStep (h : PureHeadStep e1 e2) : PureStep e1 e2 :=
  ⟨fun σ => by rw [Reducible, primStep_eq_headStep h.dec]; exact h.safe σ,
   fun σ => primStep_eq_headStep h.dec ▸ h.det σ⟩

/-- Pure steps are closed under evaluation contexts. -/
theorem PureStep.fill (h : PureStep e1 e2) : PureStep (K.fill e1) (K.fill e2) := by
  -- a reducible, non-value `e1` makes `K.fill e1` step exactly as `e1` does, inside `K`
  refine ⟨fun σ => (h.safe σ).fill K, fun σ => ?_⟩
  rw [primStep_fill (val_stuck (h.safe σ)), h.det σ]
  exact map_dirac' (Ectx.fillCfg.measurable K) _

/-- `PureStep.fill` along `n` steps. -/
theorem PureStep.fill_nsteps
    (h : nsteps PureStep n e1 e2) :
    nsteps PureStep n (K.fill e1) (K.fill e2) := by
  induction n generalizing e1 e2 with
  | zero => exact congrArg K.fill (show e1 = e2 from h)
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    exact ⟨K.fill c, hstep.fill K, ih hrest⟩

open PureStep (fill_nsteps)

/-- `PureExec` is closed under evaluation contexts. -/
theorem PureExec.fill {φ : Prop}
    [h : PureExec φ n e1 e2] : PureExec φ n (K.fill e1) (K.fill e2) where
  pure_exec hφ := fill_nsteps K (h.pure_exec hφ)

/-! ## `PureSteps`: the reflexive-transitive closure of `PureStep`

Pure computations (e.g. the list recursions of `Metrology/Code/Switching.lean`) are proved once as
`PureSteps` by induction, then used by `wp_pure_steps` and `step_pure_steps`. -/

/-- `e1` reaches `e2` in some number of pure steps. -/
def PureSteps (e1 e2 : Exp rT) : Prop := ∃ n, nsteps PureStep n e1 e2

namespace PureSteps

/-- `PureSteps` is reflexive. -/
theorem refl (e : Exp rT) : PureSteps e e := ⟨0, rfl⟩

/-- A pure step is a run of pure steps. -/
theorem single (h : PureStep e1 e2) : PureSteps e1 e2 := ⟨1, e2, h, rfl⟩

/-- `PureSteps` is transitive. -/
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

/-- `PureSteps` is closed under evaluation contexts. -/
theorem fill :
    PureSteps e1 e2 → PureSteps (K.fill e1) (K.fill e2)
  | ⟨n, h⟩ => ⟨n, fill_nsteps K h⟩

/-- A `PureExec` instance gives a run of pure steps. -/
theorem of_pureExec {φ : Prop} [h : PureExec φ n e1 e2]
    (hφ : φ) : PureSteps e1 e2 := ⟨n, h.pure_exec hφ⟩

/-- A `PureSteps` fact as an unconditional `PureExec`, for the `PureExec`-shaped rules. -/
theorem pureExec (h : PureSteps e1 e2) :
    PureExec True h.choose e1 e2 := ⟨fun _ => h.choose_spec⟩

end PureSteps

/-! ## Pure steps of each construct

The head-step rules `PureHeadStep.foo`, then their `PureExec` instances `pureExec_foo`. -/

section PureRules

variable {e r v body el er b : Exp rT} {p : Pat rT}

/-- Build a `PureHeadStep` from the head-step equation and `decompItem = none`. -/
theorem PureHeadStep.of_det (e1 e2 : Exp rT)
    (hdec : e1.decompItem = none)
    (hdet : ∀ σ, headStep ⟨e1, σ⟩ = dirac ⟨e2, σ⟩) :
    PureHeadStep e1 e2 := by
  refine ⟨fun σ => ?_, hdet, hdec⟩
  unfold HeadReducible; rw [hdet σ]; simp

/-- Beta reduction of a locally closed `lam` applied to a value. -/
theorem PureHeadStep.app_lam
    (hlam : (lam body).IsLocallyClosed) (hv : IsVal v) :
    PureHeadStep (.app (.lam body) v) (open' body v) :=
  .of_det _ _ (by
    obtain ⟨_, h1⟩ := toVal?_eq_some_of_isValue (⟨hv⟩ : v.isValue)
    obtain ⟨_, h2⟩ := toVal?_eq_some_of_isValue (⟨.lam hlam⟩ : (lam body).isValue)
    simp [decompItem, h1, h2]) fun _ => by simp [headStep, isValM_some' hv]

/-- `if true` steps to the first branch. -/
theorem PureHeadStep.cond_true (et ef : Exp rT) : PureHeadStep (.cond pl(#true) et ef) et :=
  .of_det _ _ rfl fun _ => by simp [headStep]

/-- `if false` steps to the second branch. -/
theorem PureHeadStep.cond_false (et ef : Exp rT) : PureHeadStep (.cond pl(#false) et ef) ef :=
  .of_det _ _ rfl fun _ => by simp [headStep]

/-- `fst` of a pair of values steps to the first component. -/
theorem PureHeadStep.fst_pair (h1 : IsVal e1) (h2 : IsVal e2) :
    PureHeadStep (.fst (.pair e1 e2)) e1 :=
  .of_det _ _ (by
    obtain ⟨_, h⟩ := toVal?_eq_some_of_isValue (⟨.pair h1 h2⟩ : (pair e1 e2).isValue)
    simp [decompItem, h]) fun _ => by simp [headStep, isValM_some' h1, isValM_some' h2]

/-- `snd` of a pair of values steps to the second component. -/
theorem PureHeadStep.snd_pair (h1 : IsVal e1) (h2 : IsVal e2) :
    PureHeadStep (.snd (.pair e1 e2)) e2 :=
  .of_det _ _ (by
    obtain ⟨_, h⟩ := toVal?_eq_some_of_isValue (⟨.pair h1 h2⟩ : (pair e1 e2).isValue)
    simp [decompItem, h]) fun _ => by simp [headStep, isValM_some' h1, isValM_some' h2]

/-- `case` on `inl v` steps to the left branch applied to `v`. -/
theorem PureHeadStep.case_inl (hv : IsVal v) : PureHeadStep (.case (.inl v) el er) (el.app v) :=
  .of_det _ _ (by
    obtain ⟨_, h⟩ := toVal?_eq_some_of_isValue (⟨.inl hv⟩ : (inl v).isValue)
    simp [decompItem, h]) fun _ => by simp [headStep, isValM_some' hv]

/-- `case` on `inr v` steps to the right branch applied to `v`. -/
theorem PureHeadStep.case_inr (hv : IsVal v) : PureHeadStep (.case (.inr v) el er) (er.app v) :=
  .of_det _ _ (by
    obtain ⟨_, h⟩ := toVal?_eq_some_of_isValue (⟨.inr hv⟩ : (inr v).isValue)
    simp [decompItem, h]) fun _ => by simp [headStep, isValM_some' hv]

/-- A binary operation on values steps to its result. -/
theorem PureHeadStep.binop {op : BinOp}
    (h1 : IsVal e1) (h2 : IsVal e2) (heval : op.eval e1 e2 = some r) :
    PureHeadStep (.binop op e1 e2) r :=
  .of_det _ _ (by
    obtain ⟨_, h1'⟩ := toVal?_eq_some_of_isValue (⟨h1⟩ : e1.isValue)
    obtain ⟨_, h2'⟩ := toVal?_eq_some_of_isValue (⟨h2⟩ : e2.isValue)
    simp [decompItem, h1', h2']) fun _ => by
    simp [headStep, unwrapM, isValM_some' h1, isValM_some' h2, heval]

/-- A unary operation on a value steps to its result. -/
theorem PureHeadStep.unop {op : UnOp}
    (hv : IsVal e) (heval : op.eval e = some r) :
    PureHeadStep (.unop op e) r :=
  .of_det _ _ (by
    obtain ⟨_, h⟩ := toVal?_eq_some_of_isValue (⟨hv⟩ : e.isValue)
    simp [decompItem, h]) fun _ => by simp [headStep, unwrapM, isValM_some' hv, heval]

/-- A locally closed `fix` applied to a value unfolds once. -/
theorem PureHeadStep.app_fix
    (hfix : (fix body).IsLocallyClosed) (hv : IsVal v) :
    PureHeadStep (.app (.fix body) v) (app (open' body (.fix body)) v) :=
  .of_det _ _ (by
    obtain ⟨_, h1⟩ := toVal?_eq_some_of_isValue (⟨hv⟩ : v.isValue)
    obtain ⟨_, h2⟩ := toVal?_eq_some_of_isValue (⟨.fix hfix⟩ : (fix body).isValue)
    simp [decompItem, h1, h2]) fun _ => by simp [headStep, isValM_some' hv]

/-- A successful pattern match on a value steps to `inl` of the body. -/
theorem PureHeadStep.scrut_some
    (hv : IsVal v) (hmatch : tryMatch p v = some b) :
    PureHeadStep (.scrut v p) (.inl b) :=
  .of_det _ _ (by
    obtain ⟨_, h⟩ := toVal?_eq_some_of_isValue (⟨hv⟩ : v.isValue)
    simp [decompItem, h]) fun _ => by simp [headStep, isValM_some' hv, hmatch]

/-- A failed pattern match on a value steps to `inr ()`. -/
theorem PureHeadStep.scrut_none
    (hv : IsVal v) (hmatch : tryMatch p v = none) :
    PureHeadStep (.scrut v p) (.inr pl(#())) :=
  .of_det _ _ (by
    obtain ⟨_, h⟩ := toVal?_eq_some_of_isValue (⟨hv⟩ : v.isValue)
    simp [decompItem, h]) fun _ => by simp [headStep, isValM_some' hv, hmatch]

open PureHeadStep (app_lam fst_pair snd_pair case_inl case_inr binop unop app_fix scrut_some
  scrut_none)

/-- Beta reduction as a `PureExec` step. -/
instance pureExec_app_lam :
    PureExec (v.isValue ∧ (lam body).IsLocallyClosed) 1 (.app (.lam body) v) (open' body v) where
  pure_exec h := ⟨_, (app_lam h.2 h.1.some).toPureStep, rfl⟩

/-- `if true` as a `PureExec` step. -/
instance pureExec_cond_true {et ef : Exp rT} :
    PureExec True 1 (.cond pl(#true) et ef) et where
  pure_exec _ := ⟨_, (PureHeadStep.cond_true et ef).toPureStep, rfl⟩

/-- `if false` as a `PureExec` step. -/
instance pureExec_cond_false {et ef : Exp rT} :
    PureExec True 1 (.cond pl(#false) et ef) ef where
  pure_exec _ := ⟨_, (PureHeadStep.cond_false et ef).toPureStep, rfl⟩

/-- `fst` of a pair as a `PureExec` step. -/
instance pureExec_fst_pair :
    PureExec (e1.isValue ∧ e2.isValue) 1 (.fst (.pair e1 e2)) e1 where
  pure_exec h := ⟨_, (fst_pair h.1.some h.2.some).toPureStep, rfl⟩

/-- `snd` of a pair as a `PureExec` step. -/
instance pureExec_snd_pair :
    PureExec (e1.isValue ∧ e2.isValue) 1 (.snd (.pair e1 e2)) e2 where
  pure_exec h := ⟨_, (snd_pair h.1.some h.2.some).toPureStep, rfl⟩

/-- `case` on `inl` as a `PureExec` step. -/
instance pureExec_case_inl :
    PureExec v.isValue 1 (.case (.inl v) el er) (el.app v) where
  pure_exec hv := ⟨_, (case_inl hv.some).toPureStep, rfl⟩

/-- `case` on `inr` as a `PureExec` step. -/
instance pureExec_case_inr :
    PureExec v.isValue 1 (.case (.inr v) el er) (er.app v) where
  pure_exec hv := ⟨_, (case_inr hv.some).toPureStep, rfl⟩

/-- A binary operation as a `PureExec` step. -/
instance pureExec_binop {op : BinOp} :
    PureExec (e1.isValue ∧ e2.isValue ∧ op.eval e1 e2 = some r) 1 (.binop op e1 e2) r where
  pure_exec h := ⟨_, (binop h.1.some h.2.1.some h.2.2).toPureStep, rfl⟩

/-- A unary operation as a `PureExec` step. -/
instance pureExec_unop {op : UnOp} :
    PureExec (e.isValue ∧ op.eval e = some r) 1 (.unop op e) r where
  pure_exec h := ⟨_, (unop h.1.some h.2).toPureStep, rfl⟩

/-- Unfolding `fix` as a `PureExec` step. -/
instance pureExec_app_fix :
    PureExec (v.isValue ∧ (fix body).IsLocallyClosed) 1
      (.app (.fix body) v) (app (open' body (.fix body)) v) where
  pure_exec h := ⟨_, (app_fix h.2 h.1.some).toPureStep, rfl⟩

/-- A successful pattern match as a `PureExec` step. -/
instance pureExec_scrut_some :
    PureExec (v.isValue ∧ tryMatch p v = some b) 1 (.scrut v p) (.inl b) where
  pure_exec h := ⟨_, (scrut_some h.1.some h.2).toPureStep, rfl⟩

/-- A failed pattern match as a `PureExec` step. -/
instance pureExec_scrut_none :
    PureExec (v.isValue ∧ tryMatch p v = none) 1 (.scrut v p) (.inr pl(#())) where
  pure_exec h := ⟨_, (scrut_none h.1.some h.2).toPureStep, rfl⟩

end PureRules

/-! ## Deterministic steps of one configuration -/

section DetSteps

variable {cfg1 cfg2 cfg3 : Cfg rT}

/-- A head step from `cfg1` that deterministically gives `cfg2`. -/
structure DetHeadStep (cfg1 cfg2 : Cfg rT) : Prop where
  /-- `cfg1` is head reducible. -/
  safe : HeadReducible cfg1.expr cfg1.state
  /-- `cfg1` head-steps to `cfg2` with probability one. -/
  det : headStep cfg1 = dirac cfg2
  /-- `cfg1.expr` is its own redex (no context frame), so `primStep = headStep`. -/
  dec : cfg1.expr.decompItem = none

/-- Build a `DetHeadStep` from the head-step equation and `decompItem = none`. -/
theorem DetHeadStep.of_det (cfg1 cfg2 : Cfg rT)
    (hdec : cfg1.expr.decompItem = none)
    (hdet : headStep cfg1 = dirac cfg2) : DetHeadStep cfg1 cfg2 where
  safe := by obtain ⟨e1, σ1⟩ := cfg1; unfold HeadReducible; rw [hdet]; simp
  det := hdet
  dec := hdec

/-- A step from `cfg1` that deterministically gives `cfg2`. -/
structure DetStep (cfg1 cfg2 : Cfg rT) : Prop where
  /-- `cfg1` is reducible. -/
  safe : Reducible cfg1.expr cfg1.state
  /-- `cfg1` steps to `cfg2` with probability one. -/
  det : primStep cfg1 = dirac cfg2

/-- A deterministic head step is a deterministic step. -/
theorem DetHeadStep.toDetStep (h : DetHeadStep cfg1 cfg2) :
    DetStep cfg1 cfg2 where
  safe := by obtain ⟨e1, σ1⟩ := cfg1; rw [Reducible, primStep_eq_headStep h.dec]; exact h.safe
  det := by obtain ⟨e1, σ1⟩ := cfg1; rw [primStep_eq_headStep h.dec]; exact h.det

/-- `cfg1` reaches `cfg2` in `n` deterministic steps. -/
class DetExec (n : ℕ) (cfg1 cfg2 : Cfg rT) : Prop where
  /-- `cfg1` reaches `cfg2` in `n` deterministic steps. -/
  det_exec : nsteps DetStep n cfg1 cfg2

/-- One step, then the rest found by instance search. -/
theorem DetExec.succ
    (hstep : DetStep cfg1 cfg2) [hrest : DetExec n cfg2 cfg3] :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

/-- Deterministic steps are closed under evaluation contexts. -/
theorem DetStep.fill (h : DetStep cfg1 cfg2) :
    DetStep ⟨K.fill cfg1.expr, cfg1.state⟩ ⟨K.fill cfg2.expr, cfg2.state⟩ where
  safe := h.safe.fill K
  det := by
    obtain ⟨e1, σ1⟩ := cfg1
    rw [primStep_fill (val_stuck h.safe), h.det]
    exact map_dirac' (Ectx.fillCfg.measurable K) _

/-! ## Deterministic head steps of the stateful constructs

The rules `alloc`, `load`, `store`, `tape` and `rand_tape`, as `DetHeadStep`. -/

/-- Allocation of a value is a deterministic head step. -/
theorem DetHeadStep.alloc {v : Exp rT} (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.alloc v, σ⟩
      ⟨pl(#loc σ.heap.fresh), σ.update_heap (·.insert σ.heap.fresh ⟨v, hv, hv.lc⟩)⟩ := by
  obtain ⟨w, hw⟩ := hv.check?_some
  exact .of_det _ _ (by
    obtain ⟨_, hd⟩ := toVal?_eq_some_of_isValue (⟨hv⟩ : v.isValue)
    simp [decompItem, hd]) (by simp [headStep, asValM, toVal?, hw, IsVal.subsingleton hv w])

/-- Loading an allocated location is a deterministic head step. -/
theorem DetHeadStep.load {ℓ : Loc} {v : Val rT} (σ : State rT) (hlookup : σ.heap[ℓ]? = some v) :
    DetHeadStep ⟨pl(!#loc ℓ), σ⟩ ⟨.ofVal v, σ⟩ :=
  .of_det _ _ rfl (by simp [headStep, hlookup])

/-- Storing to an allocated location is a deterministic head step. -/
theorem DetHeadStep.store {ℓ : Loc} {e : Exp rT} {v_old v_new : Val rT} (σ : State rT)
    (hlookup : σ.heap[ℓ]? = some v_old) (hnew : e.toVal? = some v_new) :
    DetHeadStep ⟨.store pl(#loc ℓ) e, σ⟩ ⟨pl(#()), σ.update_heap (·.insert ℓ v_new)⟩ :=
  .of_det _ _ (by
    obtain ⟨_, hd⟩ := toVal?_eq_some_of_isValue (e := (lit (.loc ℓ) : Exp rT)) ⟨.lit⟩
    simp [decompItem, hnew, hd]) (by simp [headStep, asValM, hnew, hlookup])

/-- Tape allocation: `tape #z` deterministically allocates a fresh empty tape of
bound `z`. -/
theorem DetHeadStep.tape {z : Int} (σ : State rT) :
    DetHeadStep ⟨pl(tape(#z)), σ⟩
      ⟨pl(#lbl σ.tapes.fresh),
       σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))⟩ :=
  .of_det _ _
    (by obtain ⟨_, hd⟩ := toVal?_eq_some_of_isValue (e := (pl(#int z) : Exp rT)) ⟨.lit⟩;
        simp [decompItem, hd])
    (by simp [headStep])

/-- Tape rand: with `σ.tapes[l] = some ⟨z, n :: ns⟩`, the random sample
`rand z l` deterministically returns `n` and pops the head. -/
theorem DetHeadStep.rand_tape {z : Int} (l : Loc)
    (n : { k : Int // 0 ≤ k ∧ k < z }) (ns : List { k : Int // 0 ≤ k ∧ k < z })
    {σ : State rT} (htape : σ.tapes[l]? = some ⟨z, n :: ns⟩) :
    DetHeadStep ⟨pl(rand(#z, #lbl l)), σ⟩
      ⟨pl(#int n), σ.update_tapes (·.insert l ⟨z, ns⟩)⟩ :=
  .of_det _ _
    (by obtain ⟨_, hd1⟩ := toVal?_eq_some_of_isValue (e := (pl(#lbl l) : Exp rT)) ⟨.lit⟩
        obtain ⟨_, hd2⟩ := toVal?_eq_some_of_isValue (e := (pl(#int z) : Exp rT)) ⟨.lit⟩
        simp [decompItem, hd1, hd2])
    (by simp [headStep, htape])

end DetSteps

end ProbLang
end
