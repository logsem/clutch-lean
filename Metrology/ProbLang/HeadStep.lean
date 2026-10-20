module

public import Metrology.ProbLang.CoreMeasures
public meta import Metrology.Meta.Discrete
public import Metrology.ProbLang.Discrete
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Distributions.Uniform

/-! # Head reduction

`headStep`, one head-reduction step as a measure on configurations, and the `head_case` tactic.
Main results: `head_step_mass`, `headStep.measurable`, and `HeadStepSupport.possible`. -/

@[expose] public section

noncomputable section

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

/-! ## Measure combinators and samplers used by `headStep` -/

/-- Apply `f` to the value of an `Option`, giving the zero measure on `none`. -/
def Option.unwrapM {α : Type _} [MeasurableSpace β] (f : α → Measure β) : Option α → Measure β
| some v => f v
| none => 0

/-- Apply `f` to the value of `e`, giving the zero measure when `e` is not a value. -/
@[simp]
def Exp.asValM [MeasurableSpace T] (e : Exp rT) (f : Val rT → Measure T) : Measure T :=
  match e.toVal? with | none => 0 | some v => f v

/-- Keep the measure `m` when `e` is a value, otherwise the zero measure. -/
def Exp.isValM [MeasurableSpace T] (e : Exp rT) (m : Measure T) : Measure T :=
  if e.isValue then m else 0

@[simp] theorem Exp.isValM_some [MeasurableSpace T] {e : Exp α} {m : Measure T} (He : e.isValue) :
    e.isValM m = m := ite_eq_left He

theorem Exp.isValM_some' [MeasurableSpace T] {e : Exp α} {m : Measure T} (w : IsVal e) :
    e.isValM m = m := isValM_some w.toIsValue

@[simp] theorem Exp.isValM_none [MeasurableSpace T] {e : Exp α} {m : Measure T} (He : ¬ e.isValue) :
    e.isValM m = 0 := ite_eq_right He

/-- Witness that `z` is positive, if it is. -/
def Int.isPos (z : Int) : Option { z : Int // 0 < z } :=
  if H : 0 < z then some ⟨z, H⟩ else none

/-- Uniform sampler of `⟨.lit (.int n), σ⟩` for `0 ≤ n < z`; the constant `-1` when `z ≤ 0`. -/
def Cfg.uniform (z : Int) (σ : State rT) : Measure (Cfg rT) :=
  match z.isPos with
  | some ⟨z, Hz⟩ =>
    PMF.uniformOfFinset (.Ico 0 z) (Finset.nonempty_Ico.mpr Hz)
      |>.toMeasure.map (⟨.lit <| .int ·, σ⟩)
  | none => dirac ⟨.lit (.int (-1)), σ⟩

/-- Uniform sampler of `⟨.lit (.real r), σ⟩` with `r` drawn from `LawfulProbLangℝ.unifUnit`. -/
def Cfg.uniformReal (σ : State rT) : Measure (Cfg rT) :=
  (LawfulProbLangℝ.unifUnit (T := rT)).map (⟨.lit <| .real ·, σ⟩)

/-! ## The head step -/

-- The isValM/asValM guards make a head redex's evaluation-position subterms values
-- (`head_ctx_step_val`); this is what makes the redex in `K[e]` unique (`head_redex_unique`).
/-- One head-reduction step of a configuration, as a sub-probability measure; the zero measure means
there is no head redex (stuck). -/
def headStep : Cfg rT → Measure (Cfg rT)
| ⟨.app (.lam e1) e2, σ⟩ =>
  e2.isValM <|
  dirac ⟨Exp.open' e1 e2, σ⟩
| ⟨.app (.fix e1) e2, σ⟩ =>
  e2.isValM <|
  dirac ⟨Exp.app (Exp.open' e1 (.fix e1)) e2, σ⟩
| ⟨.unop op e, σ⟩ =>
  e.isValM <|
  (op.eval e).unwrapM <|
  (dirac ⟨·, σ⟩)
| ⟨.binop op e1 e2, σ⟩ =>
  e1.isValM <|
  e2.isValM <|
  (op.eval e1 e2).unwrapM <|
  (dirac ⟨·, σ⟩)
| ⟨.cond (.lit (.bool true)) et _, σ⟩ => dirac ⟨et, σ⟩
| ⟨.cond (.lit (.bool false)) _ ef, σ⟩ => dirac ⟨ef, σ⟩
| ⟨.fst (.pair e1 e2), σ⟩ => e1.isValM <| e2.isValM <| (dirac ⟨e1, σ⟩)
| ⟨.snd (.pair e1 e2), σ⟩ => e1.isValM <| e2.isValM <| (dirac ⟨e2, σ⟩)
| ⟨.case (.inl e) el _, σ⟩ => e.isValM <| (dirac ⟨el.app e, σ⟩)
| ⟨.case (.inr e) _ er, σ⟩ => e.isValM <| (dirac ⟨er.app e, σ⟩)
| ⟨.alloc ed, σ⟩ =>
  ed.asValM fun vd =>
  let ℓ := σ.heap.fresh
  dirac ⟨.lit <| .loc ℓ, σ.update_heap fun t => t.insert ℓ vd⟩
| ⟨.load (.lit (.loc ℓ)), σ⟩ =>
  match σ.heap[ℓ]? with | none => 0 | some v => (dirac ⟨.ofVal v, σ⟩)
| ⟨.store (.lit (.loc ℓ)) e, σ⟩ =>
  e.asValM fun v =>
  match σ.heap[ℓ]? with
  | none => 0
  | some _ => dirac ⟨.lit .unit, σ.update_heap fun t => t.insert ℓ v⟩
| ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ => Cfg.uniform z σ
| ⟨.tape (.lit (.int z)), σ⟩ =>
  let α := σ.tapes.fresh
  dirac ⟨.lit <| .lbl α, σ.update_tapes fun t => t.insert α (.empty z)⟩
| ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ =>
  match σ.tapes[α]? with
  | none => 0
  | some ⟨M, ns⟩ =>
    if M = z
      then
        match ns with
        | [] => Cfg.uniform z σ
        | n :: ns => dirac ⟨.lit <| .int n, σ.update_tapes fun t => t.insert α ⟨M, ns⟩⟩
      else Cfg.uniform z σ
| ⟨.scrut e p, σ⟩ =>
  e.isValM <|
  match Pat.tryMatch p e with
  | some bindings => dirac ⟨.inl bindings, σ⟩
  | none => dirac ⟨.inr (.lit .unit), σ⟩
| ⟨.urand, σ⟩ => Cfg.uniformReal σ
| _ => 0

/-! ## The `head_case` tactic: one named goal per branch of `headStep` -/

/-- Rename the main goal to `name`. -/
elab "rename_goal" name:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.setUserName name.getId

/-- Split the headStep cases, but with informative goal names. -/
macro "head_case_names" : tactic =>
  `(tactic| (
    unfold headStep
    split
    on_goal 1  => rename_goal beta.lam
    on_goal 2  => rename_goal beta.fix
    on_goal 3  => rename_goal unop
    on_goal 4  => rename_goal binop
    on_goal 5  => rename_goal cond.true
    on_goal 6  => rename_goal cond.false
    on_goal 7  => rename_goal fst
    on_goal 8  => rename_goal snd
    on_goal 9  => rename_goal case.left
    on_goal 10 => rename_goal case.right
    on_goal 11 => rename_goal alloc
    on_goal 12 => rename_goal load
    on_goal 13 => rename_goal store
    on_goal 14 => rename_goal rand.plain
    on_goal 15 => rename_goal tape
    on_goal 16 => rename_goal rand.tape
    on_goal 17 => rename_goal scrut
    on_goal 18 => rename_goal urand
    on_goal 19 => rename_goal default
  ))

/-- Decompose the Cfg equality hypothesis left by `split` on `headStep`, then substitute. -/
macro "head_subst" : tactic =>
  `(tactic| (rename_i h_eq
             have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
             subst_eqs))

/-- Unfold `isValM`, split into redex/no_redex, and name goals.
    Goal order after `split` on `if`: goal 1 = true (redex), goal 2 = false (no_redex). -/
macro "head_split_isValM" redex:ident no_redex:ident : tactic =>
  `(tactic| (unfold Exp.isValM; split
             on_goal 2 => rename_goal $no_redex
             on_goal 1 => rename_goal $redex))

/-- Unfold `asValM`, split into no_redex/redex, and name goals.
    Goal order after `split` on `match toVal?`: goal 1 = none (no_redex), goal 2 = some (redex). -/
macro "head_split_asValM" no_redex:ident redex:ident : tactic =>
  `(tactic| (unfold Exp.asValM; split
             on_goal 1 => rename_goal $no_redex
             on_goal 2 => rename_goal $redex))

/-- Split a binary match (e.g. heap lookup) and name the two goals. -/
macro "head_split2" goal1:ident goal2:ident : tactic =>
  `(tactic| (split
             on_goal 1 => rename_goal $goal1
             on_goal 2 => rename_goal $goal2))

/-- Split `headStep` into its cases, with named goals for every `isValM`/`asValM`/match branch.
Goals are `<ctor>.redex`, `<ctor>.no_redex[_i]` (guard failed), `load|store.segfault` (dangling
location) and `rand.tape.{unalloc,empty,deterministic,mismatch}`; the `scrut` goals are
`scrut_success`, `scrut_failure`, `scrut_no_redex`. Unsplit branches keep the `head_case_names`
names: `cond.true`, `cond.false`, `tape`, `rand.plain`, `urand`, `default`. -/
macro "head_case" : tactic =>
  `(tactic| (
    head_case_names
    case' rand.tape =>
      head_subst
      head_split2 rand.tape.unalloc rand_tape_alloc
      case' rand_tape_alloc =>
        split
        on_goal 2 => rename_goal rand.tape.mismatch
        on_goal 1 =>
          subst_eqs
          head_split2 rand.tape.empty rand.tape.deterministic
    case' tape       => head_subst
    case' rand.plain => head_subst
    case' store =>
      head_subst
      unfold Exp.asValM; split
      on_goal 1 => rename_goal store.no_redex
      on_goal 2 => head_split2 store.segfault store.redex
    case' load =>
      head_subst
      head_split2 load.segfault load.redex
    case' alloc =>
      head_subst
      head_split_asValM alloc.no_redex alloc.redex
    case' case.right =>
      head_subst
      head_split_isValM case.right.redex case.right.no_redex
    case' case.left =>
      head_subst
      head_split_isValM case.left.redex case.left.no_redex
    case' snd =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal snd.no_redex_1
      on_goal 1 => head_split2 snd.redex snd.no_redex_2
    case' fst =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal fst.no_redex_1
      on_goal 1 => head_split2 fst.redex fst.no_redex_2
    case' cond.false => head_subst
    case' cond.true  => head_subst
    case' binop =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal binop.no_redex_1
      on_goal 1 => head_split2 binop.redex binop.no_redex_2
    case' unop =>
      head_subst
      head_split_isValM unop.redex unop.no_redex
    case' scrut =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal scrut_no_redex
      on_goal 1 =>
        head_split2 scrut_success scrut_failure
    case' beta.lam =>
      head_subst
      head_split_isValM beta.lam.redex beta.lam.no_redex
    case' beta.fix =>
      head_subst
      head_split_isValM beta.fix.redex beta.fix.no_redex
  ))

/-- The configuration `⟨e, σ⟩` can take a head step. -/
abbrev HeadReducible (e : Exp rT) (σ : State rT) : Prop :=
  headStep ⟨e, σ⟩ ≠ 0

/-! ## Mass, and values do not step -/

/-- `isValM` of a probability measure on a value is a probability measure. -/
theorem isValM_isProbabilityMeasure [MeasurableSpace T] {e : Exp α} {m : Measure T}
    (he : e.isValue) [IsProbabilityMeasure m] : IsProbabilityMeasure (e.isValM m) := by
  rw [Exp.isValM, ite_eq_left he]; infer_instance

/-- `asValM f` on a value `v` is a probability measure when `f v` is. -/
theorem asValM_isProbabilityMeasure [MeasurableSpace T] {e : Exp α} {f : Val α → Measure T}
    {v : Val α} (hv : e.toVal? = some v) [IsProbabilityMeasure (f v)] :
    IsProbabilityMeasure (e.asValM f) := by
  simp [Exp.asValM, hv]; infer_instance

/-- `Cfg.uniform` is a probability measure. -/
instance Cfg.uniform_isProbabilityMeasure {z : Int} {σ : State rT} :
    IsProbabilityMeasure (Cfg.uniform z σ) := by
  unfold Cfg.uniform Int.isPos
  by_cases hpos : 0 < z
  · simp only [hpos, dite_true]; infer_instance
  · simp only [hpos, dite_false]; infer_instance

/-- `Cfg.uniformReal` is a probability measure. -/
instance Cfg.uniformReal_isProbabilityMeasure {σ : State rT} :
    IsProbabilityMeasure (Cfg.uniformReal σ) := by
  unfold Cfg.uniformReal
  infer_instance

/-- A reducible head step loses no mass: it is a probability measure. -/
theorem head_step_mass {e : Exp rT} {σ : State rT} :
    (headStep ⟨e, σ⟩ ≠ 0) → IsProbabilityMeasure (headStep ⟨e, σ⟩) := by
  -- Each branch is `0` (hypothesis false), a Dirac, or a uniform sampler.
  head_case
  all_goals try (· simp)
  case beta.lam.redex | beta.fix.redex | cond.true | cond.false
     | fst.redex | snd.redex | case.left.redex | case.right.redex
     | alloc.redex | load.redex | store.redex | tape
     | rand.tape.deterministic
     | scrut_success | scrut_failure => intro _; infer_instance
  case unop.redex _ op e _ =>
    cases op.eval e
    · simp [Option.unwrapM]
    · simpa [Option.unwrapM] using dirac.isProbabilityMeasure
  case binop.redex _ op e1 e2 _ _ =>
    cases op.eval e1 e2
    · simp [Option.unwrapM]
    · simpa [Option.unwrapM] using dirac.isProbabilityMeasure
  case rand.plain | rand.tape.empty | rand.tape.mismatch =>
    intro _; exact Cfg.uniform_isProbabilityMeasure
  case urand => intro _; exact Cfg.uniformReal_isProbabilityMeasure

/-- Every head step has total mass at most one. -/
theorem headStep_univ_le_one (ρ : Cfg rT) : (headStep ρ) Set.univ ≤ 1 := by
  obtain ⟨e, σ⟩ := ρ
  by_cases h : headStep ⟨e, σ⟩ = 0
  · simp [h]
  · exact (head_step_mass h).measure_univ.le

/-- Values do not head-step. -/
theorem val_head_stuck {e : Exp rT} {σ : State rT} : headStep ⟨e, σ⟩ ≠ 0 → ¬e.isValue := by
  head_case <;> simp_all [Exp.isValue_iff_isValueR, Exp.isValueR]

/-- Values do not head-step, `isValueR` form. -/
theorem val_head_stuck_R {e : Exp rT} {σ : State rT} : headStep ⟨e, σ⟩ ≠ 0 → ¬e.isValueR := by
  head_case <;> simp_all [Exp.isValueR]

/-- Singleton-mass form of `val_head_stuck_R`. -/
theorem Discrete.val_head_stuck_R {e : Exp rT} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < headStep ⟨e, σ⟩ {ρ}) : ¬e.isValueR :=
  _root_.ProbLang.val_head_stuck_R fun h0 => h.ne' (by rw [h0]; rfl)

theorem Exp.toVal?_isValue {e : Exp α} : e.toVal? = some v → e.isValue := by
  intro h; by_contra hne; rw [Exp.toVal?_eq_none.mpr hne] at h; exact absurd h (by simp)

theorem Exp.toVal?_isValueR {e : Exp α} (h : e.toVal? = some v) : e.isValueR :=
  (Exp.isValue_iff_isValueR.mp (Exp.toVal?_isValue h)).1

/-- If `Ki[e]` can head-step, then `e` is value-shaped: `headStep` only fires once every
evaluation-position subterm is a value. -/
theorem head_ctx_step_val {e : Exp rT} {σ : State rT} {Ki : EctxItem rT} :
    headStep ⟨Ki.fillItem e, σ⟩ ≠ 0 → e.isValueR := by
  head_case
  all_goals try · simp
  all_goals cases Ki <;> intro h <;>
    simp_all [EctxItem.fillItem, Exp.isValue_iff_isValueR, Exp.isValueR, Exp.toVal?_isValueR]

/-! ## Measurability of the measure combinators (for any measurable `rT`) -/

theorem Option.unwrapM.measurable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → Measure β} (hf : Measurable f) :
    Measurable (Option.unwrapM f) := by
  intro S hS
  have hpre : (Option.unwrapM f : Option α → Measure β) ⁻¹' S =
      (if (0 : Measure β) ∈ S then ({none} : Set (Option α)) else ∅)
      ∪ (some '' (f ⁻¹' S)) := by
    ext o; cases o with
    | none => by_cases h0 : (0 : Measure β) ∈ S <;> simp [Option.unwrapM, h0]
    | some v => simp [Option.unwrapM]
  rw [hpre]
  refine MeasurableSet.union ?_ ?_
  · split_ifs
    · exact MeasurableSet.singleton_none
    · exact MeasurableSet.empty
  · exact MeasurableSet.image_some (hf hS)

theorem Option.unwrapM.measurable_param
    {α β γ : Type _} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {o : γ → Option α} (ho : Measurable o)
    {g : γ × α → Measure β} (hg : Measurable g) :
    Measurable (fun c : γ => Option.unwrapM (fun a => g (c, a)) (o c)) := by
  suffices h : Measurable (fun q : Option α × γ =>
      match q.1 with | none => (0 : Measure β) | some a => g (q.2, a)) by
    have hrw : (fun c : γ => Option.unwrapM (fun a => g (c, a)) (o c))
        = (fun q : Option α × γ =>
            match q.1 with | none => (0 : Measure β) | some a => g (q.2, a))
          ∘ (fun c : γ => (o c, c)) := by
      funext c
      show Option.unwrapM (fun a => g (c, a)) (o c) =
            match o c with | none => 0 | some a => g (c, a)
      unfold Option.unwrapM
      cases o c <;> rfl
    rw [hrw]
    exact h.comp (ho.prodMk measurable_id)
  intro S hS
  have hpre : (fun q : Option α × γ =>
        match q.1 with | none => (0 : Measure β) | some a => g (q.2, a)) ⁻¹' S
      = (if (0 : Measure β) ∈ S then ({none} : Set (Option α)) ×ˢ Set.univ else ∅)
        ∪ (Prod.map some id) '' ((fun p : α × γ => g (p.2, p.1)) ⁻¹' S) := by
    ext ⟨o', c⟩; cases o' with
    | none => by_cases h0 : (0 : Measure β) ∈ S <;> simp [h0]
    | some a => simp [Set.mem_preimage, Set.mem_image, Prod.map]
  rw [hpre]
  refine MeasurableSet.union ?_ ?_
  · split_ifs
    · exact MeasurableSet.singleton_none.prod MeasurableSet.univ
    · exact MeasurableSet.empty
  · exact (MeasurableEmbedding.some_mk.prodMap .id).measurableSet_image'
      (hg.comp (measurable_snd.prodMk measurable_fst) hS)

theorem Exp.isValM.measurable {T : Type _} [MeasurableSpace T] :
    Measurable (fun (p : Exp rT × Measure T) => p.1.isValM p.2) := by
  have hpred : MeasurableSet {p : Exp rT × Measure T | p.1.isValue} := by
    have : {p : Exp rT × Measure T | p.1.isValue} =
           ({e : Exp rT | e.isValueR} ∩ {e | Exp.lcb 0 e = true}) ×ˢ (Set.univ : Set (Measure T)) :=
           by
      ext ⟨e, m⟩; simp [Exp.isValue_iff_isValueR, Set.mem_inter_iff]
    rw [this]
    exact ((Exp.isValueR.measurable.setOf).inter Exp.lcb_zero.measurableSet).prod MeasurableSet.univ
  exact Measurable.ite hpred measurable_snd measurable_const

@[fun_prop]
theorem Cfg.isValue_measurable : Measurable (fun a : Cfg rT => a.expr.isValue) := by
  rw [← measurableSet_setOfPred]
  have h : {a : Cfg rT | a.expr.isValue} =
      Cfg.expr ⁻¹' ({e : Exp rT | e.isValueR} ∩ {e | Exp.lcb 0 e = true}) := by
    ext a; simp [Exp.isValue_iff_isValueR, Set.mem_inter_iff]
  rw [h]
  exact Cfg.measurable_expr ((Exp.isValueR.measurable.setOf).inter Exp.lcb_zero.measurableSet)

@[measurability]
theorem Cfg.isValue_measurableSet : MeasurableSet {a : Cfg rT | a.expr.isValue} :=
  Cfg.isValue_measurable.setOf

theorem Exp.isValM.measurable_param {T γ : Type _} [MeasurableSpace T] [MeasurableSpace γ]
    {he : γ → Exp rT} (hhe : Measurable he)
    {hm : γ → Measure T} (hhm : Measurable hm) :
    Measurable (fun c : γ => (he c).isValM (hm c)) :=
  Exp.isValM.measurable.comp (hhe.prodMk hhm)

theorem Cfg.measurable_dirac_mk {γ : Type _} [MeasurableSpace γ]
    {fe : γ → Exp rT} (he : Measurable fe)
    {fs : γ → State rT} (hs : Measurable fs) :
    Measurable (fun q : γ => (dirac (Cfg.mk (fe q) (fs q)) : Measure (Cfg rT))) :=
  measurable_dirac.comp (Cfg.measurable_iff.mpr ⟨he, hs⟩)

/-- Parameterized in `γ` rather than jointly in `(e, f)`: the evaluation map
`(v, f) ↦ f v` is not measurable for the Pi σ-algebra on `Val rT → Measure T`. -/
theorem Exp.asValM.measurable {T γ : Type _} [MeasurableSpace T] [MeasurableSpace γ]
    {g : γ × Val rT → Measure T} (hg : Measurable g) :
    Measurable (fun (p : Exp rT × γ) => p.1.asValM (fun v => g (p.2, v))) := by
  have htoVal : Measurable (fun (p : Exp rT × γ) => (p.1.toVal?, p.2)) :=
    (Exp.toVal_question.measurable (rT := rT)).comp measurable_fst |>.prodMk measurable_snd
  suffices h : Measurable (fun (q : Option (Val rT) × γ) =>
      match q.1 with | none => (0 : Measure T) | some v => g (q.2, v)) by
    have hrw : (fun (p : Exp rT × γ) => p.1.asValM (fun v => g (p.2, v)))
        = (fun (q : Option (Val rT) × γ) =>
            match q.1 with | none => (0 : Measure T) | some v => g (q.2, v))
          ∘ (fun (p : Exp rT × γ) => (p.1.toVal?, p.2)) := by
      funext ⟨e, c⟩
      show Exp.asValM e (fun v => g (c, v)) =
            match e.toVal? with | none => 0 | some v => g (c, v)
      unfold Exp.asValM
      rfl
    rw [hrw]
    exact h.comp htoVal
  intro S hS
  have hpre : (fun (q : Option (Val rT) × γ) =>
        match q.1 with | none => (0 : Measure T) | some v => g (q.2, v)) ⁻¹' S
      = (if (0 : Measure T) ∈ S then ({none} : Set (Option (Val rT))) ×ˢ Set.univ else ∅)
        ∪ (Prod.map some id) '' ((fun (p : Val rT × γ) => g (p.2, p.1)) ⁻¹' S) := by
    ext ⟨o, c⟩; cases o with
    | none => by_cases h0 : (0 : Measure T) ∈ S <;> simp [h0]
    | some v => simp [Set.mem_preimage, Set.mem_image, Prod.map]
  rw [hpre]
  refine MeasurableSet.union ?_ ?_
  · split_ifs
    · exact MeasurableSet.singleton_none.prod MeasurableSet.univ
    · exact MeasurableSet.empty
  · exact (MeasurableEmbedding.some_mk.prodMap .id).measurableSet_image'
      (hg.comp (measurable_snd.prodMk measurable_fst) hS)

/-- Pushing a fixed s-finite measure through a jointly measurable map is measurable in the
parameter. -/
theorem measurable_map_const_uncurry {α β γ : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure β) [SFinite μ] {h : α × β → γ} (hh : Measurable h) :
    Measurable (fun a : α => μ.map (fun b => h (a, b))) :=
  @Measure.measurable_map_uncurry α β γ _ _ _ h hh (fun _ => μ) measurable_const
    (by
      have : ProbabilityTheory.Kernel.mk (fun _ : α => μ) measurable_const
          = ProbabilityTheory.Kernel.const α μ := rfl
      rw [this]; infer_instance)

theorem Cfg.uniform.measurable :
    Measurable (fun (p : Int × State rT) => Cfg.uniform p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro z
  show Measurable (fun σ : State rT => Cfg.uniform z σ)
  unfold Cfg.uniform
  cases hzp : z.isPos with
  | none => exact Cfg.measurable_dirac_mk measurable_const measurable_id
  | some w =>
    obtain ⟨w, hw⟩ := w
    exact measurable_map_const_uncurry
      (PMF.uniformOfFinset (Finset.Ico 0 w) (Finset.nonempty_Ico.mpr hw)).toMeasure
      (h := fun p : State rT × Int => Cfg.mk (.lit (.int p.2)) p.1)
      (Cfg.measurable_iff.mpr
        ⟨Exp.lit.measurable.comp (BaseLit.int.measurable.comp measurable_snd), measurable_fst⟩)

theorem Cfg.uniformReal.measurable :
    Measurable (fun σ : State rT => Cfg.uniformReal σ) :=
  measurable_map_const_uncurry (LawfulProbLangℝ.unifUnit (T := rT))
    (h := fun p : State rT × rT => Cfg.mk (.lit (.real p.2)) p.1)
    (Cfg.measurable_iff.mpr
      ⟨Exp.lit.measurable.comp (BaseLit.real.measurable.comp measurable_snd), measurable_fst⟩)

/-! ## Measurability of `headStep`, branch by branch

Each non-trivial branch is a named `def` with its own measurability theorem (for elaboration
speed), proved with the `exp_zero_<ctor>_apply` macros of `CoreMeasures/Recurrences.lean`. -/

/-- The `headStep` branch for a unary operation, uncurried over the state and arguments. -/
@[simp] def headStep.c_unop (p : State rT × UnOp × Exp rT) : Measure (Cfg rT) :=
  p.2.2.isValM ((p.2.1.eval p.2.2).unwrapM (fun e' => dirac ⟨e', p.1⟩))

theorem headStep.c_unop.measurable : Measurable (headStep.c_unop (rT := rT)) := by
  have hoe : Measurable (fun p : State rT × UnOp × Exp rT => p.2.1.eval p.2.2) :=
    Exp.UnOp_eval.measurable.comp measurable_snd
  have hdir : Measurable
      (fun q : (State rT × UnOp × Exp rT) × Exp rT =>
        (dirac (Cfg.mk q.2 q.1.1) : Measure (Cfg rT))) :=
    Cfg.measurable_dirac_mk measurable_snd (measurable_fst.comp measurable_fst)
  have hu : Measurable (fun p : State rT × UnOp × Exp rT =>
      (p.2.1.eval p.2.2).unwrapM (fun e' => (dirac (Cfg.mk e' p.1) : Measure (Cfg rT)))) :=
    Option.unwrapM.measurable_param hoe hdir
  exact Exp.isValM.measurable_param (measurable_snd.comp measurable_snd) hu

/-- The `headStep` branch for `lam`/`fix` application, uncurried over the state and arguments. -/
@[simp] def headStep.c_app (p : State rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .lam e1' => p.2.2.isValM (dirac ⟨Exp.open' e1' p.2.2, p.1⟩)
  | .fix e1' => p.2.2.isValM
                  (dirac ⟨Exp.app (Exp.open' e1' (.fix e1')) p.2.2, p.1⟩)
  | _ => 0

theorem headStep.c_app.measurable :
    Measurable (headStep.c_app (rT := rT)) := by
  let c_lam_inner : (State rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.1.2.isValM (dirac ⟨Exp.open' q.2 q.1.2, q.1.1⟩)
  let c_fix_inner : (State rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.1.2.isValM (dirac ⟨Exp.app (Exp.open' q.2 (.fix q.2)) q.1.2, q.1.1⟩)
  have hrw : (headStep.c_app (rT := rT))
      = (fun q : Exp rT × (State rT × Exp rT) =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun e1' => c_lam_inner (q.2, e1')) (fun e1' => c_fix_inner (q.2, e1'))
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, e1, e2⟩
    show headStep.c_app _ = _
    unfold headStep.c_app
    cases e1 <;> rfl
  rw [hrw]
  refine Measurable.comp ?_
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have h_lam_inner : Measurable c_lam_inner := by
    refine Exp.isValM.measurable_param
      (he := fun q : (State rT × Exp rT) × Exp rT => q.1.2)
      (hm := fun q : (State rT × Exp rT) × Exp rT =>
                (dirac (Cfg.mk (Exp.open' q.2 q.1.2) q.1.1) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_snd.comp measurable_fst
    · exact Cfg.measurable_dirac_mk
        (Exp.open'.measurable.comp
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
        (measurable_fst.comp measurable_fst)
  have h_fix_inner : Measurable c_fix_inner := by
    refine Exp.isValM.measurable_param
      (he := fun q : (State rT × Exp rT) × Exp rT => q.1.2)
      (hm := fun q : (State rT × Exp rT) × Exp rT =>
                (dirac (Cfg.mk
                  (Exp.app (Exp.open' q.2 (.fix q.2)) q.1.2) q.1.1)
                  : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_snd.comp measurable_fst
    · refine Cfg.measurable_dirac_mk ?_ (measurable_fst.comp measurable_fst)
      show Measurable
          (fun q : (State rT × Exp rT) × Exp rT =>
            Exp.app (Exp.open' q.2 (.fix q.2)) q.1.2)
      refine Exp.app.measurable.comp (Measurable.prodMk ?_ ?_)
      · exact Exp.open'.measurable.comp
          (measurable_snd.prodMk (Exp.fix.measurable.comp measurable_snd))
      · exact measurable_snd.comp measurable_fst
  exp_zero_app_apply c_lam_inner, h_lam_inner, c_fix_inner, h_fix_inner

/-- The `headStep` branch for an `alloc`, uncurried over the state and arguments. -/
@[simp] def headStep.c_alloc (p : State rT × Exp rT) : Measure (Cfg rT) :=
  p.2.asValM (fun vd =>
    let ℓ := p.1.heap.fresh
    dirac ⟨.lit (.loc ℓ), p.1.update_heap (·.insert ℓ vd)⟩)

theorem headStep.c_alloc.measurable :
    Measurable (headStep.c_alloc (rT := rT)) := by
  have hreshape : Measurable
      (fun p : State rT × Exp rT => (p.2, p.1) : State rT × Exp rT → Exp rT × State rT) :=
    measurable_snd.prodMk measurable_fst
  have hg : Measurable (fun q : State rT × Val rT =>
      (dirac (Cfg.mk
        (Exp.lit (.loc q.1.heap.fresh))
        (q.1.update_heap (·.insert q.1.heap.fresh q.2)))
        : Measure (Cfg rT))) := by
    refine Cfg.measurable_dirac_mk ?_ ?_
    · show Measurable (fun q : State rT × Val rT =>
          (Exp.lit (.loc q.1.heap.fresh) : Exp rT))
      refine Exp.lit.measurable.comp (BaseLit.loc.measurable.comp ?_)
      exact LocHeap.measurable_fresh.comp (State.measurable_heap.comp measurable_fst)
    · show Measurable (fun q : State rT × Val rT =>
          (q.1.update_heap (·.insert q.1.heap.fresh q.2)))
      refine State.measurable_mk_param ?_ ?_
      · have hheap : Measurable (fun q : State rT × Val rT => q.1.heap) :=
          State.measurable_heap.comp measurable_fst
        have hfresh : Measurable (fun q : State rT × Val rT => q.1.heap.fresh) :=
          LocHeap.measurable_fresh.comp hheap
        exact (Measurable.locHeap_insert_param (V := Val rT)).comp
          (hheap.prodMk (hfresh.prodMk measurable_snd))
      · exact State.measurable_tapes.comp measurable_fst
  exact (Exp.asValM.measurable hg).comp hreshape

/-- The `headStep` branch for a `cond`, uncurried over the state and arguments. -/
@[simp] def headStep.c_cond (p : State rT × Exp rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .lit (.bool true) => dirac ⟨p.2.2.1, p.1⟩
  | .lit (.bool false) => dirac ⟨p.2.2.2, p.1⟩
  | _ => 0

theorem headStep.c_cond.measurable : Measurable (headStep.c_cond (rT := rT)) := by
  let c_lit_inner : (State rT × Exp rT × Exp rT) × BaseLit rT → Measure (Cfg rT) :=
    fun q => match q.2 with
      | .bool true => dirac ⟨q.1.2.1, q.1.1⟩
      | .bool false => dirac ⟨q.1.2.2, q.1.1⟩
      | _ => 0
  have hrw : (headStep.c_cond (rT := rT))
      = (fun q : Exp rT × (State rT × Exp rT × Exp rT) =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner (q.2, l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT × Exp rT × Exp rT =>
            (p.2.1, p.1, p.2.2.1, p.2.2.2)) := by
    funext ⟨σ, ec, et, ef⟩
    show headStep.c_cond _ = _
    unfold headStep.c_cond
    cases ec with
    | lit l => cases l with
      | bool b => cases b <;> rfl
      | _ => rfl
    | _ => rfl
  rw [hrw]
  refine Measurable.comp ?_
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk
        ((measurable_fst.comp measurable_snd).comp measurable_snd |>.prodMk
          ((measurable_snd.comp measurable_snd).comp measurable_snd))))
  have hc_lit_inner : Measurable c_lit_inner := by
    let c_bool_inner : (State rT × Exp rT × Exp rT) × Bool → Measure (Cfg rT) :=
      fun r => if r.2 then dirac ⟨r.1.2.1, r.1.1⟩ else dirac ⟨r.1.2.2, r.1.1⟩
    have hrw2 : (fun q : (State rT × Exp rT × Exp rT) × BaseLit rT =>
          c_lit_inner q)
        = (fun p : BaseLit rT × (State rT × Exp rT × Exp rT) =>
            BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
              (fun _ => 0)
              (fun b => c_bool_inner (p.2, b))
              0 (fun _ => 0) (fun _ => 0) (fun _ => 0))
          ∘ (fun q : (State rT × Exp rT × Exp rT) × BaseLit rT => (q.2, q.1)) := by
      funext ⟨c, l⟩
      show c_lit_inner _ = _
      cases l with
      | bool b => cases b <;> rfl
      | _ => rfl
    change Measurable (fun q : (State rT × Exp rT × Exp rT) × BaseLit rT =>
      c_lit_inner q)
    rw [hrw2]
    refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
    have h_bool_inner : Measurable c_bool_inner := by
      show Measurable (fun r : (State rT × Exp rT × Exp rT) × Bool =>
        if r.2 then (dirac ⟨r.1.2.1, r.1.1⟩ : Measure (Cfg rT))
                else dirac ⟨r.1.2.2, r.1.1⟩)
      refine Measurable.ite ?_ ?_ ?_
      · exact MeasurableSet.preimage (measurableSet_singleton true) measurable_snd
      · exact Cfg.measurable_dirac_mk
          ((measurable_fst.comp measurable_snd).comp measurable_fst)
          (measurable_fst.comp measurable_fst)
      · exact Cfg.measurable_dirac_mk
          ((measurable_snd.comp measurable_snd).comp measurable_fst)
          (measurable_fst.comp measurable_fst)
    baseLit_zero_bool_apply c_bool_inner, h_bool_inner
  exp_zero_lit_apply c_lit_inner, hc_lit_inner

/-- The `headStep` branch for a `case`, uncurried over the state and arguments. -/
@[simp] def headStep.c_case (p : State rT × Exp rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .inl e => e.isValM (dirac ⟨p.2.2.1.app e, p.1⟩)
  | .inr e => e.isValM (dirac ⟨p.2.2.2.app e, p.1⟩)
  | _ => 0

theorem headStep.c_case.measurable :
    Measurable (headStep.c_case (rT := rT)) := by
  let c_inl_inner : (State rT × Exp rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.isValM (dirac ⟨q.1.2.1.app q.2, q.1.1⟩)
  let c_inr_inner : (State rT × Exp rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.isValM (dirac ⟨q.1.2.2.app q.2, q.1.1⟩)
  have hrw : (headStep.c_case (rT := rT))
      = (fun q : Exp rT × State rT × Exp rT × Exp rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
            (fun e => c_inl_inner (q.2, e))
            (fun e => c_inr_inner (q.2, e))
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, ec, et, ef⟩
    show headStep.c_case _ = _
    unfold headStep.c_case
    cases ec <;> rfl
  rw [hrw]
  refine Measurable.comp ?_
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have h_inl_inner : Measurable c_inl_inner := by
    refine Exp.isValM.measurable_param
      (he := fun q : (State rT × Exp rT × Exp rT) × Exp rT => q.2)
      (hm := fun q : (State rT × Exp rT × Exp rT) × Exp rT =>
        (dirac (Cfg.mk (q.1.2.1.app q.2) q.1.1) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_snd
    · refine Cfg.measurable_dirac_mk ?_ (measurable_fst.comp measurable_fst)
      have hp : Measurable (fun q : (State rT × Exp rT × Exp rT) × Exp rT =>
          (q.1.2.1, q.2)) :=
        (measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
      exact Exp.app.measurable.comp hp
  have h_inr_inner : Measurable c_inr_inner := by
    refine Exp.isValM.measurable_param
      (he := fun q : (State rT × Exp rT × Exp rT) × Exp rT => q.2)
      (hm := fun q : (State rT × Exp rT × Exp rT) × Exp rT =>
        (dirac (Cfg.mk (q.1.2.2.app q.2) q.1.1) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_snd
    · refine Cfg.measurable_dirac_mk ?_ (measurable_fst.comp measurable_fst)
      have hp : Measurable (fun q : (State rT × Exp rT × Exp rT) × Exp rT =>
          (q.1.2.2, q.2)) :=
        (measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
      exact Exp.app.measurable.comp hp
  exp_zero_case_apply c_inl_inner, h_inl_inner, c_inr_inner, h_inr_inner

/-- The `headStep` branch for a `load`, uncurried over the state and arguments. -/
@[simp] def headStep.c_load (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .lit (.loc ℓ) => match p.1.heap[ℓ]? with
                      | none => 0
                      | some v => dirac ⟨Exp.ofVal v, p.1⟩
  | _ => 0

theorem headStep.c_load.measurable :
    Measurable (headStep.c_load (rT := rT)) := by
  let c_leaf : State rT × Loc → Measure (Cfg rT) :=
    fun q => Option.casesOn (motive := fun _ => Measure (Cfg rT))
      q.1.heap[q.2]? 0 (fun v => dirac ⟨Exp.ofVal v, q.1⟩)
  let c_lit_inner : State rT × BaseLit rT → Measure (Cfg rT) :=
    fun q =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) q.2
        (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (q.1, ℓ)) (fun _ => 0) (fun _ => 0)
  have hrw : (headStep.c_load (rT := rT))
      = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner (q.2, l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.c_load _ = _
    unfold headStep.c_load
    cases e <;> (try rfl);
      (rename_i l; cases l <;> (try rfl))
    rename_i ℓ
    show _ = c_leaf (σ, ℓ)
    simp only [c_leaf]
    cases σ.heap[ℓ]? <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  have hc_leaf : Measurable c_leaf := by
    have hheap_getElem : Measurable
        (fun q : State rT × Loc => q.1.heap[q.2]?) := by
      have hflat : Measurable (fun p : Loc × State rT => p.2.heap[p.1]?) := by
        apply measurable_from_prod_countable_right
        intro ℓ
        exact (LocHeap.measurable_getElem? ℓ).comp State.measurable_heap
      exact hflat.comp (measurable_snd.prodMk measurable_fst)
    refine Option.measurable_elim_param_zero
      (f := fun q : State rT × Loc => q.1.heap[q.2]?)
      hheap_getElem
      (some_branch := fun q : (State rT × Loc) × Val rT =>
        (dirac (Cfg.mk (Exp.ofVal q.2) q.1.1) : Measure (Cfg rT))) ?_
    exact Cfg.measurable_dirac_mk
      (Val.fst.measurable.comp measurable_snd) (measurable_fst.comp measurable_fst)
  have hc_lit : Measurable c_lit_inner := by
    have hbase : Measurable (fun p : BaseLit rT × State rT =>
        BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (p.2, ℓ)) (fun _ => 0) (fun _ => 0)) := by
      baseLit_zero_loc_apply c_leaf, hc_leaf
    exact (hbase.comp (measurable_snd.prodMk measurable_fst) :)
  exp_zero_lit_apply c_lit_inner, hc_lit

/-- The `headStep` branch for a `store`, uncurried over the state and arguments. -/
@[simp] def headStep.c_store (p : State rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .lit (.loc ℓ) => p.2.2.asValM (fun v =>
      match p.1.heap[ℓ]? with
      | none => 0
      | some _ => dirac ⟨.lit .unit, p.1.update_heap (·.insert ℓ v)⟩)
  | _ => 0

theorem headStep.c_store.measurable :
    Measurable (headStep.c_store (rT := rT)) := by
  let c_leaf_inner_someBranch : (State rT × Loc) × Val rT → Measure (Cfg rT) :=
    fun r => dirac ⟨.lit .unit, r.1.1.update_heap (·.insert r.1.2 r.2)⟩
  let c_leaf_g : (State rT × Loc) × Val rT → Measure (Cfg rT) :=
    fun r => Option.casesOn (motive := fun _ => Measure (Cfg rT))
      r.1.1.heap[r.1.2]? 0 (fun _ => c_leaf_inner_someBranch r)
  let c_leaf : (State rT × Exp rT) × Loc → Measure (Cfg rT) :=
    fun r => r.1.2.asValM (fun v => c_leaf_g ((r.1.1, r.2), v))
  let c_lit_inner : (State rT × Exp rT) × BaseLit rT → Measure (Cfg rT) :=
    fun q =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) q.2
        (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (q.1, ℓ)) (fun _ => 0) (fun _ => 0)
  have hrw : (headStep.c_store (rT := rT))
      = (fun q : Exp rT × State rT × Exp rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner ((q.2.1, q.2.2), l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, e1, e2⟩
    show headStep.c_store _ = _
    unfold headStep.c_store
    cases e1 <;> (try rfl)
    rename_i l; cases l <;> (try rfl)
    rename_i ℓ
    show _ = c_leaf ((σ, e2), ℓ)
    simp only [c_leaf, c_leaf_g, c_leaf_inner_someBranch]
    unfold Exp.asValM
    cases e2.toVal? <;> (try rfl)
    rename_i v
    cases σ.heap[ℓ]? <;> rfl
  rw [hrw]
  refine Measurable.comp ?_
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have h_someBr : Measurable c_leaf_inner_someBranch := by
    refine Cfg.measurable_dirac_mk measurable_const ?_
    show Measurable (fun r : (State rT × Loc) × Val rT =>
      r.1.1.update_heap (·.insert r.1.2 r.2))
    refine State.measurable_mk_param ?_ ?_
    · show Measurable (fun r : (State rT × Loc) × Val rT =>
        r.1.1.heap.insert r.1.2 r.2)
      have hmk : Measurable
          (fun r : (State rT × Loc) × Val rT =>
            (r.1.1.heap, r.1.2, r.2)) :=
        (State.measurable_heap.comp (measurable_fst.comp measurable_fst)).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
      exact Measurable.locHeap_insert_param.comp hmk
    · exact State.measurable_tapes.comp (measurable_fst.comp measurable_fst)
  have h_g : Measurable c_leaf_g := by
    have hheap : Measurable (fun r : (State rT × Loc) × Val rT => r.1.1.heap[r.1.2]?) := by
      have hflat : Measurable (fun p : Loc × State rT => p.2.heap[p.1]?) := by
        apply measurable_from_prod_countable_right
        intro ℓ
        exact (LocHeap.measurable_getElem? ℓ).comp State.measurable_heap
      have hproj : Measurable (fun r : (State rT × Loc) × Val rT => (r.1.2, r.1.1)) :=
        (measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_fst)
      exact hflat.comp hproj
    refine Option.measurable_elim_param_zero
      (f := fun r : (State rT × Loc) × Val rT => r.1.1.heap[r.1.2]?) hheap
      (some_branch := fun s : ((State rT × Loc) × Val rT) × Val rT =>
        c_leaf_inner_someBranch s.1) ?_
    exact h_someBr.comp measurable_fst
  have h_leaf : Measurable c_leaf := by
    have hasValM := Exp.asValM.measurable (γ := State rT × Loc) h_g
    have hreshape : Measurable (fun r : (State rT × Exp rT) × Loc =>
        (r.1.2, r.1.1, r.2) : (State rT × Exp rT) × Loc → Exp rT × State rT × Loc) :=
      (measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact hasValM.comp hreshape
  have hc_lit : Measurable c_lit_inner := by
    have hbase : Measurable (fun p : BaseLit rT × (State rT × Exp rT) =>
        BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (p.2, ℓ)) (fun _ => 0) (fun _ => 0)) := by
      baseLit_zero_loc_apply c_leaf, h_leaf
    exact (hbase.comp (measurable_snd.prodMk measurable_fst) :)
  exp_zero_lit_apply c_lit_inner, hc_lit

/-- The `headStep` branch for a `tape`, uncurried over the state and arguments. -/
@[simp] def headStep.c_tape (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .lit (.int z) =>
    let α := p.1.tapes.fresh
    dirac ⟨.lit (.lbl α), p.1.update_tapes (·.insert α (.empty z))⟩
  | _ => 0

theorem headStep.c_tape.measurable :
    Measurable (headStep.c_tape (rT := rT)) := by
  let c_int_inner : State rT × Int → Measure (Cfg rT) :=
    fun q => dirac ⟨.lit (.lbl q.1.tapes.fresh),
      q.1.update_tapes (·.insert q.1.tapes.fresh (.empty q.2))⟩
  let c_lit_inner : State rT × BaseLit rT → Measure (Cfg rT) :=
    fun q =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) q.2
        (fun z => c_int_inner (q.1, z)) (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) (fun _ => 0)
  have hrw : (headStep.c_tape (rT := rT))
      = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner (q.2, l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.c_tape _ = _
    unfold headStep.c_tape
    cases e <;> (try rfl)
    rename_i l; cases l <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  have hc_int : Measurable c_int_inner := by
    refine Cfg.measurable_dirac_mk ?_ ?_
    · exact Exp.lit.measurable.comp (BaseLit.lbl.measurable.comp
        (LocHeap.measurable_fresh.comp (State.measurable_tapes.comp measurable_fst)))
    · show Measurable (fun q : State rT × Int =>
        q.1.update_tapes (·.insert q.1.tapes.fresh (Tape.empty q.2)))
      refine State.measurable_mk_param (State.measurable_heap.comp measurable_fst) ?_
      show Measurable (fun q : State rT × Int =>
        q.1.tapes.insert q.1.tapes.fresh (Tape.empty q.2))
      have htape_empty : Measurable (Tape.empty) := Measurable.of_discrete
      have hmk : Measurable
          (fun q : State rT × Int => (q.1.tapes, q.1.tapes.fresh, Tape.empty q.2)) :=
        (State.measurable_tapes.comp measurable_fst).prodMk
          ((LocHeap.measurable_fresh.comp (State.measurable_tapes.comp measurable_fst)).prodMk
            (htape_empty.comp measurable_snd))
      exact Measurable.locHeap_insert_param.comp hmk
  have hc_lit : Measurable c_lit_inner := by
    have hbase : Measurable
        (fun p : BaseLit rT × State rT =>
          BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
            (fun z => c_int_inner (p.2, z)) (fun _ => 0) 0 (fun _ => 0) (fun _ => 0)
            (fun _ => 0)) := by
      baseLit_zero_int_apply c_int_inner, hc_int
    exact (hbase.comp (measurable_snd.prodMk measurable_fst) :)
  exp_zero_lit_apply c_lit_inner, hc_lit

/-- The `headStep` branch for a `rand`, uncurried over the state and arguments. -/
@[simp] def headStep.c_rand (p : State rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1, p.2.2 with
  | .lit (.int z), .lit .unit => Cfg.uniform z p.1
  | .lit (.int z), .lit (.lbl α) =>
    match p.1.tapes[α]? with
    | none => 0
    | some ⟨M, ns⟩ =>
      if M = z then
        match ns with
        | [] => Cfg.uniform z p.1
        | n :: ns' => dirac ⟨.lit (.int n), p.1.update_tapes (·.insert α ⟨M, ns'⟩)⟩
      else Cfg.uniform z p.1
  | _, _ => 0

theorem headStep.c_rand.measurable :
    Measurable (headStep.c_rand (rT := rT)) := by
  let c_lbl_leaf : State rT × Int × Lbl × Option Tape → Measure (Cfg rT) :=
    fun ⟨σ, z, α, optTape⟩ =>
      match optTape with
      | none => 0
      | some ⟨M, ns⟩ =>
        if M = z then
          match ns with
          | [] => Cfg.uniform z σ
          | n :: ns' => dirac ⟨.lit (.int n), σ.update_tapes (·.insert α ⟨M, ns'⟩)⟩
        else Cfg.uniform z σ
  have hc_lbl_leaf : Measurable c_lbl_leaf := by
    have hflat : Measurable
        (fun p : (Int × Lbl × Option Tape) × State rT =>
          c_lbl_leaf (p.2, p.1.1, p.1.2.1, p.1.2.2)) := by
      apply measurable_from_prod_countable_right
      intro ⟨z, α, optTape⟩
      show Measurable (fun σ : State rT => c_lbl_leaf (σ, z, α, optTape))
      simp only [c_lbl_leaf]
      match optTape with
      | none => exact measurable_const
      | some ⟨M, ns⟩ =>
        rcases eq_or_ne M z with rfl | hMz
        · simp only [↓reduceIte]
          match ns with
          | [] =>
            exact Cfg.uniform.measurable.comp
              (measurable_const.prodMk measurable_id)
          | n :: ns' =>
            refine Cfg.measurable_dirac_mk measurable_const ?_
            show Measurable (fun σ : State rT =>
              σ.update_tapes (·.insert α ⟨M, ns'⟩))
            refine State.measurable_mk_param State.measurable_heap ?_
            show Measurable (fun σ : State rT => σ.tapes.insert α ⟨M, ns'⟩)
            have hpair : Measurable
                (fun σ : State rT => (σ.tapes, α, (⟨M, ns'⟩ : Tape))) :=
              State.measurable_tapes.prodMk (measurable_const.prodMk measurable_const)
            exact Measurable.locHeap_insert_param.comp hpair
        · simp only [hMz, ↓reduceIte]
          exact Cfg.uniform.measurable.comp
            (measurable_const.prodMk measurable_id)
    have hreshape : Measurable (fun q : State rT × Int × Lbl × Option Tape =>
        ((q.2.1, q.2.2.1, q.2.2.2), q.1) :
        State rT × Int × Lbl × Option Tape → (Int × Lbl × Option Tape) × State rT) :=
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk measurable_fst
    exact hflat.comp hreshape
  let c_lbl_arm : State rT × Int × Lbl → Measure (Cfg rT) :=
    fun ⟨σ, z, α⟩ => c_lbl_leaf (σ, z, α, σ.tapes[α]?)
  have hc_lbl_arm : Measurable c_lbl_arm := by
    have hlookup : Measurable (fun p : Lbl × State rT => p.2.tapes[p.1]?) := by
      apply measurable_from_prod_countable_right
      intro α
      exact (LocHeap.measurable_getElem? α).comp State.measurable_tapes
    have hproj : Measurable
        (fun q : State rT × Int × Lbl =>
          (q.1, q.2.1, q.2.2, q.1.tapes[q.2.2]?)) :=
      measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk
          (hlookup.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst))))
    exact hc_lbl_leaf.comp hproj
  let c_unit_arm : State rT × Int × Unit → Measure (Cfg rT) :=
    fun ⟨σ, z, _⟩ => Cfg.uniform z σ
  have hc_unit_arm : Measurable c_unit_arm :=
    Cfg.uniform.measurable.comp
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  let c_l2_dispatch : (State rT × Int) × BaseLit rT → Measure (Cfg rT) :=
    fun ⟨⟨σ, z⟩, l2⟩ =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) l2
        (fun _ => 0) (fun _ => 0)
        (c_unit_arm (σ, z, ()))
        (fun _ => 0)
        (fun α => c_lbl_arm (σ, z, α))
        (fun _ => 0)
  have hc_l2 : Measurable c_l2_dispatch := by
    have hswap : Measurable
        (fun q : (State rT × Int) × BaseLit rT => (q.2, q.1)) :=
      measurable_snd.prodMk measurable_fst
    have hbase : Measurable (fun p : BaseLit rT × (State rT × Int) =>
        BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun _ => 0) (fun _ => 0)
          (c_unit_arm (p.2.1, p.2.2, ()))
          (fun _ => 0)
          (fun α => c_lbl_arm (p.2.1, p.2.2, α))
          (fun _ => 0)) := by
      apply BaseLit.measurable_casesOn_param
        (c_int := fun _ => 0) (c_bool := fun _ => 0)
        (c_unit := fun q : State rT × Int => c_unit_arm (q.1, q.2, ()))
        (c_loc := fun _ => 0)
        (c_lbl := fun q : (State rT × Int) × Lbl => c_lbl_arm (q.1.1, q.1.2, q.2))
        (c_real := fun _ => 0)
        (h_int := measurable_const) (h_bool := measurable_const)
        (h_unit := hc_unit_arm.comp
          (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const (a := ())))))
        (h_loc := measurable_const)
        (h_lbl := hc_lbl_arm.comp
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
        (h_real := measurable_const)
    exact hbase.comp hswap
  let c_e2_dispatch : (State rT × Int) × Exp rT → Measure (Cfg rT) :=
    fun ⟨⟨σ, z⟩, e2⟩ =>
      Exp.casesOn (motive := fun _ => Measure (Cfg rT)) e2
        (fun _ => 0) (fun _ => 0)
        (fun l2 => c_l2_dispatch ((σ, z), l2))
        (fun _ => 0) (fun _ => 0)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
        (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0)
  have hc_e2 : Measurable c_e2_dispatch := by
    have hswap : Measurable (fun q : (State rT × Int) × Exp rT => (q.2, q.1)) :=
      measurable_snd.prodMk measurable_fst
    have hbase : Measurable (fun p : Exp rT × (State rT × Int) =>
        Exp.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun _ => 0) (fun _ => 0)
          (fun l => c_l2_dispatch (p.2, l))
          (fun _ => 0) (fun _ => 0)
          (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
          (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
          (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
          (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0)) := by
      exp_zero_lit_apply (fun q : (State rT × Int) × BaseLit rT => c_l2_dispatch q), hc_l2
    exact hbase.comp hswap
  let c_l1_dispatch : (State rT × Exp rT) × BaseLit rT → Measure (Cfg rT) :=
    fun ⟨⟨σ, e2⟩, l1⟩ =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) l1
        (fun z => c_e2_dispatch ((σ, z), e2)) (fun _ => 0) 0 (fun _ => 0)
        (fun _ => 0) (fun _ => 0)
  have hc_l1 : Measurable c_l1_dispatch := by
    have hswap : Measurable
        (fun q : (State rT × Exp rT) × BaseLit rT => (q.2, q.1)) :=
      measurable_snd.prodMk measurable_fst
    have hbase : Measurable (fun p : BaseLit rT × (State rT × Exp rT) =>
        BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun z => c_e2_dispatch ((p.2.1, z), p.2.2)) (fun _ => 0) 0
          (fun _ => 0) (fun _ => 0) (fun _ => 0)) := by
      apply BaseLit.measurable_casesOn_param
        (c_int := fun q : (State rT × Exp rT) × Int =>
          c_e2_dispatch ((q.1.1, q.2), q.1.2))
        (c_bool := fun _ => 0) (c_unit := fun _ => 0)
        (c_loc := fun _ => 0) (c_lbl := fun _ => 0) (c_real := fun _ => 0)
        (h_int := hc_e2.comp
          (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
            (measurable_snd.comp measurable_fst)))
        (h_bool := measurable_const) (h_unit := measurable_const)
        (h_loc := measurable_const) (h_lbl := measurable_const)
        (h_real := measurable_const)
    exact hbase.comp hswap
  have hrw : (headStep.c_rand (rT := rT))
      = (fun q : Exp rT × State rT × Exp rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0)
            (fun l1 => c_l1_dispatch ((q.2.1, q.2.2), l1))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, e1, e2⟩
    show headStep.c_rand _ = _
    unfold headStep.c_rand
    cases e1 <;> (try rfl);
      rename_i l1;
      cases l1 <;> (try rfl);
      rename_i z;
      cases e2 <;> (try rfl);
      rename_i l2;
      cases l2 <;> (try rfl)
  rw [hrw]
  refine Measurable.comp ?_
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  exp_zero_lit_apply (fun q : (State rT × Exp rT) × BaseLit rT => c_l1_dispatch q), hc_l1

/-- The `headStep` branch for a `scrut`, uncurried over the state and arguments. -/
@[simp] def headStep.c_scrut (p : State rT × Exp rT × Pat rT) : Measure (Cfg rT) :=
  p.2.1.isValM
    (match Pat.tryMatch p.2.2 p.2.1 with
      | some b => dirac ⟨.inl b, p.1⟩
      | none => dirac ⟨.inr (.lit .unit), p.1⟩)

theorem headStep.c_scrut.measurable : Measurable (headStep.c_scrut (rT := rT)) := by
  have hrw : (headStep.c_scrut (rT := rT))
      = fun p : State rT × Exp rT × Pat rT =>
        p.2.1.isValM
          (Option.casesOn (motive := fun _ => Measure (Cfg rT)) (Pat.tryMatch p.2.2 p.2.1)
            (Measure.dirac (⟨.inr (.lit .unit), p.1⟩ : Cfg rT))
            (fun b => Measure.dirac (⟨.inl b, p.1⟩ : Cfg rT))) := by
    funext p
    show headStep.c_scrut p = _
    unfold headStep.c_scrut
    cases hp : Pat.tryMatch p.2.2 p.2.1 <;> rfl
  rw [hrw]
  apply Exp.isValM.measurable_param
  · exact measurable_fst.comp measurable_snd
  · refine Option.measurable_elim_param
      (f := fun p : State rT × Exp rT × Pat rT => Pat.tryMatch p.2.2 p.2.1)
      (default := fun p : State rT × Exp rT × Pat rT =>
        Measure.dirac (⟨.inr (.lit .unit), p.1⟩ : Cfg rT))
      (some_branch := fun s : (State rT × Exp rT × Pat rT) × Exp rT =>
        Measure.dirac (⟨.inl s.2, s.1.1⟩ : Cfg rT)) ?_ ?_ ?_
    · have : (fun p : State rT × Exp rT × Pat rT => Pat.tryMatch p.2.2 p.2.1)
          = (Function.uncurry (fun (p : Pat rT) (e : Exp rT) => Pat.tryMatch p e)) ∘
            (fun p : State rT × Exp rT × Pat rT => (p.2.2, p.2.1)) := by
        funext _; rfl
      rw [this]
      exact ProbLang.Exp.tryMatch.measurable_joint.comp
        ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
    · refine Cfg.measurable_dirac_mk measurable_const measurable_fst
    · refine Cfg.measurable_dirac_mk
        (Exp.inl.measurable.comp measurable_snd)
        (measurable_fst.comp measurable_fst)

/-- The `headStep` branch for a `fst`, uncurried over the state and arguments. -/
@[simp] def headStep.c_fst (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .pair e1 e2 => e1.isValM (e2.isValM (dirac ⟨e1, p.1⟩))
  | _ => 0

theorem headStep.c_fst.measurable :
    Measurable (headStep.c_fst (rT := rT)) := by
  let c_pair_inner : State rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.1.isValM (q.2.2.isValM (dirac ⟨q.2.1, q.1⟩))
  have hrw : (headStep.c_fst (rT := rT))
      = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun e1 e2 => c_pair_inner (q.2, e1, e2))
            (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.c_fst _ = _
    unfold headStep.c_fst
    cases e <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  have h_pair_inner : Measurable c_pair_inner := by
    refine Exp.isValM.measurable_param
      (he := fun q : State rT × Exp rT × Exp rT => q.2.1)
      (hm := fun q : State rT × Exp rT × Exp rT =>
        (q.2.2.isValM (dirac ⟨q.2.1, q.1⟩) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_fst.comp measurable_snd
    · refine Exp.isValM.measurable_param
        (he := fun q : State rT × Exp rT × Exp rT => q.2.2)
        (hm := fun q : State rT × Exp rT × Exp rT =>
          (dirac (Cfg.mk q.2.1 q.1) : Measure (Cfg rT)))
        ?_ ?_
      · exact measurable_snd.comp measurable_snd
      · exact Cfg.measurable_dirac_mk (measurable_fst.comp measurable_snd) measurable_fst
  exp_zero_pair_apply c_pair_inner, h_pair_inner

/-- The `headStep` branch for a `snd`, uncurried over the state and arguments. -/
@[simp] def headStep.c_snd (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .pair e1 e2 => e1.isValM (e2.isValM (dirac ⟨e2, p.1⟩))
  | _ => 0

theorem headStep.c_snd.measurable :
    Measurable (headStep.c_snd (rT := rT)) := by
  let c_pair_inner : State rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.1.isValM (q.2.2.isValM (dirac ⟨q.2.2, q.1⟩))
  have hrw : (headStep.c_snd (rT := rT))
      = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun e1 e2 => c_pair_inner (q.2, e1, e2))
            (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.c_snd _ = _
    unfold headStep.c_snd
    cases e <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  have h_pair_inner : Measurable c_pair_inner := by
    refine Exp.isValM.measurable_param
      (he := fun q : State rT × Exp rT × Exp rT => q.2.1)
      (hm := fun q : State rT × Exp rT × Exp rT =>
        (q.2.2.isValM (dirac ⟨q.2.2, q.1⟩) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_fst.comp measurable_snd
    · refine Exp.isValM.measurable_param
        (he := fun q : State rT × Exp rT × Exp rT => q.2.2)
        (hm := fun q : State rT × Exp rT × Exp rT =>
          (dirac (Cfg.mk q.2.2 q.1) : Measure (Cfg rT)))
        ?_ ?_
      · exact measurable_snd.comp measurable_snd
      · exact Cfg.measurable_dirac_mk (measurable_snd.comp measurable_snd) measurable_fst
  exp_zero_pair_apply c_pair_inner, h_pair_inner

/-- The `headStep` branch for a binary operation, uncurried over the state and arguments. -/
@[simp] def headStep.c_binop (p : State rT × BinOp × Exp rT × Exp rT) : Measure (Cfg rT) :=
  p.2.2.1.isValM (p.2.2.2.isValM
    ((p.2.1.eval p.2.2.1 p.2.2.2).unwrapM (fun e' => dirac ⟨e', p.1⟩)))

theorem headStep.c_binop.measurable : Measurable (headStep.c_binop (rT := rT)) := by
  have hoe : Measurable
      (fun p : State rT × BinOp × Exp rT × Exp rT => p.2.1.eval p.2.2.1 p.2.2.2) :=
    Exp.BinOp_eval.measurable.comp measurable_snd
  have hdir : Measurable
      (fun q : (State rT × BinOp × Exp rT × Exp rT) × Exp rT =>
        (dirac (Cfg.mk q.2 q.1.1) : Measure (Cfg rT))) :=
    Cfg.measurable_dirac_mk measurable_snd (measurable_fst.comp measurable_fst)
  have hu : Measurable (fun p : State rT × BinOp × Exp rT × Exp rT =>
      (p.2.1.eval p.2.2.1 p.2.2.2).unwrapM
        (fun e' => (dirac (Cfg.mk e' p.1) : Measure (Cfg rT)))) :=
    Option.unwrapM.measurable_param hoe hdir
  have he2 : Measurable (fun p : State rT × BinOp × Exp rT × Exp rT => p.2.2.2) :=
    (measurable_snd.comp measurable_snd).comp measurable_snd
  have hinner : Measurable (fun p : State rT × BinOp × Exp rT × Exp rT =>
      p.2.2.2.isValM ((p.2.1.eval p.2.2.1 p.2.2.2).unwrapM
        (fun e' => (dirac (Cfg.mk e' p.1) : Measure (Cfg rT))))) :=
    Exp.isValM.measurable_param he2 hu
  have he1 : Measurable (fun p : State rT × BinOp × Exp rT × Exp rT => p.2.2.1) :=
    (measurable_fst.comp measurable_snd).comp measurable_snd
  exact Exp.isValM.measurable_param he1 hinner

/-- `headStep` is measurable as a map into measures. -/
@[fun_prop]
theorem headStep.measurable :
    Measurable (headStep : Cfg rT → Measure (Cfg rT)) := by
  suffices hjoint :
      Measurable (fun p : Exp rT × State rT => headStep (Cfg.mk p.1 p.2)) by
    have hrw : (headStep : Cfg rT → Measure (Cfg rT))
        = (fun p : Exp rT × State rT => headStep (Cfg.mk p.1 p.2)) ∘
          (fun cfg : Cfg rT => (cfg.expr, cfg.state)) := by
      funext cfg; rfl
    rw [hrw]
    exact hjoint.comp (Cfg.measurable_expr.prodMk Cfg.measurable_state)
  -- Write `headStep` as `Exp.casesOn` with one continuation per constructor (`0` where no
  -- redex exists), then use `Exp.measurable_casesOn_param` with each branch's measurability.
  let c_bvar  : State rT × Nat → Measure (Cfg rT) := fun _ => 0
  let c_fvar  : State rT × Var → Measure (Cfg rT) := fun _ => 0
  let c_lit   : State rT × BaseLit rT → Measure (Cfg rT) := fun _ => 0
  let c_lam   : State rT × Exp rT → Measure (Cfg rT) := fun _ => 0
  let c_fix   : State rT × Exp rT → Measure (Cfg rT) := fun _ => 0
  let c_pair  : State rT × Exp rT × Exp rT → Measure (Cfg rT) := fun _ => 0
  let c_inl   : State rT × Exp rT → Measure (Cfg rT) := fun _ => 0
  let c_inr   : State rT × Exp rT → Measure (Cfg rT) := fun _ => 0
  let c_fail  : State rT → Measure (Cfg rT) := fun _ => 0
  let c_urand : State rT → Measure (Cfg rT) := fun σ => Cfg.uniformReal σ
  have hheq : (fun p : Exp rT × State rT => headStep (Cfg.mk p.1 p.2))
      = fun p : Exp rT × State rT => Exp.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun n => c_bvar (p.2, n)) (fun x => c_fvar (p.2, x))
          (fun l => c_lit (p.2, l))
          (fun e => c_lam (p.2, e)) (fun e => c_fix (p.2, e))
          (fun e1 e2 => headStep.c_app (p.2, e1, e2))
          (fun u e => headStep.c_unop (p.2, u, e))
          (fun b e1 e2 => headStep.c_binop (p.2, b, e1, e2))
          (fun ec et ef => headStep.c_cond (p.2, ec, et, ef))
          (fun e1 e2 => c_pair (p.2, e1, e2))
          (fun e => headStep.c_fst (p.2, e)) (fun e => headStep.c_snd (p.2, e))
          (fun e => c_inl (p.2, e)) (fun e => c_inr (p.2, e))
          (fun ec el er => headStep.c_case (p.2, ec, el, er))
          (fun e => headStep.c_alloc (p.2, e)) (fun e => headStep.c_load (p.2, e))
          (fun e1 e2 => headStep.c_store (p.2, e1, e2))
          (fun e => headStep.c_tape (p.2, e))
          (fun e1 e2 => headStep.c_rand (p.2, e1, e2))
          (c_fail p.2)
          (c_urand p.2)
          (fun e pat => headStep.c_scrut (p.2, e, pat)) := by
    funext ⟨e, σ⟩
    cases e with
    | bvar | fvar | lit | lam | fix | fail | urand => rfl
    | app e1 e2 => cases e1 <;> rfl
    | unop op e => rfl
    | binop op e1 e2 => rfl
    | cond ec et ef => cases ec <;> try rfl
                       case lit l => cases l <;> try rfl
                                     case bool b => cases b <;> rfl
    | pair _ _ => rfl
    | fst e => cases e <;> rfl
    | snd e => cases e <;> rfl
    | inl _ => rfl
    | inr _ => rfl
    | case ec el er => cases ec <;> rfl
    | alloc _ => rfl
    | load e => cases e <;> try rfl
                case lit l => cases l <;> rfl
    | store e1 e2 => cases e1 <;> try rfl
                     case lit l => cases l <;> rfl
    | tape e => cases e <;> try rfl
                case lit l => cases l <;> rfl
    | rand e1 e2 => cases e1 <;> try rfl
                    case lit l1 =>
                      cases l1 <;> try rfl
                      case int z =>
                        cases e2 <;> try rfl
                        case lit l2 => cases l2 <;> rfl
    | scrut _ _ => rfl
  rw [hheq]
  apply Exp.measurable_casesOn_param
    (c_bvar := c_bvar) (c_fvar := c_fvar) (c_lit := c_lit)
    (c_lam := c_lam) (c_fix := c_fix)
    (c_app := headStep.c_app) (c_unop := headStep.c_unop) (c_binop := headStep.c_binop)
    (c_cond := headStep.c_cond) (c_pair := c_pair)
    (c_fst := headStep.c_fst) (c_snd := headStep.c_snd)
    (c_inl := c_inl) (c_inr := c_inr) (c_case := headStep.c_case)
    (c_alloc := headStep.c_alloc) (c_load := headStep.c_load) (c_store := headStep.c_store)
    (c_tape := headStep.c_tape) (c_rand := headStep.c_rand)
    (c_fail := c_fail) (c_urand := c_urand) (c_scrut := headStep.c_scrut)
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact headStep.c_app.measurable
  · exact headStep.c_unop.measurable
  · exact headStep.c_binop.measurable
  · exact headStep.c_cond.measurable
  · exact measurable_const
  · exact headStep.c_fst.measurable
  · exact headStep.c_snd.measurable
  · exact measurable_const
  · exact measurable_const
  · exact headStep.c_case.measurable
  · exact headStep.c_alloc.measurable
  · exact headStep.c_load.measurable
  · exact headStep.c_store.measurable
  · exact headStep.c_tape.measurable
  · exact headStep.c_rand.measurable
  · exact measurable_const
  · exact Cfg.uniformReal.measurable
  · exact headStep.c_scrut.measurable

/-- `headStep` as a kernel. -/
def headStepKernel : Kernel (Cfg rT) (Cfg rT) where
  measurable' := headStep.measurable
  toFun := headStep

/-! ## Support: which configurations a head step can reach -/

/-- The configurations reachable by one head step. For `urand` it lists the points of
`unifUnitSupport`, possible only when `unifUnit` has atoms; see `HeadStepSupport.possible`
(needs `e1 ≠ urand`) versus `HeadStepSupport.ne_zero`. -/
inductive HeadStepSupport : Cfg rT → Cfg rT → Prop
| BetaLamS :
  e2.isValue →
  e' = Exp.open' e1 e2 →
  HeadStepSupport ⟨.app (.lam e1) e2, σ⟩ ⟨e', σ⟩
| BetaFixS :
  e2.isValue →
  e' = Exp.app (Exp.open' e1 (.fix e1)) e2 →
  HeadStepSupport ⟨.app (.fix e1) e2, σ⟩ ⟨e', σ⟩
| UnOpS :
  e.isValue →
  some e' = op.eval e →
  HeadStepSupport ⟨.unop op e, σ⟩ ⟨e', σ⟩
| BinOpS :
  e1.isValue →
  e2.isValue →
  some e' = op.eval e1 e2 →
  HeadStepSupport ⟨.binop op e1 e2, σ⟩ ⟨e', σ⟩
| IfTrueS :
  HeadStepSupport ⟨.cond (.lit (.bool true)) et _, σ⟩ ⟨et, σ⟩
| IfFalseS :
  HeadStepSupport ⟨.cond (.lit (.bool false)) _ ef, σ⟩ ⟨ef, σ⟩
| FstS :
  e1.isValue →
  e2.isValue →
  HeadStepSupport ⟨.fst (.pair e1 e2), σ⟩ ⟨e1, σ⟩
| SndS :
  e1.isValue →
  e2.isValue →
  HeadStepSupport ⟨.snd (.pair e1 e2), σ⟩ ⟨e2, σ⟩
| CaseLS :
  e.isValue →
  HeadStepSupport ⟨.case (.inl e) el er, σ⟩ ⟨el.app e, σ⟩
| CaseRS :
  e.isValue →
  HeadStepSupport ⟨.case (.inr e) el er, σ⟩ ⟨er.app e, σ⟩
| AllocS :
  ed.toVal? = some vd →
  ℓ = σ.heap.fresh →
  σ' = σ.update_heap (·.insert ℓ vd) →
  HeadStepSupport ⟨.alloc ed, σ⟩ ⟨.lit (.loc ℓ), σ'⟩
| LoadS :
  σ.heap[ℓ]? = some v →
  e' = Exp.ofVal v →
  HeadStepSupport ⟨.load (.lit (.loc ℓ)), σ⟩ ⟨e', σ⟩
| StoreS :
  e.toVal? = some v →
  σ.heap[ℓ]?.isSome →
  σ' = σ.update_heap (·.insert ℓ v) →
  HeadStepSupport ⟨.store (.lit (.loc ℓ)) e, σ⟩ ⟨.lit .unit, σ'⟩
/-- No tape, `0 < z`: sample uniformly below `z`. -/
| RandNoTapeS :
  0 < z →
  0 ≤ v →
  v < z →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ ⟨.lit (.int v), σ⟩
/-- No tape, `z ≤ 0`: return `-1`. -/
| RandNonposS :
  ¬ 0 < z →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ ⟨.lit (.int (-1)), σ⟩
| TapeS :
  ℓ = σ.tapes.fresh →
  σ' = σ.update_tapes (·.insert ℓ (.empty z)) →
  HeadStepSupport ⟨.tape (.lit (.int z)), σ⟩ ⟨.lit (.lbl ℓ), σ'⟩
/-- Non-empty tape with bound `z`: pop the head. -/
| RandTapeS :
  σ.tapes[α]? = some ⟨N, nn :: ns⟩ →
  z = N →
  v = nn.1 →
  σ' = σ.update_tapes (·.insert α ⟨N, ns⟩) →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩
/-- Empty tape with bound `z`, `0 < z`: sample uniformly, tape unchanged. -/
| RandTapeEmptyS :
  0 < z →
  σ.tapes[α]? = some ⟨N, []⟩ →
  z = N →
  0 ≤ v →
  v < z →
  σ' = σ →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩
/-- Tape bound `≠ z`, `0 < z`: ignore the tape, sample uniformly. -/
| RandTapeOtherS :
  0 < z →
  σ.tapes[α]? = some ⟨N, L⟩ →
  z ≠ N →
  0 ≤ v →
  v < z →
  σ' = σ →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩
/-- Empty tape with bound `z`, `z ≤ 0`: return `-1`. -/
| RandTapeNonposEmptyS :
  ¬ 0 < z →
  σ.tapes[α]? = some ⟨N, []⟩ →
  z = N →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int (-1)), σ⟩
/-- Tape bound `≠ z`, `z ≤ 0`: return `-1`. -/
| RandTapeNonposOtherS :
  ¬ 0 < z →
  σ.tapes[α]? = some ⟨N, L⟩ →
  z ≠ N →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int (-1)), σ⟩
| ScrutSuccessS :
  e.isValue →
  Pat.tryMatch p e = some bindings →
  HeadStepSupport ⟨.scrut e p, σ⟩ ⟨.inl bindings, σ⟩
| ScrutFailureS :
  e.isValue →
  Pat.tryMatch p e = none →
  HeadStepSupport ⟨.scrut e p, σ⟩ ⟨.inr (.lit .unit), σ⟩
| UrandS :
  LawfulProbLangℝ.unifUnitSupport r →
  HeadStepSupport ⟨.urand, σ⟩ ⟨.lit (.real r), σ⟩

@[simp]
theorem dirac_singleton_pos
    {a b : Cfg rT} :
    0 < (dirac a) {b} ↔ a = b := by
  constructor
  · rw [dirac_apply' a (measurableSet_singleton b), Set.indicator_singleton, Pi.single,
        Function.update]
    split <;> simp; trivial
  · simp_all [dirac_apply_of_mem (Set.mem_singleton _)]

@[simp]
theorem isValM_singleton_pos [MeasurableSpace T] {e : Exp α} {m : Measure T} {s : Set T} :
    0 < (e.isValM m) s ↔ e.isValue ∧ 0 < m s := by
  simp only [Exp.isValM]
  by_cases He : e.isValue
  · rw [ite_eq_left He]; exact ⟨fun h => ⟨He, h⟩, And.right⟩
  · rw [ite_eq_right He]; exact ⟨fun h => absurd h (by simp), fun ⟨hv, _⟩ => absurd hv He⟩

@[simp]
theorem unwrapM_singleton_pos {α β : Type _} [MeasurableSpace β]
    {f : α → Measure β} {opt : Option α} {s : Set β} :
    0 < (opt.unwrapM f) s ↔ ∃ a, opt = some a ∧ 0 < (f a) s := by
  cases opt <;> simp [Option.unwrapM]

@[simp]
theorem asValM_singleton_pos [MeasurableSpace T] {e : Exp α} {f : Val α → Measure T} :
    0 < (e.asValM f) s ↔ ∃ v, e.toVal? = some v ∧ 0 < (f v) s := by
  unfold Exp.asValM; cases e.toVal? <;> simp

theorem Cfg.uniform_singleton_pos_inv
    {z : Int} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < Cfg.uniform z σ {ρ}) :
    ρ.state = σ ∧
    ((0 < z ∧ ∃ v : Int, ρ.expr = .lit (.int v) ∧ 0 ≤ v ∧ v < z) ∨
     (¬ 0 < z ∧ ρ.expr = .lit (.int (-1)))) := by
  unfold Cfg.uniform Int.isPos at h
  by_cases hpos : 0 < z
  · simp only [hpos, dite_true] at h
    rw [Measure.map_apply (by measurability) (measurableSet_singleton ρ),
        PMF.toMeasure_uniformOfFinset_apply _ _ (by measurability),
        ENNReal.div_pos_iff] at h
    obtain ⟨hcard, _⟩ := h
    rw [Nat.cast_ne_zero, Finset.card_ne_zero, Finset.filter_nonempty_iff] at hcard
    obtain ⟨a, ha, hfa⟩ := hcard
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hfa
    rw [Finset.mem_Ico] at ha
    subst hfa
    exact ⟨rfl, .inl ⟨hpos, a, rfl, ha.1, ha.2⟩⟩
  · simp only [hpos, dite_false] at h
    rw [dirac_singleton_pos] at h
    have ⟨h1, h2⟩ := (Cfg.mk.injEq ..).mp h
    exact ⟨h2.symm, .inr ⟨hpos, h1.symm⟩⟩

/-- Decompose `0 < (dirac a) {b}` into Cfg component equalities, then substitute. -/
macro "cfg_dirac" h:ident : tactic =>
  `(tactic| (rw [dirac_singleton_pos] at $h:ident
             have ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp $h:ident))

/-- Every integer in `[0, z)` is a possible outcome of `Cfg.uniform z σ`. -/
theorem Cfg.uniform_possible {z v : Int} {σ : State rT}
    (Hz : 0 < z) (Hv0 : 0 ≤ v) (Hvz : v < z) :
    Possible (⟨.lit (.int v), σ⟩ : Cfg rT) (Cfg.uniform z σ) := by
  unfold Cfg.uniform Int.isPos
  simp only [Hz, dite_true]
  refine Possible.map (g := fun x : Int => (⟨.lit (.int x), σ⟩ : Cfg rT)) (ρ := v)
    (by measurability) ?_
  rw [possible_iff_pos, PMF.toMeasure_uniformOfFinset_apply _ _ (measurableSet_singleton v),
    ENNReal.div_pos_iff]
  refine ⟨?_, ENNReal.natCast_ne_top _⟩
  rw [ne_eq, Nat.cast_eq_zero]
  exact Finset.card_ne_zero.mpr ⟨v, by simp [Finset.mem_filter, Finset.mem_Ico, Hv0, Hvz]⟩

/-- A configuration with a `HeadStepSupport` successor is head-reducible; unlike
`HeadStepSupport.possible`, this also holds for the diffuse `urand` step. -/
theorem HeadStepSupport.ne_zero {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩) :
    headStep ⟨e1, σ1⟩ ≠ 0 := by
  cases h with
  | UrandS _ =>
    have hprob : IsProbabilityMeasure (headStep ⟨Exp.urand, σ1⟩) := by
      show IsProbabilityMeasure (Cfg.uniformReal σ1)
      rw [Cfg.uniformReal]; infer_instance
    exact hprob.ne_zero
  | BetaLamS hv he | BetaFixS hv he =>
    subst he; simp [headStep, Exp.isValM, hv]
  | IfTrueS | IfFalseS =>
    simp [headStep]
  | FstS hv1 hv2 | SndS hv1 hv2 =>
    simp [headStep, Exp.isValM, hv1, hv2]
  | CaseLS hv | CaseRS hv =>
    simp [headStep, Exp.isValM, hv]
  | UnOpS hv heval =>
    simp [headStep, Exp.isValM, hv, Option.unwrapM, ← heval]
  | BinOpS hv1 hv2 heval =>
    simp [headStep, Exp.isValM, hv1, hv2, Option.unwrapM, ← heval]
  | AllocS hvd hl hσ =>
    subst hl hσ; simp [headStep, Exp.asValM, hvd]
  | LoadS hlook he =>
    subst he; simp [headStep, hlook]
  | StoreS hv hsome hσ =>
    subst hσ
    obtain ⟨vold, hvold⟩ := Option.isSome_iff_exists.mp hsome
    simp [headStep, Exp.asValM, hv, hvold]
  | TapeS hl hσ =>
    subst hl hσ; simp [headStep]
  | ScrutSuccessS hv hmatch =>
    simp [headStep, Exp.isValM, hv, hmatch]
  | ScrutFailureS hv hmatch =>
    simp [headStep, Exp.isValM, hv, hmatch]
  | RandNoTapeS hpos hv0 hvz =>
    simp only [headStep]; exact (Cfg.uniform_possible hpos hv0 hvz).ne_zero
  | RandNonposS hpos =>
    simp [headStep, Cfg.uniform, Int.isPos, hpos]
  | RandTapeS htape hz hv hσ =>
    subst hz hv hσ; simp [headStep, htape]
  | RandTapeEmptyS hpos htape hz hv0 hvz hσ =>
    subst hσ hz; simp only [headStep, htape, ↓reduceIte]
    exact (Cfg.uniform_possible hpos hv0 hvz).ne_zero
  | RandTapeOtherS hpos htape hzN hv0 hvz hσ =>
    subst hσ; simp only [headStep, htape, ite_eq_right (Ne.symm hzN)]
    exact (Cfg.uniform_possible hpos hv0 hvz).ne_zero
  | RandTapeNonposEmptyS hpos htape hz =>
    subst hz
    simp [headStep, htape, Cfg.uniform, Int.isPos, hpos]
  | RandTapeNonposOtherS hpos htape hzN =>
    simp [headStep, htape, ite_eq_right (Ne.symm hzN), Cfg.uniform, Int.isPos, hpos]

/-- Every `HeadStepSupport` successor is a possible outcome of `headStep`; false for the diffuse
`urand` sampler, hence `e1 ≠ .urand` and `@[discrete]`. -/
@[discrete]
theorem HeadStepSupport.possible {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩) (hne : e1 ≠ .urand := by nofun) :
    Possible (⟨e2, σ2⟩ : Cfg rT) (headStep ⟨e1, σ1⟩) := by
  cases h with
  | UrandS _ => exact absurd rfl hne
  | BetaLamS hv he | BetaFixS hv he =>
    subst he; exact Possible.of_dirac_eq (by simp [headStep, Exp.isValM, hv])
  | IfTrueS | IfFalseS =>
    exact Possible.of_dirac_eq (by simp [headStep])
  | FstS hv1 hv2 | SndS hv1 hv2 =>
    exact Possible.of_dirac_eq (by simp [headStep, Exp.isValM, hv1, hv2])
  | CaseLS hv | CaseRS hv =>
    exact Possible.of_dirac_eq (by simp [headStep, Exp.isValM, hv])
  | UnOpS hv heval =>
    exact Possible.of_dirac_eq (by simp [headStep, Exp.isValM, hv, Option.unwrapM, ← heval])
  | BinOpS hv1 hv2 heval =>
    exact Possible.of_dirac_eq
      (by simp [headStep, Exp.isValM, hv1, hv2, Option.unwrapM, ← heval])
  | AllocS hvd hl hσ =>
    subst hl hσ; exact Possible.of_dirac_eq (by simp [headStep, Exp.asValM, hvd])
  | LoadS hlook he =>
    subst he; exact Possible.of_dirac_eq (by simp [headStep, hlook])
  | StoreS hv hsome hσ =>
    subst hσ
    obtain ⟨vold, hvold⟩ := Option.isSome_iff_exists.mp hsome
    exact Possible.of_dirac_eq (by simp [headStep, Exp.asValM, hv, hvold])
  | TapeS hl hσ =>
    subst hl hσ; exact Possible.of_dirac_eq (by simp [headStep])
  | ScrutSuccessS hv hmatch =>
    exact Possible.of_dirac_eq (by simp [headStep, Exp.isValM, hv, hmatch])
  | ScrutFailureS hv hmatch =>
    exact Possible.of_dirac_eq (by simp [headStep, Exp.isValM, hv, hmatch])
  | RandNoTapeS hpos hv0 hvz =>
    simp only [headStep]; exact Cfg.uniform_possible hpos hv0 hvz
  | RandNonposS hpos =>
    exact Possible.of_dirac_eq (by simp [headStep, Cfg.uniform, Int.isPos, hpos])
  | RandTapeS htape hz hv hσ =>
    subst hz hv hσ; exact Possible.of_dirac_eq (by simp [headStep, htape])
  | RandTapeEmptyS hpos htape hz hv0 hvz hσ =>
    subst hσ hz; simp only [headStep, htape, ↓reduceIte]
    exact Cfg.uniform_possible hpos hv0 hvz
  | RandTapeOtherS hpos htape hzN hv0 hvz hσ =>
    subst hσ; simp only [headStep, htape, ite_eq_right (Ne.symm hzN)]
    exact Cfg.uniform_possible hpos hv0 hvz
  | RandTapeNonposEmptyS hpos htape hz =>
    subst hz; exact Possible.of_dirac_eq (by simp [headStep, htape, Cfg.uniform, Int.isPos, hpos])
  | RandTapeNonposOtherS hpos htape hzN =>
    refine Possible.of_dirac_eq ?_
    simp only [headStep, htape, ite_eq_right (Ne.symm hzN)]
    simp [Cfg.uniform, Int.isPos, hpos]

/-- Singleton-mass form of `HeadStepSupport.possible`. -/
@[discrete]
theorem HeadStepSupport.pos
    {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩) (hne : e1 ≠ .urand := by nofun) :
    0 < headStep (⟨e1, σ1⟩ : Cfg rT) {(⟨e2, σ2⟩ : Cfg rT)} :=
  possible_iff_pos.mp (h.possible hne)

/-- An outcome of positive singleton mass is a `HeadStepSupport` successor. -/
theorem headStep_support_of_pos
    (e1 e2 : Exp rT) (σ1 σ2 : State rT) :
    0 < headStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} → HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩ := by
  head_case
  all_goals try (· simp)
  case cond.true | cond.false => intro h; cfg_dirac h; constructor
  case beta.lam.redex => intro h; cfg_dirac h; exact .BetaLamS ‹_› rfl
  case beta.fix.redex => intro h; cfg_dirac h; exact .BetaFixS ‹_› rfl
  case fst.redex => intro h; cfg_dirac h; exact .FstS ‹_› ‹_›
  case snd.redex => intro h; cfg_dirac h; exact .SndS ‹_› ‹_›
  case case.left.redex => intro h; cfg_dirac h; exact .CaseLS ‹_›
  case case.right.redex => intro h; cfg_dirac h; exact .CaseRS ‹_›
  case tape => intro h; cfg_dirac h; exact .TapeS rfl rfl
  case load.redex => intro h; cfg_dirac h; exact .LoadS ‹_› rfl
  case alloc.redex => intro h; cfg_dirac h; exact .AllocS ‹_› rfl rfl
  case store.redex =>
    intro h; cfg_dirac h
    exact .StoreS ‹_› (by rw [Option.isSome_iff_exists]; exact ⟨_, ‹_›⟩) rfl
  case rand.tape.deterministic =>
    intro h; cfg_dirac h; exact .RandTapeS ‹_› rfl rfl rfl
  case unop.redex =>
    intro h; rw [unwrapM_singleton_pos] at h
    obtain ⟨r, hr, h⟩ := h; cfg_dirac h; exact .UnOpS ‹_› hr.symm
  case binop.redex =>
    intro h; rw [unwrapM_singleton_pos] at h
    obtain ⟨r, hr, h⟩ := h; cfg_dirac h; exact .BinOpS ‹_› ‹_› hr.symm
  case rand.plain =>
    intro h
    obtain ⟨rfl, ⟨hpos, v, rfl, hv0, hvz⟩ | ⟨hpos, rfl⟩⟩ := Cfg.uniform_singleton_pos_inv h
    · exact .RandNoTapeS hpos hv0 hvz
    · exact .RandNonposS hpos
  case rand.tape.empty =>
    intro h
    obtain ⟨rfl, ⟨hpos, v, rfl, hv0, hvz⟩ | ⟨hpos, rfl⟩⟩ := Cfg.uniform_singleton_pos_inv h
    · exact .RandTapeEmptyS hpos ‹_› rfl hv0 hvz rfl
    · exact .RandTapeNonposEmptyS hpos ‹_› rfl
  case rand.tape.mismatch =>
    intro h
    obtain ⟨rfl, ⟨hpos, v, rfl, hv0, hvz⟩ | ⟨hpos, rfl⟩⟩ := Cfg.uniform_singleton_pos_inv h
    · exact .RandTapeOtherS hpos ‹_› (Ne.symm ‹_›) hv0 hvz rfl
    · exact .RandTapeNonposOtherS hpos ‹_› (Ne.symm ‹_›)
  case scrut_success => intro h; cfg_dirac h; exact .ScrutSuccessS ‹_› ‹_›
  case scrut_failure => intro h; cfg_dirac h; exact .ScrutFailureS ‹_› ‹_›
  case urand =>
    rename_i _ σ' heq
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..) ▸ heq
    intro h
    have hg : Measurable (fun r : rT => (⟨.lit (.real r), σ1⟩ : Cfg rT)) := by
      rw [Cfg.measurable_iff]
      exact ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
    have hinj : Function.Injective (fun r : rT => (⟨.lit (.real r), σ1⟩ : Cfg rT)) := by
      intro a b hab; simp only [Cfg.mk.injEq, Exp.lit.injEq, BaseLit.real.injEq, and_true] at hab
      exact hab
    unfold Cfg.uniformReal at h
    obtain ⟨r, hr, hpos⟩ := map_singleton_pos hg hinj h
    rw [← hr]
    refine .UrandS ?_
    by_contra hr_notin
    have hsub : ({r} : Set rT) ⊆ (LawfulProbLangℝ.unifUnitSupport)ᶜ :=
      Set.singleton_subset_iff.mpr hr_notin
    exact ne_of_gt hpos
      (le_zero_iff.mp ((measure_mono hsub).trans_eq LawfulProbLangℝ.unifUnitIsConcentrated))

/-- Every possible outcome of `headStep` is a `HeadStepSupport` successor. -/
theorem Possible.headStepSupport
    {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : Possible (⟨e2, σ2⟩ : Cfg rT) (headStep ⟨e1, σ1⟩)) :
    HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩ :=
  headStep_support_of_pos e1 e2 σ1 σ2 (possible_iff_pos.mp h)

/-- A head-reducible configuration has some `HeadStepSupport` successor. -/
theorem headStep_exists_support_of_ne_zero
    {e : Exp rT} {σ : State rT} (h : headStep ⟨e, σ⟩ ≠ 0) :
    ∃ ρ', HeadStepSupport ⟨e, σ⟩ ρ' := by
  revert h
  head_case
  all_goals intro h
  all_goals try (exact absurd rfl h)
  case cond.true => exact ⟨_, .IfTrueS⟩
  case cond.false => exact ⟨_, .IfFalseS⟩
  case beta.lam.redex => exact ⟨_, .BetaLamS ‹_› rfl⟩
  case beta.fix.redex => exact ⟨_, .BetaFixS ‹_› rfl⟩
  case fst.redex => exact ⟨_, .FstS ‹_› ‹_›⟩
  case snd.redex => exact ⟨_, .SndS ‹_› ‹_›⟩
  case case.left.redex => exact ⟨_, .CaseLS ‹_›⟩
  case case.right.redex => exact ⟨_, .CaseRS ‹_›⟩
  case tape => exact ⟨_, .TapeS rfl rfl⟩
  case load.redex => exact ⟨_, .LoadS ‹_› rfl⟩
  case alloc.redex => exact ⟨_, .AllocS ‹_› rfl rfl⟩
  case store.redex =>
    exact ⟨_, .StoreS ‹_› (by rw [Option.isSome_iff_exists]; exact ⟨_, ‹_›⟩) rfl⟩
  case rand.tape.deterministic => exact ⟨_, .RandTapeS ‹_› rfl rfl rfl⟩
  case scrut_success => exact ⟨_, .ScrutSuccessS ‹_› ‹_›⟩
  case scrut_failure => exact ⟨_, .ScrutFailureS ‹_› ‹_›⟩
  case unop.redex =>
    simp only [Option.unwrapM] at h
    split at h
    · rename_i hv optx r heval
      exact ⟨⟨r, σ⟩, .UnOpS hv heval.symm⟩
    · exact absurd rfl h
  case binop.redex =>
    simp only [Option.unwrapM] at h
    split at h
    · rename_i hv1 hv2 optx r heval
      exact ⟨⟨r, σ⟩, .BinOpS hv1 hv2 heval.symm⟩
    · exact absurd rfl h
  case rand.plain =>
    rename_i z
    by_cases hz : 0 < z
    · exact ⟨_, .RandNoTapeS hz (le_refl 0) hz⟩
    · exact ⟨_, .RandNonposS hz⟩
  case rand.tape.empty =>
    rename_i z α optT ns htape
    by_cases hz : 0 < z
    · exact ⟨_, .RandTapeEmptyS hz htape rfl (le_refl 0) hz rfl⟩
    · exact ⟨_, .RandTapeNonposEmptyS hz htape rfl⟩
  case rand.tape.mismatch =>
    rename_i z α optT N ns htape hne
    by_cases hz : 0 < z
    · exact ⟨_, .RandTapeOtherS hz htape (Ne.symm hne) (le_refl 0) hz rfl⟩
    · exact ⟨_, .RandTapeNonposOtherS hz htape (Ne.symm hne)⟩
  case urand =>
    rename_i _ σ' heq
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..) ▸ heq
    obtain ⟨r, hr⟩ := LawfulProbLangℝ.unifUnitSupport_nonempty rT
    exact ⟨_, .UrandS hr⟩

/-! ## Pure atomicity of `headStep` -/

omit [LawfulProbLangℝ rT] in
theorem isAtomicSupport_isValM {T : Type _} [MeasurableSpace T] (e : Exp rT) {m : Measure T}
    (hm : IsAtomicSupport m) : IsAtomicSupport (e.isValM m) := by
  by_cases hv : e.isValue
  · rw [Exp.isValM_some hv]; exact hm
  · rw [Exp.isValM_none hv]; exact isAtomicSupport_zero

omit [LawfulProbLangℝ rT] in
theorem isAtomicSupport_asValM {T : Type _} [MeasurableSpace T] (e : Exp rT)
    {f : Val rT → Measure T} (hf : ∀ v, IsAtomicSupport (f v)) :
    IsAtomicSupport (e.asValM f) := by
  unfold Exp.asValM
  split <;> first | exact isAtomicSupport_zero | exact hf _

theorem isAtomicSupport_unwrapM {β T : Type _} [MeasurableSpace T] (o : Option β)
    (f : β → Measure T) (hf : ∀ a, IsAtomicSupport (f a)) :
    IsAtomicSupport (o.unwrapM f) := by
  cases o with
  | none =>
    simpa only [Option.unwrapM] using (isAtomicSupport_zero : IsAtomicSupport (0 : Measure T))
  | some a => simpa only [Option.unwrapM] using hf a

theorem isAtomicSupport_uniform (z : Int) (σ : State rT) :
    IsAtomicSupport (Cfg.uniform z σ) := by
  by_cases hz : 0 < z
  · have hrw : Cfg.uniform z σ
        = ((PMF.uniformOfFinset (Finset.Ico (0:Int) z) (Finset.nonempty_Ico.mpr hz)).map
            (fun n : Int => (⟨.lit (.int n), σ⟩ : Cfg rT))).toMeasure := by
      unfold Cfg.uniform
      simp only [Int.isPos, dite_eq_left hz]
      rw [PMF.toMeasure_map _ _ Measurable.of_discrete]
    rw [hrw]; exact PMF.toMeasure_isAtomicSupport _
  · have hrw : Cfg.uniform z σ = Measure.dirac (⟨.lit (.int (-1)), σ⟩ : Cfg rT) := by
      unfold Cfg.uniform; simp only [Int.isPos, dite_eq_right hz]
    rw [hrw]; exact isAtomicSupport_dirac _

/-- Every head step except the diffuse `urand` sampler has purely atomic support, for any `rT`. -/
theorem headStep_atomic (e : Exp rT) (σ : State rT) (hne : e ≠ .urand) :
    IsAtomicSupport (headStep ⟨e, σ⟩) := by
  head_case_names
  case beta.lam | beta.fix | case.left | case.right =>
    exact isAtomicSupport_isValM _ (isAtomicSupport_dirac _)
  case fst | snd =>
    exact isAtomicSupport_isValM _ (isAtomicSupport_isValM _ (isAtomicSupport_dirac _))
  case unop =>
    exact isAtomicSupport_isValM _ (isAtomicSupport_unwrapM _ _ fun _ => isAtomicSupport_dirac _)
  case binop =>
    exact isAtomicSupport_isValM _ (isAtomicSupport_isValM _
      (isAtomicSupport_unwrapM _ _ fun _ => isAtomicSupport_dirac _))
  case cond.true | cond.false | tape => exact isAtomicSupport_dirac _
  case alloc => exact isAtomicSupport_asValM _ fun _ => isAtomicSupport_dirac _
  case load =>
    split
    · exact isAtomicSupport_zero
    · exact isAtomicSupport_dirac _
  case store =>
    apply isAtomicSupport_asValM; intro _
    split
    · exact isAtomicSupport_zero
    · exact isAtomicSupport_dirac _
  case rand.plain => exact isAtomicSupport_uniform _ _
  case rand.tape =>
    split
    · exact isAtomicSupport_zero
    · split
      · split
        · exact isAtomicSupport_uniform _ _
        · exact isAtomicSupport_dirac _
      · exact isAtomicSupport_uniform _ _
  case scrut =>
    apply isAtomicSupport_isValM
    split <;> exact isAtomicSupport_dirac _
  case urand =>
    rename_i heq
    exact absurd (congrArg Cfg.expr heq) hne
  case default => exact isAtomicSupport_zero

end ProbLang
