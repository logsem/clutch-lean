module

public import Metrology.ProbLang.CoreMeasures
public meta import Metrology.Meta.Discrete
public import Metrology.ProbLang.Discrete
public import Metrology.ProbLang.FFI
public import Metrology.ProbLang.Rv
public import Metrology.ProbLang.Syntax.Subset
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Distributions.Uniform

/-! # Head reduction

`ProbLangDist`, the meanings of the distribution names of `sample` and of random-variable priors;
`headStep`, one head-reduction step as a measure on configurations; and the `head_case` tactic. -/

@[expose] public section

noncomputable section

open Classical MeasureTheory ProbabilityTheory Measure ProbLang Set ENNReal
open Possible (of_dirac_eq)

namespace ProbLang

variable {rT : Type _} [MeasurableSpace rT]
variable {T : Type _} [MeasurableSpace T]
variable {α β : Type _}

/-! ## Measure combinators and samplers used by `headStep` -/

/-- Apply `f` to the value of an `Option`, giving the zero measure on `none`. -/
def Option.unwrapM {α : Type _} [MeasurableSpace β] (f : α → Measure β) : Option α → Measure β
  | some v => f v
  | none => 0

/-- Apply `f` to the value of `e`, giving the zero measure when `e` is not a value. -/
@[simp]
def Exp.asValM (e : Exp rT) (f : Val rT → Measure T) : Measure T :=
  match e.toVal? with | none => 0 | some v => f v

/-- Keep the measure `m` when `e` is a value, otherwise the zero measure. -/
def Exp.isValM (e : Exp rT) (m : Measure T) : Measure T :=
  if e.isValue then m else 0

/-- `isValM` commutes with pushing the measure forward. -/
theorem Exp.isValM_map {T' : Type _} [MeasurableSpace T'] (e : Exp α) (m : Measure T)
    (g : T → T') : (e.isValM m).map g = e.isValM (m.map g) := by
  unfold Exp.isValM
  split <;> simp

/-- `asValM` commutes with pushing the measure forward. -/
theorem Exp.asValM_map {T' : Type _} [MeasurableSpace T'] (e : Exp α) (f : Val α → Measure T)
    (g : T → T') : (e.asValM f).map g = e.asValM fun v => (f v).map g := by
  unfold Exp.asValM
  split <;> simp

/-- `unwrapM` commutes with pushing the measure forward. -/
theorem Option.unwrapM_map {T' : Type _} [MeasurableSpace T'] (o : Option α)
    (f : α → Measure T) (g : T → T') : (o.unwrapM f).map g = o.unwrapM fun a => (f a).map g := by
  cases o <;> simp [Option.unwrapM]

/-- Witness that `z` is positive, if it is. -/
def Int.isPos (z : Int) : Option { z : Int // 0 < z } :=
  if H : 0 < z then some ⟨z, H⟩ else none

/-- Uniform sampler of `⟨.lit (.int n), σ⟩` for `0 ≤ n < z`; the constant `-1` when `z ≤ 0`. -/
def Cfg.uniform (z : Int) (σ : State rT) : Measure (Cfg rT) :=
  match z.isPos with
  | some ⟨z, _⟩ => (uniformOfFinset (.Ico 0 z)).map (⟨.lit <| .int ·, σ⟩)
  | none => dirac ⟨.lit (.int (-1)), σ⟩

/-- The configuration after a foreign step's outcome `r.1`, with the new heap `r.2`. -/
def Cfg.ofFFI (σ : State rT) (r : FFIOutcome rT × LocHeap (Val rT)) : Cfg rT :=
  ⟨r.1.toExp, σ.updateHeap fun _ => r.2⟩

/-- One foreign step on the value `v` in state `σ`: a Dirac, or zero when stuck. -/
def Cfg.ffi [ProbLangFFI rT] (v : Val rT) (σ : State rT) : Measure (Cfg rT) :=
  (ProbLangFFI.ffi (v, σ.heap)).unwrapM fun r => dirac (Cfg.ofFFI σ r)

/-- When every foreign call is stuck, every foreign step is zero. -/
@[simp] theorem Cfg.ffi_of_stuck [ProbLangFFI rT] [ProbLangFFI.Stuck rT] (v : Val rT)
    (σ : State rT) : Cfg.ffi v σ = 0 := by
  simp [Cfg.ffi, Option.unwrapM]

/-- A foreign step is zero exactly when the foreign call is stuck. -/
theorem Cfg.ffi_eq_zero_iff [ProbLangFFI rT] {v : Val rT} {σ : State rT} :
    Cfg.ffi v σ = 0 ↔ ProbLangFFI.ffi (v, σ.heap) = none := by
  unfold Cfg.ffi
  cases ProbLangFFI.ffi (v, σ.heap) <;> simp [Option.unwrapM]

/-- Meanings of the distribution names of `sample`: a kernel on values per name, a probability
measure or zero at each argument. -/
class ProbLangDist (rT : Type _) [MeasurableSpace rT] where
  /-- The kernel `sample n` draws from. -/
  dist : ℕ → Kernel (Val rT) (Val rT)
  /-- Each `dist n v` is a probability measure or zero. -/
  isZeroOrProbabilityMeasure_dist (n : ℕ) (v : Val rT) : IsZeroOrProbabilityMeasure (dist n v)

attribute [instance] ProbLangDist.isZeroOrProbabilityMeasure_dist

/-- The reserved integer family has the legacy uniform-integer semantics. -/
class ProbLangDist.IsUniformInt (rT : Type _) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    [ProbLangDist rT] : Prop where
  /-- Positive bounds give the uniform distribution on the half-open integer interval. -/
  dist_pos (N : Int) (hN : 0 < N) :
    ProbLangDist.dist unifIntName (Val.int N) =
      (uniformOfFinset (Finset.Ico 0 N)).map (fun z : Int => Val.int (rT := rT) z)
  /-- Nonpositive bounds give the legacy sentinel value. -/
  dist_nonpos (N : Int) (hN : N ≤ 0) :
    ProbLangDist.dist unifIntName (Val.int (rT := rT) N) =
      dirac (Val.int (rT := rT) (-1))
  /-- Non-integer arguments are outside the reserved integer family. -/
  dist_other (v : Val rT) (hv : ∀ N : Int, v ≠ Val.int N) :
    ProbLangDist.dist unifIntName v = 0

/-- The reserved real family has the legacy unit-uniform semantics. -/
class ProbLangDist.IsUniformReal (rT : Type _) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    [ProbLangDist rT] : Prop where
  /-- Every argument gives the unit-uniform real distribution, embedded as values. -/
  dist_eq (v : Val rT) :
    ProbLangDist.dist unifRealName v =
      (LawfulProbLangℝ.unifUnit (T := rT)).map (fun r : rT => Val.real r)

/-- The reserved integer family draws only integer values. -/
class ProbLangDist.IsIntValued (rT : Type _) [MeasurableSpace rT] [ProbLangDist rT] : Prop where
  /-- Each law of the reserved integer family vanishes off the integer values. -/
  dist_compl_range_int (v : Val rT) :
    ProbLangDist.dist unifIntName v (range fun z : Int => Val.int z)ᶜ = 0

/-- A value of positive mass under the reserved integer family is an integer. -/
theorem ProbLangDist.exists_int_of_dist_pos [ProbLangDist rT] [ProbLangDist.IsIntValued rT]
    {v w : Val rT} (h : 0 < ProbLangDist.dist unifIntName v {w}) : ∃ z : Int, w = Val.int z := by
  by_contra! hw
  refine h.ne' (measure_mono_null (fun w' hw' => ?_)
    (ProbLangDist.IsIntValued.dist_compl_range_int v))
  rintro ⟨z, rfl⟩
  exact hw z (mem_singleton_iff.mp hw').symm

/-- Each kernel of a `ProbLangDist` has mass at most one. -/
instance ProbLangDist.isFiniteKernel_dist [ProbLangDist rT] (n : ℕ) :
    IsFiniteKernel (ProbLangDist.dist (rT := rT) n) :=
  ⟨1, one_lt_top, fun _ => prob_le_one⟩

/-- Sampler of `⟨w, σ⟩` with the value `w` drawn from `ProbLangDist.dist n v`. -/
def Cfg.sample [ProbLangDist rT] (n : ℕ) (v : Val rT) (σ : State rT) : Measure (Cfg rT) :=
  (ProbLangDist.dist n v).map (⟨.ofVal ·, σ⟩)

/-- Allocation of a random variable with prior `ProbLangDist.dist n v`, at a fresh label. -/
def Cfg.randvar (n : ℕ) (v : Val rT) (σ : State rT) : Measure (Cfg rT) :=
  let l := σ.rvs.fresh
  dirac ⟨.lit (.lbl l), σ.updateRvs (·.insert l (RvCell.fresh n v))⟩

/-- A test of the random variable `l` through observation `k` at argument `a`: the result is drawn
from the posterior predictive, and the random variable records it. -/
def Cfg.test [ProbLangDist rT] [ProbLangObs rT] (k : ℕ) (a : Val rT) (l : Lbl) (σ : State rT) :
    Measure (Cfg rT) :=
  match σ.rvs[l]? with
  | none => 0
  | some c => (c.testCell ProbLangDist.dist k a).map fun p =>
    ⟨.lit (.int p.1), σ.updateRvs (·.insert l p.2)⟩

/-- A step that only replaces the random variables: an expression and new random variables drawn
from `μ`. -/
def Cfg.rvsStep (μ : Measure (Exp rT × LocHeap (RvCell rT))) (σ : State rT) : Measure (Cfg rT) :=
  μ.map fun p => ⟨p.1, σ.updateRvs fun _ => p.2⟩

/-- The expression and random variables after a test of the random variable `l` in `r`. -/
def Cfg.testRvs [ProbLangDist rT] [ProbLangObs rT] (k : ℕ) (a : Val rT) (l : Lbl)
    (r : LocHeap (RvCell rT)) : Measure (Exp rT × LocHeap (RvCell rT)) :=
  match r[l]? with
  | none => 0
  | some c => (c.testCell ProbLangDist.dist k a).map fun p => (.lit (.int p.1), r.insert l p.2)

section

variable [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] {e : Exp α}
  {m : Measure T}

/-- `isValM` keeps the measure when the expression is a value. -/
@[simp] theorem Exp.isValM_some (He : e.isValue) :
    e.isValM m = m := ite_eq_left He

/-- `isValM` keeps the measure given an `IsVal` witness. -/
theorem Exp.isValM_some' (w : IsVal e) :
    e.isValM m = m := isValM_some w.toIsValue

/-- `isValM` is the zero measure when the expression is not a value. -/
@[simp] theorem Exp.isValM_none (He : ¬ e.isValue) :
    e.isValM m = 0 := ite_eq_right He

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
    dirac ⟨.lit <| .loc ℓ, σ.updateHeap fun t => t.insert ℓ vd⟩
  | ⟨.load (.lit (.loc ℓ)), σ⟩ =>
    match σ.heap[ℓ]? with | none => 0 | some v => (dirac ⟨.ofVal v, σ⟩)
  | ⟨.store (.lit (.loc ℓ)) e, σ⟩ =>
    e.asValM fun v =>
    match σ.heap[ℓ]? with
    | none => 0
    | some _ => dirac ⟨.lit .unit, σ.updateHeap fun t => t.insert ℓ v⟩
  | ⟨.tape n e, σ⟩ =>
    e.asValM fun v =>
    let α := σ.tapes.fresh
    dirac ⟨.lit <| .lbl α, σ.updateTapes fun t => t.insert α (.empty n v)⟩
  | ⟨.sample n e (.lit .unit), σ⟩ => e.asValM fun v => Cfg.sample n v σ
  | ⟨.sample n e (.lit (.lbl α)), σ⟩ =>
    e.asValM fun v =>
    match σ.tapes[α]? with
    | none => 0
    | some t =>
      if t.name = n ∧ t.arg = v then
        let σ' := σ.updateTapes fun m => m.insert α t.shift
        match t.head? with
        | none => Cfg.sample n v σ'
        | some w => dirac ⟨.ofVal w, σ'⟩
      else Cfg.sample n v σ
  | ⟨.scrut e p, σ⟩ =>
    e.isValM <|
    match Pat.tryMatch p e with
    | some bindings => dirac ⟨.inl bindings, σ⟩
    | none => dirac ⟨.inr (.lit .unit), σ⟩
  | ⟨.allocN (.lit (.int n)) ev, σ⟩ =>
    ev.asValM fun v =>
      if 0 < n then
        dirac ⟨.lit (.loc σ.heap.fresh), σ.updateHeap (fun h => LocHeap.allocN h v n.toNat)⟩
      else 0
  | ⟨.ffi e, σ⟩ => e.asValM fun v => Cfg.ffi v σ
  | ⟨.randvar n e, σ⟩ => e.asValM fun v => Cfg.randvar n v σ
  | ⟨.test k (.lit (.lbl l)) e, σ⟩ => e.asValM fun a => Cfg.test k a l σ
  | _ => 0

/-- Allocating a tape for a value creates a fresh empty tape. -/
@[simp] theorem headStep_tape {n : ℕ} {e : Exp rT} {v : Val rT} {σ : State rT}
    (hv : e.toVal? = some v) :
    headStep ⟨.tape n e, σ⟩ =
      dirac ⟨.lit (.lbl σ.tapes.fresh), σ.updateTapes (·.insert σ.tapes.fresh (.empty n v))⟩ := by
  simp only [headStep, Exp.asValM, hv]

/-- Sampling with unit draws freshly from the requested family. -/
@[simp] theorem headStep_sample {n : ℕ} {e : Exp rT} {v : Val rT} {σ : State rT}
    (hv : e.toVal? = some v) :
    headStep ⟨.sample n e (.lit .unit), σ⟩ = Cfg.sample n v σ := by
  simp only [headStep, Exp.asValM, hv]

/-- A matching tape returns and consumes its presampled head. -/
@[simp] theorem headStep_sample_tape_some {n : ℕ} {e : Exp rT} {v w : Val rT}
    {α : Lbl} {t : Tape rT} {σ : State rT} (hv : e.toVal? = some v)
    (htape : σ.tapes[α]? = some t) (hfamily : t.name = n ∧ t.arg = v)
    (hhead : t.head? = some w) :
    headStep ⟨.sample n e (.lit (.lbl α)), σ⟩ =
      dirac ⟨.ofVal w, σ.updateTapes (·.insert α t.shift)⟩ := by
  simp only [headStep, Exp.asValM, hv, htape, ite_eq_left hfamily, hhead]

/-- A matching tape hole is consumed before drawing freshly. -/
@[simp] theorem headStep_sample_tape_none {n : ℕ} {e : Exp rT} {v : Val rT}
    {α : Lbl} {t : Tape rT} {σ : State rT} (hv : e.toVal? = some v)
    (htape : σ.tapes[α]? = some t) (hfamily : t.name = n ∧ t.arg = v)
    (hhead : t.head? = none) :
    headStep ⟨.sample n e (.lit (.lbl α)), σ⟩ =
      Cfg.sample n v (σ.updateTapes (·.insert α t.shift)) := by
  simp only [headStep, Exp.asValM, hv, htape, ite_eq_left hfamily, hhead]

/-- A mismatching tape is ignored by a fresh draw. -/
@[simp] theorem headStep_sample_tape_other {n : ℕ} {e : Exp rT} {v : Val rT}
    {α : Lbl} {t : Tape rT} {σ : State rT} (hv : e.toVal? = some v)
    (htape : σ.tapes[α]? = some t) (hfamily : ¬(t.name = n ∧ t.arg = v)) :
    headStep ⟨.sample n e (.lit (.lbl α)), σ⟩ = Cfg.sample n v σ := by
  simp only [headStep, Exp.asValM, hv, htape, ite_eq_right hfamily]

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
    on_goal 1 => rename_goal beta.lam
    on_goal 2 => rename_goal beta.fix
    on_goal 3 => rename_goal unop
    on_goal 4 => rename_goal binop
    on_goal 5 => rename_goal cond.true
    on_goal 6 => rename_goal cond.false
    on_goal 7 => rename_goal fst
    on_goal 8 => rename_goal snd
    on_goal 9 => rename_goal case.left
    on_goal 10 => rename_goal case.right
    on_goal 11 => rename_goal alloc
    on_goal 12 => rename_goal load
    on_goal 13 => rename_goal store
    on_goal 14 => rename_goal tape
    on_goal 15 => rename_goal sample.plain
    on_goal 16 => rename_goal sample.tape
    on_goal 17 => rename_goal scrut
    on_goal 18 => rename_goal allocN
    on_goal 19 => rename_goal ffi
    on_goal 20 => rename_goal randvar
    on_goal 21 => rename_goal test
    on_goal 22 => rename_goal default
  ))

/-- Decompose the Cfg equality hypothesis left by `split` on `headStep`, then substitute. -/
macro "head_subst" : tactic =>
  `(tactic| (
    rename_i h_eq
    have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
    subst_eqs))

/-- Unfold `isValM` and split it into named redex and no-redex goals. -/
macro "head_split_isValM" redex:ident no_redex:ident : tactic =>
  `(tactic| (
    unfold Exp.isValM
    split
    on_goal 2 => rename_goal $no_redex
    on_goal 1 => rename_goal $redex))

/-- Unfold `asValM` and split it into named no-redex and redex goals. -/
macro "head_split_asValM" no_redex:ident redex:ident : tactic =>
  `(tactic| (
    unfold Exp.asValM
    split
    on_goal 1 => rename_goal $no_redex
    on_goal 2 => rename_goal $redex))

/-- Split a binary match (e.g. heap lookup) and name the two goals. -/
macro "head_split2" goal1:ident goal2:ident : tactic =>
  `(tactic| (
    split
    on_goal 1 => rename_goal $goal1
    on_goal 2 => rename_goal $goal2))

/-- Split `headStep` into one named goal per branch, using the `<ctor>.redex` and `<ctor>.no_redex`
naming scheme. -/
macro "head_case" : tactic =>
  `(tactic| (
    head_case_names
    case' sample.tape =>
      head_subst
      head_split_asValM sample.tape.no_redex sample_tape_value
      case' sample_tape_value =>
        head_split2 sample.tape.unalloc sample_tape_alloc
        case' sample_tape_alloc =>
          simp only
          split
          on_goal 2 => rename_goal sample.tape.mismatch
          on_goal 1 =>
            subst_eqs
            head_split2 sample.tape.empty sample.tape.deterministic
    case' ffi =>
      head_subst
      head_split_asValM ffi.no_redex ffi.redex
    case' tape =>
      head_subst
      head_split_asValM tape.no_redex tape.redex
    case' sample.plain =>
      head_subst
      head_split_asValM sample.plain.no_redex sample.plain.redex
    case' store =>
      head_subst
      unfold Exp.asValM
      split
      on_goal 1 => rename_goal store.no_redex
      on_goal 2 => head_split2 store.segfault store.redex
    case' load =>
      head_subst
      head_split2 load.segfault load.redex
    case' allocN =>
      head_subst
      head_split_asValM allocN.no_redex allocN.value
      case' allocN.value => head_split2 allocN.redex allocN.nonpos
    case' alloc =>
      head_subst
      head_split_asValM alloc.no_redex alloc.redex
    case' randvar =>
      head_subst
      head_split_asValM randvar.no_redex randvar.redex
    case' test =>
      head_subst
      head_split_asValM test.no_redex test.redex
    case' case.right =>
      head_subst
      head_split_isValM case.right.redex case.right.no_redex
    case' case.left =>
      head_subst
      head_split_isValM case.left.redex case.left.no_redex
    case' snd =>
      head_subst
      unfold Exp.isValM
      split
      on_goal 2 => rename_goal snd.no_redex_1
      on_goal 1 => head_split2 snd.redex snd.no_redex_2
    case' fst =>
      head_subst
      unfold Exp.isValM
      split
      on_goal 2 => rename_goal fst.no_redex_1
      on_goal 1 => head_split2 fst.redex fst.no_redex_2
    case' cond.false => head_subst
    case' cond.true => head_subst
    case' binop =>
      head_subst
      unfold Exp.isValM
      split
      on_goal 2 => rename_goal binop.no_redex_1
      on_goal 1 => head_split2 binop.redex binop.no_redex_2
    case' unop =>
      head_subst
      head_split_isValM unop.redex unop.no_redex
    case' scrut =>
      head_subst
      unfold Exp.isValM
      split
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
theorem isValM_isProbabilityMeasure
    (he : e.isValue) [IsProbabilityMeasure m] : IsProbabilityMeasure (e.isValM m) := by
  rw [Exp.isValM, ite_eq_left he]; infer_instance

/-- `asValM f` on a value `v` is a probability measure when `f v` is. -/
theorem asValM_isProbabilityMeasure {f : Val α → Measure T}
    {v : Val α} (hv : e.toVal? = some v) [IsProbabilityMeasure (f v)] :
    IsProbabilityMeasure (e.asValM f) := by
  simp [Exp.asValM, hv]; infer_instance

end

section

variable {e : Exp rT} {σ : State rT}

/-- `Cfg.uniform` is a probability measure. -/
instance Cfg.uniform_isProbabilityMeasure {z : Int} :
    IsProbabilityMeasure (Cfg.uniform z σ) := by
  unfold Cfg.uniform Int.isPos
  by_cases hpos : 0 < z
  · simp only [hpos, dite_true]
    have := isProbabilityMeasure_uniformOfFinset (Finset.nonempty_Ico.mpr hpos)
    infer_instance
  · simp only [hpos, dite_false]; infer_instance

/-- A nonzero foreign step is a probability measure. -/
theorem Cfg.ffi_isProbabilityMeasure [ProbLangFFI rT] {v : Val rT} (h : Cfg.ffi v σ ≠ 0) :
    IsProbabilityMeasure (Cfg.ffi v σ) := by
  unfold Cfg.ffi at h ⊢
  cases hr : ProbLangFFI.ffi (v, σ.heap)
  · simp [hr, Option.unwrapM] at h
  · exact dirac.isProbabilityMeasure

/-- The configuration a test reaches when it observes `y`. -/
abbrev Cfg.testOutcome (k : ℕ) (a : Val rT) (l : Lbl) (σ : State rT)
    (c : RvCell rT) (y : Int) : Cfg rT :=
  ⟨.lit (.int y), σ.updateRvs (·.insert l (c.observe k a y))⟩

/-- The configuration a test reaches is measurable in the observed value. -/
theorem Cfg.measurable_testOutcome [ProbLangObs rT] {k : ℕ} {a : Val rT} {l : Lbl}
    {c : RvCell rT} :
    Measurable (fun x : Val rT => Cfg.testOutcome k a l σ c (ProbLangObs.obs k (a, x))) := by
  have hH : Measurable (Cfg.testOutcome k a l σ c) := .of_discrete
  exact hH.comp (RvCell.measurable_obs_apply k a)

/-- Placing an expression and new random variables in a state is measurable. -/
theorem Cfg.measurable_rvsStep_mk (σ : State rT) :
    Measurable (fun p : Exp rT × LocHeap (RvCell rT) =>
      (⟨p.1, σ.updateRvs fun _ => p.2⟩ : Cfg rT)) :=
  Cfg.measurable_iff.mpr ⟨measurable_fst, State.measurable_mk_param measurable_const
    measurable_const measurable_snd⟩

/-- Allocating a random variable only replaces the random variables. -/
theorem Cfg.randvar_eq_rvsStep (n : ℕ) (v : Val rT) (σ : State rT) :
    Cfg.randvar n v σ =
      Cfg.rvsStep (dirac (.lit (.lbl σ.rvs.fresh), σ.rvs.insert σ.rvs.fresh (RvCell.fresh n v)))
        σ := by
  rw [Cfg.rvsStep, map_dirac' (Cfg.measurable_rvsStep_mk σ)]
  rfl

section

variable [ProbLangDist rT] {n : ℕ} {v : Val rT}

/-- `Cfg.sample` is a probability measure or zero. -/
instance Cfg.sample_isZeroOrProbabilityMeasure :
    IsZeroOrProbabilityMeasure (Cfg.sample n v σ) := by
  unfold Cfg.sample
  infer_instance

/-- A nonzero `Cfg.sample` is a probability measure. -/
theorem Cfg.sample_isProbabilityMeasure (h : Cfg.sample n v σ ≠ 0) :
    IsProbabilityMeasure (Cfg.sample n v σ) :=
  ⟨IsZeroOrProbabilityMeasure.measure_univ.resolve_left (h <| measure_univ_eq_zero.mp ·)⟩

/-- `Cfg.sample` is zero exactly when its kernel is zero at the argument. -/
theorem Cfg.sample_eq_zero_iff :
    Cfg.sample n v σ = 0 ↔ ProbLangDist.dist n v = 0 := by
  have hg : Measurable (fun w : Val rT => (⟨.ofVal w, σ⟩ : Cfg rT)) :=
    Cfg.measurable_iff.mpr ⟨Exp.ofVal.measurable, measurable_const⟩
  exact map_eq_zero_iff hg.aemeasurable

/-- A measurable map on the state commutes with `Cfg.sample`. -/
theorem Cfg.sample_map_state {f : State rT → State rT} (hf : Measurable f) :
    (Cfg.sample n v σ).map (fun ρ => ⟨ρ.expr, f ρ.state⟩) = Cfg.sample n v (f σ) := by
  unfold Cfg.sample
  rw [Measure.map_map (Cfg.measurable_mapState hf)
    (f := fun w : Val rT => (⟨Exp.ofVal w, σ⟩ : Cfg rT))
    (Cfg.measurable_iff.mpr ⟨Exp.ofVal.measurable, measurable_const⟩)]
  rfl

end

/-- All value outcomes paired with the fixed state `σ`. -/
def Cfg.sampleSet (σ : State rT) : Set (Cfg rT) :=
  Set.range fun w : Val rT => ⟨Exp.ofVal w, σ⟩

/-- Value outcomes in `S`, paired with the fixed state `σ`. -/
def Cfg.sampleSetOn (S : Set (Val rT)) (σ : State rT) : Set (Cfg rT) :=
  {ρ | ∃ w ∈ S, ρ = ⟨Exp.ofVal w, σ⟩}

/-- The set of all value outcomes in a fixed state is measurable. -/
theorem Cfg.measurableSet_sampleSet [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (σ : State rT) :
    MeasurableSet (Cfg.sampleSet σ) := by
  have hval : MeasurableSet { ρ : Cfg rT | ∃ w, ρ.expr = Exp.ofVal w } := by
    simpa using measurableSet_TglCfgSet (MeasurableSet.univ : MeasurableSet (Set.univ))
  have hstate : MeasurableSet { ρ : Cfg rT | ρ.state = σ } :=
    (MeasurableSet.singleton σ).preimage Cfg.measurable_state
  have heq : Cfg.sampleSet σ =
      { ρ : Cfg rT | ∃ w, ρ.expr = Exp.ofVal w } ∩ { ρ | ρ.state = σ } := by
    ext ρ
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨⟨w, rfl⟩, rfl⟩
    · rintro ⟨⟨w, hw⟩, hσ⟩
      cases ρ
      cases hw
      cases hσ
      exact ⟨w, rfl⟩
  rw [heq]
  exact hval.inter hstate

/-- A measurable value carrier gives a measurable fixed-state sample carrier. -/
theorem Cfg.measurableSet_sampleSetOn [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    {S : Set (Val rT)} (hS : MeasurableSet S) (σ : State rT) :
    MeasurableSet (Cfg.sampleSetOn S σ) := by
  have hval : MeasurableSet {ρ : Cfg rT | ∃ w, ρ.expr = Exp.ofVal w ∧ w ∈ S} :=
    measurableSet_TglCfgSet hS
  have hstate : MeasurableSet {ρ : Cfg rT | ρ.state = σ} :=
    (MeasurableSet.singleton σ).preimage Cfg.measurable_state
  have heq : Cfg.sampleSetOn S σ =
      {ρ : Cfg rT | ∃ w, ρ.expr = Exp.ofVal w ∧ w ∈ S} ∩ {ρ | ρ.state = σ} := by
    ext ρ
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, rfl, hw⟩, rfl⟩
    · rintro ⟨⟨w, hw, hS⟩, hσ⟩
      cases ρ
      cases hw
      cases hσ
      exact ⟨w, hS, rfl⟩
  rw [heq]
  exact hval.inter hstate

section

variable [ProbLangDist rT] {n : ℕ} {v : Val rT}

/-- A family sample is concentrated on value outcomes in its input state. -/
theorem Cfg.concentrated_sample [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (σ : State rT) :
    Concentrated (Cfg.sample n v σ) (Cfg.sampleSet σ) := by
  let f : Val rT → Cfg rT := fun w => ⟨Exp.ofVal w, σ⟩
  have hf : Measurable f :=
    Cfg.measurable_iff.mpr ⟨Exp.ofVal.measurable, measurable_const⟩
  have himage : MeasurableSet (f '' Set.univ) := by
    simpa only [f, Cfg.sampleSet, Set.image_univ] using Cfg.measurableSet_sampleSet σ
  simpa only [Cfg.sample, Cfg.sampleSet, Set.image_univ] using
    (Concentrated.map (T := Set.univ) hf himage (Concentrated.univ :
      Concentrated (ProbLangDist.dist n v) Set.univ))

/-- A family sample inherits any measurable carrier of its distribution. -/
theorem Cfg.concentrated_sampleSetOn [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    {S : Set (Val rT)} (hS : MeasurableSet S)
    (hconc : Concentrated (ProbLangDist.dist n v) S) (σ : State rT) :
    Concentrated (Cfg.sample n v σ) (Cfg.sampleSetOn S σ) := by
  let f : Val rT → Cfg rT := fun w => ⟨Exp.ofVal w, σ⟩
  have hf : Measurable f :=
    Cfg.measurable_iff.mpr ⟨Exp.ofVal.measurable, measurable_const⟩
  have himage : f '' S = Cfg.sampleSetOn S σ := by
    ext ρ
    simp only [Set.mem_image, Cfg.sampleSetOn, Set.mem_ofPred_eq, f]
    exact ⟨fun ⟨w, hw, hρ⟩ => ⟨w, hw, hρ.symm⟩,
      fun ⟨w, hw, hρ⟩ => ⟨w, hw, hρ.symm⟩⟩
  rw [Cfg.sample, ← himage]
  exact Concentrated.map hf (himage ▸ Cfg.measurableSet_sampleSetOn hS σ) hconc

end

/-- A measurable carrier for all outcomes of a labeled family sample. -/
def Cfg.sampleTapeSet (n : ℕ) (v : Val rT) (α : Lbl) (σ : State rT) : Set (Cfg rT) :=
  match σ.tapes[α]? with
  | none => ∅
  | some t =>
    if t.name = n ∧ t.arg = v then
      let σ' := σ.updateTapes (·.insert α t.shift)
      match t.head? with
      | none => Cfg.sampleSet σ'
      | some w => {⟨Exp.ofVal w, σ'⟩}
    else Cfg.sampleSet σ

/-- A measurable carrier for a labeled sample restricted to a carrier of the requested law. -/
def Cfg.sampleTapeSetOn (n : ℕ) (v : Val rT) (α : Lbl) (S : Set (Val rT))
    (σ : State rT) : Set (Cfg rT) :=
  match σ.tapes[α]? with
  | none => ∅
  | some t =>
    if t.name = n ∧ t.arg = v then
      let σ' := σ.updateTapes (·.insert α t.shift)
      match t.head? with
      | none => Cfg.sampleSetOn S σ'
      | some w => {⟨Exp.ofVal w, σ'⟩}
    else Cfg.sampleSetOn S σ

/-- The carrier for a labeled family sample is measurable. -/
theorem Cfg.measurableSet_sampleTapeSet [LawfulProbLangℝ rT]
    [MeasurableSingletonClass rT] (n : ℕ) (v : Val rT) (α : Lbl) (σ : State rT) :
    MeasurableSet (Cfg.sampleTapeSet n v α σ) := by
  simp only [Cfg.sampleTapeSet]
  split
  · exact MeasurableSet.empty
  · split
    · split
      · exact Cfg.measurableSet_sampleSet _
      · exact MeasurableSet.singleton _
    · exact Cfg.measurableSet_sampleSet _

/-- A labeled sample carrier is measurable when the requested-law carrier is measurable. -/
theorem Cfg.measurableSet_sampleTapeSetOn [LawfulProbLangℝ rT]
    [MeasurableSingletonClass rT] {S : Set (Val rT)} (hS : MeasurableSet S)
    (n : ℕ) (v : Val rT) (α : Lbl) (σ : State rT) :
    MeasurableSet (Cfg.sampleTapeSetOn n v α S σ) := by
  simp only [Cfg.sampleTapeSetOn]
  split
  · exact MeasurableSet.empty
  · split
    · split
      · exact Cfg.measurableSet_sampleSetOn hS _
      · exact MeasurableSet.singleton _
    · exact Cfg.measurableSet_sampleSetOn hS _

section

variable [ProbLangDist rT] {n : ℕ} {v : Val rT}

/-- A labeled sample head step is concentrated on `sampleTapeSet`. -/
theorem Cfg.concentrated_headStep_sample_tape [LawfulProbLangℝ rT]
    [MeasurableSingletonClass rT] [ProbLangFFI rT] [ProbLangObs rT]
    {e : Exp rT} (hv : e.toVal? = some v)
    (α : Lbl) (σ : State rT) :
    Concentrated (headStep ⟨Exp.sample n e (.lit (.lbl α)), σ⟩)
      (Cfg.sampleTapeSet n v α σ) := by
  simp only [headStep, Exp.asValM, hv, Cfg.sampleTapeSet]
  split
  · simp [Concentrated]
  · split
    · split
      · exact Cfg.concentrated_sample _
      · simp [Concentrated]
    · exact Cfg.concentrated_sample _

/-- A labeled family sample inherits a measurable carrier of its requested distribution. -/
theorem Cfg.concentrated_headStep_sampleTapeSetOn [LawfulProbLangℝ rT]
    [MeasurableSingletonClass rT] [ProbLangFFI rT] [ProbLangObs rT]
    {S : Set (Val rT)} (hS : MeasurableSet S)
    (hconc : Concentrated (ProbLangDist.dist n v) S)
    {e : Exp rT} (hv : e.toVal? = some v) (α : Lbl) (σ : State rT) :
    Concentrated (headStep ⟨Exp.sample n e (.lit (.lbl α)), σ⟩)
      (Cfg.sampleTapeSetOn n v α S σ) := by
  simp only [headStep, Exp.asValM, hv, Cfg.sampleTapeSetOn]
  split
  · simp [Concentrated]
  · split
    · split
      · exact Cfg.concentrated_sampleSetOn hS hconc _
      · simp [Concentrated]
    · exact Cfg.concentrated_sampleSetOn hS hconc _

/-- `Cfg.randvar` is a probability measure. -/
instance Cfg.randvar_isProbabilityMeasure : IsProbabilityMeasure (Cfg.randvar n v σ) := by
  unfold Cfg.randvar
  infer_instance

variable [ProbLangObs rT] {k : ℕ} {l : Lbl}

/-- `Cfg.test` is a probability measure or zero. -/
instance Cfg.test_isZeroOrProbabilityMeasure :
    IsZeroOrProbabilityMeasure (Cfg.test k v l σ) := by
  unfold Cfg.test RvCell.testCell
  split <;> infer_instance

/-- A nonzero `Cfg.test` is a probability measure. -/
theorem Cfg.test_isProbabilityMeasure (h : Cfg.test k v l σ ≠ 0) :
    IsProbabilityMeasure (Cfg.test k v l σ) :=
  ⟨IsZeroOrProbabilityMeasure.measure_univ.resolve_left (h <| measure_univ_eq_zero.mp ·)⟩

variable {a : Val rT} {c : RvCell rT}

/-- `Cfg.test` at an allocated random variable, as a pushforward of its posterior. -/
theorem Cfg.test_eq_map (h : σ.rvs[l]? = some c) :
    Cfg.test k a l σ = (c.post ProbLangDist.dist).map
      (fun x => Cfg.testOutcome k a l σ c (ProbLangObs.obs k (a, x))) := by
  have hH : Measurable (fun p : Int × RvCell rT =>
      (⟨.lit (.int p.1), σ.updateRvs (·.insert l p.2)⟩ : Cfg rT)) := by
    refine Cfg.measurable_iff.mpr ⟨Exp.lit.measurable.comp (BaseLit.int.measurable.comp
      measurable_fst), ?_⟩
    show Measurable (fun p : Int × RvCell rT =>
      State.mk σ.heap σ.tapes (σ.rvs.insert l p.2))
    exact State.measurable_mk_param measurable_const measurable_const
      ((Measurable.locHeap_insert l).comp (measurable_const.prodMk measurable_snd))
  simp only [Cfg.test, h, RvCell.testCell]
  rw [map_map hH (RvCell.measurable_testOutcome c k a)]
  rfl

/-- A test at an allocated random variable is its predictive law, pushed to the outcomes. -/
theorem Cfg.test_eq_map_predictive (h : σ.rvs[l]? = some c) :
    Cfg.test k a l σ =
      (RvCell.predictive ProbLangDist.dist k a c).map (Cfg.testOutcome k a l σ c) := by
  rw [Cfg.test_eq_map h, RvCell.predictive,
    map_map .of_discrete (RvCell.measurable_obs_apply k a)]
  rfl

/-- A nonzero test observes some result of positive posterior mass. -/
theorem Cfg.test_exists (h : Cfg.test k a l σ ≠ 0) :
    ∃ c y, σ.rvs[l]? = some c ∧
      c.post ProbLangDist.dist ((fun x => ProbLangObs.obs k (a, x)) ⁻¹' {y}) ≠ 0 := by
  rcases hc : σ.rvs[l]? with _ | c
  · simp [Cfg.test, hc] at h
  · rw [Cfg.test_eq_map hc] at h
    have hP : c.post ProbLangDist.dist ≠ 0 := fun h0 => h (by rw [h0, Measure.map_zero])
    have : (ae (c.post ProbLangDist.dist)).NeBot := ae_neBot.mpr hP
    obtain ⟨x, hx⟩ := (ae_fiber_ne_zero (c.post ProbLangDist.dist)
      (fun x => ProbLangObs.obs k (a, x))).exists
    exact ⟨c, _, rfl, hx⟩

/-- A test is zero exactly when the label holds no random variable with a nonzero posterior. -/
theorem Cfg.test_eq_zero_iff :
    Cfg.test k a l σ = 0 ↔ ∀ c, σ.rvs[l]? = some c → c.post ProbLangDist.dist = 0 := by
  rcases hc : σ.rvs[l]? with _ | c
  · simp [Cfg.test, hc]
  · rw [Cfg.test_eq_map hc, Measure.map_eq_zero_iff Cfg.measurable_testOutcome.aemeasurable]
    simp

/-- A test is zero or not independently of the heap and the tapes. -/
theorem Cfg.test_eq_zero_iff_of_rvs {σ' : State rT} (h : σ'.rvs = σ.rvs) :
    Cfg.test k a l σ' = 0 ↔ Cfg.test k a l σ = 0 := by
  rw [Cfg.test_eq_zero_iff, Cfg.test_eq_zero_iff, h]

/-- A test only replaces the random variables. -/
theorem Cfg.test_eq_rvsStep : Cfg.test k a l σ = Cfg.rvsStep (Cfg.testRvs k a l σ.rvs) σ := by
  have hH : Measurable (fun p : Int × RvCell rT =>
      ((.lit (.int p.1) : Exp rT), σ.rvs.insert l p.2)) :=
    (Exp.lit.measurable.comp (BaseLit.int.measurable.comp measurable_fst)).prodMk
      ((Measurable.locHeap_insert l).comp (measurable_const.prodMk measurable_snd))
  rcases hc : σ.rvs[l]? with _ | c
  · simp [Cfg.test, Cfg.testRvs, Cfg.rvsStep, hc]
  · simp only [Cfg.test, Cfg.testRvs, Cfg.rvsStep, hc]
    rw [map_map (Cfg.measurable_rvsStep_mk σ) hH]
    rfl

/-- The random-variable part of a test is a probability measure or zero. -/
instance Cfg.testRvs_isZeroOrProbabilityMeasure (r : LocHeap (RvCell rT)) :
    IsZeroOrProbabilityMeasure (Cfg.testRvs k a l r) := by
  unfold Cfg.testRvs
  split <;> infer_instance

/-- A test only changes the random variables of the state. -/
theorem Cfg.test_ae_state {P : State rT → Prop} (hP : MeasurableSet {σ | P σ})
    (h : ∀ f, P (σ.updateRvs f)) : ∀ᵐ ρ ∂Cfg.test k a l σ, P ρ.state := by
  rcases hc : σ.rvs[l]? with _ | c
  · simp [Cfg.test, hc]
  · rw [Cfg.test_eq_map hc]
    exact (ae_map_iff Cfg.measurable_testOutcome.aemeasurable (Cfg.measurable_state hP)).mpr
      (ae_of_all _ fun x => h (·.insert l (c.observe k a (ProbLangObs.obs k (a, x)))))

/-- A test commutes with a measurable state change that keeps the random variables and commutes
with updating them. -/
theorem Cfg.test_map_state {g : State rT → State rT} (hg : Measurable g)
    (hrvs : (g σ).rvs = σ.rvs) (hupd : ∀ f, g (σ.updateRvs f) = (g σ).updateRvs f) :
    (Cfg.test k a l σ).map (fun ρ => ⟨ρ.expr, g ρ.state⟩) = Cfg.test k a l (g σ) := by
  rcases hc : σ.rvs[l]? with _ | c
  · have hc' : (g σ).rvs[l]? = none := by rw [hrvs, hc]
    simp [Cfg.test, hc, hc']
  · have hc' : (g σ).rvs[l]? = some c := by rw [hrvs, hc]
    have hG : Measurable (fun ρ : Cfg rT => (⟨ρ.expr, g ρ.state⟩ : Cfg rT)) :=
      Cfg.measurable_iff.mpr ⟨Cfg.measurable_expr, hg.comp Cfg.measurable_state⟩
    rw [Cfg.test_eq_map hc, Cfg.test_eq_map hc', map_map hG Cfg.measurable_testOutcome]
    congr 1
    funext x
    simp only [Function.comp, Cfg.testOutcome, hupd]

end

/-- A measurable map on the state commutes with `Cfg.uniform`. -/
theorem Cfg.uniform_map_state {z : Int} {f : State rT → State rT} (hf : Measurable f) :
    (Cfg.uniform z σ).map (fun ρ => ⟨ρ.expr, f ρ.state⟩) = Cfg.uniform z (f σ) := by
  unfold Cfg.uniform
  split
  · rw [Measure.map_map (Cfg.measurable_mapState hf) (by measurability)]
    rfl
  · exact map_dirac' (Cfg.measurable_mapState hf) _

variable [LawfulProbLangℝ rT]

/-- `Cfg.uniformReal` is a probability measure. -/
instance Cfg.uniformReal_isProbabilityMeasure :
    IsProbabilityMeasure (Cfg.uniformReal σ) := by
  unfold Cfg.uniformReal
  infer_instance

/-- A measurable map on the state commutes with `Cfg.uniformReal`. -/
theorem Cfg.uniformReal_map_state {f : State rT → State rT} (hf : Measurable f) :
    (Cfg.uniformReal σ).map (fun ρ => ⟨ρ.expr, f ρ.state⟩) = Cfg.uniformReal (f σ) := by
  unfold Cfg.uniformReal
  rw [Measure.map_map (Cfg.measurable_mapState hf)
    (f := fun r : rT => (⟨.lit (.real r), σ⟩ : Cfg rT)) (Cfg.measurable_iff.mpr
    ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩)]
  rfl

variable [ProbLangDist rT]

section

variable [ProbLangDist.IsUniformInt rT]

/-- Sampling the reserved integer family agrees with the legacy uniform sampler. -/
theorem Cfg.sample_unifInt (z : Int) (σ : State rT) :
    Cfg.sample unifIntName (Val.int z) σ = Cfg.uniform z σ := by
  by_cases hz : 0 < z
  · unfold Cfg.sample
    rw [ProbLangDist.IsUniformInt.dist_pos z hz]
    unfold Cfg.uniform Int.isPos
    simp only [hz, dite_true]
    have hf : Measurable (fun q : Int => Val.int (rT := rT) q) := by
      rw [measurable_comap_iff]
      exact Exp.lit.measurable.comp BaseLit.int.measurable
    have hg : Measurable (fun w : Val rT => (⟨.ofVal w, σ⟩ : Cfg rT)) :=
      Cfg.measurable_iff.mpr ⟨Exp.ofVal.measurable, measurable_const⟩
    rw [Measure.map_map hg hf]
    rfl
  · have hz' : z ≤ 0 := le_of_not_gt hz
    unfold Cfg.sample
    rw [ProbLangDist.IsUniformInt.dist_nonpos z hz']
    unfold Cfg.uniform Int.isPos
    simp only [hz, dite_false]
    rw [map_dirac]
    rfl

end

section

variable [ProbLangDist.IsUniformReal rT]

/-- Sampling the reserved real family agrees with the legacy uniform-real sampler. -/
theorem Cfg.sample_unifReal (v : Val rT) (σ : State rT) :
    Cfg.sample unifRealName v σ = Cfg.uniformReal σ := by
  have hreal : Measurable (fun r : rT => (Val.real r : Val rT)) := by
    rw [measurable_comap_iff]
    exact Exp.lit.measurable.comp BaseLit.real.measurable
  have hcfg : Measurable (fun w : Val rT => (⟨.ofVal w, σ⟩ : Cfg rT)) :=
    Cfg.measurable_iff.mpr ⟨Exp.ofVal.measurable, measurable_const⟩
  unfold Cfg.sample Cfg.uniformReal
  rw [ProbLangDist.IsUniformReal.dist_eq,
    Measure.map_map hcfg hreal]
  rfl

end

variable [ProbLangFFI rT] [ProbLangObs rT]

/-- A reducible head step loses no mass: it is a probability measure. -/
theorem head_step_mass :
    (headStep ⟨e, σ⟩ ≠ 0) → IsProbabilityMeasure (headStep ⟨e, σ⟩) := by
  -- Each branch is `0` (hypothesis false), a Dirac, or a uniform sampler.
  head_case
  all_goals try (· simp)
  case beta.lam.redex | beta.fix.redex | cond.true | cond.false
     | fst.redex | snd.redex | case.left.redex | case.right.redex
     | alloc.redex | allocN.redex | load.redex | store.redex | tape.redex
     | sample.tape.deterministic | scrut_success | scrut_failure => intro _; infer_instance
  case unop.redex _ op e _ =>
    cases op.eval e
    · simp [Option.unwrapM]
    · simpa [Option.unwrapM] using dirac.isProbabilityMeasure
  case binop.redex _ op e1 e2 _ _ =>
    cases op.eval e1 e2
    · simp [Option.unwrapM]
    · simpa [Option.unwrapM] using dirac.isProbabilityMeasure
  case ffi.redex => exact Cfg.ffi_isProbabilityMeasure
  case sample.plain.redex | sample.tape.empty | sample.tape.mismatch =>
    exact Cfg.sample_isProbabilityMeasure
  case randvar.redex => intro _; exact Cfg.randvar_isProbabilityMeasure
  case test.redex => exact Cfg.test_isProbabilityMeasure

/-- A head step that is not a foreign call is the step with stuck foreign code. -/
theorem headStep_eq_stuck_of_ne_ffi (he : ∀ e', e ≠ .ffi e') :
    headStep ⟨e, σ⟩ = @headStep rT _ _ _ ProbLangFFI.stuck _ ⟨e, σ⟩ := by
  unfold headStep
  split <;> first | rfl | (rename_i heq; exact absurd (congrArg Cfg.expr heq) (he _))

/-- Every head step has total mass at most one. -/
theorem headStep_univ_le_one (ρ : Cfg rT) : (headStep ρ) univ ≤ 1 := by
  obtain ⟨e, σ⟩ := ρ
  by_cases h : headStep ⟨e, σ⟩ = 0
  · simp [h]
  · exact (head_step_mass h).measure_univ.le

/-- Values do not head-step, `isValueR` form. -/
theorem val_head_stuck_R : headStep ⟨e, σ⟩ ≠ 0 → ¬e.isValueR := by
  intro h hv
  cases e <;> first | exact h rfl | simp [Exp.isValueR] at hv

/-- Values do not head-step. -/
theorem val_head_stuck (h : headStep ⟨e, σ⟩ ≠ 0) : ¬e.isValue := by
  rw [Exp.isValue_iff_isValueR]
  exact fun hv => val_head_stuck_R h hv.1

/-- Singleton-mass form of `val_head_stuck_R`. -/
theorem Discrete.val_head_stuck_R {ρ : Cfg rT}
    (h : 0 < headStep ⟨e, σ⟩ {ρ}) : ¬e.isValueR :=
  _root_.ProbLang.val_head_stuck_R fun h0 => h.ne' (by rw [h0]; rfl)

/-- An expression with a `toVal?` value is a value. -/
theorem Exp.toVal?_isValue {e : Exp α} {v : Val α} : e.toVal? = some v → e.isValue := by
  intro h; by_contra hne; rw [Exp.toVal?_eq_none.mpr hne] at h; exact absurd h (by simp)

/-- An expression with a `toVal?` value is a raw value. -/
theorem Exp.toVal?_isValueR {e : Exp α} {v : Val α} (h : e.toVal? = some v) : e.isValueR :=
  (Exp.isValue_iff_isValueR.mp (Exp.toVal?_isValue h)).1

/-- If `Ki[e]` can head-step, then `e` is value-shaped: `headStep` only fires once every
evaluation-position subterm is a value. -/
theorem head_ctx_step_val {Ki : EctxItem rT} :
    headStep ⟨Ki.fillItem e, σ⟩ ≠ 0 → e.isValueR := by
  head_case
  all_goals try · simp
  all_goals cases Ki <;> intro h <;>
    simp_all [EctxItem.fillItem, Exp.isValue_iff_isValueR, Exp.isValueR, Exp.toVal?_isValueR]

end

/-! ## Measurability of the measure combinators (for any measurable `rT`) -/

/-- `isValM` is measurable in the expression and the measure. -/
theorem Exp.isValM.measurable :
    Measurable (fun (p : Exp rT × Measure T) => p.1.isValM p.2) := by
  have hpred : MeasurableSet {p : Exp rT × Measure T | p.1.isValue} := by
    have : {p : Exp rT × Measure T | p.1.isValue} =
        ({e : Exp rT | e.isValueR} ∩ {e | Exp.lcb 0 e = true}) ×ˢ (univ : Set (Measure T)) := by
      ext ⟨e, m⟩; simp [Exp.isValue_iff_isValueR, mem_inter_iff]
    rw [this]
    exact ((Exp.isValueR.measurable.setOf).inter Exp.lcb_zero.measurableSet).prod MeasurableSet.univ
  exact Measurable.ite hpred measurable_snd measurable_const

/-- Being a value is a measurable predicate on configurations. -/
@[fun_prop]
theorem Cfg.isValue_measurable : Measurable (fun a : Cfg rT => a.expr.isValue) := by
  rw [← measurableSet_setOfPred]
  have h : {a : Cfg rT | a.expr.isValue} =
      Cfg.expr ⁻¹' ({e : Exp rT | e.isValueR} ∩ {e | Exp.lcb 0 e = true}) := by
    ext a; simp [Exp.isValue_iff_isValueR, mem_inter_iff]
  rw [h]
  exact Cfg.measurable_expr ((Exp.isValueR.measurable.setOf).inter Exp.lcb_zero.measurableSet)

/-- The set of configurations holding a value is measurable. -/
@[measurability]
theorem Cfg.isValue_measurableSet : MeasurableSet {a : Cfg rT | a.expr.isValue} :=
  Cfg.isValue_measurable.setOf

/-- `isValM` is measurable in a parameter. -/
theorem Exp.isValM.measurable_param {γ : Type _} [MeasurableSpace γ]
    {he : γ → Exp rT} (hhe : Measurable he)
    {hm : γ → Measure T} (hhm : Measurable hm) :
    Measurable (fun c : γ => (he c).isValM (hm c)) :=
  Exp.isValM.measurable.comp (hhe.prodMk hhm)

/-- The Dirac measure on a configuration is measurable in its components. -/
theorem Cfg.measurable_dirac_mk {γ : Type _} [MeasurableSpace γ]
    {fe : γ → Exp rT} (he : Measurable fe)
    {fs : γ → State rT} (hs : Measurable fs) :
    Measurable (fun q : γ => (dirac (Cfg.mk (fe q) (fs q)) : Measure (Cfg rT))) :=
  measurable_dirac.comp (Cfg.measurable_iff.mpr ⟨he, hs⟩)

/-- Measurability of `asValM` in a parameter, with the function taken jointly over the parameter and
value. -/
theorem Exp.asValM.measurable {γ : Type _} [MeasurableSpace γ]
    {g : γ × Val rT → Measure T} (hg : Measurable g) :
    Measurable (fun (p : Exp rT × γ) => p.1.asValM (fun v => g (p.2, v))) := by
  have htoVal : Measurable (fun (p : Exp rT × γ) => (p.1.toVal?, p.2)) :=
    (Exp.toVal_question.measurable).comp measurable_fst |>.prodMk measurable_snd
  suffices h : Measurable (fun (q : Option (Val rT) × γ) =>
      match q.1 with | none => (0 : Measure T) | some v => g (q.2, v)) by
    have hrw : (fun (p : Exp rT × γ) => p.1.asValM (fun v => g (p.2, v))) =
        (fun (q : Option (Val rT) × γ) =>
            match q.1 with | none => (0 : Measure T) | some v => g (q.2, v)) ∘
          (fun (p : Exp rT × γ) => (p.1.toVal?, p.2)) := by
      funext ⟨e, c⟩
      show Exp.asValM e (fun v => g (c, v)) = match e.toVal? with | none => 0 | some v => g (c, v)
      unfold Exp.asValM
      rfl
    rw [hrw]
    exact h.comp htoVal
  intro S hS
  have hpre : (fun (q : Option (Val rT) × γ) =>
        match q.1 with | none => (0 : Measure T) | some v => g (q.2, v)) ⁻¹' S =
      (if (0 : Measure T) ∈ S then ({none} : Set (Option (Val rT))) ×ˢ univ else ∅)
        ∪ (Prod.map some id) '' ((fun (p : Val rT × γ) => g (p.2, p.1)) ⁻¹' S) := by
    ext ⟨o, c⟩
    cases o with
    | none => by_cases h0 : (0 : Measure T) ∈ S <;> simp [h0]
    | some v => simp [mem_preimage, mem_image, Prod.map]
  rw [hpre]
  refine MeasurableSet.union ?_ ?_
  · split_ifs
    · exact MeasurableSet.singleton_none.prod MeasurableSet.univ
    · exact MeasurableSet.empty
  · exact (MeasurableEmbedding.some_mk.prodMap .id).measurableSet_image'
      (hg.comp (measurable_snd.prodMk measurable_fst) hS)

section

/-- `Option.unwrapM f` is measurable when `f` is. -/
theorem Option.unwrapM.measurable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → Measure β} (hf : Measurable f) :
    Measurable (Option.unwrapM f) := by
  intro S hS
  have hpre : (Option.unwrapM f : Option α → Measure β) ⁻¹' S =
      (if (0 : Measure β) ∈ S then ({none} : Set (Option α)) else ∅)
      ∪ (some '' (f ⁻¹' S)) := by
    ext o
    cases o with
    | none => by_cases h0 : (0 : Measure β) ∈ S <;> simp [Option.unwrapM, h0]
    | some v => simp [Option.unwrapM]
  rw [hpre]
  refine MeasurableSet.union ?_ ?_
  · split_ifs
    · exact MeasurableSet.singleton_none
    · exact MeasurableSet.empty
  · exact MeasurableSet.image_some (hf hS)

/-- `Option.unwrapM` is measurable jointly in a parameter and the option. -/
theorem Option.unwrapM.measurable_param
    {α β γ : Type _} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {o : γ → Option α} (ho : Measurable o)
    {g : γ × α → Measure β} (hg : Measurable g) :
    Measurable (fun c : γ => Option.unwrapM (fun a => g (c, a)) (o c)) := by
  suffices h : Measurable (fun q : Option α × γ =>
      match q.1 with | none => (0 : Measure β) | some a => g (q.2, a)) by
    have hrw : (fun c : γ => Option.unwrapM (fun a => g (c, a)) (o c)) = (fun q : Option α × γ =>
            match q.1 with | none => (0 : Measure β) | some a => g (q.2, a)) ∘
          (fun c : γ => (o c, c)) := by
      funext c
      show Option.unwrapM (fun a => g (c, a)) (o c) =
            match o c with | none => 0 | some a => g (c, a)
      unfold Option.unwrapM
      cases o c <;> rfl
    rw [hrw]
    exact h.comp (ho.prodMk measurable_id)
  intro S hS
  have hpre : (fun q : Option α × γ =>
        match q.1 with | none => (0 : Measure β) | some a => g (q.2, a)) ⁻¹' S =
      (if (0 : Measure β) ∈ S then ({none} : Set (Option α)) ×ˢ univ else ∅)
        ∪ (Prod.map some id) '' ((fun p : α × γ => g (p.2, p.1)) ⁻¹' S) := by
    ext ⟨o', c⟩
    cases o' with
    | none => by_cases h0 : (0 : Measure β) ∈ S <;> simp [h0]
    | some a => simp [mem_preimage, mem_image, Prod.map]
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
  @measurable_map_uncurry α β γ _ _ _ h hh (fun _ => μ) measurable_const (by
      have : Kernel.mk (fun _ : α => μ) measurable_const =
          Kernel.const α μ := rfl
      rw [this]; infer_instance)

/-- `Cfg.uniform` is measurable. -/
theorem Cfg.uniform.measurable :
    Measurable (fun (p : Int × State rT) => Cfg.uniform p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro z
  show Measurable (fun σ : State rT => Cfg.uniform z σ)
  unfold Cfg.uniform
  cases hzp : z.isPos with
  | none => exact Cfg.measurable_dirac_mk measurable_const measurable_id
  | some w =>
    exact measurable_map_const_uncurry (uniformOfFinset (Finset.Ico 0 w.1))
      (h := fun p : State rT × Int => Cfg.mk (.lit (.int p.2)) p.1)
      (Cfg.measurable_iff.mpr
        ⟨Exp.lit.measurable.comp (BaseLit.int.measurable.comp measurable_snd), measurable_fst⟩)

/-- `Cfg.ofFFI` is measurable in the state and the outcome. -/
theorem Cfg.ofFFI.measurable :
    Measurable (fun p : State rT × (FFIOutcome rT × LocHeap (Val rT)) => Cfg.ofFFI p.1 p.2) :=
  Cfg.measurable_iff.mpr ⟨FFIOutcome.toExp.measurable.comp (measurable_fst.comp measurable_snd),
    State.measurable_mk_param (measurable_snd.comp measurable_snd)
      (State.measurable_tapes.comp measurable_fst) (State.measurable_rvs.comp measurable_fst)⟩

/-- `Cfg.ffi` is measurable in the state and the argument. -/
theorem Cfg.ffi.measurable [ProbLangFFI rT] :
    Measurable (fun p : State rT × Val rT => Cfg.ffi p.2 p.1) :=
  Option.unwrapM.measurable_param
    (ProbLangFFI.measurable_ffi.comp
      (measurable_snd.prodMk (State.measurable_heap.comp measurable_fst)))
    (measurable_dirac.comp (Cfg.ofFFI.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))

/-- `Cfg.sample` is measurable in the name, the state and the argument. -/
theorem Cfg.sample.measurable [ProbLangDist rT] :
    Measurable (fun p : ℕ × State rT × Val rT => Cfg.sample p.1 p.2.2 p.2.1) := by
  refine measurable_from_prod_countable_right fun n => ?_
  have hk : Measurable fun p : State rT × Val rT => ProbLangDist.dist n p.2 :=
    (ProbLangDist.dist n).measurable.comp measurable_snd
  have : IsFiniteKernel (Kernel.mk _ hk) :=
    ⟨1, one_lt_top, fun p => prob_le_one (μ := ProbLangDist.dist n p.2)⟩
  exact measurable_map_uncurry
    (h := fun q : (State rT × Val rT) × Val rT => Cfg.mk (Exp.ofVal q.2) q.1.1)
    (Cfg.measurable_iff.mpr ⟨Exp.ofVal.measurable.comp measurable_snd,
      measurable_fst.comp measurable_fst⟩) hk

variable [LawfulProbLangℝ rT]

/-- `Cfg.uniformReal` is measurable. -/
theorem Cfg.uniformReal.measurable :
    Measurable (fun σ : State rT => Cfg.uniformReal σ) :=
  measurable_map_const_uncurry (LawfulProbLangℝ.unifUnit (T := rT))
    (h := fun p : State rT × rT => Cfg.mk (.lit (.real p.2)) p.1)
    (Cfg.measurable_iff.mpr
      ⟨Exp.lit.measurable.comp (BaseLit.real.measurable.comp measurable_snd), measurable_fst⟩)

end

/-- The `headStep` branch for a foreign call, uncurried over the state and arguments. -/
@[simp] def headStep.cFFI [ProbLangFFI rT] (p : State rT × Exp rT) : Measure (Cfg rT) :=
  p.2.asValM fun v => Cfg.ffi v p.1

/-- Measurability of the `ffi` branch of `headStep`. -/
theorem headStep.cFFI.measurable [ProbLangFFI rT] :
    Measurable (headStep.cFFI (rT := rT)) :=
  (Exp.asValM.measurable Cfg.ffi.measurable).comp
    (f := fun p : State rT × Exp rT => (p.2, p.1)) (by fun_prop)

/-! ## Measurability of `headStep`, branch by branch

Each non-trivial branch is a named `def` with its own measurability theorem (for elaboration
speed), proved with the `exp_zero_<ctor>_apply` macros of `CoreMeasures/Recurrences.lean`. -/

/-- The `headStep` branch for `lam`/`fix` application, uncurried over the state and arguments. -/
@[simp] def headStep.cApp (p : State rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .lam e1' => p.2.2.isValM (dirac ⟨Exp.open' e1' p.2.2, p.1⟩)
  | .fix e1' => p.2.2.isValM
                  (dirac ⟨Exp.app (Exp.open' e1' (.fix e1')) p.2.2, p.1⟩)
  | _ => 0

/-- Measurability of the `app` branch of `headStep`. -/
theorem headStep.cApp.measurable :
    Measurable (headStep.cApp (rT := rT)) := by
  let c_lam_inner : (State rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.1.2.isValM (dirac ⟨Exp.open' q.2 q.1.2, q.1.1⟩)
  let c_fix_inner : (State rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.1.2.isValM (dirac ⟨Exp.app (Exp.open' q.2 (.fix q.2)) q.1.2, q.1.1⟩)
  have hrw : headStep.cApp = (fun q : Exp rT × (State rT × Exp rT) =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun e1' => c_lam_inner (q.2, e1')) (fun e1' => c_fix_inner (q.2, e1'))
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)) ∘
        (fun p : State rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, e1, e2⟩
    show headStep.cApp _ = _
    unfold headStep.cApp
    cases e1 <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have h_lam_inner : Measurable c_lam_inner := by
    refine Exp.isValM.measurable_param (he := fun q : (State rT × Exp rT) × Exp rT => q.1.2)
      (hm := fun q : (State rT × Exp rT) × Exp rT =>
                (dirac (Cfg.mk (Exp.open' q.2 q.1.2) q.1.1) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_snd.comp measurable_fst
    · exact Cfg.measurable_dirac_mk (Exp.open'.measurable.comp
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
        (measurable_fst.comp measurable_fst)
  have h_fix_inner : Measurable c_fix_inner := by
    refine Exp.isValM.measurable_param (he := fun q : (State rT × Exp rT) × Exp rT => q.1.2)
      (hm := fun q : (State rT × Exp rT) × Exp rT =>
                (dirac (Cfg.mk (Exp.app (Exp.open' q.2 (.fix q.2)) q.1.2) q.1.1) :
                  Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_snd.comp measurable_fst
    · refine Cfg.measurable_dirac_mk ?_ (measurable_fst.comp measurable_fst)
      refine Exp.app.measurable.comp (Measurable.prodMk ?_ ?_)
      · exact Exp.open'.measurable.comp
          (measurable_snd.prodMk (Exp.fix.measurable.comp measurable_snd))
      · exact measurable_snd.comp measurable_fst
  exp_zero_app_apply c_lam_inner, h_lam_inner, c_fix_inner, h_fix_inner

/-- The head-step branch for block allocation. -/
@[simp] def headStep.cAllocN (p : State rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  ((Exp.litExtract p.2.1).bind BaseLit.intExtract).unwrapM fun n =>
    p.2.2.asValM fun v =>
      if 0 < n then
        dirac ⟨.lit (.loc p.1.heap.fresh),
          p.1.updateHeap (fun h => LocHeap.allocN h v n.toNat)⟩
      else 0

/-- Block allocation is measurable in its state and operands. -/
theorem headStep.cAllocN.measurable :
    Measurable (headStep.cAllocN (rT := rT)) := by
  let g : Int × State rT × Val rT → Measure (Cfg rT) := fun q =>
    if 0 < q.1 then
      dirac ⟨.lit (.loc q.2.1.heap.fresh),
        q.2.1.updateHeap (fun h => LocHeap.allocN h q.2.2 q.1.toNat)⟩
    else 0
  have hg : Measurable g := by
    apply measurable_from_prod_countable_right
    intro n
    dsimp only [g]
    split_ifs
    · refine Cfg.measurable_dirac_mk ?_ ?_
      · exact Exp.lit.measurable.comp (BaseLit.loc.measurable.comp
          (LocHeap.measurable_fresh.comp (State.measurable_heap.comp measurable_fst)))
      · refine State.measurable_mk_param ?_ ?_ ?_
        · exact (LocHeap.measurable_allocN n.toNat).comp
            ((State.measurable_heap.comp measurable_fst).prodMk measurable_snd)
        · exact State.measurable_tapes.comp measurable_fst
        · exact State.measurable_rvs.comp measurable_fst
    · exact measurable_const
  have hg' : Measurable (fun q : (State rT × Int) × Val rT => g (q.1.2, q.1.1, q.2)) :=
    hg.comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have he : Measurable (fun p : State rT × Exp rT × Exp rT =>
      (Exp.litExtract p.2.1).bind BaseLit.intExtract) := by
    refine Option.measurable_bind_param
      (f := fun p : State rT × Exp rT × Exp rT => Exp.litExtract p.2.1)
      (some_branch := fun q : (State rT × Exp rT × Exp rT) × BaseLit rT =>
        BaseLit.intExtract q.2) ?_ ?_
    · exact Exp.litExtract.measurable.comp (measurable_fst.comp measurable_snd)
    · exact BaseLit.intExtract.measurable.comp measurable_snd
  unfold headStep.cAllocN
  apply Option.unwrapM.measurable_param he (g := fun q :
    (State rT × Exp rT × Exp rT) × Int =>
      q.1.2.2.asValM (fun v => g (q.2, q.1.1, v)))
  exact (Exp.asValM.measurable hg').comp
    ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

/-- The `headStep` branch for an `alloc`, uncurried over the state and arguments. -/
@[simp] def headStep.cAlloc (p : State rT × Exp rT) : Measure (Cfg rT) :=
  p.2.asValM (fun vd =>
    let ℓ := p.1.heap.fresh
    dirac ⟨.lit (.loc ℓ), p.1.updateHeap (·.insert ℓ vd)⟩)

/-- Measurability of the `alloc` branch of `headStep`. -/
theorem headStep.cAlloc.measurable :
    Measurable (headStep.cAlloc (rT := rT)) := by
  have hreshape : Measurable
      (fun p : State rT × Exp rT => (p.2, p.1) : State rT × Exp rT → Exp rT × State rT) :=
    measurable_snd.prodMk measurable_fst
  have hg : Measurable (fun q : State rT × Val rT =>
      (dirac (Cfg.mk (Exp.lit (.loc q.1.heap.fresh))
        (q.1.updateHeap (·.insert q.1.heap.fresh q.2))) :
        Measure (Cfg rT))) := by
    refine Cfg.measurable_dirac_mk ?_ ?_
    · refine Exp.lit.measurable.comp (BaseLit.loc.measurable.comp ?_)
      exact LocHeap.measurable_fresh.comp (State.measurable_heap.comp measurable_fst)
    · show Measurable (fun q : State rT × Val rT =>
          (q.1.updateHeap (·.insert q.1.heap.fresh q.2)))
      refine State.measurable_mk_param ?_ ?_ ?_
      · have hheap : Measurable (fun q : State rT × Val rT => q.1.heap) :=
          State.measurable_heap.comp measurable_fst
        have hfresh : Measurable (fun q : State rT × Val rT => q.1.heap.fresh) :=
          LocHeap.measurable_fresh.comp hheap
        exact (Measurable.locHeap_insert_param (V := Val rT)).comp
          (hheap.prodMk (hfresh.prodMk measurable_snd))
      · exact State.measurable_tapes.comp measurable_fst
      · exact State.measurable_rvs.comp measurable_fst
  exact (Exp.asValM.measurable hg).comp hreshape

/-- The `headStep` branch for a `cond`, uncurried over the state and arguments. -/
@[simp] def headStep.cCond (p : State rT × Exp rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .lit (.bool true) => dirac ⟨p.2.2.1, p.1⟩
  | .lit (.bool false) => dirac ⟨p.2.2.2, p.1⟩
  | _ => 0

/-- Measurability of the `cond` branch of `headStep`. -/
theorem headStep.cCond.measurable : Measurable (headStep.cCond (rT := rT)) := by
  let c_lit_inner : (State rT × Exp rT × Exp rT) × BaseLit rT → Measure (Cfg rT) :=
    fun q => match q.2 with
      | .bool true => dirac ⟨q.1.2.1, q.1.1⟩
      | .bool false => dirac ⟨q.1.2.2, q.1.1⟩
      | _ => 0
  have hrw : headStep.cCond = (fun q : Exp rT × (State rT × Exp rT × Exp rT) =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1 (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner (q.2, l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)) ∘
        (fun p : State rT × Exp rT × Exp rT × Exp rT =>
            (p.2.1, p.1, p.2.2.1, p.2.2.2)) := by
    funext ⟨σ, ec, et, ef⟩
    show headStep.cCond _ = _
    unfold headStep.cCond
    cases ec with
    | lit l => cases l with
      | bool b => cases b <;> rfl
      | _ => rfl
    | _ => rfl
  rw [hrw]
  refine Measurable.comp ?_ ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).comp measurable_snd |>.prodMk
          ((measurable_snd.comp measurable_snd).comp measurable_snd))))
  have hc_lit_inner : Measurable c_lit_inner := by
    let c_bool_inner : (State rT × Exp rT × Exp rT) × Bool → Measure (Cfg rT) :=
      fun r => if r.2 then dirac ⟨r.1.2.1, r.1.1⟩ else dirac ⟨r.1.2.2, r.1.1⟩
    have hrw2 : (fun q : (State rT × Exp rT × Exp rT) × BaseLit rT =>
          c_lit_inner q) =
        (fun p : BaseLit rT × (State rT × Exp rT × Exp rT) =>
            BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1 (fun _ => 0)
              (fun b => c_bool_inner (p.2, b))
              0 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)) ∘
          (fun q : (State rT × Exp rT × Exp rT) × BaseLit rT => (q.2, q.1)) := by
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
        if r.2 then (dirac ⟨r.1.2.1, r.1.1⟩ : Measure (Cfg rT)) else dirac ⟨r.1.2.2, r.1.1⟩)
      refine Measurable.ite ?_ ?_ ?_
      · exact MeasurableSet.preimage (measurableSet_singleton true) measurable_snd
      · exact Cfg.measurable_dirac_mk ((measurable_fst.comp measurable_snd).comp measurable_fst)
          (measurable_fst.comp measurable_fst)
      · exact Cfg.measurable_dirac_mk ((measurable_snd.comp measurable_snd).comp measurable_fst)
          (measurable_fst.comp measurable_fst)
    baseLit_zero_bool_apply c_bool_inner, h_bool_inner
  exp_zero_lit_apply c_lit_inner, hc_lit_inner

/-- The `headStep` branch for a `case`, uncurried over the state and arguments. -/
@[simp] def headStep.cCase (p : State rT × Exp rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .inl e => e.isValM (dirac ⟨p.2.2.1.app e, p.1⟩)
  | .inr e => e.isValM (dirac ⟨p.2.2.2.app e, p.1⟩)
  | _ => 0

/-- Measurability of the `case` branch of `headStep`. -/
theorem headStep.cCase.measurable :
    Measurable (headStep.cCase (rT := rT)) := by
  let c_inl_inner : (State rT × Exp rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.isValM (dirac ⟨q.1.2.1.app q.2, q.1.1⟩)
  let c_inr_inner : (State rT × Exp rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.isValM (dirac ⟨q.1.2.2.app q.2, q.1.1⟩)
  have hrw : headStep.cCase = (fun q : Exp rT × State rT × Exp rT × Exp rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
            (fun e => c_inl_inner (q.2, e))
            (fun e => c_inr_inner (q.2, e))
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)) ∘
        (fun p : State rT × Exp rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, ec, et, ef⟩
    show headStep.cCase _ = _
    unfold headStep.cCase
    cases ec <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have h_inl_inner : Measurable c_inl_inner := by
    refine Exp.isValM.measurable_param (he := fun q : (State rT × Exp rT × Exp rT) × Exp rT => q.2)
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
    refine Exp.isValM.measurable_param (he := fun q : (State rT × Exp rT × Exp rT) × Exp rT => q.2)
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
@[simp] def headStep.cLoad (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .lit (.loc ℓ) => match p.1.heap[ℓ]? with
                      | none => 0
                      | some v => dirac ⟨Exp.ofVal v, p.1⟩
  | _ => 0

/-- Measurability of the `load` branch of `headStep`. -/
theorem headStep.cLoad.measurable :
    Measurable (headStep.cLoad (rT := rT)) := by
  let c_leaf : State rT × Loc → Measure (Cfg rT) :=
    fun q => Option.casesOn (motive := fun _ => Measure (Cfg rT))
      q.1.heap[q.2]? 0 (fun v => dirac ⟨Exp.ofVal v, q.1⟩)
  let c_lit_inner : State rT × BaseLit rT → Measure (Cfg rT) := fun q =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) q.2
        (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (q.1, ℓ)) (fun _ => 0) (fun _ => 0)
        (fun _ => 0)
  have hrw : headStep.cLoad = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1 (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner (q.2, l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)) ∘
        (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.cLoad _ = _
    unfold headStep.cLoad
    cases e <;> (try rfl)
    rename_i l
    cases l <;> (try rfl)
    rename_i ℓ
    show _ = c_leaf (σ, ℓ)
    simp only [c_leaf]
    cases σ.heap[ℓ]? <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  have hc_leaf : Measurable c_leaf := by
    have hheap_getElem : Measurable (fun q : State rT × Loc => q.1.heap[q.2]?) := by
      have hflat : Measurable (fun p : Loc × State rT => p.2.heap[p.1]?) := by
        apply measurable_from_prod_countable_right
        intro ℓ
        exact (LocHeap.measurable_getElem? ℓ).comp State.measurable_heap
      exact hflat.comp (measurable_snd.prodMk measurable_fst)
    refine Option.measurable_elim_param_zero (f := fun q : State rT × Loc => q.1.heap[q.2]?)
      hheap_getElem
      (some_branch := fun q : (State rT × Loc) × Val rT =>
        (dirac (Cfg.mk (Exp.ofVal q.2) q.1.1) : Measure (Cfg rT))) ?_
    exact Cfg.measurable_dirac_mk
      (Val.fst.measurable.comp measurable_snd) (measurable_fst.comp measurable_fst)
  have hc_lit : Measurable c_lit_inner := by
    have hbase : Measurable (fun p : BaseLit rT × State rT =>
        BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (p.2, ℓ)) (fun _ => 0) (fun _ => 0)
          (fun _ => 0)) := by
      baseLit_zero_loc_apply c_leaf, hc_leaf
    exact (hbase.comp (measurable_snd.prodMk measurable_fst) :)
  exp_zero_lit_apply c_lit_inner, hc_lit

/-- The `headStep` branch for a `store`, uncurried over the state and arguments. -/
@[simp] def headStep.cStore (p : State rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .lit (.loc ℓ) => p.2.2.asValM (fun v =>
      match p.1.heap[ℓ]? with
      | none => 0
      | some _ => dirac ⟨.lit .unit, p.1.updateHeap (·.insert ℓ v)⟩)
  | _ => 0

/-- Measurability of the `store` branch of `headStep`. -/
theorem headStep.cStore.measurable :
    Measurable (headStep.cStore (rT := rT)) := by
  let c_leaf_inner_someBranch : (State rT × Loc) × Val rT → Measure (Cfg rT) :=
    fun r => dirac ⟨.lit .unit, r.1.1.updateHeap (·.insert r.1.2 r.2)⟩
  let c_leaf_g : (State rT × Loc) × Val rT → Measure (Cfg rT) :=
    fun r => Option.casesOn (motive := fun _ => Measure (Cfg rT))
      r.1.1.heap[r.1.2]? 0 (fun _ => c_leaf_inner_someBranch r)
  let c_leaf : (State rT × Exp rT) × Loc → Measure (Cfg rT) :=
    fun r => r.1.2.asValM (fun v => c_leaf_g ((r.1.1, r.2), v))
  let c_lit_inner : (State rT × Exp rT) × BaseLit rT → Measure (Cfg rT) := fun q =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) q.2
        (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (q.1, ℓ)) (fun _ => 0) (fun _ => 0)
        (fun _ => 0)
  have hrw : headStep.cStore = (fun q : Exp rT × State rT × Exp rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1 (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner ((q.2.1, q.2.2), l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)) ∘
        (fun p : State rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, e1, e2⟩
    show headStep.cStore _ = _
    unfold headStep.cStore
    cases e1 <;> (try rfl)
    rename_i l
    cases l <;> (try rfl)
    rename_i ℓ
    show _ = c_leaf ((σ, e2), ℓ)
    simp only [c_leaf, c_leaf_g, c_leaf_inner_someBranch]
    unfold Exp.asValM
    cases e2.toVal? <;> (try rfl)
    rename_i v
    cases σ.heap[ℓ]? <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have h_someBr : Measurable c_leaf_inner_someBranch := by
    refine Cfg.measurable_dirac_mk measurable_const ?_
    show Measurable (fun r : (State rT × Loc) × Val rT =>
      r.1.1.updateHeap (·.insert r.1.2 r.2))
    refine State.measurable_mk_param ?_ ?_ ?_
    · show Measurable (fun r : (State rT × Loc) × Val rT =>
        r.1.1.heap.insert r.1.2 r.2)
      have hmk : Measurable (fun r : (State rT × Loc) × Val rT =>
            (r.1.1.heap, r.1.2, r.2)) :=
        (State.measurable_heap.comp (measurable_fst.comp measurable_fst)).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
      exact Measurable.locHeap_insert_param.comp hmk
    · exact State.measurable_tapes.comp (measurable_fst.comp measurable_fst)
    · exact State.measurable_rvs.comp (measurable_fst.comp measurable_fst)
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
          (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (p.2, ℓ)) (fun _ => 0) (fun _ => 0)
          (fun _ => 0)) := by
      baseLit_zero_loc_apply c_leaf, h_leaf
    exact (hbase.comp (measurable_snd.prodMk measurable_fst) :)
  exp_zero_lit_apply c_lit_inner, hc_lit

/-- A fresh sample step, uncurried over the state, family, and argument. -/
@[simp] def headStep.cSampleFresh [ProbLangDist rT]
    (p : State rT × ℕ × Exp rT) : Measure (Cfg rT) :=
  p.2.2.asValM fun v => Cfg.sample p.2.1 v p.1

/-- Measurability of a fresh sample step. -/
theorem headStep.cSampleFresh.measurable [ProbLangDist rT] :
    Measurable (headStep.cSampleFresh (rT := rT)) := by
  have hg : Measurable fun q : (State rT × ℕ) × Val rT => Cfg.sample q.1.2 q.2 q.1.1 :=
    Cfg.sample.measurable.comp
      (f := fun q : (State rT × ℕ) × Val rT => (q.1.2, q.1.1, q.2)) (by fun_prop)
  exact (Exp.asValM.measurable hg).comp
    (f := fun p : State rT × ℕ × Exp rT => (p.2.2, p.1, p.2.1)) (by fun_prop)

/-- The head-step branch for tape allocation. -/
@[simp] def headStep.cTape (p : State rT × ℕ × Exp rT) : Measure (Cfg rT) :=
  p.2.2.asValM fun v =>
    dirac ⟨.lit (.lbl p.1.tapes.fresh),
      p.1.updateTapes (·.insert p.1.tapes.fresh (.empty p.2.1 v))⟩

/-- Measurability of tape allocation. -/
theorem headStep.cTape.measurable : Measurable (headStep.cTape (rT := rT)) := by
  have hfresh : Measurable fun q : (State rT × ℕ) × Val rT => q.1.1.tapes.fresh :=
    LocHeap.measurable_fresh.comp
      (State.measurable_tapes.comp (measurable_fst.comp measurable_fst))
  have hg : Measurable fun q : (State rT × ℕ) × Val rT =>
      (dirac ⟨.lit (.lbl q.1.1.tapes.fresh),
        q.1.1.updateTapes (·.insert q.1.1.tapes.fresh (.empty q.1.2 q.2))⟩ :
          Measure (Cfg rT)) := by
    refine Cfg.measurable_dirac_mk
      (Exp.lit.measurable.comp (BaseLit.lbl.measurable.comp hfresh)) ?_
    refine State.measurable_mk_param
      (State.measurable_heap.comp (measurable_fst.comp measurable_fst)) ?_
      (State.measurable_rvs.comp (measurable_fst.comp measurable_fst))
    exact Measurable.locHeap_insert_param.comp
      ((State.measurable_tapes.comp (measurable_fst.comp measurable_fst)).prodMk
        (hfresh.prodMk (Tape.measurable_empty.comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  exact (Exp.asValM.measurable hg).comp
    (f := fun p : State rT × ℕ × Exp rT => (p.2.2, p.1, p.2.1)) (by fun_prop)

/-- A tape-backed sample after looking up its tape. -/
@[simp] def headStep.cSampleTapeLeaf [ProbLangDist rT]
    (p : State rT × ℕ × Val rT × Lbl × Option (Tape rT)) : Measure (Cfg rT) :=
  match p.2.2.2.2 with
  | none => 0
  | some t =>
    if t.name = p.2.1 ∧ t.arg = p.2.2.1 then
      let σ' := p.1.updateTapes (·.insert p.2.2.2.1 t.shift)
      match t.head? with
      | none => Cfg.sample p.2.1 p.2.2.1 σ'
      | some w => dirac ⟨.ofVal w, σ'⟩
    else Cfg.sample p.2.1 p.2.2.1 p.1

/-- Measurability of a tape-backed sample after lookup. -/
theorem headStep.cSampleTapeLeaf.measurable [MeasurableEq rT] [ProbLangDist rT] :
    Measurable (headStep.cSampleTapeLeaf (rT := rT)) := by
  let g : (State rT × ℕ × Val rT × Lbl × Option (Tape rT)) × Tape rT →
      Measure (Cfg rT) := fun q =>
    if q.2.name = q.1.2.1 ∧ q.2.arg = q.1.2.2.1 then
      let σ' := q.1.1.updateTapes (·.insert q.1.2.2.2.1 q.2.shift)
      match q.2.head? with
      | none => Cfg.sample q.1.2.1 q.1.2.2.1 σ'
      | some w => dirac ⟨.ofVal w, σ'⟩
    else Cfg.sample q.1.2.1 q.1.2.2.1 q.1.1
  have hrw : headStep.cSampleTapeLeaf (rT := rT) =
      fun p => Option.unwrapM (fun t => g (p, t)) p.2.2.2.2 := by
    funext ⟨σ, n, v, α, o⟩
    cases o <;> rfl
  rw [hrw]
  have hσ : Measurable fun q :
      (State rT × ℕ × Val rT × Lbl × Option (Tape rT)) × Tape rT => q.1.1 :=
    measurable_fst.comp measurable_fst
  have hg : Measurable g := by
    have hmatch : MeasurableSet {q :
        (State rT × ℕ × Val rT × Lbl × Option (Tape rT)) × Tape rT |
        q.2.name = q.1.2.1 ∧ q.2.arg = q.1.2.2.1} :=
      (measurableSet_eq_fun (Tape.measurable_name.comp measurable_snd) (by fun_prop)).inter
        (measurableSet_eq_fun (Tape.measurable_arg.comp measurable_snd) (by fun_prop))
    refine Measurable.ite hmatch ?_ ?_
    · have hσ' : Measurable fun q :
          (State rT × ℕ × Val rT × Lbl × Option (Tape rT)) × Tape rT =>
          q.1.1.updateTapes (·.insert q.1.2.2.2.1 q.2.shift) := by
        refine State.measurable_mk_param (State.measurable_heap.comp hσ) ?_
          (State.measurable_rvs.comp hσ)
        have hlabel : Measurable fun q :
            (State rT × ℕ × Val rT × Lbl × Option (Tape rT)) × Tape rT =>
            q.1.2.2.2.1 := by fun_prop
        exact Measurable.locHeap_insert_param.comp
          ((State.measurable_tapes.comp hσ).prodMk
            (hlabel.prodMk (Tape.measurable_shift.comp measurable_snd)))
      have hnone : Measurable fun q :
          (State rT × ℕ × Val rT × Lbl × Option (Tape rT)) × Tape rT =>
          Cfg.sample q.1.2.1 q.1.2.2.1
            (q.1.1.updateTapes (·.insert q.1.2.2.2.1 q.2.shift)) :=
        Cfg.sample.measurable.comp (f := fun q :
            (State rT × ℕ × Val rT × Lbl × Option (Tape rT)) × Tape rT =>
          (q.1.2.1, q.1.1.updateTapes (·.insert q.1.2.2.2.1 q.2.shift),
            q.1.2.2.1)) (by fun_prop)
      have hsome : Measurable fun q :
          ((State rT × ℕ × Val rT × Lbl × Option (Tape rT)) × Tape rT) ×
            Val rT =>
          dirac (Cfg.mk (.ofVal q.2)
            (q.1.1.1.updateTapes (·.insert q.1.1.2.2.2.1 q.1.2.shift))) :=
        Cfg.measurable_dirac_mk (Exp.ofVal.measurable.comp measurable_snd)
          (hσ'.comp measurable_fst)
      refine Metrology.Shapes.measurable_of_eq _ (fun q :
          (State rT × ℕ × Val rT × Lbl × Option (Tape rT)) × Tape rT =>
          Option.casesOn q.2.head?
            (Cfg.sample q.1.2.1 q.1.2.2.1
              (q.1.1.updateTapes (·.insert q.1.2.2.2.1 q.2.shift)))
            (fun w => dirac ⟨.ofVal w,
              q.1.1.updateTapes (·.insert q.1.2.2.2.1 q.2.shift)⟩)) (fun q => ?_) ?_
      · cases q.2.head? <;> rfl
      · exact Option.measurable_elim_param
          (Tape.measurable_head?.comp measurable_snd) hnone hsome
    · exact Cfg.sample.measurable.comp (f := fun q :
          (State rT × ℕ × Val rT × Lbl × Option (Tape rT)) × Tape rT =>
          (q.1.2.1, q.1.1, q.1.2.2.1)) (by fun_prop)
  have hopt : Measurable fun p : State rT × ℕ × Val rT × Lbl × Option (Tape rT) =>
      p.2.2.2.2 := by fun_prop
  exact Option.unwrapM.measurable_param hopt hg

/-- The full `sample` branch, including fresh and tape-backed draws. -/
@[simp] def headStep.cSample [ProbLangDist rT]
    (p : State rT × ℕ × Exp rT × Exp rT) : Measure (Cfg rT) :=
  p.2.2.1.asValM fun v =>
    match p.2.2.2 with
    | .lit .unit => Cfg.sample p.2.1 v p.1
    | .lit (.lbl α) => headStep.cSampleTapeLeaf (p.1, p.2.1, v, α, p.1.tapes[α]?)
    | _ => 0

/-- Measurability of the full `sample` branch. -/
theorem headStep.cSample.measurable [MeasurableEq rT] [ProbLangDist rT] :
    Measurable (headStep.cSample (rT := rT)) := by
  let cUnit : (State rT × ℕ × Val rT) × Unit → Measure (Cfg rT) := fun q =>
    Cfg.sample q.1.2.1 q.1.2.2 q.1.1
  have hcUnit : Measurable cUnit :=
    Cfg.sample.measurable.comp (f := fun q : (State rT × ℕ × Val rT) × Unit =>
      (q.1.2.1, q.1.1, q.1.2.2)) (by fun_prop)
  let cLbl : (State rT × ℕ × Val rT) × Lbl → Measure (Cfg rT) := fun q =>
    headStep.cSampleTapeLeaf
      (q.1.1, q.1.2.1, q.1.2.2, q.2, q.1.1.tapes[q.2]?)
  have hcLbl : Measurable cLbl := by
    have hflat : Measurable fun q : Lbl × (State rT × ℕ × Val rT) =>
        headStep.cSampleTapeLeaf
          (q.2.1, q.2.2.1, q.2.2.2, q.1, q.2.1.tapes[q.1]?) := by
      refine measurable_from_prod_countable_right fun α => ?_
      exact headStep.cSampleTapeLeaf.measurable.comp
        (f := fun q : State rT × ℕ × Val rT =>
          (q.1, q.2.1, q.2.2, α, q.1.tapes[α]?)) (by fun_prop)
    exact hflat.comp (measurable_snd.prodMk measurable_fst)
  let cLit : (State rT × ℕ × Val rT) × BaseLit rT → Measure (Cfg rT) := fun q =>
    match q.2 with
    | .unit => cUnit (q.1, ())
    | .lbl α => cLbl (q.1, α)
    | _ => 0
  have hcLit : Measurable cLit := by
    have hbase : Measurable (fun q : BaseLit rT × (State rT × ℕ × Val rT) =>
        BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
          (fun _ => 0) (fun _ => 0) (cUnit (q.2, ())) (fun _ => 0)
          (fun α => cLbl (q.2, α)) (fun _ => 0) (fun _ => 0)) := by
      apply BaseLit.measurable_casesOn_param
        (c_int := fun _ => 0) (c_bool := fun _ => 0)
        (c_unit := fun q : State rT × ℕ × Val rT => cUnit (q, ()))
        (c_loc := fun _ => 0)
        (c_lbl := fun q : (State rT × ℕ × Val rT) × Lbl => cLbl q)
        (c_real := fun _ => 0)
        (c_code := fun _ => 0)
        (h_int := measurable_const) (h_bool := measurable_const)
        (h_unit := hcUnit.comp (measurable_id.prodMk measurable_const))
        (h_loc := measurable_const) (h_lbl := hcLbl)
        (h_real := measurable_const) (h_code := measurable_const)
    refine Metrology.Shapes.measurable_of_eq cLit (fun q =>
      BaseLit.casesOn q.2 (fun _ => 0) (fun _ => 0) (cUnit (q.1, ()))
        (fun _ => 0) (fun α => cLbl (q.1, α)) (fun _ => 0) (fun _ => 0)) ?_ ?_
    · intro q
      dsimp only [cLit]
      cases q.2 <;> rfl
    · exact hbase.comp (measurable_snd.prodMk measurable_fst)
  let cTarget : (State rT × ℕ × Val rT) × Exp rT → Measure (Cfg rT) := fun q =>
    match q.2 with
    | .lit l => cLit (q.1, l)
    | _ => 0
  have hcTarget : Measurable cTarget := by
    have hExp : Measurable (fun q : Exp rT × (State rT × ℕ × Val rT) =>
        Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
          (fun _ => 0) (fun _ => 0) (fun l => cLit (q.2, l))
          (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)
          (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0)
          (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
          (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
          (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ => 0)
          (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)) := by
      exp_zero_lit_apply
        (fun q : (State rT × ℕ × Val rT) × BaseLit rT => cLit q), hcLit
    refine Metrology.Shapes.measurable_of_eq cTarget (fun q =>
      Exp.casesOn q.2 (fun _ => 0) (fun _ => 0) (fun l => cLit (q.1, l))
        (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)
        (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0)
        (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
        (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ => 0)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)) ?_ ?_
    · intro q
      dsimp only [cTarget]
      cases q.2 <;> rfl
    · exact hExp.comp (measurable_snd.prodMk measurable_fst)
  have hg : Measurable fun q : (State rT × ℕ × Exp rT) × Val rT =>
      cTarget ((q.1.1, q.1.2.1, q.2), q.1.2.2) :=
    hcTarget.comp (by fun_prop)
  have hfull : Measurable (fun p : State rT × ℕ × Exp rT × Exp rT =>
      p.2.2.1.asValM fun v => cTarget ((p.1, p.2.1, v), p.2.2.2)) :=
    (Exp.asValM.measurable hg).comp
      (f := fun p : State rT × ℕ × Exp rT × Exp rT =>
        (p.2.2.1, (p.1, p.2.1, p.2.2.2))) (by fun_prop)
  refine Metrology.Shapes.measurable_of_eq headStep.cSample _ ?_ hfull
  rintro ⟨σ, n, e, et⟩
  dsimp only [headStep.cSample, cTarget, cLit, cUnit, cLbl]
  cases et <;> try rfl
  rename_i l
  cases l <;> rfl

/-- `Cfg.randvar` is measurable in the prior name, the state and the argument. -/
theorem Cfg.randvar.measurable :
    Measurable (fun p : ℕ × State rT × Val rT => Cfg.randvar p.1 p.2.2 p.2.1) := by
  have hrvs : Measurable (fun p : ℕ × State rT × Val rT => p.2.1.rvs) :=
    State.measurable_rvs.comp (measurable_fst.comp measurable_snd)
  have hfresh : Measurable (fun p : ℕ × State rT × Val rT => p.2.1.rvs.fresh) :=
    LocHeap.measurable_fresh.comp hrvs
  refine Cfg.measurable_dirac_mk (Exp.lit.measurable.comp (BaseLit.lbl.measurable.comp hfresh)) ?_
  show Measurable (fun p : ℕ × State rT × Val rT =>
    State.mk p.2.1.heap p.2.1.tapes
      (p.2.1.rvs.insert p.2.1.rvs.fresh (RvCell.fresh p.1 p.2.2)))
  exact State.measurable_mk_param (by fun_prop) (by fun_prop)
    (Measurable.locHeap_insert_param.comp (hrvs.prodMk (hfresh.prodMk
      (RvCell.measurable_fresh.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))))

/-- The `headStep` branch for an `randvar`, uncurried over the state and arguments. -/
@[simp] def headStep.cRandvar (p : State rT × ℕ × Exp rT) : Measure (Cfg rT) :=
  p.2.2.asValM fun v => Cfg.randvar p.2.1 v p.1

/-- Measurability of the `randvar` branch of `headStep`. -/
theorem headStep.cRandvar.measurable : Measurable (headStep.cRandvar (rT := rT)) := by
  have hg : Measurable fun q : (State rT × ℕ) × Val rT => Cfg.randvar q.1.2 q.2 q.1.1 :=
    Cfg.randvar.measurable.comp
      (f := fun q : (State rT × ℕ) × Val rT => (q.1.2, q.1.1, q.2)) (by fun_prop)
  exact (Exp.asValM.measurable hg).comp
    (f := fun p : State rT × ℕ × Exp rT => (p.2.2, p.1, p.2.1)) (by fun_prop)

/-- `Cfg.test` is measurable in the observation name, the label, the state and the argument. -/
theorem Cfg.test.measurable [ProbLangDist rT] [ProbLangObs rT] :
    Measurable (fun p : (ℕ × Lbl) × State rT × Val rT => Cfg.test p.1.1 p.2.2 p.1.2 p.2.1) := by
  refine measurable_from_prod_countable_right fun kl => ?_
  obtain ⟨k, l⟩ := kl
  show Measurable fun q : State rT × Val rT => Cfg.test k q.2 l q.1
  have hT : Measurable (fun r : (State rT × Val rT) × RvCell rT =>
      RvCell.testCell ProbLangDist.dist k r.1.2 r.2) :=
    (RvCell.measurable_testCell_uncurry k).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have : IsFiniteKernel (Kernel.mk _ hT) :=
    ⟨1, one_lt_top, fun r => by rw [Kernel.coe_mk]; exact prob_le_one⟩
  have hcfg : Measurable (fun s : ((State rT × Val rT) × RvCell rT) × (Int × RvCell rT) =>
      (⟨.lit (.int s.2.1), s.1.1.1.updateRvs (·.insert l s.2.2)⟩ : Cfg rT)) := by
    refine Cfg.measurable_iff.mpr ⟨Exp.lit.measurable.comp (BaseLit.int.measurable.comp
      (measurable_fst.comp measurable_snd)), ?_⟩
    show Measurable (fun s : ((State rT × Val rT) × RvCell rT) × (Int × RvCell rT) =>
      State.mk s.1.1.1.heap s.1.1.1.tapes (s.1.1.1.rvs.insert l s.2.2))
    exact State.measurable_mk_param (by fun_prop) (by fun_prop)
      ((Measurable.locHeap_insert l).comp ((State.measurable_rvs.comp
        (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
          (measurable_snd.comp measurable_snd)))
  have hrw : (fun q : State rT × Val rT => Cfg.test k q.2 l q.1) = fun q =>
      Option.casesOn (motive := fun _ => Measure (Cfg rT)) q.1.rvs[l]? 0 fun c =>
        (RvCell.testCell ProbLangDist.dist k (q, c).1.2 (q, c).2).map fun p =>
          (⟨.lit (.int p.1), (q, c).1.1.updateRvs (·.insert l p.2)⟩ : Cfg rT) := by
    funext q
    simp only [Cfg.test]
    rcases q.1.rvs[l]? with _ | c <;> rfl
  rw [hrw]
  exact Option.measurable_elim_param ((LocHeap.measurable_getElem? l).comp
    (State.measurable_rvs.comp measurable_fst)) measurable_const
    (Measure.measurable_map_uncurry hcfg hT)

/-- The `headStep` branch for a `test`, uncurried over the state and arguments. -/
@[simp] def headStep.cTest [ProbLangDist rT] [ProbLangObs rT] (p : State rT × ℕ × Exp rT × Exp rT) :
    Measure (Cfg rT) :=
  ((Exp.litExtract p.2.2.1).bind BaseLit.lblExtract).unwrapM fun l =>
    p.2.2.2.asValM fun a => Cfg.test p.2.1 a l p.1

/-- Measurability of the `test` branch of `headStep`. -/
theorem headStep.cTest.measurable [ProbLangDist rT] [ProbLangObs rT] :
    Measurable (headStep.cTest (rT := rT)) := by
  have hg : Measurable fun r : ((State rT × ℕ × Exp rT × Exp rT) × Lbl) × Val rT =>
      Cfg.test r.1.1.2.1 r.2 r.1.2 r.1.1.1 :=
    Cfg.test.measurable.comp (f := fun r : ((State rT × ℕ × Exp rT × Exp rT) × Lbl) × Val rT =>
        ((r.1.1.2.1, r.1.2), r.1.1.1, r.2)) (by fun_prop)
  have he : Measurable (fun p : State rT × ℕ × Exp rT × Exp rT =>
      (Exp.litExtract p.2.2.1).bind BaseLit.lblExtract) := by
    refine Option.measurable_bind_param
      (f := fun p : State rT × ℕ × Exp rT × Exp rT => Exp.litExtract p.2.2.1)
      (some_branch := fun q : (State rT × ℕ × Exp rT × Exp rT) × BaseLit rT =>
        BaseLit.lblExtract q.2) ?_ ?_
    · exact Exp.litExtract.measurable.comp (measurable_fst.comp (measurable_snd.comp
        measurable_snd))
    · exact BaseLit.lblExtract.measurable.comp measurable_snd
  unfold headStep.cTest
  apply Option.unwrapM.measurable_param he (g := fun q :
    (State rT × ℕ × Exp rT × Exp rT) × Lbl =>
      q.1.2.2.2.asValM (fun a => Cfg.test q.1.2.1 a q.2 q.1.1))
  exact (Exp.asValM.measurable hg).comp
    ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
      measurable_id)

/-- The `headStep` branch for a `fst`, uncurried over the state and arguments. -/
@[simp] def headStep.cFst (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .pair e1 e2 => e1.isValM (e2.isValM (dirac ⟨e1, p.1⟩))
  | _ => 0

/-- Measurability of the `fst` branch of `headStep`. -/
theorem headStep.cFst.measurable :
    Measurable (headStep.cFst (rT := rT)) := by
  let c_pair_inner : State rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.1.isValM (q.2.2.isValM (dirac ⟨q.2.1, q.1⟩))
  have hrw : headStep.cFst = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun e1 e2 => c_pair_inner (q.2, e1, e2))
            (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)) ∘
        (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.cFst _ = _
    unfold headStep.cFst
    cases e <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  have h_pair_inner : Measurable c_pair_inner := by
    refine Exp.isValM.measurable_param (he := fun q : State rT × Exp rT × Exp rT => q.2.1)
      (hm := fun q : State rT × Exp rT × Exp rT =>
        (q.2.2.isValM (dirac ⟨q.2.1, q.1⟩) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_fst.comp measurable_snd
    · refine Exp.isValM.measurable_param (he := fun q : State rT × Exp rT × Exp rT => q.2.2)
        (hm := fun q : State rT × Exp rT × Exp rT =>
          (dirac (Cfg.mk q.2.1 q.1) : Measure (Cfg rT)))
        ?_ ?_
      · exact measurable_snd.comp measurable_snd
      · exact Cfg.measurable_dirac_mk (measurable_fst.comp measurable_snd) measurable_fst
  exp_zero_pair_apply c_pair_inner, h_pair_inner

/-- The `headStep` branch for a `snd`, uncurried over the state and arguments. -/
@[simp] def headStep.cSnd (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .pair e1 e2 => e1.isValM (e2.isValM (dirac ⟨e2, p.1⟩))
  | _ => 0

/-- Measurability of the `snd` branch of `headStep`. -/
theorem headStep.cSnd.measurable :
    Measurable (headStep.cSnd (rT := rT)) := by
  let c_pair_inner : State rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.1.isValM (q.2.2.isValM (dirac ⟨q.2.2, q.1⟩))
  have hrw : headStep.cSnd = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun e1 e2 => c_pair_inner (q.2, e1, e2))
            (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)) ∘
        (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.cSnd _ = _
    unfold headStep.cSnd
    cases e <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  have h_pair_inner : Measurable c_pair_inner := by
    refine Exp.isValM.measurable_param (he := fun q : State rT × Exp rT × Exp rT => q.2.1)
      (hm := fun q : State rT × Exp rT × Exp rT =>
        (q.2.2.isValM (dirac ⟨q.2.2, q.1⟩) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_fst.comp measurable_snd
    · refine Exp.isValM.measurable_param (he := fun q : State rT × Exp rT × Exp rT => q.2.2)
        (hm := fun q : State rT × Exp rT × Exp rT =>
          (dirac (Cfg.mk q.2.2 q.1) : Measure (Cfg rT)))
        ?_ ?_
      · exact measurable_snd.comp measurable_snd
      · exact Cfg.measurable_dirac_mk (measurable_snd.comp measurable_snd) measurable_fst
  exp_zero_pair_apply c_pair_inner, h_pair_inner

section

variable [LawfulProbLangℝ rT]

/-- The `headStep` branch for a unary operation, uncurried over the state and arguments. -/
@[simp] def headStep.cUnop (p : State rT × UnOp × Exp rT) : Measure (Cfg rT) :=
  p.2.2.isValM ((p.2.1.eval p.2.2).unwrapM (fun e' => dirac ⟨e', p.1⟩))

/-- Measurability of the `unop` branch of `headStep`. -/
theorem headStep.cUnop.measurable : Measurable (headStep.cUnop (rT := rT)) := by
  have hoe : Measurable (fun p : State rT × UnOp × Exp rT => p.2.1.eval p.2.2) :=
    Exp.UnOp_eval.measurable.comp measurable_snd
  have hdir : Measurable (fun q : (State rT × UnOp × Exp rT) × Exp rT =>
        (dirac (Cfg.mk q.2 q.1.1) : Measure (Cfg rT))) :=
    Cfg.measurable_dirac_mk measurable_snd (measurable_fst.comp measurable_fst)
  have hu : Measurable (fun p : State rT × UnOp × Exp rT =>
      (p.2.1.eval p.2.2).unwrapM (fun e' => (dirac (Cfg.mk e' p.1) : Measure (Cfg rT)))) :=
    Option.unwrapM.measurable_param hoe hdir
  exact Exp.isValM.measurable_param (measurable_snd.comp measurable_snd) hu

/-- The `headStep` branch for a `scrut`, uncurried over the state and arguments. -/
@[simp] def headStep.cScrut (p : State rT × Exp rT × Pat rT) : Measure (Cfg rT) :=
  p.2.1.isValM (match Pat.tryMatch p.2.2 p.2.1 with
      | some b => dirac ⟨.inl b, p.1⟩
      | none => dirac ⟨.inr (.lit .unit), p.1⟩)

/-- Measurability of the `scrut` branch of `headStep`. -/
theorem headStep.cScrut.measurable : Measurable (headStep.cScrut (rT := rT)) := by
  have hrw : headStep.cScrut = fun p : State rT × Exp rT × Pat rT =>
        p.2.1.isValM
          (Option.casesOn (motive := fun _ => Measure (Cfg rT)) (Pat.tryMatch p.2.2 p.2.1)
            (dirac (⟨.inr (.lit .unit), p.1⟩ : Cfg rT))
            (fun b => dirac (⟨.inl b, p.1⟩ : Cfg rT))) := by
    funext p
    unfold headStep.cScrut
    cases hp : Pat.tryMatch p.2.2 p.2.1 <;> rfl
  rw [hrw]
  apply Exp.isValM.measurable_param
  · exact measurable_fst.comp measurable_snd
  · refine Option.measurable_elim_param
      (f := fun p : State rT × Exp rT × Pat rT => Pat.tryMatch p.2.2 p.2.1)
      (default := fun p : State rT × Exp rT × Pat rT =>
        dirac (⟨.inr (.lit .unit), p.1⟩ : Cfg rT))
      (some_branch := fun s : (State rT × Exp rT × Pat rT) × Exp rT =>
        dirac (⟨.inl s.2, s.1.1⟩ : Cfg rT)) ?_ ?_ ?_
    · have : (fun p : State rT × Exp rT × Pat rT => Pat.tryMatch p.2.2 p.2.1) =
          (Function.uncurry (fun (p : Pat rT) (e : Exp rT) => Pat.tryMatch p e)) ∘
            (fun p : State rT × Exp rT × Pat rT => (p.2.2, p.2.1)) := by
        funext _; rfl
      rw [this]
      exact Exp.tryMatch.measurable_joint.comp
        ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
    · refine Cfg.measurable_dirac_mk measurable_const measurable_fst
    · refine Cfg.measurable_dirac_mk (Exp.inl.measurable.comp measurable_snd)
        (measurable_fst.comp measurable_fst)

/-- The `headStep` branch for a binary operation, uncurried over the state and arguments. -/
@[simp] def headStep.cBinop (p : State rT × BinOp × Exp rT × Exp rT) : Measure (Cfg rT) :=
  p.2.2.1.isValM (p.2.2.2.isValM ((p.2.1.eval p.2.2.1 p.2.2.2).unwrapM (fun e' => dirac ⟨e', p.1⟩)))

/-- Measurability of the `binop` branch of `headStep`. -/
theorem headStep.cBinop.measurable : Measurable (headStep.cBinop (rT := rT)) := by
  have hoe : Measurable
      (fun p : State rT × BinOp × Exp rT × Exp rT => p.2.1.eval p.2.2.1 p.2.2.2) :=
    Exp.BinOp_eval.measurable.comp measurable_snd
  have hdir : Measurable (fun q : (State rT × BinOp × Exp rT × Exp rT) × Exp rT =>
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

variable [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]

/-- `headStep` is measurable as a map into measures. -/
@[fun_prop]
theorem headStep.measurable :
    Measurable (headStep : Cfg rT → Measure (Cfg rT)) := by
  suffices hjoint : Measurable (fun p : Exp rT × State rT => headStep (Cfg.mk p.1 p.2)) by
    have hrw : (headStep : Cfg rT → Measure (Cfg rT)) =
        (fun p : Exp rT × State rT => headStep (Cfg.mk p.1 p.2)) ∘
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
  have hheq : (fun p : Exp rT × State rT => headStep (Cfg.mk p.1 p.2)) =
      fun p : Exp rT × State rT => Exp.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun n => c_bvar (p.2, n)) (fun x => c_fvar (p.2, x))
          (fun l => c_lit (p.2, l))
          (fun e => c_lam (p.2, e)) (fun e => c_fix (p.2, e))
          (fun e1 e2 => headStep.cApp (p.2, e1, e2))
          (fun u e => headStep.cUnop (p.2, u, e))
          (fun b e1 e2 => headStep.cBinop (p.2, b, e1, e2))
          (fun ec et ef => headStep.cCond (p.2, ec, et, ef))
          (fun e1 e2 => c_pair (p.2, e1, e2))
          (fun e => headStep.cFst (p.2, e)) (fun e => headStep.cSnd (p.2, e))
          (fun e => c_inl (p.2, e)) (fun e => c_inr (p.2, e))
          (fun ec el er => headStep.cCase (p.2, ec, el, er))
          (fun e => headStep.cAlloc (p.2, e)) (fun e => headStep.cLoad (p.2, e))
          (fun e1 e2 => headStep.cStore (p.2, e1, e2))
          (fun n e => headStep.cTape (p.2, n, e))
          (c_fail p.2)
          (fun e => headStep.cFFI (p.2, e))
          (fun n e et => headStep.cSample (p.2, n, e, et))
          (fun e pat => headStep.cScrut (p.2, e, pat))
          (fun en ev => headStep.cAllocN (p.2, en, ev))
          (fun n e => headStep.cRandvar (p.2, n, e))
          (fun k ec ea => headStep.cTest (p.2, k, ec, ea)) := by
    funext ⟨e, σ⟩
    cases e with
    | bvar | fvar | lit | lam | fix | fail | ffi | tape | randvar => rfl
    | sample n e et =>
      cases et <;> try
        solve
        | simp only [headStep, headStep.cSample, headStep.cSampleTapeLeaf]
          unfold Exp.asValM
          split <;> rfl
      case lit l =>
        cases l <;> simp only [headStep, headStep.cSample, headStep.cSampleTapeLeaf] <;>
          unfold Exp.asValM <;> split <;> rfl
    | test k ec ea =>
      cases ec <;> try rfl
      case lit l => cases l <;> rfl
    | app e1 e2 => cases e1 <;> rfl
    | unop op e => rfl
    | binop op e1 e2 => rfl
    | cond ec et ef =>
      cases ec <;> try rfl
      case lit l =>
        cases l <;> try rfl
        case bool b => cases b <;> rfl
    | pair _ _ => rfl
    | fst e => cases e <;> rfl
    | snd e => cases e <;> rfl
    | inl _ => rfl
    | inr _ => rfl
    | case ec el er => cases ec <;> rfl
    | alloc _ => rfl
    | allocN en ev =>
      cases en <;> try rfl
      case lit l => cases l <;> rfl
    | load e =>
      cases e <;> try rfl
      case lit l => cases l <;> rfl
    | store e1 e2 =>
      cases e1 <;> try rfl
      case lit l => cases l <;> rfl
    | scrut _ _ => rfl
  rw [hheq]
  apply Exp.measurable_casesOn_param (c_bvar := c_bvar) (c_fvar := c_fvar) (c_lit := c_lit)
    (c_lam := c_lam) (c_fix := c_fix)
    (c_app := headStep.cApp) (c_unop := headStep.cUnop) (c_binop := headStep.cBinop)
    (c_cond := headStep.cCond) (c_pair := c_pair)
    (c_fst := headStep.cFst) (c_snd := headStep.cSnd)
    (c_inl := c_inl) (c_inr := c_inr) (c_case := headStep.cCase)
    (c_alloc := headStep.cAlloc) (c_load := headStep.cLoad) (c_store := headStep.cStore)
    (c_tape := headStep.cTape) (c_fail := c_fail) (c_ffi := headStep.cFFI)
    (c_sample := headStep.cSample)
    (c_scrut := headStep.cScrut) (c_allocN := headStep.cAllocN) (c_randvar := headStep.cRandvar)
    (c_test := headStep.cTest)
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact headStep.cApp.measurable
  · exact headStep.cUnop.measurable
  · exact headStep.cBinop.measurable
  · exact headStep.cCond.measurable
  · exact measurable_const
  · exact headStep.cFst.measurable
  · exact headStep.cSnd.measurable
  · exact measurable_const
  · exact measurable_const
  · exact headStep.cCase.measurable
  · exact headStep.cAlloc.measurable
  · exact headStep.cLoad.measurable
  · exact headStep.cStore.measurable
  · exact headStep.cTape.measurable
  · exact measurable_const
  · exact headStep.cFFI.measurable
  · exact headStep.cSample.measurable
  · exact headStep.cScrut.measurable
  · exact headStep.cAllocN.measurable
  · exact headStep.cRandvar.measurable
  · exact headStep.cTest.measurable

/-- `headStep` as a kernel. -/
def headStepKernel : Kernel (Cfg rT) (Cfg rT) where
  measurable' := headStep.measurable
  toFun := headStep

end

/-! ## Support: which configurations a head step can reach -/

/-- Every integer in `[0, z)` is a possible outcome of `Cfg.uniform z σ`. -/
theorem Cfg.uniform_possible {z v : Int} {σ : State rT}
    (Hz : 0 < z) (Hv0 : 0 ≤ v) (Hvz : v < z) :
    Possible (⟨.lit (.int v), σ⟩ : Cfg rT) (Cfg.uniform z σ) := by
  unfold Cfg.uniform Int.isPos
  simp only [Hz, dite_true]
  refine Possible.map (g := fun x : Int => (⟨.lit (.int x), σ⟩ : Cfg rT)) (ρ := v)
    (by measurability) ?_
  rw [possible_iff_pos, Measure.uniformOfFinset_apply, div_pos_iff]
  refine ⟨?_, natCast_ne_top _⟩
  rw [ne_eq, Nat.cast_eq_zero]
  exact Finset.card_ne_zero.mpr ⟨v, by simp [Finset.mem_filter, Finset.mem_Ico, Hv0, Hvz]⟩

variable [LawfulProbLangℝ rT]

/-- A Dirac measure charges a singleton exactly when the points agree. -/
@[simp]
theorem dirac_singleton_pos
    {a b : Cfg rT} :
    0 < (dirac a) {b} ↔ a = b := by
  constructor
  · rw [dirac_apply' a (measurableSet_singleton b), indicator_singleton, Pi.single,
        Function.update]
    split <;> simp; trivial
  · simp_all [dirac_apply_of_mem (mem_singleton _)]

/-- `isValM` charges a set exactly when the expression is a value and `m` charges it. -/
@[simp]
theorem isValM_singleton_pos {e : Exp α} {m : Measure T} {s : Set T} :
    0 < (e.isValM m) s ↔ e.isValue ∧ 0 < m s := by
  simp only [Exp.isValM]
  by_cases He : e.isValue
  · rw [ite_eq_left He]; exact ⟨fun h => ⟨He, h⟩, And.right⟩
  · rw [ite_eq_right He]; exact ⟨fun h => absurd h (by simp), fun ⟨hv, _⟩ => absurd hv He⟩

/-- `unwrapM` charges a set exactly when the option holds a value whose measure does. -/
@[simp]
theorem unwrapM_singleton_pos {α β : Type _} [MeasurableSpace β]
    {f : α → Measure β} {opt : Option α} {s : Set β} :
    0 < (opt.unwrapM f) s ↔ ∃ a, opt = some a ∧ 0 < (f a) s := by
  cases opt <;> simp [Option.unwrapM]

/-- `asValM` charges a set exactly when the expression has a value whose measure does. -/
@[simp]
theorem asValM_singleton_pos {e : Exp α} {f : Val α → Measure T} {s : Set T} :
    0 < (e.asValM f) s ↔ ∃ v, e.toVal? = some v ∧ 0 < (f v) s := by
  unfold Exp.asValM; cases e.toVal? <;> simp

/-- Inversion of positivity of `Cfg.uniform` on a singleton configuration. -/
theorem Cfg.uniform_singleton_pos_inv
    {z : Int} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < Cfg.uniform z σ {ρ}) :
    ρ.state = σ ∧ ((0 < z ∧ ∃ v : Int, ρ.expr = .lit (.int v) ∧ 0 ≤ v ∧ v < z) ∨
        (¬ 0 < z ∧ ρ.expr = .lit (.int (-1)))) := by
  unfold Cfg.uniform Int.isPos at h
  by_cases hpos : 0 < z
  · simp only [hpos, dite_true] at h
    rw [map_apply (by measurability) (measurableSet_singleton ρ),
        Measure.uniformOfFinset_apply,
        div_pos_iff] at h
    obtain ⟨hcard, _⟩ := h
    rw [Nat.cast_ne_zero, Finset.card_ne_zero, Finset.filter_nonempty_iff] at hcard
    obtain ⟨a, ha, hfa⟩ := hcard
    simp only [mem_preimage, mem_singleton_iff] at hfa
    rw [Finset.mem_Ico] at ha
    subst hfa
    exact ⟨rfl, .inl ⟨hpos, a, rfl, ha.1, ha.2⟩⟩
  · simp only [hpos, dite_false] at h
    rw [dirac_singleton_pos] at h
    have ⟨h1, h2⟩ := (Cfg.mk.injEq ..).mp h
    exact ⟨h2.symm, .inr ⟨hpos, h1.symm⟩⟩

/-- Decompose `0 < (dirac a) {b}` into Cfg component equalities, then substitute. -/
macro "cfg_dirac" h:ident : tactic =>
  `(tactic| (
    rw [dirac_singleton_pos] at $h:ident
    have ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp $h:ident))

/-- `Cfg.uniform` has atomic support. -/
theorem isAtomicSupport_uniform (z : Int) (σ : State rT) :
    IsAtomicSupport (Cfg.uniform z σ) := by
  by_cases hz : 0 < z
  · refine isAtomicSupport_of_countable
      ((finite_Ico 0 z).image fun n => (⟨.lit (.int n), σ⟩ : Cfg rT)).countable ?_
    unfold Cfg.uniform
    simp only [Int.isPos, dite_eq_left hz]
    rw [map_apply (by measurability) ((finite_Ico 0 z).image _).measurableSet.compl,
      uniformOfFinset_apply_eq_zero_iff, Finset.coe_Ico]
    exact disjoint_left.mpr fun n hn hn' => hn' ⟨n, hn, rfl⟩
  · have hrw : Cfg.uniform z σ = dirac (⟨.lit (.int (-1)), σ⟩ : Cfg rT) := by
      unfold Cfg.uniform; simp only [Int.isPos, dite_eq_right hz]
    rw [hrw]; exact isAtomicSupport_dirac _

section

variable [ProbLangDist rT] {n : ℕ} {v w : Val rT} {σ : State rT}

/-- A value of positive mass gives an outcome of positive mass of `Cfg.sample`. -/
theorem Cfg.sample_singleton_pos (h : 0 < ProbLangDist.dist n v {w}) :
    0 < Cfg.sample n v σ {⟨.ofVal w, σ⟩} := by
  unfold Cfg.sample
  rw [map_apply (by measurability) (measurableSet_singleton _)]
  exact h.trans_le (measure_mono fun w' hw' => by rw [mem_singleton_iff.mp hw']; rfl)

/-- An outcome of positive mass of `Cfg.sample` is a value of positive mass in the same state. -/
theorem Cfg.sample_singleton_pos_inv {ρ : Cfg rT} (h : 0 < Cfg.sample n v σ {ρ}) :
    ∃ w, ρ = ⟨.ofVal w, σ⟩ ∧ 0 < ProbLangDist.dist n v {w} := by
  unfold Cfg.sample at h
  rw [map_apply (by measurability) (measurableSet_singleton _)] at h
  obtain ⟨w, hw⟩ := nonempty_of_measure_ne_zero h.ne'
  refine ⟨w, (hw : _ = ρ).symm, h.trans_le (measure_mono fun w' (hw' : _ = ρ) => ?_)⟩
  exact Exp.ofVal_injective (Cfg.mk.inj (hw'.trans hw.symm)).1

/-- The reserved integer family is atomic for every argument. -/
theorem isAtomicSupport_sample_unifInt [ProbLangDist.IsIntValued rT] :
    IsAtomicSupport (Cfg.sample unifIntName v σ) := by
  have hS := (countable_range fun z : Int => Val.int (rT := rT) z).image
    fun w : Val rT => (⟨.ofVal w, σ⟩ : Cfg rT)
  refine isAtomicSupport_of_countable hS ?_
  unfold Cfg.sample
  rw [map_apply (by measurability) hS.measurableSet.compl]
  exact measure_mono_null (fun w hw hwS => hw ⟨w, hwS, rfl⟩)
    (ProbLangDist.IsIntValued.dist_compl_range_int v)

section

variable [ProbLangDist.IsUniformInt rT]

/-- The uniform-integer family draws only integer values. -/
instance ProbLangDist.IsUniformInt.isIntValued : ProbLangDist.IsIntValued rT where
  dist_compl_range_int v := by
    have hf : Measurable fun z : Int => Val.int (rT := rT) z := by
      rw [measurable_comap_iff]
      exact Exp.lit.measurable.comp BaseLit.int.measurable
    have hS := countable_range fun z : Int => Val.int (rT := rT) z
    rcases Classical.em (∃ z : Int, v = Val.int z) with ⟨z, rfl⟩ | hother
    · by_cases hz : 0 < z
      · rw [ProbLangDist.IsUniformInt.dist_pos z hz, map_apply hf hS.measurableSet.compl]
        simp
      · rw [ProbLangDist.IsUniformInt.dist_nonpos z (le_of_not_gt hz),
          dirac_apply' _ hS.measurableSet.compl, indicator_of_notMem (by simp)]
    · rw [ProbLangDist.IsUniformInt.dist_other v (not_exists.mp hother)]
      rfl

/-- Each integer in `[0, z)` has positive mass under the uniform-integer law for `z > 0`. -/
theorem ProbLangDist.dist_unifInt_pos {z q : Int} (hz : 0 < z) (hq0 : 0 ≤ q) (hqz : q < z) :
    0 < ProbLangDist.dist unifIntName (Val.int (rT := rT) z) {Val.int q} := by
  have h := Cfg.uniform_possible (rT := rT) (σ := default) hz hq0 hqz
  rw [← Cfg.sample_unifInt, possible_iff_pos] at h
  obtain ⟨w, hw, hpos⟩ := Cfg.sample_singleton_pos_inv h
  obtain rfl := @Exp.ofVal_injective rT (Val.int q) w (Cfg.mk.inj hw).1
  exact hpos

/-- The sentinel `-1` has positive mass under the uniform-integer law for `z ≤ 0`. -/
theorem ProbLangDist.dist_unifInt_nonpos {z : Int} (hz : ¬0 < z) :
    0 < ProbLangDist.dist unifIntName (Val.int (rT := rT) z) {Val.int (-1)} := by
  rw [ProbLangDist.IsUniformInt.dist_nonpos z (le_of_not_gt hz),
    dirac_apply_of_mem (mem_singleton _)]
  exact one_pos

/-- A value of positive mass under a uniform-integer law lies in `[0, z)`, or is the sentinel. -/
theorem ProbLangDist.dist_unifInt_pos_inv {z : Int}
    (h : 0 < ProbLangDist.dist unifIntName (Val.int z) {w}) :
    (0 < z ∧ ∃ q, w = Val.int q ∧ 0 ≤ q ∧ q < z) ∨ (¬0 < z ∧ w = Val.int (-1)) := by
  have h' := Cfg.sample_singleton_pos (σ := (default : State rT)) h
  rw [Cfg.sample_unifInt] at h'
  obtain ⟨-, ⟨hz, q, hq, hq0, hqz⟩ | ⟨hz, hq⟩⟩ := Cfg.uniform_singleton_pos_inv h'
  · exact .inl ⟨hz, q, @Exp.ofVal_injective rT w (Val.int q) hq, hq0, hqz⟩
  · exact .inr ⟨hz, @Exp.ofVal_injective rT w (Val.int (-1)) hq⟩

end

end

section Test

variable [ProbLangDist rT] [ProbLangObs rT] {k : ℕ} {a : Val rT} {l : Lbl} {σ : State rT}
  {c : RvCell rT}

/-- The mass a test puts on observing `y` is the posterior mass of the fiber of `y`. -/
theorem Cfg.test_apply_testOutcome (h : σ.rvs[l]? = some c) (y : Int) :
    Cfg.test k a l σ {Cfg.testOutcome k a l σ c y} =
      c.post ProbLangDist.dist ((fun x => ProbLangObs.obs k (a, x)) ⁻¹' {y}) := by
  rw [Cfg.test_eq_map h, map_apply Cfg.measurable_testOutcome (measurableSet_singleton _)]
  congr 1
  ext x
  simp only [mem_preimage, mem_singleton_iff]
  exact ⟨fun hx => by simpa using congrArg Cfg.expr hx, fun hx => hx ▸ rfl⟩

/-- Every outcome of positive mass of a test observes a result of positive posterior mass. -/
theorem Cfg.test_support {ρ : Cfg rT} (h : 0 < Cfg.test k a l σ {ρ}) :
    ∃ c y, σ.rvs[l]? = some c ∧
      c.post ProbLangDist.dist ((fun x => ProbLangObs.obs k (a, x)) ⁻¹' {y}) ≠ 0 ∧
      ρ = Cfg.testOutcome k a l σ c y := by
  rcases hc : σ.rvs[l]? with _ | c
  · simp [Cfg.test, hc] at h
  · have h' := h
    rw [Cfg.test_eq_map hc, map_apply Cfg.measurable_testOutcome (measurableSet_singleton _)] at h'
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero h'.ne'
    have hρ : ρ = Cfg.testOutcome k a l σ c (ProbLangObs.obs k (a, x)) := (hx : _ = ρ).symm
    refine ⟨c, _, rfl, ?_, hρ⟩
    rw [← Cfg.test_apply_testOutcome hc, ← hρ]
    exact h.ne'

/-- A test has atomic support. -/
theorem isAtomicSupport_test : IsAtomicSupport (Cfg.test k a l σ) := by
  rcases hc : σ.rvs[l]? with _ | c
  · simp only [Cfg.test, hc]
    exact isAtomicSupport_zero
  · have hS : (range (Cfg.testOutcome k a l σ c)).Countable := countable_range _
    refine isAtomicSupport_of_countable hS ?_
    rw [Cfg.test_eq_map hc, map_apply Cfg.measurable_testOutcome hS.measurableSet.compl]
    convert measure_empty (μ := c.post ProbLangDist.dist)
    ext x
    simp

end Test

variable [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]

/-- One head step of `randvar n v` allocates a fresh random variable. -/
@[simp] theorem headStep_randvar (n : ℕ) (v : Val rT) (σ : State rT) :
    headStep ⟨.randvar n (.ofVal v), σ⟩ = Cfg.randvar n v σ := by
  simp [headStep, Exp.asValM, Exp.toVal?_ofVal]

/-- One head step of `test k l a` tests the random variable at `l`. -/
@[simp] theorem headStep_test (k : ℕ) (l : Lbl) (a : Val rT) (σ : State rT) :
    headStep ⟨.test k (.lit (.lbl l)) (.ofVal a), σ⟩ = Cfg.test k a l σ := by
  simp [headStep, Exp.asValM, Exp.toVal?_ofVal]

/-- The configurations one head step can reach, with the `urand` and `sample` cases covered by
`HeadStepSupport.possible`. -/
inductive HeadStepSupport : Cfg rT → Cfg rT → Prop
  /-- Beta-reduce a lambda applied to a value. -/
  | BetaLamS {e1 e2 e' : Exp rT} {σ : State rT} :
    e2.isValue →
    e' = Exp.open' e1 e2 →
    HeadStepSupport ⟨.app (.lam e1) e2, σ⟩ ⟨e', σ⟩
  /-- Unfold a fixpoint applied to a value. -/
  | BetaFixS {e1 e2 e' : Exp rT} {σ : State rT} :
    e2.isValue →
    e' = Exp.app (Exp.open' e1 (.fix e1)) e2 →
    HeadStepSupport ⟨.app (.fix e1) e2, σ⟩ ⟨e', σ⟩
  /-- Evaluate a unary operation on a value. -/
  | UnOpS {op : UnOp} {e e' : Exp rT} {σ : State rT} :
    e.isValue →
    some e' = op.eval e →
    HeadStepSupport ⟨.unop op e, σ⟩ ⟨e', σ⟩
  /-- Evaluate a binary operation on two values. -/
  | BinOpS {op : BinOp} {e1 e2 e' : Exp rT} {σ : State rT} :
    e1.isValue →
    e2.isValue →
    some e' = op.eval e1 e2 →
    HeadStepSupport ⟨.binop op e1 e2, σ⟩ ⟨e', σ⟩
  /-- Conditional on `true` takes the first branch. -/
  | IfTrueS {et : Exp rT} {σ : State rT} :
    HeadStepSupport ⟨.cond (.lit (.bool true)) et _, σ⟩ ⟨et, σ⟩
  /-- Conditional on `false` takes the second branch. -/
  | IfFalseS {ef : Exp rT} {σ : State rT} :
    HeadStepSupport ⟨.cond (.lit (.bool false)) _ ef, σ⟩ ⟨ef, σ⟩
  /-- First projection of a pair of values. -/
  | FstS {e1 e2 : Exp rT} {σ : State rT} :
    e1.isValue →
    e2.isValue →
    HeadStepSupport ⟨.fst (.pair e1 e2), σ⟩ ⟨e1, σ⟩
  /-- Second projection of a pair of values. -/
  | SndS {e1 e2 : Exp rT} {σ : State rT} :
    e1.isValue →
    e2.isValue →
    HeadStepSupport ⟨.snd (.pair e1 e2), σ⟩ ⟨e2, σ⟩
  /-- Case analysis on a left injection of a value. -/
  | CaseLS {e el er : Exp rT} {σ : State rT} :
    e.isValue →
    HeadStepSupport ⟨.case (.inl e) el er, σ⟩ ⟨el.app e, σ⟩
  /-- Case analysis on a right injection of a value. -/
  | CaseRS {e el er : Exp rT} {σ : State rT} :
    e.isValue →
    HeadStepSupport ⟨.case (.inr e) el er, σ⟩ ⟨er.app e, σ⟩
  /-- Allocate a fresh heap location holding a value. -/
  | AllocS {ed : Exp rT} {vd : Val rT} {ℓ : Loc} {σ σ' : State rT} :
    ed.toVal? = some vd →
    ℓ = σ.heap.fresh →
    σ' = σ.updateHeap (·.insert ℓ vd) →
    HeadStepSupport ⟨.alloc ed, σ⟩ ⟨.lit (.loc ℓ), σ'⟩
  /-- Allocate a positive number of consecutive heap cells. -/
  | AllocNS {ev : Exp rT} {v : Val rT} {n : Int} {ℓ : Loc} {σ σ' : State rT} :
    ev.toVal? = some v →
    0 < n →
    ℓ = σ.heap.fresh →
    σ' = σ.updateHeap (fun h => LocHeap.allocN h v n.toNat) →
    HeadStepSupport ⟨.allocN (.lit (.int n)) ev, σ⟩ ⟨.lit (.loc ℓ), σ'⟩
  /-- Read an allocated heap location. -/
  | LoadS {σ : State rT} {ℓ : Loc} {v : Val rT} {e' : Exp rT} :
    σ.heap[ℓ]? = some v →
    e' = Exp.ofVal v →
    HeadStepSupport ⟨.load (.lit (.loc ℓ)), σ⟩ ⟨e', σ⟩
  /-- Write to an allocated heap location. -/
  | StoreS {e : Exp rT} {v : Val rT} {σ σ' : State rT} {ℓ : Loc} :
    e.toVal? = some v →
    σ.heap[ℓ]?.isSome →
    σ' = σ.updateHeap (·.insert ℓ v) →
    HeadStepSupport ⟨.store (.lit (.loc ℓ)) e, σ⟩ ⟨.lit .unit, σ'⟩
  /-- Allocate a fresh empty tape for a distribution family. -/
  | TapeS {n : ℕ} {e : Exp rT} {v : Val rT} {ℓ : Lbl} {σ σ' : State rT} :
    e.toVal? = some v →
    ℓ = σ.tapes.fresh →
    σ' = σ.updateTapes (·.insert ℓ (.empty n v)) →
    HeadStepSupport ⟨.tape n e, σ⟩ ⟨.lit (.lbl ℓ), σ'⟩
  /-- Draw a value of positive mass from the reserved integer family. -/
  | UnifIntS {e : Exp rT} {v w : Val rT} {σ : State rT} :
    e.toVal? = some v →
    0 < ProbLangDist.dist unifIntName v {w} →
    HeadStepSupport ⟨.rand e (.lit .unit), σ⟩ ⟨.ofVal w, σ⟩
  /-- Draw freshly from a nonzero distribution family. -/
  | SampleS {n : ℕ} {e : Exp rT} {v w : Val rT} {σ : State rT} :
    n ≠ unifIntName →
    e.toVal? = some v →
    ProbLangDist.dist n v ≠ 0 →
    HeadStepSupport ⟨.sample n e (.lit .unit), σ⟩ ⟨.ofVal w, σ⟩
  /-- Return and consume a presampled value from a matching tape. -/
  | SampleTapeS {n : ℕ} {e : Exp rT} {v w : Val rT} {α : Lbl}
      {t : Tape rT} {σ σ' : State rT} :
    e.toVal? = some v →
    σ.tapes[α]? = some t →
    t.name = n ∧ t.arg = v →
    t.head? = some w →
    σ' = σ.updateTapes (·.insert α t.shift) →
    HeadStepSupport ⟨.sample n e (.lit (.lbl α)), σ⟩ ⟨.ofVal w, σ'⟩
  /-- A hole in a matching reserved-integer tape draws a value of positive mass and is consumed. -/
  | UnifIntTapeEmptyS {e : Exp rT} {v w : Val rT} {α : Lbl} {t : Tape rT} {σ σ' : State rT} :
    e.toVal? = some v →
    σ.tapes[α]? = some t →
    t.name = unifIntName ∧ t.arg = v →
    t.head? = none →
    0 < ProbLangDist.dist unifIntName v {w} →
    σ' = σ.updateTapes (·.insert α t.shift) →
    HeadStepSupport ⟨.rand e (.lit (.lbl α)), σ⟩ ⟨.ofVal w, σ'⟩
  /-- A mismatching tape is ignored by a reserved-integer draw of positive mass. -/
  | UnifIntTapeOtherS {e : Exp rT} {v w : Val rT} {α : Lbl} {t : Tape rT} {σ : State rT} :
    e.toVal? = some v →
    σ.tapes[α]? = some t →
    ¬(t.name = unifIntName ∧ t.arg = v) →
    0 < ProbLangDist.dist unifIntName v {w} →
    HeadStepSupport ⟨.rand e (.lit (.lbl α)), σ⟩ ⟨.ofVal w, σ⟩
  /-- Draw freshly and consume a hole from a matching tape. -/
  | SampleTapeEmptyS {n : ℕ} {e : Exp rT} {v w : Val rT} {α : Lbl}
      {t : Tape rT} {σ σ' : State rT} :
    n ≠ unifIntName →
    e.toVal? = some v →
    σ.tapes[α]? = some t →
    t.name = n ∧ t.arg = v →
    t.head? = none →
    ProbLangDist.dist n v ≠ 0 →
    σ' = σ.updateTapes (·.insert α t.shift) →
    HeadStepSupport ⟨.sample n e (.lit (.lbl α)), σ⟩ ⟨.ofVal w, σ'⟩
  /-- A mismatching tape is ignored by a fresh draw. -/
  | SampleTapeOtherS {n : ℕ} {e : Exp rT} {v w : Val rT} {α : Lbl}
      {t : Tape rT} {σ : State rT} :
    n ≠ unifIntName →
    e.toVal? = some v →
    σ.tapes[α]? = some t →
    ¬(t.name = n ∧ t.arg = v) →
    ProbLangDist.dist n v ≠ 0 →
    HeadStepSupport ⟨.sample n e (.lit (.lbl α)), σ⟩ ⟨.ofVal w, σ⟩
  /-- Pattern matching a value succeeds with the resulting bindings. -/
  | ScrutSuccessS {e : Exp rT} {p : Pat rT} {bindings : Exp rT} {σ : State rT} :
    e.isValue →
    Pat.tryMatch p e = some bindings →
    HeadStepSupport ⟨.scrut e p, σ⟩ ⟨.inl bindings, σ⟩
  /-- Pattern matching a value fails. -/
  | ScrutFailureS {e : Exp rT} {p : Pat rT} {σ : State rT} :
    e.isValue →
    Pat.tryMatch p e = none →
    HeadStepSupport ⟨.scrut e p, σ⟩ ⟨.inr (.lit .unit), σ⟩
  /-- Take the foreign step on a value. -/
  | FFIS {e : Exp rT} {v : Val rT} {σ : State rT} {r : FFIOutcome rT × LocHeap (Val rT)} :
    e.toVal? = some v →
    ProbLangFFI.ffi (v, σ.heap) = some r →
    HeadStepSupport ⟨.ffi e, σ⟩ ⟨r.1.toExp, σ.updateHeap fun _ => r.2⟩
  /-- Allocate a fresh random variable. -/
  | RandvarS {n : ℕ} {e : Exp rT} {v : Val rT} {l : Lbl} {σ σ' : State rT} :
    e.toVal? = some v →
    l = σ.rvs.fresh →
    σ' = σ.updateRvs (·.insert l (RvCell.fresh n v)) →
    HeadStepSupport ⟨.randvar n e, σ⟩ ⟨.lit (.lbl l), σ'⟩
  /-- Test a random variable, observing a result of positive posterior mass. -/
  | TestS {k : ℕ} {l : Lbl} {e : Exp rT} {a : Val rT} {c : RvCell rT} {y : Int} {σ : State rT} :
    e.toVal? = some a →
    σ.rvs[l]? = some c →
    c.post ProbLangDist.dist ((fun x => ProbLangObs.obs k (a, x)) ⁻¹' {y}) ≠ 0 →
    HeadStepSupport ⟨.test k (.lit (.lbl l)) e, σ⟩
      ⟨.lit (.int y), σ.updateRvs (·.insert l (c.observe k a y))⟩

/-- A configuration with a `HeadStepSupport` successor is head-reducible. -/
theorem HeadStepSupport.ne_zero {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩) :
    headStep ⟨e1, σ1⟩ ≠ 0 := by
  cases h with
  | FFIS hv hr => simp [headStep, Exp.asValM, hv, Cfg.ffi, hr, Option.unwrapM]
  | SampleS _ hv hd =>
    simpa [headStep, Exp.asValM, hv, Cfg.sample_eq_zero_iff] using hd
  | SampleTapeS hv htape hfamily hhead hσ =>
    subst hσ
    simp [headStep, Exp.asValM, hv, htape, hfamily, hhead]
  | SampleTapeEmptyS _ hv htape hfamily hhead hd hσ =>
    subst hσ
    simpa [headStep, Exp.asValM, hv, htape, hfamily, hhead, Cfg.sample_eq_zero_iff]
      using hd
  | SampleTapeOtherS _ hv htape hfamily hd =>
    simpa [headStep, Exp.asValM, hv, htape, hfamily, Cfg.sample_eq_zero_iff] using hd
  | UnifIntS hv hw =>
    rw [headStep_sample hv]
    exact (possible_iff_pos.mpr (Cfg.sample_singleton_pos hw)).ne_zero
  | UnifIntTapeEmptyS hv htape hfamily hhead hw hσ =>
    subst hσ
    rw [headStep_sample_tape_none hv htape hfamily hhead]
    exact (possible_iff_pos.mpr (Cfg.sample_singleton_pos hw)).ne_zero
  | UnifIntTapeOtherS hv htape hfamily hw =>
    rw [headStep_sample_tape_other hv htape hfamily]
    exact (possible_iff_pos.mpr (Cfg.sample_singleton_pos hw)).ne_zero
  | RandvarS hv hl hσ =>
    subst hl hσ
    simp [headStep, Exp.asValM, hv, Cfg.randvar]
  | @TestS k l _ a c y _ hv hc hy =>
    intro h0
    have h1 := Cfg.test_apply_testOutcome (k := k) (a := a) hc y
    simp only [headStep, Exp.asValM, hv] at h0
    rw [h0, Measure.coe_zero, Pi.zero_apply] at h1
    exact hy h1.symm
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
  | AllocNS hvd hn hl hσ =>
    subst hl hσ
    simp [headStep, Exp.asValM, hvd, hn]
  | LoadS hlook he =>
    subst he; simp [headStep, hlook]
  | StoreS hv hsome hσ =>
    subst hσ
    obtain ⟨vold, hvold⟩ := Option.isSome_iff_exists.mp hsome
    simp [headStep, Exp.asValM, hv, hvold]
  | TapeS hv hl hσ =>
    subst hl hσ; simp [headStep, Exp.asValM, hv]
  | ScrutSuccessS hv hmatch =>
    simp [headStep, Exp.isValM, hv, hmatch]
  | ScrutFailureS hv hmatch =>
    simp [headStep, Exp.isValM, hv, hmatch]

/-- Every `HeadStepSupport` successor of a head that is no sampler is a possible outcome of
`headStep`. -/
@[discrete]
theorem HeadStepSupport.possible {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩) (hns : ¬ e1.IsSampler := by problang_side) :
    Possible (⟨e2, σ2⟩ : Cfg rT) (headStep ⟨e1, σ1⟩) := by
  cases h with
  | FFIS hv hr =>
    exact of_dirac_eq (by simp [headStep, Exp.asValM, hv, Cfg.ffi, hr, Option.unwrapM, Cfg.ofFFI])
  | SampleS hn _ _ | SampleTapeEmptyS hn _ _ _ _ _ _
      | SampleTapeOtherS hn _ _ _ _ =>
    exact (hns (Exp.isSampler_sample hn _ _)).elim
  | SampleTapeS hv htape hfamily hhead hσ =>
    subst hσ
    exact of_dirac_eq (by simp [headStep, Exp.asValM, hv, htape, hfamily, hhead])
  | UnifIntS hv hw =>
    rw [headStep_sample hv]
    exact possible_iff_pos.mpr (Cfg.sample_singleton_pos hw)
  | UnifIntTapeEmptyS hv htape hfamily hhead hw hσ =>
    subst hσ
    rw [headStep_sample_tape_none hv htape hfamily hhead]
    exact possible_iff_pos.mpr (Cfg.sample_singleton_pos hw)
  | UnifIntTapeOtherS hv htape hfamily hw =>
    rw [headStep_sample_tape_other hv htape hfamily]
    exact possible_iff_pos.mpr (Cfg.sample_singleton_pos hw)
  | RandvarS hv hl hσ =>
    subst hl hσ; exact of_dirac_eq (by simp [headStep, Exp.asValM, hv, Cfg.randvar])
  | TestS hv hc hy =>
    rw [possible_iff_pos]
    simp only [headStep, Exp.asValM, hv]
    rw [Cfg.test_apply_testOutcome hc]
    exact pos_iff_ne_zero.mpr hy
  | BetaLamS hv he | BetaFixS hv he =>
    subst he; exact of_dirac_eq (by simp [headStep, Exp.isValM, hv])
  | IfTrueS | IfFalseS =>
    exact of_dirac_eq (by simp [headStep])
  | FstS hv1 hv2 | SndS hv1 hv2 =>
    exact of_dirac_eq (by simp [headStep, Exp.isValM, hv1, hv2])
  | CaseLS hv | CaseRS hv =>
    exact of_dirac_eq (by simp [headStep, Exp.isValM, hv])
  | UnOpS hv heval =>
    exact of_dirac_eq (by simp [headStep, Exp.isValM, hv, Option.unwrapM, ← heval])
  | BinOpS hv1 hv2 heval =>
    exact of_dirac_eq (by simp [headStep, Exp.isValM, hv1, hv2, Option.unwrapM, ← heval])
  | AllocS hvd hl hσ =>
    subst hl hσ; exact of_dirac_eq (by simp [headStep, Exp.asValM, hvd])
  | AllocNS hvd hn hl hσ =>
    subst hl hσ
    exact of_dirac_eq (by simp [headStep, Exp.asValM, hvd, hn])
  | LoadS hlook he =>
    subst he; exact of_dirac_eq (by simp [headStep, hlook])
  | StoreS hv hsome hσ =>
    subst hσ
    obtain ⟨vold, hvold⟩ := Option.isSome_iff_exists.mp hsome
    exact of_dirac_eq (by simp [headStep, Exp.asValM, hv, hvold])
  | TapeS hv hl hσ =>
    subst hl hσ; exact of_dirac_eq (by simp [headStep, Exp.asValM, hv])
  | ScrutSuccessS hv hmatch =>
    exact of_dirac_eq (by simp [headStep, Exp.isValM, hv, hmatch])
  | ScrutFailureS hv hmatch =>
    exact of_dirac_eq (by simp [headStep, Exp.isValM, hv, hmatch])

/-- Singleton-mass form of `HeadStepSupport.possible`. -/
@[discrete]
theorem HeadStepSupport.pos
    {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩) (hns : ¬ e1.IsSampler := by problang_side) :
    0 < headStep (⟨e1, σ1⟩ : Cfg rT) {(⟨e2, σ2⟩ : Cfg rT)} :=
  possible_iff_pos.mp (h.possible hns)

section

variable [ProbLangDist.IsUniformInt rT] {e : Exp rT} {z q : Int} {α : Lbl} {t : Tape rT}
  {σ σ' : State rT} (hv : e.toVal? = some (Val.int z))

include hv

/-- A positive uniform-integer draw without a tape reaches each integer in `[0, z)`. -/
theorem HeadStepSupport.rand_pos (hz : 0 < z) (hq0 : 0 ≤ q) (hqz : q < z) :
    HeadStepSupport ⟨.rand e (.lit .unit), σ⟩ ⟨.lit (.int q), σ⟩ :=
  .UnifIntS hv (ProbLangDist.dist_unifInt_pos hz hq0 hqz)

/-- A nonpositive uniform-integer draw without a tape reaches the sentinel. -/
theorem HeadStepSupport.rand_nonpos (hz : ¬0 < z) :
    HeadStepSupport ⟨.rand e (.lit .unit), σ⟩ ⟨.lit (.int (-1)), σ⟩ :=
  .UnifIntS hv (ProbLangDist.dist_unifInt_nonpos hz)

/-- A hole in a matching positive uniform-integer tape reaches each integer in `[0, z)`. -/
theorem HeadStepSupport.rand_tape_empty_pos (hz : 0 < z) (htape : σ.tapes[α]? = some t)
    (hfamily : t.name = unifIntName ∧ t.arg = Val.int z) (hhead : t.head? = none) (hq0 : 0 ≤ q)
    (hqz : q < z) (hσ : σ' = σ.updateTapes (·.insert α t.shift)) :
    HeadStepSupport ⟨.rand e (.lit (.lbl α)), σ⟩ ⟨.lit (.int q), σ'⟩ :=
  .UnifIntTapeEmptyS hv htape hfamily hhead (ProbLangDist.dist_unifInt_pos hz hq0 hqz) hσ

/-- A hole in a matching nonpositive uniform-integer tape reaches the sentinel. -/
theorem HeadStepSupport.rand_tape_empty_nonpos (hz : ¬0 < z) (htape : σ.tapes[α]? = some t)
    (hfamily : t.name = unifIntName ∧ t.arg = Val.int z) (hhead : t.head? = none)
    (hσ : σ' = σ.updateTapes (·.insert α t.shift)) :
    HeadStepSupport ⟨.rand e (.lit (.lbl α)), σ⟩ ⟨.lit (.int (-1)), σ'⟩ :=
  .UnifIntTapeEmptyS hv htape hfamily hhead (ProbLangDist.dist_unifInt_nonpos hz) hσ

/-- A positive uniform-integer draw past a mismatching tape reaches each integer in `[0, z)`. -/
theorem HeadStepSupport.rand_tape_other_pos (hz : 0 < z) (htape : σ.tapes[α]? = some t)
    (hfamily : ¬(t.name = unifIntName ∧ t.arg = Val.int z)) (hq0 : 0 ≤ q) (hqz : q < z) :
    HeadStepSupport ⟨.rand e (.lit (.lbl α)), σ⟩ ⟨.lit (.int q), σ⟩ :=
  .UnifIntTapeOtherS hv htape hfamily (ProbLangDist.dist_unifInt_pos hz hq0 hqz)

/-- A nonpositive uniform-integer draw past a mismatching tape reaches the sentinel. -/
theorem HeadStepSupport.rand_tape_other_nonpos (hz : ¬0 < z) (htape : σ.tapes[α]? = some t)
    (hfamily : ¬(t.name = unifIntName ∧ t.arg = Val.int z)) :
    HeadStepSupport ⟨.rand e (.lit (.lbl α)), σ⟩ ⟨.lit (.int (-1)), σ⟩ :=
  .UnifIntTapeOtherS hv htape hfamily (ProbLangDist.dist_unifInt_nonpos hz)

end

/-- An outcome of positive singleton mass is a `HeadStepSupport` successor. -/
theorem headStep_support_of_pos
    (e1 e2 : Exp rT) (σ1 σ2 : State rT) :
    0 < headStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} → HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩ := by
  head_case
  all_goals try (· simp)
  case cond.true | cond.false =>
    intro h
    cfg_dirac h
    constructor
  case beta.lam.redex =>
    intro h
    cfg_dirac h
    exact .BetaLamS ‹_› rfl
  case beta.fix.redex =>
    intro h
    cfg_dirac h
    exact .BetaFixS ‹_› rfl
  case fst.redex =>
    intro h
    cfg_dirac h
    exact .FstS ‹_› ‹_›
  case snd.redex =>
    intro h
    cfg_dirac h
    exact .SndS ‹_› ‹_›
  case case.left.redex =>
    intro h
    cfg_dirac h
    exact .CaseLS ‹_›
  case case.right.redex =>
    intro h
    cfg_dirac h
    exact .CaseRS ‹_›
  case tape.redex =>
    intro h
    cfg_dirac h
    exact .TapeS ‹_› rfl rfl
  case load.redex =>
    intro h
    cfg_dirac h
    exact .LoadS ‹_› rfl
  case alloc.redex =>
    intro h
    cfg_dirac h
    exact .AllocS ‹_› rfl rfl
  case allocN.redex =>
    intro h
    cfg_dirac h
    exact .AllocNS ‹_› ‹_› rfl rfl
  case store.redex =>
    intro h
    cfg_dirac h
    exact .StoreS ‹_› (by rw [Option.isSome_iff_exists]; exact ⟨_, ‹_›⟩) rfl
  case sample.tape.deterministic =>
    intro h
    cfg_dirac h
    exact .SampleTapeS ‹_› ‹_› ‹_› ‹_› rfl
  case unop.redex =>
    intro h
    rw [unwrapM_singleton_pos] at h
    obtain ⟨r, hr, h⟩ := h; cfg_dirac h; exact .UnOpS ‹_› hr.symm
  case binop.redex =>
    intro h
    rw [unwrapM_singleton_pos] at h
    obtain ⟨r, hr, h⟩ := h; cfg_dirac h; exact .BinOpS ‹_› ‹_› hr.symm
  case scrut_success =>
    intro h
    cfg_dirac h
    exact .ScrutSuccessS ‹_› ‹_›
  case scrut_failure =>
    intro h
    cfg_dirac h
    exact .ScrutFailureS ‹_› ‹_›
  case ffi.redex =>
    intro h
    unfold Cfg.ffi at h
    rw [unwrapM_singleton_pos] at h
    obtain ⟨r, hr, h⟩ := h
    cfg_dirac h
    exact .FFIS ‹_› hr
  case sample.plain.redex =>
    intro h
    rename_i ρ n e ov v hv
    obtain ⟨w, hρ, hw⟩ := Cfg.sample_singleton_pos_inv h
    obtain ⟨rfl, rfl⟩ := Cfg.mk.inj hρ
    by_cases hn : n = unifIntName
    · subst n
      exact .UnifIntS hv hw
    · exact .SampleS hn hv fun h0 => by simp [h0] at hw
  case sample.tape.empty =>
    intro h
    rename_i ρ n e α ov v hv ot t htape hfamily oh hhead
    obtain ⟨w, hρ, hw⟩ := Cfg.sample_singleton_pos_inv h
    obtain ⟨rfl, rfl⟩ := Cfg.mk.inj hρ
    by_cases hn : n = unifIntName
    · subst n
      exact .UnifIntTapeEmptyS hv htape hfamily hhead hw rfl
    · exact .SampleTapeEmptyS hn hv htape hfamily hhead (fun h0 => by simp [h0] at hw) rfl
  case sample.tape.mismatch =>
    intro h
    rename_i ρ n e α ov v hv ot t htape hfamily
    obtain ⟨w, hρ, hw⟩ := Cfg.sample_singleton_pos_inv h
    obtain ⟨rfl, rfl⟩ := Cfg.mk.inj hρ
    by_cases hn : n = unifIntName
    · subst n
      exact .UnifIntTapeOtherS hv htape hfamily hw
    · exact .SampleTapeOtherS hn hv htape hfamily fun h0 => by simp [h0] at hw
  case randvar.redex =>
    intro h
    unfold Cfg.randvar at h
    cfg_dirac h
    exact .RandvarS ‹_› rfl rfl
  case test.redex =>
    intro h
    obtain ⟨c, y, hc, hy, hρ⟩ := Cfg.test_support h
    rw [hρ]
    exact .TestS ‹_› hc hy

/-- Every possible outcome of `headStep` is a `HeadStepSupport` successor. -/
theorem Possible.headStepSupport
    {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : Possible (⟨e2, σ2⟩ : Cfg rT) (headStep ⟨e1, σ1⟩)) :
    HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩ :=
  headStep_support_of_pos e1 e2 σ1 σ2 (possible_iff_pos.mp h)

/-- A head-reducible configuration has some `HeadStepSupport` successor. -/
theorem headStep_exists_support_of_ne_zero [ProbLangDist.IsIntValued rT]
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
  case tape.redex => exact ⟨_, .TapeS ‹_› rfl rfl⟩
  case load.redex => exact ⟨_, .LoadS ‹_› rfl⟩
  case alloc.redex => exact ⟨_, .AllocS ‹_› rfl rfl⟩
  case allocN.redex => exact ⟨_, .AllocNS ‹_› ‹_› rfl rfl⟩
  case store.redex =>
    exact ⟨_, .StoreS ‹_› (by rw [Option.isSome_iff_exists]; exact ⟨_, ‹_›⟩) rfl⟩
  case sample.tape.deterministic =>
    exact ⟨_, .SampleTapeS ‹_› ‹_› ‹_› ‹_› rfl⟩
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
  case ffi.redex =>
    unfold Cfg.ffi Option.unwrapM at h
    beta_reduce at h
    split at h
    · exact ⟨_, .FFIS ‹_› ‹_›⟩
    · exact absurd rfl h
  case sample.plain.redex =>
    rename_i ρ n e ov v hv
    change Cfg.sample n v σ ≠ 0 at h
    by_cases hn : n = unifIntName
    · subst n
      obtain ⟨ρ', hρ'⟩ := isAtomicSupport_sample_unifInt.exists_pos h
      obtain ⟨w, rfl, hw⟩ := Cfg.sample_singleton_pos_inv hρ'
      exact ⟨_, .UnifIntS hv hw⟩
    · have hd : ProbLangDist.dist n v ≠ 0 := mt Cfg.sample_eq_zero_iff.mpr h
      have hu : ProbLangDist.dist n v Set.univ ≠ 0 := fun h0 =>
        hd (measure_univ_eq_zero.mp h0)
      obtain ⟨w, -⟩ := nonempty_of_measure_ne_zero hu
      exact ⟨⟨.ofVal w, σ⟩, .SampleS hn hv hd⟩
  case sample.tape.empty =>
    rename_i ρ n e α ov v hv ot t htape hfamily oh hhead
    let σ' := σ.updateTapes (·.insert α t.shift)
    change Cfg.sample n v σ' ≠ 0 at h
    by_cases hn : n = unifIntName
    · subst n
      obtain ⟨ρ', hρ'⟩ := isAtomicSupport_sample_unifInt.exists_pos h
      obtain ⟨w, rfl, hw⟩ := Cfg.sample_singleton_pos_inv hρ'
      exact ⟨_, .UnifIntTapeEmptyS hv htape hfamily hhead hw rfl⟩
    · have hd : ProbLangDist.dist n v ≠ 0 := mt Cfg.sample_eq_zero_iff.mpr h
      have hu : ProbLangDist.dist n v Set.univ ≠ 0 := fun h0 =>
        hd (measure_univ_eq_zero.mp h0)
      obtain ⟨w, -⟩ := nonempty_of_measure_ne_zero hu
      exact ⟨⟨.ofVal w, σ'⟩, .SampleTapeEmptyS hn hv htape hfamily hhead hd rfl⟩
  case sample.tape.mismatch =>
    rename_i ρ n e α ov v hv ot t htape hfamily
    by_cases hn : n = unifIntName
    · subst n
      obtain ⟨ρ', hρ'⟩ := isAtomicSupport_sample_unifInt.exists_pos h
      obtain ⟨w, rfl, hw⟩ := Cfg.sample_singleton_pos_inv hρ'
      exact ⟨_, .UnifIntTapeOtherS hv htape hfamily hw⟩
    · have hd : ProbLangDist.dist n v ≠ 0 := mt Cfg.sample_eq_zero_iff.mpr h
      have hu : ProbLangDist.dist n v Set.univ ≠ 0 := fun h0 =>
        hd (measure_univ_eq_zero.mp h0)
      obtain ⟨w, -⟩ := nonempty_of_measure_ne_zero hu
      exact ⟨⟨.ofVal w, σ⟩, .SampleTapeOtherS hn hv htape hfamily hd⟩
  case randvar.redex => exact ⟨_, .RandvarS ‹_› rfl rfl⟩
  case test.redex =>
    obtain ⟨c, y, hc, hy⟩ := Cfg.test_exists h
    exact ⟨_, .TestS ‹_› hc hy⟩

/-! ## Pure atomicity of `headStep` -/

/-- `isValM` preserves atomic support. -/
theorem isAtomicSupport_isValM (e : Exp α) {m : Measure T}
    (hm : IsAtomicSupport m) : IsAtomicSupport (e.isValM m) := by
  by_cases hv : e.isValue
  · rw [Exp.isValM_some hv]; exact hm
  · rw [Exp.isValM_none hv]; exact isAtomicSupport_zero

/-- `asValM` preserves atomic support. -/
theorem isAtomicSupport_asValM (e : Exp α)
    {f : Val α → Measure T} (hf : ∀ v, IsAtomicSupport (f v)) :
    IsAtomicSupport (e.asValM f) := by
  unfold Exp.asValM
  split <;> first | exact isAtomicSupport_zero | exact hf _

/-- `unwrapM` preserves atomic support. -/
theorem isAtomicSupport_unwrapM {β : Type _} (o : Option β)
    (f : β → Measure T) (hf : ∀ a, IsAtomicSupport (f a)) :
    IsAtomicSupport (o.unwrapM f) := by
  cases o with
  | none =>
    simpa only [Option.unwrapM] using (isAtomicSupport_zero : IsAtomicSupport (0 : Measure T))
  | some a => simpa only [Option.unwrapM] using hf a

/-- Every head step except a possibly diffuse sample has purely atomic support. -/
theorem headStep_atomic [ProbLangDist.IsIntValued rT] (e : Exp rT) (σ : State rT)
    (hns : ¬ e.IsSampler := by problang_side) :
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
  case cond.true | cond.false => exact isAtomicSupport_dirac _
  case tape => exact isAtomicSupport_asValM _ fun _ => isAtomicSupport_dirac _
  case alloc => exact isAtomicSupport_asValM _ fun _ => isAtomicSupport_dirac _
  case allocN =>
    apply isAtomicSupport_asValM
    intro _
    split <;> first | exact isAtomicSupport_dirac _ | exact isAtomicSupport_zero
  case load =>
    split
    · exact isAtomicSupport_zero
    · exact isAtomicSupport_dirac _
  case store =>
    apply isAtomicSupport_asValM
    intro _
    split
    · exact isAtomicSupport_zero
    · exact isAtomicSupport_dirac _
  case scrut =>
    apply isAtomicSupport_isValM
    split <;> exact isAtomicSupport_dirac _
  case ffi => exact isAtomicSupport_asValM _ fun _ =>
    isAtomicSupport_unwrapM _ _ fun _ => isAtomicSupport_dirac _
  case sample.plain =>
    rename_i ρ n arg σ' heq
    by_cases hn : n = unifIntName
    · subst n
      exact isAtomicSupport_asValM arg fun v => isAtomicSupport_sample_unifInt
    · exact (hns ((Cfg.mk.inj heq).1 ▸ Exp.isSampler_sample hn arg (.lit .unit))).elim
  case sample.tape =>
    rename_i ρ n arg α σ' heq
    by_cases hn : n = unifIntName
    · subst n
      apply isAtomicSupport_asValM
      intro v
      split
      · exact isAtomicSupport_zero
      · split
        · split
          · exact isAtomicSupport_sample_unifInt
          · exact isAtomicSupport_dirac _
        · exact isAtomicSupport_sample_unifInt
    · exact (hns ((Cfg.mk.inj heq).1 ▸ Exp.isSampler_sample hn arg (.lit (.lbl α)))).elim
  case randvar => exact isAtomicSupport_asValM _ fun _ => isAtomicSupport_dirac _
  case test => exact isAtomicSupport_asValM _ fun _ => isAtomicSupport_test
  case default => exact isAtomicSupport_zero

end ProbLang
