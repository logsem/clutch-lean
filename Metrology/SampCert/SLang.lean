import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.LocallyClosed
import Metrology.ProbLang.HeadStep
import Metrology.ProbLang.DetStep
import Metrology.ProbLang.Exec
import Metrology.ProbLang.Metatheory
import SampCert.SLang
import SampCert.Foundations.While
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Distributions.Uniform

noncomputable section

/-## Experiment: Translation validation from SLang to ProbLang. -/
namespace EmbedSLang

open SLang ProbLang Classical MeasureTheory ProbabilityTheory Measure PMF Measurable

class abbrev SLangType (T : Type) := Countable T, MeasurableSpace T, MeasurableSingletonClass T

class ProbLangEmbeddable (T : Type _) where
  as_expr : T → Exp
  as_expr_isVal : ∀ t, IsVal (as_expr t)
  as_expr_lc : ∀ t, Exp.IsLocallyClosed (as_expr t)
  /-- Embedded values are syntactically closed (no free variables).
      All existing instances satisfy this trivially since they encode primitive
      data as `.lit` / `.pair` of literals. Used to discharge freshness premises
      `x ∉ (as_expr t).fv` automatically. -/
  as_expr_fv : ∀ t, (as_expr t).fv = ∅
export ProbLangEmbeddable (as_expr as_expr_isVal as_expr_lc as_expr_fv)

/-- Convenience: any atom is fresh in `as_expr t`. -/
theorem as_expr_not_fv [ProbLangEmbeddable T] (x : Var) (t : T) : x ∉ (as_expr t).fv := by
  rw [as_expr_fv]; simp

/-! ## Discrete measure theory helpers -/

theorem SLang.count_bind_probBind [SLangType T] [SLangType U] {s1 : SLang T} {s2 : T → SLang U} :
    (count <| s2 ·) ∘ₘ (count s1) = count (s1.probBind s2) := by
  refine ext_of_singleton fun u => ?_
  simp [bind_apply .of_discrete of_discrete.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul₀ of_discrete.aemeasurable of_discrete.aemeasurable,
    lintegral_count, probBind]

/-! ## SLang embedding -/

/-- Convert a SLang term into a distribution over ProbLang states. -/
def SLang.spec [SLangType T] [ProbLangEmbeddable T] (s : SLang T) (σ : State) : Measure Cfg :=
  count s |>.map as_expr |>.map (⟨·, σ⟩)

/-- A SLang program is the denotation of a ProbLang program -/
def IsEmbedding [SLangType T] [ProbLangEmbeddable T] (s : SLang T) (e : Exp) : Prop :=
  ∀ (σ : State), limExec ⟨e, σ⟩ = SLang.spec s σ

-- NOTE: Some of these theorems may need additional hypotheses.

-- fillItem version of primStep_fill
-- #check primStep_fill

/-- `∑'` and `⨆` commute for monotone ℕ-indexed ENNReal sequences over any countable type. -/
theorem ENNReal.tsum_iSup_of_monotone' {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {f : ℕ → α → ENNReal} (hf : ∀ a, Monotone (f · a)) :
    ∑' a, ⨆ n, f n a = ⨆ n, ∑' a, f n a := by
  simp_rw [← MeasureTheory.lintegral_count]
  exact MeasureTheory.lintegral_iSup (fun _ => Measurable.of_discrete) (fun _ _ hmn a => hf a hmn)

-- Admitted: ⨆ over monotone ENNReal can merge two indices
-- (⨆ i, f i) * (⨆ j, g j) = ⨆ n, f n * g n  when both monotone
theorem iSup_mul_iSup_of_monotone {f g : ℕ → ENNReal} (hf : Monotone f) (hg : Monotone g) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ n, f n * g n := by
  apply le_antisymm
  · -- LHS = ⨆ i, ⨆ j, f i * g j
    rw [ENNReal.iSup_mul]
    apply iSup_le; intro i
    rw [ENNReal.mul_iSup]
    apply iSup_le; intro j
    -- f i * g j ≤ f (max i j) * g (max i j) ≤ ⨆ n, f n * g n
    apply le_trans (mul_le_mul' (hf (le_max_left i j)) (hg (le_max_right i j)))
    exact le_iSup (fun n => f n * g n) (max i j)
  · -- ⨆ n, f n * g n ≤ (⨆ i, f i) * (⨆ j, g j)
    exact ENNReal.iSup_mul_le

-- Split: n steps of Ki[e] can be bounded by splitting through intermediate configs
theorem execN_fill_item_le (Ki : EctxItem) (n : Nat) {e : Exp} {σ : State} {c : Cfg} :
    execN n (Ki.fillItemCfg ⟨e, σ⟩) {c} ≤
      ∑' a, execN n ⟨Ki.fillItem a.expr, a.state⟩ {c} * execN n ⟨e, σ⟩ {a} := by
  rw [Discrete.execN_fill_item_eq]
  rw [ENNReal.tsum_comm]
  apply ENNReal.tsum_le_tsum; intro a
  -- RHS per a: expand execN n {a} via execExactN_sum, distribute
  rw [mul_comm, execExactN_sum]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum; intro j
  by_cases hj : j < n
  · simp only [hj, ↑reduceIte]
    exact mul_le_mul' le_rfl (execN_mono_singleton (Nat.sub_le n j) _ c)
  · have : n - j = 0 := Nat.sub_eq_zero_of_le (not_lt.mp hj)
    simp [this, hj]

-- Combine: j steps for e to reach a, then i steps for Ki[a] to reach c, takes i+j steps total
theorem execN_fill_item_ge (Ki : EctxItem) (i j : Nat) {e : Exp} {σ : State} {c : Cfg} :
    ∑' a, execN i (Ki.fillItemCfg a) {c} * execN j ⟨e, σ⟩ {a} ≤
      execN (i + j) (Ki.fillItemCfg ⟨e, σ⟩) {c} := by
  rw [Discrete.execN_fill_item_eq]
  -- RHS = ∑' k a, execExactN k ... {a} * execN ((i+j)-k) ... {c}
  -- Bound: restrict to k < j terms, and use (i+j)-k ≥ i for k < j
  rw [ENNReal.tsum_comm]
  apply ENNReal.tsum_le_tsum; intro a
  rw [show execN i (Ki.fillItemCfg a) {c} * execN j ⟨e, σ⟩ {a} =
      execN j ⟨e, σ⟩ {a} * execN i (Ki.fillItemCfg a) {c} from mul_comm _ _]
  -- LHS: execN j {a} * execN i {c}
  -- = (∑' k, if k < j then execExactN k {a} else 0) * execN i {c}   (execExactN_sum)
  rw [execExactN_sum]
  -- LHS: (∑' k, if k < j then execExactN k {a} else 0) * execN i {c}
  -- Distribute: ∑' k, (if k < j then execExactN k {a} else 0) * execN i {c}
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum; intro k
  by_cases hk : k < j
  · simp only [hk, ↑reduceIte]
    exact mul_le_mul' le_rfl (execN_mono_singleton (by omega : i ≤ i + j - k) _ c)
  · simp [hk]

theorem limExec_fill_item (Ki : EctxItem) {e : Exp} {σ : State} :
    limExec ⟨Ki.fillItem e, σ⟩ =
      (limExec ⟨e, σ⟩).bind (fun c => limExec ⟨Ki.fillItem c.expr, c.state⟩) := by
  -- Convert the measure bind to an explicit sum
  refine Measure.ext_of_singleton fun c => ?_
  rw [Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  rw [lintegral_countable']
  unfold limExec
  -- Goal: (⨆ i, execN i ⟨Ki.fillItem e, σ⟩) {c} =
  --   ∑' a, (⨆ i, execN i ⟨Ki.fillItem a.expr, a.state⟩) {c} * (⨆ i, execN i ⟨e, σ⟩) {a}
  simp only [Discrete.iSup_measure_apply]
  -- Goal: ⨆ i, execN i ... {c} = ∑' a, (⨆ i, execN i ... {c}) * (⨆ i, execN i ... {a})
  apply le_antisymm
  · -- ≤: use execN_fill_item_le + monotonicity
    apply iSup_le; intro n
    calc execN n ⟨Ki.fillItem e, σ⟩ {c}
        ≤ ∑' a, execN n ⟨Ki.fillItem a.expr, a.state⟩ {c} * execN n ⟨e, σ⟩ {a} :=
          execN_fill_item_le Ki n
      _ ≤ ∑' a, (⨆ i, execN i ⟨Ki.fillItem a.expr, a.state⟩ {c}) * (⨆ i, execN i ⟨e, σ⟩ {a}) := by
          apply ENNReal.tsum_le_tsum; intro a
          exact mul_le_mul'
            (le_iSup (fun i => (execN i ⟨Ki.fillItem a.expr, a.state⟩) {c}) n)
            (le_iSup (fun i => (execN i ⟨e, σ⟩) {a}) n)
  · -- ≥: combine two ⨆ into one, commute ∑' and ⨆, use execN_fill_item_ge
    have merge : ∀ a, (⨆ i, execN i ⟨Ki.fillItem a.expr, a.state⟩ {c}) *
        (⨆ i, execN i ⟨e, σ⟩ {a}) =
        ⨆ n, execN n ⟨Ki.fillItem a.expr, a.state⟩ {c} * execN n ⟨e, σ⟩ {a} :=
      fun a => iSup_mul_iSup_of_monotone
        (fun i j hij => execN_mono_singleton hij _ c)
        (fun i j hij => execN_mono_singleton hij _ a)
    simp_rw [merge]
    have commute := ENNReal.tsum_iSup_of_monotone
      (f := fun n a => execN n ⟨Ki.fillItem a.expr, a.state⟩ {c} * execN n ⟨e, σ⟩ {a})
      (fun a n m hnm => mul_le_mul' (execN_mono_singleton hnm _ c)
                                     (execN_mono_singleton hnm _ a))
    rw [commute]
    apply iSup_le; intro n
    calc ∑' a, execN n ⟨Ki.fillItem a.expr, a.state⟩ {c} * execN n ⟨e, σ⟩ {a}
        ≤ execN (n + n) ⟨Ki.fillItem e, σ⟩ {c} := execN_fill_item_ge Ki n n
      _ ≤ ⨆ i, execN i ⟨Ki.fillItem e, σ⟩ {c} :=
          le_iSup (fun i => execN i ⟨Ki.fillItem e, σ⟩ {c}) (n + n)

-- Corollary: decompose app through argument evaluation.
-- Follows from limExec_fill_item with Ki = .appR ef.
theorem limExec_app {ef e : Exp} {σ : State} :
    limExec ⟨.app ef e, σ⟩ = (limExec ⟨e, σ⟩).bind (fun c => limExec ⟨.app ef c.expr, c.state⟩) :=
  limExec_fill_item (.appR ef)

theorem limExec_beta {body v : Exp} {σ : State} (hv : IsVal v) :
    limExec ⟨.app (.lam body) v, σ⟩ = limExec ⟨Exp.open' body v, σ⟩ := by
  have hnv : ¬ (Exp.app (.lam body) v).isValue := by intro ⟨h⟩; cases h
  rw [limExec_not_final hnv]
  have hred : ∃ ρ, 0 < headStep ⟨.app (.lam body) v, σ⟩ {ρ} := by
    refine ⟨⟨Exp.open' body v, σ⟩, ?_⟩; simp [headStep, Exp.isValM_some' hv]
  rw [primStep_eq_headStep_discrete hred]
  simp [headStep, Exp.isValM_some' hv, Measure.dirac_bind Measurable.of_discrete]

/-- `execN`-level version of a deterministic head step: `execN (n+1) ρ = execN n ρ'`. -/
theorem execN_detHeadStep {ρ ρ' : Cfg} (hnv : ¬ ρ.expr.isValue)
    (h : DetHeadStep_discrete ρ ρ') (n : Nat) : execN (n+1) ρ = execN n ρ' := by
  rw [execN_succ_not_isValue hnv, primStep_eq_headStep_discrete ⟨ρ', h.pos⟩]
  -- headStep ρ = dirac ρ'
  have hother : ∀ c ≠ ρ', (headStep ρ) {c} = 0 := by
    intro c hc
    have hdisj : Disjoint ({ρ'} : Set Cfg) {c} :=
      Set.disjoint_singleton.mpr (Ne.symm hc)
    have hunion : (headStep ρ) ({ρ'} ∪ {c}) = (headStep ρ) {ρ'} + (headStep ρ) {c} :=
      measure_union hdisj (MeasurableSet.singleton c)
    have hsub : (headStep ρ) ({ρ'} ∪ {c}) ≤ 1 :=
      (measure_mono (Set.subset_univ _)).trans (Discrete.headStep_univ_le_one ρ)
    rw [hunion, h.det] at hsub
    have : 1 + (headStep ρ) {c} ≤ 1 + 0 := by simpa using hsub
    have hfin : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
    exact le_antisymm (ENNReal.le_of_add_le_add_left hfin this) (zero_le)
  have hdirac : headStep ρ = dirac ρ' := by
    refine Measure.ext_of_singleton fun c => ?_
    by_cases hc : c = ρ'
    · subst hc; rw [h.det]; simp
    · rw [hother c hc]; simp [dirac_apply', hc]
  rw [hdirac, Measure.dirac_bind Measurable.of_discrete]

/-- `execN n ρ ≤ limExec ρ`. -/
theorem execN_le_limExec (n : Nat) (ρ : Cfg) : execN n ρ ≤ limExec ρ :=
  le_iSup (fun i => execN i ρ) n

/-- A deterministic step (under any ectx) preserves `limExec`. -/
theorem limExec_detStep {ρ ρ' : Cfg} (h : DetStep_discrete ρ ρ') : limExec ρ = limExec ρ' := by
  have hnv : ¬ ρ.expr.isValue := Discrete.val_stuck (h.det ▸ one_pos)
  rw [limExec_not_final hnv]
  -- primStep ρ = dirac ρ' since primStep ρ {ρ'} = 1 and total mass ≤ 1.
  have hother : ∀ c ≠ ρ', (primStep ρ) {c} = 0 := by
    intro c hc
    have hdisj : Disjoint ({ρ'} : Set Cfg) {c} :=
      Set.disjoint_singleton.mpr (Ne.symm hc)
    have hunion : (primStep ρ) ({ρ'} ∪ {c}) = (primStep ρ) {ρ'} + (primStep ρ) {c} :=
      measure_union hdisj (MeasurableSet.singleton c)
    have hsub : (primStep ρ) ({ρ'} ∪ {c}) ≤ 1 :=
      (measure_mono (Set.subset_univ _)).trans (primStep_univ_le_one ρ)
    rw [hunion, h.det] at hsub
    have : 1 + (primStep ρ) {c} ≤ 1 + 0 := by simpa using hsub
    have hfin : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
    exact le_antisymm (ENNReal.le_of_add_le_add_left hfin this) (zero_le)
  have hdirac : primStep ρ = dirac ρ' := by
    refine Measure.ext_of_singleton fun c => ?_
    by_cases hc : c = ρ'
    · subst hc; rw [h.det]; simp
    · rw [hother c hc]; simp [dirac_apply', hc]
  rw [hdirac, Measure.dirac_bind Measurable.of_discrete]

/-- Generic one-step unfolding for `limExec` at a deterministic head redex. -/
theorem limExec_detHeadStep {ρ ρ' : Cfg} (hnv : ¬ ρ.expr.isValue)
    (h : DetHeadStep_discrete ρ ρ') : limExec ρ = limExec ρ' := by
  rw [limExec_not_final hnv, primStep_eq_headStep_discrete ⟨ρ', h.pos⟩]
  -- `headStep ρ = dirac ρ'`: mass 1 at ρ', total mass ≤ 1 ⇒ rest vanishes.
  have hother : ∀ c ≠ ρ', (headStep ρ) {c} = 0 := by
    intro c hc
    have hdisj : Disjoint ({ρ'} : Set Cfg) {c} :=
      Set.disjoint_singleton.mpr (Ne.symm hc)
    have hunion : (headStep ρ) ({ρ'} ∪ {c}) = (headStep ρ) {ρ'} + (headStep ρ) {c} :=
      measure_union hdisj (MeasurableSet.singleton c)
    have hsub : (headStep ρ) ({ρ'} ∪ {c}) ≤ 1 :=
      (measure_mono (Set.subset_univ _)).trans (Discrete.headStep_univ_le_one ρ)
    rw [hunion, h.det] at hsub
    have : 1 + (headStep ρ) {c} ≤ 1 + 0 := by simpa using hsub
    have hfin : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
    exact le_antisymm (ENNReal.le_of_add_le_add_left hfin this) (zero_le)
  have hdirac : headStep ρ = dirac ρ' := by
    refine Measure.ext_of_singleton fun c => ?_
    by_cases hc : c = ρ'
    · subst hc; rw [h.det]; simp
    · rw [hother c hc]; simp [dirac_apply', hc]
  rw [hdirac, Measure.dirac_bind Measurable.of_discrete]

/-- Generic unfolding of a recursive closure at a value argument.

Given `F = .fix (close (.lam (close body x)) f)` where `body` is LC and free in `f`, `x`,
and a value `u` such that `f ∉ u.fv` and `x ≠ f`, reducing `.app F u` yields
`.app F u  ↪*  subst (subst body x u) f F`. This is the single-iteration unfolding
of any fix-lam-close/close form, and it's the LN-canonical presentation: the caller
supplies the open body (using atoms `f` and `x`) and an LC value, and this lemma
does the two `open_close_subst_lc_gen` commutations implicit in the two beta steps. -/
theorem limExec_app_fix_lam_close {f x : Var}
    {body u : Exp} (hbody : Exp.IsLocallyClosed body)
    (hu : Exp.IsLocallyClosed u) (hu_val : IsVal u) (hfu : f ∉ u.fv)
    {σ : State} :
    let F := .fix (Exp.close (.lam (Exp.close body x)) f)
    limExec ⟨.app F u, σ⟩ =
      limExec ⟨Exp.subst (Exp.subst body x u) f F, σ⟩ := by
  intro F
  -- loop = inner .lam; F = .fix (close loop f).  Both LC:
  have hloop_lc : Exp.IsLocallyClosed (.lam (Exp.close body x)) := by
    refine Exp.IsLocallyClosed.lam (insert x body.fv) _ (fun y hy => ?_)
    have hyx : y ≠ x := fun h => hy (by simp [h])
    rw [Exp.open_close_subst_lc x y body hbody]
    exact Exp.subst_lc hbody (.fvar _)
  have hF_lc : Exp.IsLocallyClosed F := by
    refine Exp.IsLocallyClosed.fix (insert f (Exp.lam (Exp.close body x)).fv) _ (fun g hg => ?_)
    have hgf : g ≠ f := fun h => hg (by simp [h])
    rw [Exp.open_close_subst_lc f g _ hloop_lc]
    exact Exp.subst_lc hloop_lc (.fvar _)
  -- Step A: app-fix.
  have hnv₁ : ¬ (Exp.app F u).isValue := by intro ⟨h⟩; cases h
  have hstep₁ : DetHeadStep_discrete ⟨.app F u, σ⟩
      ⟨.app (Exp.open' (Exp.close (.lam (Exp.close body x)) f) F) u, σ⟩ :=
    DetHeadStep_discrete.app_fix hu_val σ
  rw [limExec_detHeadStep hnv₁ hstep₁]
  -- open' (close loop f) F = subst loop f F (both LC).
  rw [Exp.open_close_subst_lc_gen f (.lam (Exp.close body x)) F hloop_lc hF_lc]
  -- Push subst into .lam.
  show limExec ⟨.app (.lam (Exp.subst (Exp.close body x) f F)) u, σ⟩ = _
  -- Step B: app-lam.
  have hnv₂ : ¬ (Exp.app (.lam (Exp.subst (Exp.close body x) f F)) u).isValue := by
    intro ⟨h⟩; cases h
  have hstep₂ : DetHeadStep_discrete
      ⟨.app (.lam (Exp.subst (Exp.close body x) f F)) u, σ⟩
      ⟨Exp.open' (Exp.subst (Exp.close body x) f F) u, σ⟩ :=
    DetHeadStep_discrete.app_lam hu_val σ
  rw [limExec_detHeadStep hnv₂ hstep₂]
  -- open' (subst (close body x) f F) u
  --   = subst (open' (close body x) u) f F   [since f ∉ u.fv, F LC]
  --   = subst (subst body x u) f F           [by open_close_subst_lc_gen]
  have hu_no_f : Exp.subst u f F = u := Exp.subst_fresh f u F hfu
  rw [show Exp.open' (Exp.subst (Exp.close body x) f F) u =
        Exp.subst (Exp.open' (Exp.close body x) u) f F from by
      rw [Exp.subst_open f F u _ hF_lc, hu_no_f]]
  rw [Exp.open_close_subst_lc_gen x body u hbody hu]

-- Values and literals
def probLangPure [ProbLangEmbeddable T] (t : T) : Exp := as_expr t
def probLangInt (z : Int) : Exp := .lit (.int z)
def probLangBool (b : Bool) : Exp := .lit (.bool b)
def probLangUnit : Exp := .lit .unit

-- Pairs
def probLangPair (e1 e2 : Exp) : Exp := .pair e1 e2
def probLangFst (e : Exp) : Exp := .fst e
def probLangSnd (e : Exp) : Exp := .snd e

-- Arithmetic
def probLangAdd (e1 e2 : Exp) : Exp := .binop .plus e1 e2
def probLangSub (e1 e2 : Exp) : Exp := .binop .minus e1 e2
def probLangMul (e1 e2 : Exp) : Exp := .binop .mult e1 e2
def probLangNegInt (e : Exp) : Exp := .unop .minus e

-- Comparisons and booleans
def probLangLt (e1 e2 : Exp) : Exp := .binop .lt e1 e2
def probLangDiv (e1 e2 : Exp) : Exp := .binop .div e1 e2
def probLangMod (e1 e2 : Exp) : Exp := .binop .mod e1 e2
def probLangEq (e1 e2 : Exp) : Exp := .binop .eq e1 e2
def probLangNot (e : Exp) : Exp := .unop .neg e
def probLangAnd (e1 e2 : Exp) : Exp := .binop .and e1 e2

-- Control flow
def probLangCond (ec et ef : Exp) : Exp := .cond ec et ef
def probLangApp (ef ea : Exp) : Exp := .app ef ea
/-- Build a lambda from an atom-indexed body: user passes `body` using `fvar x`,
    we close over the atom to produce `lam (close body x)`. -/
def probLangLam (x : Var) (body : Exp) : Exp := .lam (Exp.close body x)

theorem probLangPure_isEmbedding [SLangType T] [ProbLangEmbeddable T] {t : T} :
    IsEmbedding (probPure t) (probLangPure t) := by
  refine fun σ => ?_
  rw [probLangPure, limExec_of_isVal (as_expr_isVal t)]
  apply Measure.ext_of_singleton
  intro ⟨e', σ'⟩
  rw [SLang.spec, Measure.map_apply ?M1 ?M2, Measure.map_apply ?M3 ?M4]
  case M1 => exact measurable_id'
  case M2 => apply measurableSet_singleton
  case M3 => exact .of_discrete
  case M4 => exact .preimage trivial (fun _ => id)
  rw [withDensity_apply _ MeasurableSet.of_discrete]
  simp only [dirac_apply, Set.indicator, probPure, Set.mem_singleton_iff, Cfg.mk.injEq,
    Pi.one_apply, Set.preimage, Cfg.mk.injEq]
  by_cases hσ : σ = σ'
  · subst hσ; simp only [and_true]
    by_cases he : as_expr t = e'
    · subst he
      simp only [↓reduceIte, ← lintegral_indicator .of_discrete, lintegral_count,
        Set.indicator, Set.mem_setOf_eq]
      have : ∀ a, (if as_expr a = as_expr t then if a = t then 1 else 0 else (0 : ENNReal)) =
          if a = t then 1 else 0 := by intro a; split_ifs <;> simp_all
      simp_rw [this, tsum_ite_eq]
    · simp [he, ← lintegral_indicator .of_discrete, lintegral_count, Set.indicator, Set.mem_setOf_eq]
      symm; simp only [ENNReal.tsum_eq_zero]
      intro a; split_ifs <;> simp_all
  · simp [hσ]

/-- LN bind: `let x := e1; body` desugars to `app (lam (close body x)) e1`.
    Caller passes the body open at atom `x`; we close it. -/
def probLangBind (x : Var) (e1 body : Exp) : Exp :=
  .app (.lam (Exp.close body x)) e1

/-! ### Free-variable push-through

  Lemmas for showing `y ∉ (probLang... ).fv`. Most cases reduce to showing
  freshness in the underlying sub-expressions; combined with `as_expr_fv`,
  freshness premises become near-automatic.

  Usage: `simp [probLangBind_fv, as_expr_fv, Finset.notMem_union]` etc. -/

theorem probLangBind_fv (x : Var) (e1 body : Exp) :
    (probLangBind x e1 body).fv = e1.fv ∪ (Exp.close body x).fv := by
  unfold probLangBind; simp [Exp.fv, Finset.union_comm]

theorem probLangBind_fresh {y x : Var} {e1 body : Exp}
    (hy_e1 : y ∉ e1.fv) (hy_body : y ∉ body.fv) :
    y ∉ (probLangBind x e1 body).fv := by
  rw [probLangBind_fv, Finset.notMem_union]
  exact ⟨hy_e1, Exp.close_preserve_not_fvar _ hy_body⟩

theorem probLangLam_fv (x : Var) (body : Exp) :
    (probLangLam x body).fv = (Exp.close body x).fv := by
  unfold probLangLam; rfl

theorem probLangLam_fresh {y x : Var} {body : Exp} (hy : y ∉ body.fv) :
    y ∉ (probLangLam x body).fv := by
  rw [probLangLam_fv]; exact Exp.close_preserve_not_fvar _ hy

theorem probLangBind_isEmbedding [SLangType T] [ProbLangEmbeddable T] [SLangType U]
    [ProbLangEmbeddable U] {s1 : SLang T} {s2 : T → SLang U} {e1 body : Exp} {x : Var}
    (hbody : Exp.IsLocallyClosed body)
    (h1 : IsEmbedding s1 e1)
    (h2 : ∀ t, IsEmbedding (s2 t) (Exp.subst body x (as_expr t))) :
    IsEmbedding (probBind s1 s2) (probLangBind x e1 body) := by
  intro σ
  rw [probLangBind, limExec_app, h1 σ]
  unfold SLang.spec
  rw [Measure.bind_map .of_discrete .of_discrete, Measure.bind_map .of_discrete .of_discrete]
  -- Rewrite the kernel: limExec_beta puts us at `open' (close body x) (as_expr t)`,
  -- which equals `subst body x (as_expr t)` by `open_close_subst_lc_gen`.
  conv_lhs =>
    arg 2; ext t; simp only [Function.comp]
    rw [limExec_beta (as_expr_isVal t),
        Exp.open_close_subst_lc_gen x body (as_expr t) hbody (as_expr_lc t),
        h2 t σ]
  unfold SLang.spec
  have fuse : ∀ (μ : Measure U),
      (μ.map as_expr).map (fun e => (⟨e, σ⟩ : Cfg)) =
      (fun u => dirac (⟨as_expr u, σ⟩ : Cfg)) ∘ₘ μ := by
    intro μ
    rw [← Measure.bind_dirac_eq_map _ Measurable.of_discrete,
        Measure.bind_map .of_discrete .of_discrete]; rfl
  simp_rw [fuse]
  rw [← SLang.count_bind_probBind,
      Measure.bind_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]

/-! ## Uniform byte embedding -/

instance : Countable UInt8 := ⟨⟨fun u => u.toNat, fun a b h => by ext; exact h⟩⟩
instance : MeasurableSpace UInt8 := ⊤
instance : MeasurableSingletonClass UInt8 := ⟨fun _ => trivial⟩

instance instProbLangEmbeddableUInt8 : ProbLangEmbeddable UInt8 where
  as_expr u := .lit (.int u.toNat)
  as_expr_isVal _ := .lit
  as_expr_lc _ := .lit _
  as_expr_fv _ := rfl

-- ProbLang expression: rand 255 ()
-- Cfg.uniform 256 σ samples uniformly from Finset.Ico 0 256 = {0,...,255}
-- (matches UInt8's 256-outcome uniform distribution).
def probLangUniformByte : Exp := .rand (.lit (.int 256)) (.lit .unit)

theorem probLangUniformByte_isEmbedding :
    IsEmbedding probUniformByte probLangUniformByte := by
  intro σ
  have hnv : ¬ probLangUniformByte.isValue := by intro ⟨h⟩; cases h
  rw [limExec_not_final hnv]
  have hred : ∃ ρ, 0 < headStep ⟨probLangUniformByte, σ⟩ {ρ} := by
    rw [show probLangUniformByte = Exp.rand (.lit (.int 256)) (.lit .unit) from rfl]
    simp only [headStep]
    exact ⟨_, Discrete.Cfg.uniform_singleton_pos_of_mem (v := 0) (by norm_num) (by norm_num) (by norm_num)⟩
  rw [primStep_eq_headStep_discrete hred]
  show (headStep ⟨probLangUniformByte, σ⟩).bind limExec = _
  have hhead : headStep ⟨probLangUniformByte, σ⟩ = Cfg.uniform 256 σ := by
    simp [probLangUniformByte, headStep]
  rw [hhead]
  -- limExec ∘ₘ Cfg.uniform 256 σ = Cfg.uniform 256 σ
  -- because Cfg.uniform only produces value configs
  have bind_dirac : limExec ∘ₘ Cfg.uniform 256 σ = Cfg.uniform 256 σ := by
    -- Cfg.uniform 256 σ = PMF.toMeasure(...).map (⟨.lit (.int ·), σ⟩)
    -- These are all value configs, so limExec = dirac on each.
    unfold Cfg.uniform Int.isPos
    simp only [show (0 : Int) < 256 from by norm_num, dite_true]
    rw [Measure.bind_map .of_discrete .of_discrete]
    -- Goal: (limExec ∘ f) ∘ₘ μ = μ.map f where f v = ⟨.lit (.int v), σ⟩
    -- Since limExec ⟨.lit (.int v), σ⟩ = dirac ⟨.lit (.int v), σ⟩, we get (dirac ∘ f) ∘ₘ μ = μ.map f
    show (limExec ∘ fun v => (⟨.lit (.int v), σ⟩ : Cfg)) ∘ₘ _ = _
    conv_lhs => arg 2; ext v; rw [Function.comp, limExec_of_isVal (.lit (b := .int v))]
    rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  rw [bind_dirac]
  -- Cfg.uniform 256 σ = SLang.spec probUniformByte σ
  unfold SLang.spec
  apply Measure.ext_of_singleton; intro ⟨e', σ'⟩
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      withDensity_apply _ MeasurableSet.of_discrete]
  simp only [Set.preimage, Set.mem_singleton_iff, Cfg.mk.injEq, Set.mem_setOf_eq]
  by_cases hσ : σ = σ'
  · subst hσ; simp only [and_true]
    -- LHS: Cfg.uniform 256 σ {⟨e', σ⟩}
    -- Unfold Cfg.uniform: PMF.uniformOfFinset(.Ico 0 256).toMeasure.map (⟨.lit (.int ·), σ⟩)
    unfold Cfg.uniform Int.isPos
    simp only [show (0 : Int) < 256 from by norm_num, dite_true]
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    -- LHS: uniformOfFinset(.Ico 0 256).toMeasure {v | ⟨.lit (.int v), σ⟩ = ⟨e', σ⟩}
    --     = uniformOfFinset(.Ico 0 256).toMeasure {v | .lit (.int v) = e'}
    simp only [Set.preimage]
    simp only [Set.mem_singleton_iff, Cfg.mk.injEq, and_true]
    rw [PMF.toMeasure_apply]
    swap; exact MeasurableSet.of_discrete
    conv_rhs => rw [← lintegral_indicator (f := probUniformByte) MeasurableSet.of_discrete, lintegral_count]
    simp only [Set.indicator, Set.mem_setOf_eq, as_expr, SLang.probUniformByte, PMF.uniformOfFinset_apply, Finset.mem_Ico]
    by_cases he : ∃ (v : ℤ), Exp.lit (BaseLit.int v) = e' ∧ 0 ≤ v ∧ v < 256
    · -- e' = .lit (.int v) for some v ∈ [0, 256)
      obtain ⟨v, rfl, hv0, hv256⟩ := he
      simp only [Exp.lit.injEq, BaseLit.int.injEq]
      -- LHS: ∑' x : ℤ, if x = v then ... else 0
      rw [tsum_ite_eq]
      simp only [hv0, hv256, and_self, ↓reduceIte]
      -- RHS: ∑' a : UInt8, if a.toNat = v then 1/256 else 0
      have hu : ∃ (u : UInt8), (↑u.toNat : ℤ) = v :=
        ⟨⟨v.toNat, by omega⟩, by simp; omega⟩
      obtain ⟨u, hu⟩ := hu
      simp_rw [show ∀ a : UInt8, ((↑a.toNat : ℤ) = v) = (a = u) from fun a => by
        rw [← hu]; exact propext ⟨fun h => UInt8.ext (Nat.cast_inj.mp h), fun h => by rw [h]⟩]
      rw [tsum_ite_eq]
      simp [UInt8.size]
    · -- e' doesn't match any valid UInt8 literal
      push Not at he
      -- LHS = 0
      have lhs_zero : ∀ x : ℤ, (if Exp.lit (BaseLit.int x) = e' then
          if 0 ≤ x ∧ x < 256 then (↑(Finset.Ico (0 : ℤ) 256).card)⁻¹ else 0 else 0) =
          (0 : ENNReal) := by
        intro x; split_ifs with h1 h2
        · exact absurd h2.2 (not_lt.mpr (he x h1 h2.1))
        · rfl
        · rfl
      simp_rw [lhs_zero, tsum_zero]
      -- RHS = 0
      symm; simp only [ENNReal.tsum_eq_zero]
      intro a; split_ifs with h
      · have : (↑a.toNat : ℤ) < 256 := by
          have := a.toNat_lt; omega
        exact absurd this (not_lt.mpr (he _ h (Int.natCast_nonneg _)))
      · rfl
  · have : {x : UInt8 | as_expr x = e' ∧ σ = σ'} = ∅ := by ext; simp [hσ]
    simp only [this, Measure.restrict_empty, lintegral_zero_measure]
    unfold Cfg.uniform Int.isPos
    simp [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
          Set.preimage, Cfg.mk.injEq, hσ]

/-! ## While loop embedding -/

/--
  LN translation of `probWhile cond body init`:
    `(rec f x = if condE x then let v := bodyE x; f v else x) initE`

  Atoms `f`, `x`, `v` are passed in as `Var`s; the body is built in terms of
  `fvar f / fvar x / fvar v` and then closed at the appropriate boundaries.

  Both `condE` and `bodyE` are function expressions, applied to the loop
  state `fvar x` inside the body. -/
def probLangWhile (f x v : Var) (condE bodyE initE : Exp) : Exp :=
  -- Inner body: if condE x then let v := bodyE x; f v else x
  let body : Exp :=
    .cond (.app condE (.fvar x))
      (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
      (.fvar x)
  -- Wrap in `fix f. lam x. body`: close body over x then over f.
  .app (.fix (Exp.close (.lam (Exp.close body x)) f)) initE

/-- The expression `probLangWhile` unfolds to after one beta-fix + beta-lam, with
    `u` (intended: `as_expr t`) substituted for the loop variable. The recursive
    call still points at the original closed fixpoint `F`. -/
def probLangWhile_unfolded (v : Var) (condE bodyE F u : Exp) : Exp :=
  .cond (.app condE u)
        (.app (.lam (Exp.close (.app F (.fvar v)) v)) (.app bodyE u))
        u

/-- Concrete double-subst simplification on the `probLangWhile` inner body.

    This is the `subst (subst innerBody x u) f F` computation that the generic
    `limExec_app_fix_lam_close` lemma sets up. It's purely symbolic: no limExec,
    no measure theory — just `Exp.subst` reducing through `.cond / .app / .lam /
    close / fvar`. -/
theorem probLangWhile_subst_reduces
    {f x v : Var} (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    {condE bodyE u F : Exp}
    (hfcondE : f ∉ condE.fv) (hfbodyE : f ∉ bodyE.fv)
    (hxcondE : x ∉ condE.fv) (hxbodyE : x ∉ bodyE.fv)
    (hfu : f ∉ u.fv) (hvu : v ∉ u.fv)
    (hvF : v ∉ F.fv) :
    Exp.subst
      (Exp.subst
        (.cond (.app condE (.fvar x))
          (.app (.lam (Exp.close (.app (.fvar f) (.fvar v)) v)) (.app bodyE (.fvar x)))
          (.fvar x))
        x u)
      f F
    =
    .cond (.app condE u)
          (.app (.lam (Exp.close (.app F (.fvar v)) v)) (.app bodyE u))
          u := by
  -- Outer .cond: subst pushes in; each subexpression reduces independently.
  show Exp.cond _ _ _ = Exp.cond _ _ _
  congr 1
  · -- Cond discriminant: .app condE (.fvar x)
    show Exp.app _ _ = Exp.app _ _
    congr 1
    · -- condE branch: x ∉ condE.fv and f ∉ condE.fv leave condE untouched.
      show Exp.subst (Exp.subst condE x u) f F = condE
      rw [Exp.subst_fresh x condE u hxcondE, Exp.subst_fresh f condE F hfcondE]
    · -- (fvar x → u) then subst f F = u  (since f ∉ u.fv)
      show Exp.subst (Exp.subst (Exp.fvar x) x u) f F = u
      simp only [Exp.subst]
      exact Exp.subst_fresh f u F hfu
  · -- Inner .lam (close (.app (fvar f) (fvar v)) v) ... after subst x u then f F:
    -- subst at x: fvar f ≠ x, fvar v ≠ x, so .app (fvar f) (fvar v) unchanged.
    --   But close is at v, so we're doing subst (closeRec 0 v (.app (fvar f) (fvar v))) x u
    --   = closeRec 0 v (subst (.app (fvar f) (fvar v)) x u)  [subst_closeRec, x ≠ v, v ∉ u.fv]
    --   = closeRec 0 v (.app (fvar f) (fvar v))  [since x ≠ f, x ≠ v]
    -- Then subst at f: push inside close; fvar f → F.
    --   subst (closeRec 0 v (.app (fvar f) (fvar v))) f F
    --   = closeRec 0 v (subst (.app (fvar f) (fvar v)) f F)  [subst_closeRec, f ≠ v, v ∉ F.fv]
    --   = closeRec 0 v (.app F (fvar v))
    show Exp.app _ _ = Exp.app _ _
    congr 1
    · -- the .lam (close (.app (fvar f) (fvar v)) v) under subst x u then subst f F
      show Exp.lam _ = Exp.lam _
      congr 1
      show Exp.subst (Exp.subst (Exp.close _ v) x u) f F = Exp.close _ v
      simp only [Exp.close]
      rw [Exp.subst_closeRec x v u 0 _ hxv hvu]
      rw [Exp.subst_closeRec f v F 0 _ hfv hvF]
      congr 1
      simp [Exp.subst, Ne.symm hfx, hxv, hfv]
    · -- .app bodyE (.fvar x)
      show Exp.app _ _ = Exp.app _ _
      congr 1
      · show Exp.subst (Exp.subst bodyE x u) f F = bodyE
        rw [Exp.subst_fresh x bodyE u hxbodyE, Exp.subst_fresh f bodyE F hfbodyE]
      · show Exp.subst (Exp.subst (Exp.fvar x) x u) f F = u
        simp only [Exp.subst]
        exact Exp.subst_fresh f u F hfu
  · -- "fvar x → u" on the else-branch of the cond
    show Exp.subst (Exp.subst (Exp.fvar x) x u) f F = u
    simp only [Exp.subst]
    exact Exp.subst_fresh f u F hfu

/-- One-iteration unfolding of `probLangWhile` at `as_expr t`.

    Combines the generic `limExec_app_fix_lam_close` with the concrete
    `probLangWhile_subst_reduces` simplification to turn the closed loop
    expression into its opened form with `as_expr t` substituted. -/
theorem limExec_probLangWhile_app [SLangType T] [ProbLangEmbeddable T]
    {f x v : Var} (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    {condE bodyE : Exp}
    (hcondE_lc : Exp.IsLocallyClosed condE) (hbodyE_lc : Exp.IsLocallyClosed bodyE)
    (hfcondE : f ∉ condE.fv) (hfbodyE : f ∉ bodyE.fv)
    (hxcondE : x ∉ condE.fv) (hxbodyE : x ∉ bodyE.fv)
    (hvcondE : v ∉ condE.fv) (hvbodyE : v ∉ bodyE.fv)
    (hfas : ∀ (t : T), f ∉ (as_expr t).fv)
    (_hxas : ∀ (t : T), x ∉ (as_expr t).fv)
    (hvas : ∀ (t : T), v ∉ (as_expr t).fv)
    (t : T) {σ : State} :
    let F : Exp := .fix (Exp.close (.lam (Exp.close
      (.cond (.app condE (.fvar x))
        (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
        (.fvar x)) x)) f)
    limExec ⟨.app F (as_expr t), σ⟩
      = limExec ⟨probLangWhile_unfolded v condE bodyE F (as_expr t), σ⟩ := by
  intro F
  -- innerBody: the open body at atoms f, x, v.
  set innerBody : Exp :=
    .cond (.app condE (.fvar x))
          (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
          (.fvar x) with hinner_def
  -- Local-closure of innerBody.
  have hfv_v : (Exp.app (.fvar f) (.fvar v) : Exp).IsLocallyClosed :=
    .app (.fvar _) (.fvar _)
  have hinner_lc : Exp.IsLocallyClosed innerBody := by
    refine .cond (.app hcondE_lc (.fvar _)) ?_ (.fvar _)
    -- probLangBind v e1 body = .app (.lam (close body v)) e1
    refine .app ?_ (.app hbodyE_lc (.fvar _))
    refine Exp.IsLocallyClosed.lam (insert v (Exp.app (.fvar f) (.fvar v)).fv) _ (fun y hy => ?_)
    have hyv : y ≠ v := fun h => hy (by simp [h])
    rw [Exp.open_close_subst_lc v y _ hfv_v]
    exact Exp.subst_lc hfv_v (.fvar _)
  -- v ∉ innerBody.fv: the probLangBind closes v off, and v ∉ condE.fv ∪ bodyE.fv,
  -- v ≠ f, v ≠ x are direct hypotheses.
  have hv_inner : v ∉ innerBody.fv := by
    show v ∉ _
    simp only [hinner_def, probLangBind, Exp.fv, Finset.mem_union, Finset.mem_singleton,
      not_or]
    refine ⟨⟨⟨hvcondE, fun h => hxv h.symm⟩, ?_, hvbodyE, fun h => hxv h.symm⟩, fun h => hxv h.symm⟩
    -- v ∉ (close (.app (fvar f) (fvar v)) v).fv by close_var_not_fvar.
    exact Exp.close_var_not_fvar_rec v 0 _
  -- v ∉ F.fv via close_preserve_not_fvar.
  have hvF : v ∉ F.fv := by
    -- F = .fix (close (.lam (close innerBody x)) f)
    -- (.fix e).fv = e.fv; (.lam e).fv = e.fv
    show v ∉ Exp.fv _
    have h1 : v ∉ (Exp.close innerBody x).fv :=
      Exp.close_preserve_not_fvar _ hv_inner
    -- .lam has same fv as body
    have h2 : v ∉ (Exp.lam (Exp.close innerBody x)).fv := by
      simp only [Exp.fv]; exact h1
    exact Exp.close_preserve_not_fvar _ h2
  -- Apply generic fix-unfolding.
  rw [limExec_app_fix_lam_close (f := f) (x := x) hinner_lc
        (as_expr_lc t) (as_expr_isVal t) (hfas t)]
  -- Now the double subst simplifies via probLangWhile_subst_reduces.
  have hsubst : Exp.subst (Exp.subst innerBody x (as_expr t)) f F =
      probLangWhile_unfolded v condE bodyE F (as_expr t) := by
    rw [hinner_def]
    simp only [probLangBind, probLangWhile_unfolded]
    exact probLangWhile_subst_reduces hfx hfv hxv
      hfcondE hfbodyE hxcondE hxbodyE (hfas t) (hvas t) hvF
  rw [hsubst]

/-- Recurrence for `limExec ⟨.app F (as_expr t), σ⟩`: mirrors `probWhileFunctional`.

    Uses the value-indexed form `(count (body t)).bind (fun t' => limExec ⟨.app F (as_expr t'), σ⟩)`
    which is better-behaved than `(SLang.spec …).bind …` because every sampled value is
    already in `as_expr`-form (no need for beta-lam reduction pointwise).

    On `cond t = false`, terminates immediately at `as_expr t`.
    On `cond t = true`, binds through one iteration of `body t`, then recurses. -/
theorem limExec_probLangWhile_recurrence [SLangType T] [ProbLangEmbeddable T]
    {cond : T → Bool} {body : T → SLang T}
    {f x v : Var} (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    {condE bodyE : Exp}
    (hcondE_lc : Exp.IsLocallyClosed condE) (hbodyE_lc : Exp.IsLocallyClosed bodyE)
    (hfcondE : f ∉ condE.fv) (hfbodyE : f ∉ bodyE.fv)
    (hxcondE : x ∉ condE.fv) (hxbodyE : x ∉ bodyE.fv)
    (hvcondE : v ∉ condE.fv) (hvbodyE : v ∉ bodyE.fv)
    (hfas : ∀ (t : T), f ∉ (as_expr t).fv)
    (hxas : ∀ (t : T), x ∉ (as_expr t).fv)
    (hvas : ∀ (t : T), v ∉ (as_expr t).fv)
    (hcond : ∀ t σ, limExec ⟨.app condE (as_expr t), σ⟩ = dirac ⟨.lit (.bool (cond t)), σ⟩)
    (hbody : ∀ t, IsEmbedding (body t) (.app bodyE (as_expr t)))
    (t : T) {σ : State} :
    let F : Exp := .fix (Exp.close (.lam (Exp.close
      (.cond (.app condE (.fvar x))
        (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
        (.fvar x)) x)) f)
    limExec ⟨.app F (as_expr t), σ⟩ =
      (if cond t then
        (count (body t)).bind (fun t' => limExec ⟨.app F (as_expr t'), σ⟩)
       else dirac ⟨as_expr t, σ⟩) := by
  intro F
  -- Upfront: LC of innerBody, loopLam, and F (needed twice: in
  -- limExec_app_fix_lam_close's preamble, and again for the beta-lam in the true-branch).
  set innerBody : Exp :=
    .cond (.app condE (.fvar x))
          (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
          (.fvar x) with hinner_def
  have hfv_v : (Exp.app (.fvar f) (.fvar v) : Exp).IsLocallyClosed :=
    .app (.fvar _) (.fvar _)
  have hinner_lc : Exp.IsLocallyClosed innerBody := by
    refine .cond (.app hcondE_lc (.fvar _)) ?_ (.fvar _)
    refine .app ?_ (.app hbodyE_lc (.fvar _))
    refine Exp.IsLocallyClosed.lam (insert v (Exp.app (.fvar f) (.fvar v)).fv) _ (fun y hy => ?_)
    have hyv : y ≠ v := fun h => hy (by simp [h])
    rw [Exp.open_close_subst_lc v y _ hfv_v]
    exact Exp.subst_lc hfv_v (.fvar _)
  have hloopLam_lc : Exp.IsLocallyClosed (.lam (Exp.close innerBody x)) := by
    refine Exp.IsLocallyClosed.lam (insert x innerBody.fv) _ (fun y hy => ?_)
    have hyx : y ≠ x := fun h => hy (by simp [h])
    rw [Exp.open_close_subst_lc x y innerBody hinner_lc]
    exact Exp.subst_lc hinner_lc (.fvar _)
  have hF_lc : Exp.IsLocallyClosed F := by
    refine Exp.IsLocallyClosed.fix (insert f (Exp.lam (Exp.close innerBody x)).fv) _ (fun g hg => ?_)
    have hgf : g ≠ f := fun h => hg (by simp [h])
    rw [Exp.open_close_subst_lc f g _ hloopLam_lc]
    exact Exp.subst_lc hloopLam_lc (.fvar _)
  have hv_inner : v ∉ innerBody.fv := by
    show v ∉ _
    simp only [hinner_def, probLangBind, Exp.fv, Finset.mem_union, Finset.mem_singleton,
      not_or]
    refine ⟨⟨⟨hvcondE, fun h => hxv h.symm⟩, ?_, hvbodyE, fun h => hxv h.symm⟩, fun h => hxv h.symm⟩
    exact Exp.close_var_not_fvar_rec v 0 _
  have hvF : v ∉ F.fv := by
    show v ∉ Exp.fv _
    have h1 : v ∉ (Exp.close innerBody x).fv :=
      Exp.close_preserve_not_fvar _ hv_inner
    have h2 : v ∉ (Exp.lam (Exp.close innerBody x)).fv := by
      simp only [Exp.fv]; exact h1
    exact Exp.close_preserve_not_fvar _ h2
  -- Step 1: use one-iteration unfolding.
  rw [limExec_probLangWhile_app hfx hfv hxv hcondE_lc hbodyE_lc
        hfcondE hfbodyE hxcondE hxbodyE hvcondE hvbodyE hfas hxas hvas t]
  simp only [probLangWhile_unfolded]
  -- Step 2: evaluate the cond discriminant via limExec_fill_item with Ki = .condC.
  rw [show (Exp.cond (Exp.app condE (as_expr t))
              (Exp.app (Exp.lam (Exp.close (Exp.app F (.fvar v)) v)) (Exp.app bodyE (as_expr t)))
              (as_expr t) : Exp)
        = EctxItem.fillItem (.condC _ _) (Exp.app condE (as_expr t)) from rfl,
      limExec_fill_item, hcond t σ, Measure.dirac_bind Measurable.of_discrete]
  simp only [EctxItem.fillItem]
  -- Step 3: split on cond t and apply DetHeadStep_discrete.cond_{true,false}.
  by_cases hct : cond t = true
  · rw [hct]
    simp only [if_true]
    have hnv : ¬ (Exp.cond (.lit (.bool true))
        (Exp.app (.lam (Exp.close (Exp.app F (.fvar v)) v)) (Exp.app bodyE (as_expr t)))
        (as_expr t)).isValue := by intro ⟨h⟩; cases h
    rw [limExec_detHeadStep hnv (DetHeadStep_discrete.cond_true _ _ σ)]
    -- Step 4: evaluate .app bodyE (as_expr t) via limExec_fill_item with Ki = .appR.
    rw [show (Exp.app (.lam (Exp.close (Exp.app F (.fvar v)) v)) (Exp.app bodyE (as_expr t)) : Exp)
          = EctxItem.fillItem (.appR _) (Exp.app bodyE (as_expr t)) from rfl,
        limExec_fill_item]
    simp only [EctxItem.fillItem]
    rw [hbody t σ]
    -- Step 5: unfold SLang.spec as (count (body t)).map as_expr |>.map (⟨·, σ⟩) and push
    -- the bind through both maps.
    unfold SLang.spec
    rw [Measure.bind_map Measurable.of_discrete Measurable.of_discrete]
    rw [Measure.bind_map Measurable.of_discrete Measurable.of_discrete]
    -- Now: (count (body t)).bind (fun t' => limExec ⟨.app (.lam (close (.app F (fvar v)) v)) (as_expr t'), σ⟩)
    -- which should equal: (count (body t)).bind (fun t' => limExec ⟨.app F (as_expr t'), σ⟩)
    congr 1
    funext t'
    -- Goal: limExec ⟨.app (.lam (close (.app F (fvar v)) v)) (as_expr t'), σ⟩
    --     = limExec ⟨.app F (as_expr t'), σ⟩
    simp only [Function.comp]
    rw [limExec_beta (as_expr_isVal t')]
    congr 1
    -- Goal: open' (close (.app F (fvar v)) v) (as_expr t') = .app F (as_expr t')
    rw [Exp.open_close_subst_lc_gen v _ (as_expr t') (.app hF_lc (.fvar _)) (as_expr_lc t')]
    -- subst (.app F (fvar v)) v (as_expr t') = .app (subst F v (as_expr t')) (as_expr t')
    -- subst F v (as_expr t') = F since v ∉ F.fv.
    simp only [Exp.subst]
    rw [Exp.subst_fresh v F (as_expr t') hvF]
    simp
  · have hct' : cond t = false := by
      cases hc : cond t with
      | true => exact absurd hc hct
      | false => rfl
    simp only [hct']
    have hnv : ¬ (Exp.cond (.lit (.bool false))
        (Exp.app (.lam (Exp.close (Exp.app F (.fvar v)) v)) (Exp.app bodyE (as_expr t)))
        (as_expr t)).isValue := by intro ⟨h⟩; cases h
    rw [limExec_detHeadStep hnv (DetHeadStep_discrete.cond_false _ _ σ)]
    exact limExec_of_isVal (as_expr_isVal t)

/-- Forward direction: finite unrollings of `probWhile` are dominated pointwise
    by `limExec` of the closed form. -/
theorem SLang_spec_probWhileCut_le [SLangType T] [ProbLangEmbeddable T]
    {cond : T → Bool} {body : T → SLang T}
    {f x v : Var} (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    {condE bodyE : Exp}
    (hcondE_lc : Exp.IsLocallyClosed condE) (hbodyE_lc : Exp.IsLocallyClosed bodyE)
    (hfcondE : f ∉ condE.fv) (hfbodyE : f ∉ bodyE.fv)
    (hxcondE : x ∉ condE.fv) (hxbodyE : x ∉ bodyE.fv)
    (hvcondE : v ∉ condE.fv) (hvbodyE : v ∉ bodyE.fv)
    (hfas : ∀ (t : T), f ∉ (as_expr t).fv)
    (hxas : ∀ (t : T), x ∉ (as_expr t).fv)
    (hvas : ∀ (t : T), v ∉ (as_expr t).fv)
    (hcond : ∀ t σ, limExec ⟨.app condE (as_expr t), σ⟩ = dirac ⟨.lit (.bool (cond t)), σ⟩)
    (hbody : ∀ t, IsEmbedding (body t) (.app bodyE (as_expr t)))
    (k : Nat) (t : T) (σ : State) :
    let F : Exp := .fix (Exp.close (.lam (Exp.close
      (.cond (.app condE (.fvar x))
        (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
        (.fvar x)) x)) f)
    SLang.spec (probWhileCut cond body k t) σ ≤ limExec ⟨.app F (as_expr t), σ⟩ := by
  intro F
  induction k generalizing t with
  | zero =>
    -- probWhileCut 0 = probZero = (fun _ => 0), so SLang.spec is 0.
    have hzero : (probWhileCut cond body 0 t : SLang T) = (fun _ => 0) := rfl
    show SLang.spec (probWhileCut cond body 0 t) σ ≤ _
    rw [hzero]
    have : SLang.spec (fun _ : T => (0 : ENNReal)) σ = (0 : Measure Cfg) := by
      unfold SLang.spec _root_.count
      simp
    rw [this]
    exact bot_le
  | succ k ih =>
    -- probWhileCut (k+1) = probWhileFunctional body (probWhileCut k).
    show SLang.spec (probWhileFunctional cond body (probWhileCut cond body k) t) σ ≤ _
    rw [limExec_probLangWhile_recurrence hfx hfv hxv hcondE_lc hbodyE_lc
          hfcondE hfbodyE hxcondE hxbodyE hvcondE hvbodyE hfas hxas hvas
          hcond hbody t]
    unfold probWhileFunctional
    by_cases hct : cond t = true
    · rw [hct]; simp only [if_true]
      show SLang.spec (probBind (body t) (probWhileCut cond body k)) σ ≤ _
      -- Rewrite LHS: SLang.spec s = (count s).map as_expr .map (⟨·, σ⟩)
      -- count (body t >>= wh) = (count ∘ wh) ∘ₘ (count (body t))   [SLang.count_bind_probBind]
      unfold SLang.spec
      rw [← SLang.count_bind_probBind]
      -- Now ((count (body t) >>= ...).map as_expr .map (⟨·, σ⟩)).
      -- Push .map into bind twice using Measure.bind_map_comm.
      rw [Measure.bind_map_comm, Measure.bind_map_comm]
      -- Goal: (count (body t)).bind (fun t' => count (probWhileCut cond body k t') |>.map as_expr |>.map (⟨·, σ⟩))
      --       ≤ (count (body t)).bind (fun t' => limExec ⟨.app F (as_expr t'), σ⟩)
      -- This is bind monotonicity in the kernel, applied pointwise via IH.
      exact Measure.bind_mono_right _ _ _ (fun t' => ih t')
    · have hct' : cond t = false := by
        cases hc : cond t with
        | true => exact absurd hc hct
        | false => rfl
      simp only [hct']
      -- LHS: SLang.spec (probPure t) σ = dirac ⟨as_expr t, σ⟩. RHS: dirac ⟨as_expr t, σ⟩.
      refine le_of_eq ?_
      show SLang.spec (SLang.probPure t) σ = _
      unfold SLang.spec
      -- count (probPure t) = dirac t
      have hc_eq : _root_.count (SLang.probPure t) = (dirac t : Measure T) := by
        refine Measure.ext_of_singleton fun u => ?_
        rw [_root_.Discrete.count_singleton]
        unfold SLang.probPure
        rw [dirac_apply' _ (MeasurableSet.singleton u)]
        by_cases hut : u = t
        · subst hut; simp
        · simp only [Set.indicator_apply, Set.mem_singleton_iff,
                     show t ≠ u from fun h => hut h.symm, ↑reduceIte]
          simp [hut]
      simp only [show (false = true) = False from by simp, if_false]
      rw [hc_eq]
      rw [map_dirac' Measurable.of_discrete, map_dirac' Measurable.of_discrete]

/-! ### Backward-direction helpers -/

/-- `SLang.spec` is monotone in its first (function) argument. -/
theorem SLang.spec_mono [SLangType T] [ProbLangEmbeddable T]
    {s s' : SLang T} (h : ∀ t, s t ≤ s' t) (σ : State) :
    SLang.spec s σ ≤ SLang.spec s' σ := by
  unfold SLang.spec
  refine Measure.map_mono (Measure.map_mono ?_ Measurable.of_discrete) Measurable.of_discrete
  -- count s ≤ count s' from withDensity_mono.
  show Measure.count.withDensity s ≤ Measure.count.withDensity s'
  exact MeasureTheory.withDensity_mono (Filter.Eventually.of_forall h)

/-- `SLang.spec` distributes over an iSup of monotone functions, at every singleton. -/
theorem SLang.spec_iSup_of_monotone_apply [SLangType T] [ProbLangEmbeddable T]
    {s : ℕ → SLang T} (hmono : ∀ t, Monotone (s · t)) (σ : State) (c : Cfg) :
    SLang.spec (fun t => ⨆ k, s k t) σ {c} = ⨆ k, SLang.spec (s k) σ {c} := by
  -- Pointwise expand at the singleton.
  have expand : ∀ (sl : SLang T),
      SLang.spec sl σ {c} = ∑' x, sl x * ({c} : Set Cfg).indicator 1 ⟨as_expr x, σ⟩ := by
    intro sl
    unfold SLang.spec
    rw [Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton _),
        Measure.map_apply Measurable.of_discrete (.preimage (MeasurableSet.singleton _)
          Measurable.of_discrete),
        show (_root_.count sl) = Measure.count.withDensity sl from rfl,
        withDensity_apply _ (.preimage (.preimage (MeasurableSet.singleton _)
          Measurable.of_discrete) Measurable.of_discrete),
        ← lintegral_indicator (.preimage (.preimage (MeasurableSet.singleton _)
          Measurable.of_discrete) Measurable.of_discrete), lintegral_count]
    congr 1; funext x
    by_cases hx : (⟨as_expr x, σ⟩ : Cfg) ∈ ({c} : Set Cfg)
    · have hxp : x ∈ (as_expr ⁻¹' ((fun e => (⟨e, σ⟩ : Cfg)) ⁻¹' ({c} : Set Cfg))) :=
        Set.mem_preimage.mpr (Set.mem_preimage.mpr hx)
      rw [Set.indicator_of_mem hxp, Set.indicator_of_mem hx]; simp
    · have hxnp : x ∉ (as_expr ⁻¹' ((fun e => (⟨e, σ⟩ : Cfg)) ⁻¹' ({c} : Set Cfg))) := fun h =>
        hx (Set.mem_preimage.mp (Set.mem_preimage.mp h))
      rw [Set.indicator_of_notMem hxnp, Set.indicator_of_notMem hx]; simp
  rw [expand]
  -- Goal: ∑' x, (⨆ k, s k x) * ind = ⨆ k, SLang.spec (s k) σ {c}.
  -- Pointwise: (⨆ k, s k x) * ind = ⨆ k, s k x * ind.
  have hpw : ∀ x : T, (⨆ k, s k x) * ({c} : Set Cfg).indicator 1 (⟨as_expr x, σ⟩ : Cfg)
      = ⨆ k, s k x * ({c} : Set Cfg).indicator 1 (⟨as_expr x, σ⟩ : Cfg) := by
    intro x; rw [ENNReal.iSup_mul]
  simp_rw [hpw]
  -- Define g : ℕ → T → ENNReal as g k x = s k x * ind
  set g : ℕ → T → ENNReal := fun k x => s k x * ({c} : Set Cfg).indicator 1 (⟨as_expr x, σ⟩ : Cfg)
  show ∑' x, ⨆ k, g k x = _
  rw [ENNReal.tsum_iSup_of_monotone' (f := g) (fun x m n hmn =>
    mul_le_mul' (hmono x hmn) le_rfl)]
  refine iSup_congr (fun k => ?_)
  show ∑' x, g k x = _
  show ∑' x, s k x * _ = SLang.spec (s k) σ {c}
  rw [← expand (s k)]

/-- `SLang.spec` distributes over an iSup of monotone functions. -/
theorem SLang.spec_iSup_of_monotone [SLangType T] [ProbLangEmbeddable T]
    {s : ℕ → SLang T} (hmono : ∀ t, Monotone (s · t)) (σ : State) :
    SLang.spec (fun t => ⨆ k, s k t) σ = ⨆ k, SLang.spec (s k) σ := by
  refine Measure.ext_of_singleton fun c => ?_
  rw [SLang.spec_iSup_of_monotone_apply hmono σ c, Discrete.iSup_measure_apply]

/-- The recurrence at the `SLang.spec` level: mirrors `limExec_probLangWhile_recurrence`.
    `SLang.spec (probWhile t)` is a fixed point of the same operator that `limExec ⟨.app F …⟩`
    satisfies. -/
theorem SLang.spec_probWhile_recurrence [SLangType T] [ProbLangEmbeddable T]
    {cond : T → Bool} {body : T → SLang T} (t : T) (σ : State) :
    SLang.spec (probWhile cond body t) σ =
      if cond t then
        (count (body t)).bind (fun t' => SLang.spec (probWhile cond body t') σ)
      else dirac ⟨as_expr t, σ⟩ := by
  -- LHS: SLang.spec (probWhile t) σ = ⨆ k, SLang.spec (probWhileCut k t) σ.
  have hLHS : SLang.spec (probWhile cond body t) σ
      = ⨆ k, SLang.spec (probWhileCut cond body k t) σ := by
    have hpoint : (probWhile cond body t : SLang T)
        = fun u => ⨆ k, probWhileCut cond body k t u := rfl
    rw [hpoint]
    exact SLang.spec_iSup_of_monotone
      (fun u k m hkm => SLang.probWhileCut_monotonic cond body t u hkm) σ
  rw [hLHS]
  by_cases hct : cond t = true
  · simp only [hct, if_true]
    show ⨆ k, SLang.spec (probWhileCut cond body k t) σ
        = (fun t' => SLang.spec (probWhile cond body t') σ) ∘ₘ _root_.count (body t)
    rw [show ((fun t' => SLang.spec (probWhile cond body t') σ) ∘ₘ _root_.count (body t))
          = (_root_.count (body t)).bind (fun t' => SLang.spec (probWhile cond body t') σ) by
        rfl]
    -- RHS: (count (body t)).bind (fun t' => SLang.spec (probWhile t') σ)
    -- Use SLang.spec_iSup_of_monotone in reverse on t' inside the bind.
    -- Strategy: show ⨆ k+1, SLang.spec (probWhileCut (k+1) t) σ
    --           = (count (body t)).bind (⨆ k, SLang.spec (probWhileCut k t') σ)
    have hRHS : (count (body t)).bind (fun t' => SLang.spec (probWhile cond body t') σ) =
        ⨆ k, SLang.spec (probWhileCut cond body (k+1) t) σ := by
      -- probWhileCut (k+1) t = probWhileFunctional cond body (probWhileCut k) t
      --                     = body t >>= probWhileCut k     (since cond t = true)
      have hUnfold : ∀ k, SLang.spec (probWhileCut cond body (k+1) t) σ =
          SLang.spec (probBind (body t) (probWhileCut cond body k)) σ := by
        intro k
        congr 1
        funext u
        show probWhileCut cond body (k+1) t u = _
        unfold probWhileCut probWhileFunctional
        rw [hct]; simp
      simp_rw [hUnfold]
      -- Each side at k: SLang.spec (probBind (body t) (probWhileCut k)) σ.
      -- Want this = (count (body t)).bind (fun t' => SLang.spec (probWhileCut k t') σ).
      have hbind_spec : ∀ k,
          SLang.spec (probBind (body t) (probWhileCut cond body k)) σ =
          (count (body t)).bind (fun t' => SLang.spec (probWhileCut cond body k t') σ) := by
        intro k
        unfold SLang.spec
        rw [← SLang.count_bind_probBind]
        rw [Measure.bind_map_comm, Measure.bind_map_comm]
      simp_rw [hbind_spec]
      -- Goal: (count (body t)).bind (fun t' => spec (probWhile t') σ)
      --     = ⨆ k, (count (body t)).bind (fun t' => spec (probWhileCut k t') σ)
      symm
      apply Measure.ext_of_singleton
      intro c
      rw [Discrete.iSup_measure_apply]
      simp_rw [Measure.bind_apply (MeasurableSet.singleton c)
        Measurable.of_discrete.aemeasurable]
      -- Pointwise inside the integrals: spec (probWhile t') σ {c} = ⨆ k, spec (probWhileCut k t') σ {c}.
      have h_pw : ∀ t' : T, SLang.spec (probWhile cond body t') σ {c}
          = ⨆ k, SLang.spec (probWhileCut cond body k t') σ {c} := by
        intro t'
        have hpoint : (probWhile cond body t' : SLang T)
            = fun u => ⨆ k, probWhileCut cond body k t' u := rfl
        rw [hpoint]
        exact SLang.spec_iSup_of_monotone_apply
          (fun u k m hkm => SLang.probWhileCut_monotonic cond body t' u hkm) σ c
      simp_rw [h_pw]
      rw [lintegral_iSup
          (fun k => Measurable.of_discrete) (fun m n hmn t' =>
            SLang.spec_mono
              (fun u => SLang.probWhileCut_monotonic cond body t' u hmn) σ {c})]
    rw [hRHS]
    -- Goal: ⨆ k, S(probWhileCut k t) σ = ⨆ k, S(probWhileCut (k+1) t) σ.
    refine le_antisymm ?_ ?_
    · refine iSup_le (fun k => ?_)
      cases k with
      | zero =>
        -- k = 0: probWhileCut 0 = 0, so SLang.spec = 0.
        have : SLang.spec (probWhileCut cond body 0 t) σ = 0 := by
          have hzero : (probWhileCut cond body 0 t : SLang T) = (fun _ => 0) := rfl
          rw [hzero]
          unfold SLang.spec _root_.count
          simp
        rw [this]
        exact bot_le
      | succ k =>
        exact le_iSup (fun k => SLang.spec (probWhileCut cond body (k+1) t) σ) k
    · refine iSup_le (fun k => ?_)
      exact le_iSup (fun k => SLang.spec (probWhileCut cond body k t) σ) (k+1)
  · -- cond t = false case
    have hct' : cond t = false := Bool.eq_false_iff.mpr hct
    simp only [hct', show (false = true) = False from by simp, if_false]
    -- ⨆ k, SLang.spec (probWhileCut k t) σ = dirac ⟨as_expr t, σ⟩
    refine le_antisymm ?_ ?_
    · refine iSup_le (fun k => ?_)
      cases k with
      | zero =>
        have : SLang.spec (probWhileCut cond body 0 t) σ = 0 := by
          have hzero : (probWhileCut cond body 0 t : SLang T) = (fun _ => 0) := rfl
          rw [hzero]
          unfold SLang.spec _root_.count
          simp
        rw [this]
        exact bot_le
      | succ k =>
        have : probWhileCut cond body (k+1) t = SLang.probPure t := by
          unfold probWhileCut probWhileFunctional
          rw [hct']; simp
        rw [this]
        -- SLang.spec (probPure t) σ = dirac ⟨as_expr t, σ⟩
        unfold SLang.spec
        have hc_eq : _root_.count (SLang.probPure t) = (dirac t : Measure T) := by
          refine Measure.ext_of_singleton fun u => ?_
          rw [_root_.Discrete.count_singleton]
          unfold SLang.probPure
          rw [dirac_apply' _ (MeasurableSet.singleton u)]
          by_cases hut : u = t
          · subst hut; simp
          · simp only [Set.indicator_apply, Set.mem_singleton_iff,
                       show t ≠ u from fun h => hut h.symm, ↑reduceIte]
            simp [hut]
        rw [hc_eq, map_dirac' Measurable.of_discrete, map_dirac' Measurable.of_discrete]
    · -- dirac ⟨as_expr t, σ⟩ ≤ ⨆ k, SLang.spec (probWhileCut k t) σ
      refine le_iSup_of_le 1 ?_
      have : probWhileCut cond body 1 t = SLang.probPure t := by
        unfold probWhileCut probWhileFunctional
        rw [hct']; simp
      rw [this]
      -- SLang.spec (probPure t) σ = dirac ⟨as_expr t, σ⟩
      unfold SLang.spec
      have hc_eq : _root_.count (SLang.probPure t) = (dirac t : Measure T) := by
        refine Measure.ext_of_singleton fun u => ?_
        rw [_root_.Discrete.count_singleton]
        unfold SLang.probPure
        rw [dirac_apply' _ (MeasurableSet.singleton u)]
        by_cases hut : u = t
        · subst hut; simp
        · simp only [Set.indicator_apply, Set.mem_singleton_iff,
                     show t ≠ u from fun h => hut h.symm, ↑reduceIte]
          simp [hut]
      rw [hc_eq, map_dirac' Measurable.of_discrete, map_dirac' Measurable.of_discrete]

/-- Top-level embedding of `probWhile`.

    Strategy: combine the forward direction (`SLang_spec_probWhileCut_le`) with a
    backward direction via fuel induction:
    - **Forward (≥)**: `SLang.spec (probWhileCut k init) σ ≤ limExec ⟨.app F (as_expr init), σ⟩`
      for each `k`. Taking iSup_k gives `SLang.spec (probWhile init) ≤ limExec ⟨.app F (as_expr init), σ⟩`.
      Needs: iSup pushes through `(count _).map as_expr .map (⟨·, σ⟩)`.
    - **Backward (≤)**: `execN n ⟨.app F (as_expr init), σ⟩ ≤ SLang.spec (probWhile init) σ`
      pointwise. Taking iSup_n gives `limExec ≤ SLang.spec (probWhile init)`.
      Hard part: relate `n` primSteps to some finite number of `probWhileCut` iterations.

    Current state: forward direction sub-lemma proven; backward direction is the gap. -/
theorem probLangWhile_isEmbedding [SLangType T] [ProbLangEmbeddable T]
    {cond : T → Bool} {body : T → SLang T} {init : T}
    {condE bodyE : Exp} {f x v : Var}
    (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    (hcondE_lc : Exp.IsLocallyClosed condE) (hbodyE_lc : Exp.IsLocallyClosed bodyE)
    (hfcondE : f ∉ condE.fv) (hfbodyE : f ∉ bodyE.fv)
    (hxcondE : x ∉ condE.fv) (hxbodyE : x ∉ bodyE.fv)
    (hvcondE : v ∉ condE.fv) (hvbodyE : v ∉ bodyE.fv)
    (hfas : ∀ (t : T), f ∉ (as_expr t).fv)
    (hxas : ∀ (t : T), x ∉ (as_expr t).fv)
    (hvas : ∀ (t : T), v ∉ (as_expr t).fv)
    (hcond : ∀ t σ, limExec ⟨.app condE (as_expr t), σ⟩ = dirac ⟨.lit (.bool (cond t)), σ⟩)
    (hbody : ∀ t, IsEmbedding (body t) (.app bodyE (as_expr t))) :
    IsEmbedding (probWhile cond body init) (probLangWhile f x v condE bodyE (as_expr init)) := by
  intro σ
  -- Reusable: SLang.spec applied at S, expanded to a tsum.
  have expand : ∀ (s : SLang T) (S : Set Cfg) (_ : MeasurableSet S),
      SLang.spec s σ S =
      ∑' x, s x * (S.indicator 1 ⟨as_expr x, σ⟩) := by
    intro s S hS
    unfold SLang.spec
    rw [Measure.map_apply Measurable.of_discrete hS,
        Measure.map_apply Measurable.of_discrete (.preimage hS Measurable.of_discrete),
        show (_root_.count s) = Measure.count.withDensity s from rfl,
        withDensity_apply _ (.preimage (.preimage hS Measurable.of_discrete)
          Measurable.of_discrete),
        ← lintegral_indicator (.preimage (.preimage hS Measurable.of_discrete)
          Measurable.of_discrete), lintegral_count]
    congr 1; funext x
    by_cases hx : ⟨as_expr x, σ⟩ ∈ S
    · have hxp : x ∈ (as_expr ⁻¹' ((fun e => (⟨e, σ⟩ : Cfg)) ⁻¹' S)) :=
        Set.mem_preimage.mpr (Set.mem_preimage.mpr hx)
      rw [Set.indicator_of_mem hxp, Set.indicator_of_mem hx]; simp
    · have hxnp : x ∉ (as_expr ⁻¹' ((fun e => (⟨e, σ⟩ : Cfg)) ⁻¹' S)) := fun h =>
        hx (Set.mem_preimage.mp (Set.mem_preimage.mp h))
      rw [Set.indicator_of_notMem hxnp, Set.indicator_of_notMem hx]; simp
  -- Set the closed-form fix-lambda once.
  set F : Exp := .fix (Exp.close (.lam (Exp.close
    (.cond (.app condE (.fvar x))
      (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
      (.fvar x)) x)) f) with hF_def
  -- ν(t) := SLang.spec (probWhile cond body t) σ.  Key fact: ν satisfies the loop recurrence.
  set ν : T → Measure Cfg := fun t => SLang.spec (probWhile cond body t) σ with hν_def
  have hν_rec : ∀ t : T, ν t = if cond t then
      (_root_.count (body t)).bind (fun t' => ν t') else dirac ⟨as_expr t, σ⟩ := by
    intro t
    show SLang.spec (probWhile cond body t) σ = _
    exact SLang.spec_probWhile_recurrence t σ
  refine le_antisymm ?_ ?_
  · -- BACKWARD: limExec ⟨.app F (as_expr init), σ⟩ ≤ ν(init).
    -- Strategy: reduce to ∀ n, execN n ⟨.app F (as_expr init), σ⟩ ≤ ν(init), then
    -- prove the stronger ∀ n t, execN n ⟨.app F (as_expr t), σ⟩ ≤ ν(t) by strong induction
    -- on n using the hcond/hbody hypotheses + ν's recurrence.
    suffices hMain : ∀ n c t, execN n ⟨.app F (as_expr t), σ⟩ {c} ≤ ν t {c} by
      -- Take iSup over n. limExec = iSup execN. ν is constant in n.
      have h_sing : ∀ c, limExec ⟨.app F (as_expr init), σ⟩ {c} ≤ ν init {c} := by
        intro c
        rw [Discrete.limExec_apply]
        exact iSup_le (fun n => hMain n c init)
      -- Now extend the singleton bound to all measurable sets.
      -- Use a simpler lemma: if μ {c} ≤ ν {c} for all c on a countable space, then μ ≤ ν.
      have h_lift : ∀ μ₁ μ₂ : Measure Cfg,
          (∀ c, μ₁ {c} ≤ μ₂ {c}) → μ₁ ≤ μ₂ := by
        intros μ₁ μ₂ hsing
        refine Measure.le_iff.mpr (fun S hS => ?_)
        rw [show S = ⋃ c : S, ({c.val} : Set Cfg) from by ext c'; simp]
        rw [measure_iUnion (fun ⟨a, _⟩ ⟨b, _⟩ hab => by
            simp only [Set.disjoint_singleton]; intro h; apply hab; exact Subtype.ext h)
          (fun _ => MeasurableSet.singleton _)]
        rw [measure_iUnion (μ := μ₂) (fun ⟨a, _⟩ ⟨b, _⟩ hab => by
            simp only [Set.disjoint_singleton]; intro h; apply hab; exact Subtype.ext h)
          (fun _ => MeasurableSet.singleton _)]
        exact ENNReal.tsum_le_tsum (fun c => hsing c.val)
      exact h_lift _ _ h_sing
    -- Now: prove ∀ n c t, execN n ⟨.app F (as_expr t), σ⟩ {c} ≤ ν t {c}.
    -- Strong induction on n.
    -- innerBody and the LC proofs follow the same pattern as
    -- limExec_probLangWhile_recurrence.
    set innerBody : Exp :=
      .cond (.app condE (.fvar x))
            (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
            (.fvar x) with hinner_def
    have hfv_v : (Exp.app (.fvar f) (.fvar v) : Exp).IsLocallyClosed :=
      .app (.fvar _) (.fvar _)
    have hinner_lc : Exp.IsLocallyClosed innerBody := by
      refine .cond (.app hcondE_lc (.fvar _)) ?_ (.fvar _)
      refine .app ?_ (.app hbodyE_lc (.fvar _))
      refine Exp.IsLocallyClosed.lam (insert v (Exp.app (.fvar f) (.fvar v)).fv) _ (fun y hy => ?_)
      rw [Exp.open_close_subst_lc v y _ hfv_v]
      exact Exp.subst_lc hfv_v (.fvar _)
    have hloopLam_lc : Exp.IsLocallyClosed (.lam (Exp.close innerBody x)) := by
      refine Exp.IsLocallyClosed.lam (insert x innerBody.fv) _ (fun y hy => ?_)
      rw [Exp.open_close_subst_lc x y innerBody hinner_lc]
      exact Exp.subst_lc hinner_lc (.fvar _)
    have hF_lc : Exp.IsLocallyClosed F := by
      rw [hF_def]
      refine Exp.IsLocallyClosed.fix (insert f (Exp.lam (Exp.close innerBody x)).fv) _
        (fun g hg => ?_)
      rw [Exp.open_close_subst_lc f g _ hloopLam_lc]
      exact Exp.subst_lc hloopLam_lc (.fvar _)
    -- Useful hypothesis-like facts for the proof.
    have hvF : v ∉ F.fv := by
      have hv_inner : v ∉ innerBody.fv := by
        show v ∉ _
        simp only [hinner_def, probLangBind, Exp.fv, Finset.mem_union, Finset.mem_singleton,
          not_or]
        refine ⟨⟨⟨hvcondE, fun h => hxv h.symm⟩, ?_, hvbodyE, fun h => hxv h.symm⟩, fun h => hxv h.symm⟩
        exact Exp.close_var_not_fvar_rec v 0 _
      show v ∉ Exp.fv _
      have h1 : v ∉ (Exp.close innerBody x).fv :=
        Exp.close_preserve_not_fvar _ hv_inner
      have h2 : v ∉ (Exp.lam (Exp.close innerBody x)).fv := by
        simp only [Exp.fv]; exact h1
      exact Exp.close_preserve_not_fvar _ h2
    -- The "loopLam after F-substitution" expression — the inner lambda after the fix
    -- step has been resolved.  This is the body of `app F (as_expr t)`'s first reduct.
    set loopLamSubF : Exp := Exp.subst (.lam (Exp.close innerBody x)) f F with hloopLamSubF_def
    have hloopLamSubF_eq : loopLamSubF = .lam (Exp.subst (Exp.close innerBody x) f F) := by
      simp [hloopLamSubF_def, Exp.subst]
    -- The final unfolded expression after both fix and lam betas.
    set unfolded : T → Exp := fun t' =>
      .cond (.app condE (as_expr t'))
            (.app (.lam (Exp.close (.app F (.fvar v)) v)) (.app bodyE (as_expr t')))
            (as_expr t') with hunfolded_def
    -- After 2 det primSteps (app-fix then app-lam), `app F (as_expr t)` reaches `unfolded t`.
    have hstep1 : ∀ t' : T, DetHeadStep_discrete ⟨.app F (as_expr t'), σ⟩
        ⟨.app loopLamSubF (as_expr t'), σ⟩ := by
      intro t'
      have hF_unfold : F = .fix (Exp.close (.lam (Exp.close innerBody x)) f) := hF_def
      have h := DetHeadStep_discrete.app_fix (as_expr_isVal t') σ
        (body := Exp.close (.lam (Exp.close innerBody x)) f)
      have heq : Exp.open' (Exp.close (.lam (Exp.close innerBody x)) f)
            (.fix (Exp.close (.lam (Exp.close innerBody x)) f))
          = loopLamSubF := by
        rw [← hF_unfold]
        exact Exp.open_close_subst_lc_gen f (.lam (Exp.close innerBody x)) F hloopLam_lc hF_lc
      rw [heq, ← hF_unfold] at h
      exact h
    have hstep2 : ∀ t' : T, DetHeadStep_discrete ⟨.app loopLamSubF (as_expr t'), σ⟩
        ⟨unfolded t', σ⟩ := by
      intro t'
      rw [hloopLamSubF_eq]
      have h := DetHeadStep_discrete.app_lam (as_expr_isVal t') σ (body := Exp.subst (Exp.close innerBody x) f F)
      -- h gives ⟨open' (subst ...) (as_expr t'), σ⟩ as the next step.
      -- Need open' (subst (close innerBody x) f F) (as_expr t') = unfolded t'.
      have hopen_subst : Exp.open' (Exp.subst (Exp.close innerBody x) f F) (as_expr t')
          = Exp.subst (Exp.subst innerBody x (as_expr t')) f F := by
        rw [show Exp.open' (Exp.subst (Exp.close innerBody x) f F) (as_expr t')
              = Exp.subst (Exp.open' (Exp.close innerBody x) (as_expr t')) f F by
            rw [Exp.subst_open f F (as_expr t') _ hF_lc,
                Exp.subst_fresh f (as_expr t') F (hfas t')]]
        rw [Exp.open_close_subst_lc_gen x innerBody (as_expr t') hinner_lc (as_expr_lc t')]
      have hsubst_eq : Exp.subst (Exp.subst innerBody x (as_expr t')) f F = unfolded t' := by
        rw [hinner_def]
        simp only [unfolded, probLangBind]
        exact probLangWhile_subst_reduces hfx hfv hxv
          hfcondE hfbodyE hxcondE hxbodyE (hfas t') (hvas t') hvF
      rw [hopen_subst, hsubst_eq] at h
      exact h
    -- Non-value witness for `app F u` and `app loopLamSubF u`.
    have hnv1 : ∀ t' : T, ¬ (Exp.app F (as_expr t')).isValue := fun _ ⟨h⟩ => by cases h
    have hnv2 : ∀ t' : T, ¬ (Exp.app loopLamSubF (as_expr t')).isValue := fun _ ⟨h⟩ => by cases h
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro c t
      -- Cases on n: 0, 1, ≥ 2.
      match hn : n with
      | 0 => simp [execN]
      | 1 =>
        -- execN 1 of non-value: (primStep _).bind (execN 0) = bind to zero = 0.
        rw [execN_succ_not_isValue (hnv1 t) 0]
        rw [Measure.bind_apply (MeasurableSet.singleton _)
          Measurable.of_discrete.aemeasurable]
        simp [execN]
      | (m + 2) =>
        -- After 2 det steps, reach unfolded form.
        rw [execN_detHeadStep (hnv1 t) (hstep1 t) (m+1)]
        rw [execN_detHeadStep (hnv2 t) (hstep2 t) m]
        -- Now bound execN m ⟨unfolded t, σ⟩ {c} ≤ ν t {c}.
        -- unfolded t = .cond (.app condE (as_expr t)) BODY (as_expr t)
        --            = (EctxItem.condC BODY (as_expr t)).fillItem (.app condE (as_expr t))
        set BODY : Exp :=
          .app (.lam (Exp.close (.app F (.fvar v)) v)) (.app bodyE (as_expr t)) with hBODY_def
        have hunfolded_eq : unfolded t = (EctxItem.condC BODY (as_expr t)).fillItem
            (.app condE (as_expr t)) := by
          simp [unfolded, EctxItem.fillItem, BODY]
        rw [hunfolded_eq]
        -- Apply execN_fill_item_le with Ki = .condC BODY (as_expr t).
        refine (execN_fill_item_le (.condC BODY (as_expr t)) m).trans ?_
        -- Now: ∑' a, execN m ⟨cond a.expr BODY (as_expr t), a.state⟩ {c} * execN m ⟨app condE (as_expr t), σ⟩ {a}
        -- Bound execN m ⟨app condE (as_expr t), σ⟩ {a} ≤ limExec ⟨app condE (as_expr t), σ⟩ {a} = dirac ⟨lit (bool (cond t)), σ⟩ {a}.
        have h_cond_bound : ∀ a, execN m ⟨.app condE (as_expr t), σ⟩ {a}
            ≤ (Measure.dirac (⟨.lit (.bool (cond t)), σ⟩ : Cfg)) {a} := by
          intro a
          calc execN m ⟨.app condE (as_expr t), σ⟩ {a}
              ≤ limExec ⟨.app condE (as_expr t), σ⟩ {a} := execN_le_limExec _ _ _
            _ = (Measure.dirac (⟨.lit (.bool (cond t)), σ⟩ : Cfg)) {a} := by rw [hcond t σ]
        have hsum_bound :
            ∑' a, execN m ⟨EctxItem.fillItem (.condC BODY (as_expr t)) a.expr, a.state⟩ {c}
              * execN m ⟨.app condE (as_expr t), σ⟩ {a}
            ≤ ∑' a, execN m ⟨EctxItem.fillItem (.condC BODY (as_expr t)) a.expr, a.state⟩ {c}
              * (Measure.dirac (⟨.lit (.bool (cond t)), σ⟩ : Cfg)) {a} := by
          refine ENNReal.tsum_le_tsum (fun a => mul_le_mul' le_rfl (h_cond_bound a))
        refine hsum_bound.trans ?_
        -- The dirac collapses the tsum to a single term.
        rw [show (∑' (a : Cfg), execN m ⟨EctxItem.fillItem (.condC BODY (as_expr t)) a.expr, a.state⟩ {c}
              * (Measure.dirac (⟨.lit (.bool (cond t)), σ⟩ : Cfg)) {a})
          = execN m ⟨EctxItem.fillItem (.condC BODY (as_expr t)) (.lit (.bool (cond t))), σ⟩ {c} by
          rw [show (fun a : Cfg =>
              execN m ⟨EctxItem.fillItem (.condC BODY (as_expr t)) a.expr, a.state⟩ {c}
              * (Measure.dirac (⟨.lit (.bool (cond t)), σ⟩ : Cfg)) {a})
            = (fun a : Cfg => if a = ⟨.lit (.bool (cond t)), σ⟩
                then execN m ⟨EctxItem.fillItem (.condC BODY (as_expr t)) a.expr, a.state⟩ {c}
                else 0) by
            funext a
            rw [Measure.dirac_apply' _ (MeasurableSet.singleton _)]
            simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
            by_cases ha : a = (⟨.lit (.bool (cond t)), σ⟩ : Cfg)
            · simp [ha]
            · have hne : ¬ (⟨.lit (.bool (cond t)), σ⟩ : Cfg) = a := fun h => ha h.symm
              simp [ha, hne]]
          rw [tsum_ite_eq]]
        -- Now: execN m ⟨cond (lit (bool (cond t))) BODY (as_expr t), σ⟩ {c} ≤ ν t {c}.
        -- One det step: cond_true / cond_false picks branch.
        by_cases hct : cond t = true
        · rw [hct]
          rw [hν_rec t]
          simp only [hct, if_true]
          -- ν t = (count (body t)).bind (fun t' => ν t')
          show execN m ⟨.cond (.lit (.bool true)) BODY (as_expr t), σ⟩ {c} ≤ _
          have hnv : ¬ (Exp.cond (.lit (.bool true)) BODY (as_expr t)).isValue := by
            intro ⟨h⟩; cases h
          cases m with
          | zero => simp [execN]
          | succ k =>
            rw [execN_detHeadStep hnv (DetHeadStep_discrete.cond_true _ _ _) k]
            -- Goal: execN k ⟨BODY, σ⟩ {c} ≤ (count (body t)).bind (fun t' => ν t') {c}
            -- BODY = app (lam (close (app F (fvar v)) v)) (app bodyE (as_expr t))
            -- Use execN_fill_item_le with Ki = .appR (lam ...).
            set lamApp : Exp := .lam (Exp.close (.app F (.fvar v)) v) with hlamApp_def
            have hBODY_eq : BODY = (EctxItem.appR lamApp).fillItem (.app bodyE (as_expr t)) := by
              simp [BODY, EctxItem.fillItem, lamApp]
            rw [hBODY_eq]
            refine (execN_fill_item_le (.appR lamApp) k).trans ?_
            -- ∑' a, execN k ⟨app lamApp a.expr, a.state⟩ {c} * execN k ⟨app bodyE (as_expr t), σ⟩ {a}
            -- Bound execN k ⟨app bodyE (as_expr t), σ⟩ {a} ≤ limExec ... {a} = SLang.spec (body t) σ {a}.
            have h_body_bound : ∀ a, execN k ⟨.app bodyE (as_expr t), σ⟩ {a}
                ≤ SLang.spec (body t) σ {a} := by
              intro a
              calc execN k ⟨.app bodyE (as_expr t), σ⟩ {a}
                  ≤ limExec ⟨.app bodyE (as_expr t), σ⟩ {a} := execN_le_limExec _ _ _
                _ = SLang.spec (body t) σ {a} := by rw [hbody t σ]
            have hsum_bound2 : ∑' a,
                execN k ⟨EctxItem.fillItem (.appR lamApp) a.expr, a.state⟩ {c}
                  * execN k ⟨.app bodyE (as_expr t), σ⟩ {a}
                ≤ ∑' a, execN k ⟨EctxItem.fillItem (.appR lamApp) a.expr, a.state⟩ {c}
                  * SLang.spec (body t) σ {a} := by
              exact ENNReal.tsum_le_tsum (fun a => mul_le_mul' le_rfl (h_body_bound a))
            refine hsum_bound2.trans ?_
            -- SLang.spec (body t) σ {a} = body t (something) ... only nonzero when a = ⟨as_expr t', σ⟩.
            -- count (body t) = withDensity body. (count (body t)).bind ν {c} = ∑' t', body t t' * ν t' {c}.
            -- Goal: ∑' a, execN k ⟨app lamApp a.expr, a.state⟩ {c} * SLang.spec (body t) σ {a}
            --       ≤ ∑' t', body t t' * ν t' {c}.
            -- Compute SLang.spec (body t) σ {a}: nonzero iff a = ⟨as_expr t', σ⟩ for some t'.
            have h_spec_apply : ∀ a : Cfg, SLang.spec (body t) σ {a}
                = ∑' t' : T, (body t) t' * (({a} : Set Cfg).indicator 1 (⟨as_expr t', σ⟩ : Cfg)) := by
              intro a
              unfold SLang.spec
              rw [Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton _),
                  Measure.map_apply Measurable.of_discrete (.preimage (MeasurableSet.singleton _)
                    Measurable.of_discrete),
                  show (_root_.count (body t)) = Measure.count.withDensity (body t) from rfl,
                  withDensity_apply _ (.preimage (.preimage (MeasurableSet.singleton _)
                    Measurable.of_discrete) Measurable.of_discrete),
                  ← lintegral_indicator (.preimage (.preimage (MeasurableSet.singleton _)
                    Measurable.of_discrete) Measurable.of_discrete), lintegral_count]
              congr 1; funext t'
              by_cases hx : (⟨as_expr t', σ⟩ : Cfg) ∈ ({a} : Set Cfg)
              · have hxp : t' ∈ (as_expr ⁻¹' ((fun e => (⟨e, σ⟩ : Cfg)) ⁻¹' ({a} : Set Cfg))) :=
                  Set.mem_preimage.mpr (Set.mem_preimage.mpr hx)
                rw [Set.indicator_of_mem hxp, Set.indicator_of_mem hx]; simp
              · have hxnp : t' ∉ (as_expr ⁻¹' ((fun e => (⟨e, σ⟩ : Cfg)) ⁻¹' ({a} : Set Cfg))) := fun h =>
                  hx (Set.mem_preimage.mp (Set.mem_preimage.mp h))
                rw [Set.indicator_of_notMem hxnp, Set.indicator_of_notMem hx]; simp
            -- Goal RHS: (count (body t)).bind ν {c} = ∑' t', body t t' * ν t' {c}.
            have h_bind_form : ((_root_.count (body t)).bind (fun t' => ν t')) {c}
                = ∑' t' : T, body t t' * (ν t') {c} := by
              rw [Measure.bind_apply (MeasurableSet.singleton _)
                Measurable.of_discrete.aemeasurable]
              show ∫⁻ t', (ν t') {c} ∂(Measure.count.withDensity (body t)) = _
              rw [lintegral_withDensity_eq_lintegral_mul₀
                Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable,
                lintegral_count]
              rfl
            rw [h_bind_form]
            -- Now show: ∑' a, execN k ⟨app lamApp a.expr, a.state⟩ {c} * SLang.spec (body t) σ {a}
            --        ≤ ∑' t', body t t' * ν t' {c}.
            -- Substitute h_spec_apply, swap sums, drop indicator → restrict to a = ⟨as_expr t', σ⟩.
            simp_rw [h_spec_apply]
            -- ∑' a, _ * ∑' t', body t t' * indicator
            -- = ∑' a, ∑' t', _ * (body t t' * indicator)
            -- = ∑' t', ∑' a, _ * body t t' * indicator
            -- = ∑' t', body t t' * (∑' a, _ * indicator)
            -- = ∑' t', body t t' * (the only a with indicator 1, which is ⟨as_expr t', σ⟩)
            -- Pull the outer factor inside the sum: _ * ∑' t', f t' = ∑' t', _ * f t'.
            simp_rw [← ENNReal.tsum_mul_left]
            rw [ENNReal.tsum_comm]
            refine ENNReal.tsum_le_tsum (fun t' => ?_)
            -- ∑' a, execN k ⟨app lamApp a.expr, a.state⟩ {c} * (body t t' * indicator a (⟨as_expr t', σ⟩))
            -- = body t t' * (∑' a, execN k ... * indicator)
            -- = body t t' * execN k ⟨app lamApp (as_expr t'), σ⟩ {c}
            rw [show (fun a : Cfg => execN k ⟨EctxItem.fillItem (.appR lamApp) a.expr, a.state⟩ {c}
                  * (body t t' * (({a} : Set Cfg).indicator 1 (⟨as_expr t', σ⟩ : Cfg))))
                = (fun a : Cfg => body t t' *
                  (execN k ⟨EctxItem.fillItem (.appR lamApp) a.expr, a.state⟩ {c}
                    * (({a} : Set Cfg).indicator 1 (⟨as_expr t', σ⟩ : Cfg)))) from by
              funext a; ring]
            rw [ENNReal.tsum_mul_left]
            refine mul_le_mul' le_rfl ?_
            -- ∑' a, execN k ⟨app lamApp a.expr, a.state⟩ {c} * indicator a = execN k ⟨app lamApp (as_expr t'), σ⟩ {c}
            -- (the sum collapses since indicator picks a = ⟨as_expr t', σ⟩).
            rw [show (fun a : Cfg => execN k ⟨EctxItem.fillItem (.appR lamApp) a.expr, a.state⟩ {c}
                * (({a} : Set Cfg).indicator 1 (⟨as_expr t', σ⟩ : Cfg)))
              = (fun a : Cfg => if a = ⟨as_expr t', σ⟩
                  then execN k ⟨EctxItem.fillItem (.appR lamApp) a.expr, a.state⟩ {c}
                  else 0) from by
              funext a
              by_cases h : (⟨as_expr t', σ⟩ : Cfg) ∈ ({a} : Set Cfg)
              · simp only [Set.indicator_of_mem h, Pi.one_apply, mul_one]
                have : a = ⟨as_expr t', σ⟩ := by simp at h; exact h.symm
                simp [this]
              · simp only [Set.indicator_of_notMem h, mul_zero]
                have : a ≠ ⟨as_expr t', σ⟩ := fun ha => h (by simp [ha])
                simp [this]]
            rw [tsum_ite_eq]
            simp only [EctxItem.fillItem]
            -- Goal: execN k ⟨app lamApp (as_expr t'), σ⟩ {c} ≤ ν t' {c}
            -- One more det step: app-lam beta on (lam (close (app F (fvar v)) v)) applied to (as_expr t')
            -- → open' (close (app F (fvar v)) v) (as_expr t') = subst (app F (fvar v)) v (as_expr t') = app F (as_expr t').
            cases k with
            | zero => simp [execN]
            | succ j =>
              have hnv_la : ¬ (Exp.app lamApp (as_expr t')).isValue := by intro ⟨h⟩; cases h
              have hstep_la : DetHeadStep_discrete ⟨Exp.app lamApp (as_expr t'), σ⟩
                  ⟨.app F (as_expr t'), σ⟩ := by
                rw [hlamApp_def]
                have h := DetHeadStep_discrete.app_lam (as_expr_isVal t') σ
                  (body := Exp.close (.app F (.fvar v)) v)
                have hopen_eq : Exp.open' (Exp.close (.app F (.fvar v)) v) (as_expr t')
                    = .app F (as_expr t') := by
                  rw [Exp.open_close_subst_lc_gen v (.app F (.fvar v)) (as_expr t')
                      (.app hF_lc (.fvar _)) (as_expr_lc t')]
                  simp [Exp.subst, Exp.subst_fresh v F (as_expr t') hvF]
                rw [hopen_eq] at h
                exact h
              rw [execN_detHeadStep hnv_la hstep_la j]
              -- Apply IH: j < m+2 = n. j = (succ k)'s predecessor of `m+2`-flow chain.
              -- We have n = m + 2, m = succ k = k+1, k = succ j = j+1. So j+1+1+2 = n+2? wait n = m+2 = (k+1)+2 = k+3 = (j+1)+3 = j+4.
              -- We need j < n = j + 4, which is trivially true.
              exact ih j (by omega) c t'
        · -- cond t = false
          have hct' : cond t = false := Bool.eq_false_iff.mpr hct
          rw [hct']
          rw [hν_rec t]
          simp only [hct', show (false = true) = False from by simp, if_false]
          show execN m ⟨.cond (.lit (.bool false)) BODY (as_expr t), σ⟩ {c} ≤ _
          have hnv : ¬ (Exp.cond (.lit (.bool false)) BODY (as_expr t)).isValue := by
            intro ⟨h⟩; cases h
          cases m with
          | zero => simp [execN]
          | succ k =>
            rw [execN_detHeadStep hnv (DetHeadStep_discrete.cond_false _ _ _) k]
            -- execN k ⟨as_expr t, σ⟩ {c}: as_expr t is a value.
            cases k with
            | zero => simp [execN]
            | succ j =>
              rw [execN_succ_isValue ⟨as_expr_isVal t⟩ j]
  · -- FORWARD: SLang.spec (probWhile) ≤ limExec
    refine Measure.le_iff.mpr ?_
    intro S hS
    -- LHS = ∑' x, probWhile x * indicator
    rw [expand (probWhile cond body init) S hS]
    -- Use probWhile = ⨆ k, probWhileCut k pointwise.
    have probWhile_iSup : ∀ x : T,
        probWhile cond body init x = ⨆ k, probWhileCut cond body k init x := fun _ => rfl
    simp_rw [probWhile_iSup, ENNReal.iSup_mul]
    -- Now LHS is ∑' x, ⨆ k, (probWhileCut k init x * indicator).
    -- Swap tsum and iSup using monotonicity.
    have hmono : ∀ x, Monotone (fun k =>
        probWhileCut cond body k init x * S.indicator 1 ⟨as_expr x, σ⟩) :=
      fun x _ _ hmn => mul_le_mul' (SLang.probWhileCut_monotonic cond body init x hmn) le_rfl
    rw [ENNReal.tsum_iSup_of_monotone' hmono]
    -- Now bounded by ⨆ k, ∑' x, probWhileCut k init x * indicator
    --              = ⨆ k, SLang.spec (probWhileCut k init) σ S       [reverse expand]
    --              ≤ ⨆ k, limExec ⟨app F (as_expr init), σ⟩ S         [SLang_spec_probWhileCut_le]
    --              = limExec ⟨app F (as_expr init), σ⟩ S              [iSup of constant]
    have step_eq : (⨆ k, ∑' x, probWhileCut cond body k init x * S.indicator 1 ⟨as_expr x, σ⟩) =
        ⨆ k, SLang.spec (probWhileCut cond body k init) σ S := by
      refine iSup_congr (fun k => ?_)
      rw [← expand (probWhileCut cond body k init) S hS]
    rw [step_eq]
    -- limExec ⟨app F (as_expr init), σ⟩ at S = (constant in k); just need SLang_spec_probWhileCut_le.
    refine iSup_le (fun k => ?_)
    -- Goal: SLang.spec (probWhileCut k init) σ S ≤ limExec ... S
    have hk := SLang_spec_probWhileCut_le hfx hfv hxv hcondE_lc hbodyE_lc
      hfcondE hfbodyE hxcondE hxbodyE hvcondE hvbodyE hfas hxas hvas hcond hbody k init σ
    -- hk : SLang.spec (probWhileCut k init) σ ≤ limExec ⟨.app F' (as_expr init), σ⟩
    -- where F' is definitionally F. Match goal.
    show SLang.spec (probWhileCut cond body k init) σ S ≤ _
    -- The probLangWhile_unfolded is irrelevant — we need to identify
    -- limExec (probLangWhile f x v condE bodyE (as_expr init)) σ with limExec ⟨app F (as_expr init), σ⟩.
    -- probLangWhile expands to .app F (as_expr init) by definition; check below.
    have hPL : (probLangWhile f x v condE bodyE (as_expr init) : Exp) = .app F (as_expr init) := by
      rfl
    rw [hPL]
    exact hk S

/-! ## Generic combinator: meta-recursion-on-Nat ↔ probWhile-with-accumulator

  Many SampCert primitives are defined by Lean meta-recursion on a `ℕ` parameter.
  To embed them faithfully when the parameter is computed at *runtime* in ProbLang,
  we need a closed ProbLang term that takes the counter as a runtime argument.
  Building one bespoke `fix`-based ProbLang term per primitive is tedious; instead,
  we re-express each meta-recursive primitive as a `probWhile` over an accumulator,
  prove this is equivalent on the SLang side, then reuse the existing
  `probLangWhile_isEmbedding` to embed it. -/

/-- Meta-level structural recursion on `ℕ`: build the SLang term that runs
    `step 0 base ; step 1 _ ; ... ; step (n-1) _`, threading the running accumulator. -/
def probNatRec (base : T) (step : ℕ → T → SLang T) : ℕ → SLang T
  | 0 => probPure base
  | n+1 => probBind (probNatRec base step n) (step n)

/-- The body of the accumulator loop (parameterized by the meta-level count `n`).
    State `(rem, acc)` — `rem` counts down from `n` to `0`; the index passed to
    `step` is `n - rem`, which counts up from `0` to `n - 1` over the loop. -/
def probNatRec_body (n : ℕ) (step : ℕ → T → SLang T) : ℕ × T → SLang (ℕ × T) :=
  fun s => probBind (step (n - s.1) s.2) (fun acc' => probPure (s.1 - 1, acc'))

/-- `probWhile`-based formulation: state `(remaining, acc)`, decrement remaining,
    apply `step (n - remaining)` to acc on each iteration. -/
def probNatRec_loop (base : T) (step : ℕ → T → SLang T) (n : ℕ) : SLang T :=
  probBind
    (probWhile (fun s : ℕ × T => 0 < s.1) (probNatRec_body n step) (n, base))
    (fun s : ℕ × T => probPure s.2)

/-- Helper: starting from `acc`, run `len` step calls with consecutive indices
    `start, start+1, ..., start+len-1`. Forward index order. -/
def probNatRec_offset (acc : T) (step : ℕ → T → SLang T) (start : ℕ) : ℕ → SLang T
  | 0 => probPure acc
  | len+1 => probBind (step start acc) (fun acc' => probNatRec_offset acc' step (start + 1) len)

/-! ### Helper: `probWhileCut` evaluation on the accumulator loop.

    `probNatRec` is defined by *outer* recursion: `probNatRec _ _ (n+1) = bind (probNatRec _ _ n) (step n)`.
    To match against `probNatRec_offset`, which is defined by *inner* recursion (head step first),
    we'll need an equivalence lemma between them as well. -/

/-- Generalized "append one step at the end" for `probNatRec_offset`. -/
theorem probNatRec_offset_append [Countable T]
    (acc : T) (step : ℕ → T → SLang T) (start n : ℕ) :
    probBind (probNatRec_offset acc step start n) (step (start + n))
    = probNatRec_offset acc step start (n + 1) := by
  induction n generalizing start acc with
  | zero =>
    show probBind (probPure acc) (step (start + 0)) = probBind (step start acc) (fun acc' => probPure acc')
    rw [SLang.pure_bind, Nat.add_zero, SLang.bind_pure]
  | succ n ih =>
    show probBind (probBind (step start acc) _) (step (start + (n+1)))
       = probBind (step start acc) _
    rw [SLang.bind_bind]
    congr 1
    funext acc'
    have := ih acc' (start + 1)
    show probBind (probNatRec_offset acc' step (start + 1) n) (step (start + (n+1)))
       = probNatRec_offset acc' step (start + 1) (n + 1)
    rw [show start + (n+1) = (start + 1) + n by omega]
    exact this

/-- `probNatRec` written in inner-recursion form: `probNatRec base step n = probNatRec_offset base step 0 n`. -/
theorem probNatRec_eq_offset [Countable T] (base : T) (step : ℕ → T → SLang T) (n : ℕ) :
    probNatRec base step n = probNatRec_offset base step 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show probBind (probNatRec base step n) (step n) = probNatRec_offset base step 0 (n+1)
    rw [ih]
    have h := probNatRec_offset_append base step 0 n
    rw [Nat.zero_add] at h
    exact h

/-- `probWhileCut` on the accumulator loop stabilizes at state `(0, ·)`: for any `k ≥ 1`,
    `probWhileCut cond body k (0, acc) = pure (0, acc)`. -/
theorem probWhileCut_natRec_zero_succ [Countable T] (step : ℕ → T → SLang T) (n : ℕ)
    (k : ℕ) (acc : T) :
    probWhileCut (fun s : ℕ × T => 0 < s.1) (probNatRec_body n step) (k + 1) (0, acc)
    = probPure (0, acc) := by
  show probWhileFunctional _ _ (probWhileCut _ _ k) (0, acc) = _
  unfold probWhileFunctional
  simp only [show ¬ (0 : ℕ) < 0 from Nat.lt_irrefl 0, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  rfl

/-- After `≥ m + 1` cuts (one extra to see `cond = false` and exit), with state `(m, acc)`:
    the loop runs `m` body steps starting at index `n - m`, then returns `(0, acc_final)`.
    Generalized over the cut-count `k` so it stabilizes for `k ≥ m+1`. -/
theorem probWhileCut_natRec_loop_ge [Countable T] (step : ℕ → T → SLang T)
    (n : ℕ) :
    ∀ (m : ℕ) (acc : T) (k : ℕ), m ≤ n → m + 1 ≤ k →
    probWhileCut (fun s : ℕ × T => 0 < s.1) (probNatRec_body n step) k (m, acc)
    = probBind (probNatRec_offset acc step (n - m) m) (fun acc_final => probPure (0, acc_final)) := by
  intro m
  induction m with
  | zero =>
    -- m = 0: state (0, acc), cond is false, result is pure regardless of remaining cuts ≥ 1.
    intro acc k _ hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [probWhileCut_natRec_zero_succ step n k' acc]
    show probPure (0, acc) = probBind (probNatRec_offset acc step (n - 0) 0) _
    show probPure (0, acc) = probBind (probPure acc) (fun acc_final => probPure (0, acc_final))
    rw [SLang.pure_bind]
  | succ m ih =>
    intro acc k hmn hk
    have hmn' : m ≤ n := Nat.le_of_succ_le hmn
    have hk' : m + 1 ≤ k - 1 := by omega
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk'' : m + 1 ≤ k' := by omega
    -- Helper: IH applied at any acc' with cut-count k'.
    have inner_step' : ∀ acc' : T,
        probWhileCut (fun s : ℕ × T => 0 < s.1) (probNatRec_body n step) k' (m, acc')
        = probBind (probNatRec_offset acc' step (n - m) m) (fun a => probPure (0, a)) := by
      intro acc'; exact ih acc' k' hmn' hk''
    -- Now do the rewrite chain.
    show probWhileCut _ _ (k' + 1) (m+1, acc) = _
    show probWhileFunctional _ _ (probWhileCut _ _ k') (m+1, acc) = _
    unfold probWhileFunctional
    simp only [show 0 < m + 1 from Nat.succ_pos m, decide_true, ↓reduceIte]
    -- Goal: bind (probNatRec_body n step (m+1, acc)) (probWhileCut _ _ k') = ...
    have body_eval :
        probNatRec_body n step (m+1, acc)
        = probBind (step (n - (m+1)) acc) (fun acc' => probPure (m, acc')) := by
      show probBind (step (n - (m+1, acc).1) (m+1, acc).2) (fun acc' => probPure ((m+1, acc).1 - 1, acc'))
        = _
      simp
    show probBind (probNatRec_body n step (m+1, acc)) _ = _
    rw [body_eval, SLang.bind_bind]
    have rewrite_inner : (fun (a : T) =>
        probBind (probPure (m, a))
          (probWhileCut (fun s : ℕ × T => 0 < s.1) (probNatRec_body n step) k'))
      = (fun (a : T) =>
        probBind (probNatRec_offset a step (n - m) m) (fun b => probPure (0, b))) := by
      funext a
      rw [SLang.pure_bind]
      exact inner_step' a
    rw [rewrite_inner]
    rw [← SLang.bind_bind]
    congr 1
    show probBind (step (n - (m+1)) acc) (fun a => probNatRec_offset a step (n - m) m)
       = probNatRec_offset acc step (n - (m+1)) (m + 1)
    rw [show (n - m) = (n - (m+1) + 1) by omega]
    rfl

/-- The two formulations are equal as SLang terms. -/
theorem probNatRec_eq_loop [Countable T] (base : T) (step : ℕ → T → SLang T) (n : ℕ) :
    probNatRec base step n = probNatRec_loop base step n := by
  rw [probNatRec_eq_offset]
  unfold probNatRec_loop
  -- For each pointwise output x, take the sup of probWhileCut over k.
  -- For all k ≥ n+1, probWhileCut k (n, base) is constant (by probWhileCut_natRec_loop_ge).
  -- So the sequence is eventually constant, and probWhile = that constant value.
  have hwhile :
      probWhile (fun s : ℕ × T => 0 < s.1) (probNatRec_body n step) (n, base)
      = probBind (probNatRec_offset base step 0 n) (fun a => probPure (0, a)) := by
    funext x
    refine probWhile_apply _ _ _ _ _ ?_
    apply tendsto_atTop_of_eventually_const (i₀ := n + 1)
    intro k hk
    rw [probWhileCut_natRec_loop_ge step n n base k (le_refl n) hk]
    rw [show n - n = 0 from Nat.sub_self n]
  rw [hwhile, SLang.bind_bind]
  -- Goal: probNatRec_offset base step 0 n
  --     = bind (probNatRec_offset base step 0 n) (fun a => bind (pure (0, a)) (fun s => pure s.2))
  -- Inner: bind (pure (0, a)) (fun s => pure s.2) = pure a
  have hinner : (fun a : T => probBind (probPure ((0 : ℕ), a))
                  (fun s : ℕ × T => probPure s.2))
              = (fun a : T => probPure a) := by
    funext a
    rw [SLang.pure_bind]
  rw [hinner, SLang.bind_pure]

/-! ### Upward-counting variant of `probNatRec_loop` (used for ProbLang embedding)

  The downward-counting `probNatRec_loop` above introduces a `n - rem` subtraction
  in the body, which mismatches between Nat and Int when `rem > n` — making the
  universal `IsEmbedding` requirement of `probLangWhile_isEmbedding` awkward to
  satisfy. The upward variant counts `idx` from `0` to `n`, calling `step idx acc`
  directly with no subtraction. This matches between SLang and ProbLang for all
  `idx : ℕ`. -/

/-- Upward-counting body: at state `(idx, acc)`, run `step idx acc`, return
    `(idx+1, acc')`. -/
def probNatRec_bodyUp (step : ℕ → T → SLang T) : ℕ × T → SLang (ℕ × T) :=
  fun s => probBind (step s.1 s.2) (fun acc' => probPure (s.1 + 1, acc'))

/-- Upward-counting `probWhile` formulation. State `(idx, acc)`, condition
    `idx < n`, increment idx each iteration. -/
def probNatRec_loopUp (base : T) (step : ℕ → T → SLang T) (n : ℕ) : SLang T :=
  probBind
    (probWhile (fun s : ℕ × T => decide (s.1 < n)) (probNatRec_bodyUp step) (0, base))
    (fun s : ℕ × T => probPure s.2)

/-! ### probWhileCut analysis for the upward variant. -/

/-- At state `(k, acc)` with `n ≤ k`, the loop terminates immediately: any cut ≥ 1
    yields `pure (k, acc)`. -/
theorem probWhileCut_natRecUp_atTop [Countable T] (step : ℕ → T → SLang T) (n : ℕ)
    (k : ℕ) (j : ℕ) (acc : T) (hk : n ≤ k) :
    probWhileCut (fun s : ℕ × T => decide (s.1 < n)) (probNatRec_bodyUp step) (j + 1) (k, acc)
    = probPure (k, acc) := by
  show probWhileFunctional _ _ (probWhileCut _ _ j) (k, acc) = _
  unfold probWhileFunctional
  simp only [show ¬ k < n from Nat.not_lt.mpr hk, decide_false, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- After enough cuts, `probWhileCut` from `(idx, acc)` with `idx ≤ n` equals running
    `n - idx` body steps starting at index `idx`. We need `(n - idx) + 1 ≤ k` cuts.
    Stated by induction on `rem := n - idx`. -/
theorem probWhileCut_natRecUp_loop_ge [Countable T] (step : ℕ → T → SLang T) (n : ℕ) :
    ∀ (rem : ℕ) (idx : ℕ) (acc : T) (k : ℕ), n - idx = rem → idx ≤ n → rem + 1 ≤ k →
    probWhileCut (fun s : ℕ × T => decide (s.1 < n)) (probNatRec_bodyUp step) k (idx, acc)
    = probBind (probNatRec_offset acc step idx rem)
        (fun a => probPure (n, a)) := by
  intro rem
  induction rem with
  | zero =>
    intro idx acc k hrem hidx hk
    have heq : idx = n := by omega
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [heq]
    rw [probWhileCut_natRecUp_atTop step n n k' acc (le_refl n)]
    show probPure (n, acc) = probBind (probPure acc) _
    rw [SLang.pure_bind]
  | succ rem ih =>
    intro idx acc k hrem hidx hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hidx_lt : idx < n := by omega
    have hrem' : n - (idx + 1) = rem := by omega
    have hidx1 : idx + 1 ≤ n := hidx_lt
    have hk' : rem + 1 ≤ k' := by omega
    show probWhileFunctional _ _ (probWhileCut _ _ k') (idx, acc) = _
    unfold probWhileFunctional
    simp only [show idx < n from hidx_lt, decide_true, ↓reduceIte]
    have body_eval :
        probNatRec_bodyUp step (idx, acc)
        = probBind (step idx acc) (fun acc' => probPure (idx + 1, acc')) := by
      show probBind (step (idx, acc).1 (idx, acc).2) _ = _; simp
    show (probNatRec_bodyUp step (idx, acc)).probBind _ = _
    rw [body_eval, SLang.bind_bind]
    have ih' := fun a => ih (idx + 1) a k' hrem' hidx1 hk'
    have rewrite_inner : (fun (a : T) =>
        probBind (probPure (idx + 1, a))
          (probWhileCut (fun s : ℕ × T => decide (s.1 < n)) (probNatRec_bodyUp step) k'))
      = (fun (a : T) =>
        probBind (probNatRec_offset a step (idx + 1) rem)
          (fun b => probPure (n, b))) := by
      funext a; rw [SLang.pure_bind]; exact ih' a
    rw [rewrite_inner, ← SLang.bind_bind]
    rfl

/-- The two formulations are equal as SLang terms (upward variant). -/
theorem probNatRec_eq_loopUp [Countable T] (base : T) (step : ℕ → T → SLang T) (n : ℕ) :
    probNatRec base step n = probNatRec_loopUp base step n := by
  rw [probNatRec_eq_offset]
  unfold probNatRec_loopUp
  have hwhile :
      probWhile (fun s : ℕ × T => decide (s.1 < n)) (probNatRec_bodyUp step) (0, base)
      = probBind (probNatRec_offset base step 0 (n - 0)) (fun a => probPure (n, a)) := by
    funext x
    refine probWhile_apply _ _ _ _ _ ?_
    apply tendsto_atTop_of_eventually_const (i₀ := (n - 0) + 1)
    intro k hk
    rw [probWhileCut_natRecUp_loop_ge step n (n - 0) 0 base k rfl (Nat.zero_le _) hk]
  rw [show n - 0 = n from Nat.sub_zero n] at hwhile
  rw [hwhile, SLang.bind_bind]
  have hinner : (fun a : T => probBind (probPure ((n : ℕ), a))
                  (fun s : ℕ × T => probPure s.2))
              = (fun a : T => probPure a) := by
    funext a
    rw [SLang.pure_bind]
  rw [hinner, SLang.bind_pure]

/-! ### Embeddable instances for primitives used by the generic combinator -/

instance : Countable Nat := inferInstance
instance : MeasurableSpace Nat := ⊤
instance : MeasurableSingletonClass Nat := ⟨fun _ => trivial⟩

/-- `Nat` embeds as the integer literal of its underlying value. -/
instance instProbLangEmbeddableNat : ProbLangEmbeddable Nat where
  as_expr n := .lit (.int n)
  as_expr_isVal _ := .lit
  as_expr_lc _ := .lit _
  as_expr_fv _ := rfl

instance : Countable Int := inferInstance
instance : MeasurableSpace Int := ⊤
instance : MeasurableSingletonClass Int := ⟨fun _ => trivial⟩

instance : ProbLangEmbeddable Int where
  as_expr z := .lit (.int z)
  as_expr_isVal _ := .lit
  as_expr_lc _ := .lit _
  as_expr_fv _ := rfl

/-- Pair of two embeddable types embeds as a ProbLang `.pair`. -/
instance instProbLangEmbeddableProd (A B : Type)
    [ProbLangEmbeddable A] [ProbLangEmbeddable B] : ProbLangEmbeddable (A × B) where
  as_expr p := .pair (as_expr p.1) (as_expr p.2)
  as_expr_isVal p := .pair (as_expr_isVal p.1) (as_expr_isVal p.2)
  as_expr_lc p := .pair (as_expr_lc p.1) (as_expr_lc p.2)
  as_expr_fv p := by simp [Exp.fv, as_expr_fv]

/-! ## ProbLang side of the generic combinator (upward-counting)

  Target: build a closed ProbLang expression that embeds
  `probNatRec_loopUp base step n`. We assemble it as a `probLangBind` over
  `probLangWhile` with:
    state type ℕ × T
    cond  := λ s. fst s < n
    body  := λ s. bind (stepE (fst s) (snd s)) (λ acc'. pair (fst s + 1) acc')
    init  := as_expr (0, base)
  Outer bind projects out the second component (the accumulator) at the end.

  Going upward (rather than `n - rem` downward) avoids any Int-vs-Nat
  subtraction mismatch — `fst s` is always non-negative since the only
  states reachable from `(0, base)` via `+1` increments stay in ℕ. -/

/-- Cond expression for the natRec loop: `λ s. fst s < nE`. The bound `nE` is an
    arbitrary closed `Exp` (typically `.lit (.int n)` for static use, or `.fvar nV`
    bound in an outer scope for runtime use). Caller's responsibility: `nE` is LC
    and `nE` does not contain `xs`. -/
def plProbNatRec_condE (xs : Var) (nE : Exp) : Exp :=
  .lam (Exp.close (.binop .lt (.fst (.fvar xs)) nE) xs)

/-- Body expression for the natRec loop. Parameterized by `stepE : ℕ → T → SLang T`.

    Body: `λ s. let acc' := stepE (fst s) (snd s); pair (fst s + 1) acc'`. -/
def plProbNatRec_bodyE (xs ws : Var) (stepE : Exp) : Exp :=
  .lam (Exp.close
    (probLangBind ws
      (.app (.app stepE (.fst (.fvar xs))) (.snd (.fvar xs)))
      (.pair (.binop .plus (.fst (.fvar xs)) (.lit (.int 1))) (.fvar ws)))
    xs)

/-- Closed ProbLang expression for `probNatRec_loopUp base step n`. The chosen
    fresh variables `f, x, v, xs, ws, w` must be pairwise distinct and not
    occur in `stepE`. -/
def plProbNatRec_loop {T : Type} [ProbLangEmbeddable T]
    (f x v xs ws w : Var) (nE : Exp) (base : T) (stepE : Exp) : Exp :=
  probLangBind w
    (probLangWhile f x v
      (plProbNatRec_condE xs nE)
      (plProbNatRec_bodyE xs ws stepE)
      (@as_expr (Nat × T) _ (0, base)))
    (.snd (.fvar w))

/-- Variant of `plProbNatRec_loop` taking an arbitrary `Exp` for the initial accumulator
    value (so we can pass a free variable bound in an outer scope). -/
def plProbNatRec_loopE (f x v xs ws w : Var) (nE baseE stepE : Exp) : Exp :=
  probLangBind w
    (probLangWhile f x v
      (plProbNatRec_condE xs nE)
      (plProbNatRec_bodyE xs ws stepE)
      (.pair (.lit (.int 0)) baseE))
    (.snd (.fvar w))

/-! ### Free-variable freshness for the natRec loop expressions

  Each `plProbNatRec_*_fresh` lemma gives a sufficient set of conditions for an
  atom to be fresh in the corresponding closed expression. Since the bound
  atoms (`xs`, `ws`, `f`, `x`, `v`, `w`) get closed away, we only need to
  rule them out when they happen to equal the queried atom. -/

theorem plProbNatRec_condE_fresh {a xs : Var} {nE : Exp}
    (ha_xs : a ≠ xs) (ha_nE : a ∉ nE.fv) :
    a ∉ (plProbNatRec_condE xs nE).fv := by
  unfold plProbNatRec_condE
  apply Exp.close_preserve_not_fvar
  simp [Exp.fv, ha_nE]
  exact ha_xs

theorem plProbNatRec_bodyE_fresh {a xs ws : Var} {stepE : Exp}
    (ha_xs : a ≠ xs) (ha_ws : a ≠ ws) (ha_step : a ∉ stepE.fv) :
    a ∉ (plProbNatRec_bodyE xs ws stepE).fv := by
  unfold plProbNatRec_bodyE
  apply Exp.close_preserve_not_fvar
  refine probLangBind_fresh ?_ ?_
  · -- a ∉ (app (app stepE (fst (fvar xs))) (snd (fvar xs))).fv
    simp only [Exp.fv, Finset.notMem_union, Finset.notMem_singleton]
    exact ⟨⟨ha_step, ha_xs⟩, ha_xs⟩
  · -- a ∉ (pair (binop plus (fst (fvar xs)) (lit 1)) (fvar ws)).fv
    simp only [Exp.fv, Finset.notMem_union, Finset.notMem_singleton, Finset.notMem_empty,
               not_false_iff, and_true]
    exact ⟨ha_xs, ha_ws⟩

theorem probLangWhile_fresh {a f x v : Var} {condE bodyE initE : Exp}
    (ha_f : a ≠ f) (ha_x : a ≠ x) (ha_v : a ≠ v)
    (ha_cond : a ∉ condE.fv) (ha_body : a ∉ bodyE.fv) (ha_init : a ∉ initE.fv) :
    a ∉ (probLangWhile f x v condE bodyE initE).fv := by
  unfold probLangWhile
  simp only [Exp.fv, Finset.notMem_union]
  refine ⟨?_, ha_init⟩
  apply Exp.close_preserve_not_fvar
  apply Exp.close_preserve_not_fvar
  -- inner body: cond (app condE (fvar x)) (probLangBind v (app bodyE (fvar x)) (app (fvar f) (fvar v))) (fvar x)
  simp only [Exp.fv, Finset.notMem_union, Finset.notMem_singleton]
  refine ⟨⟨⟨ha_cond, ha_x⟩, ?_⟩, ha_x⟩
  refine probLangBind_fresh ?_ ?_
  · simp only [Exp.fv, Finset.notMem_union, Finset.notMem_singleton]
    exact ⟨ha_body, ha_x⟩
  · simp only [Exp.fv, Finset.notMem_union, Finset.notMem_singleton]
    exact ⟨ha_f, ha_v⟩

theorem plProbNatRec_loop_fresh [ProbLangEmbeddable T] {a f x v xs ws w : Var}
    {nE : Exp} {base : T} {stepE : Exp}
    (ha_w : a ≠ w) (ha_f : a ≠ f) (ha_x : a ≠ x) (ha_v : a ≠ v)
    (ha_xs : a ≠ xs) (ha_ws : a ≠ ws)
    (ha_nE : a ∉ nE.fv) (ha_step : a ∉ stepE.fv) :
    a ∉ (plProbNatRec_loop f x v xs ws w nE base stepE).fv := by
  unfold plProbNatRec_loop
  refine probLangBind_fresh ?_ ?_
  · refine probLangWhile_fresh ha_f ha_x ha_v
      (plProbNatRec_condE_fresh ha_xs ha_nE)
      (plProbNatRec_bodyE_fresh ha_xs ha_ws ha_step) ?_
    simp [Exp.fv, as_expr_fv]
  · simp [Exp.fv]; exact ha_w

theorem plProbNatRec_loopE_fresh {a f x v xs ws w : Var}
    {nE baseE stepE : Exp}
    (ha_w : a ≠ w) (ha_f : a ≠ f) (ha_x : a ≠ x) (ha_v : a ≠ v)
    (ha_xs : a ≠ xs) (ha_ws : a ≠ ws)
    (ha_nE : a ∉ nE.fv) (ha_baseE : a ∉ baseE.fv) (ha_step : a ∉ stepE.fv) :
    a ∉ (plProbNatRec_loopE f x v xs ws w nE baseE stepE).fv := by
  unfold plProbNatRec_loopE
  refine probLangBind_fresh ?_ ?_
  · refine probLangWhile_fresh ha_f ha_x ha_v
      (plProbNatRec_condE_fresh ha_xs ha_nE)
      (plProbNatRec_bodyE_fresh ha_xs ha_ws ha_step) ?_
    simp [Exp.fv, ha_baseE]
  · simp [Exp.fv]; exact ha_w

/-! ### Substitution push-through

  Substitution at an atom `a` distributes through closed-binder constructions
  whenever the substitute (the value being plugged in) doesn't capture any of
  the bound atoms. These give a clean `subst (plProbNatRec_loopE …) a u
  = plProbNatRec_loopE …` rewrite that the user-facing proofs can use without
  re-deriving the subst push from scratch. -/

theorem probLangBind_subst {a x : Var} {e1 body u : Exp}
    (hax : a ≠ x) (hxu : x ∉ u.fv) :
    Exp.subst (probLangBind x e1 body) a u
      = probLangBind x (Exp.subst e1 a u) (Exp.subst body a u) := by
  unfold probLangBind
  show Exp.app _ _ = Exp.app _ _
  simp only [Exp.subst]
  rw [Exp.subst_close a x u body hax hxu]

/-- Helper: subst pushes through `lam (close body x)` when `a ≠ x` and `x ∉ u.fv`. -/
theorem subst_lam_close {a x : Var} {body u : Exp} (hax : a ≠ x) (hxu : x ∉ u.fv) :
    Exp.subst (.lam (Exp.close body x)) a u
      = .lam (Exp.close (Exp.subst body a u) x) := by
  show Exp.lam _ = Exp.lam _
  congr 1
  show Exp.subst (Exp.close body x) a u = _
  exact Exp.subst_close a x u body hax hxu

theorem plProbNatRec_condE_subst {a xs : Var} {nE u : Exp}
    (hax : a ≠ xs) (hxsu : xs ∉ u.fv) :
    Exp.subst (plProbNatRec_condE xs nE) a u
      = plProbNatRec_condE xs (Exp.subst nE a u) := by
  unfold plProbNatRec_condE
  rw [subst_lam_close hax hxsu]
  have h1 : Exp.subst (Exp.fst (.fvar xs)) a u = .fst (.fvar xs) := by
    show Exp.fst _ = Exp.fst _; congr 1
    show (if a = xs then u else Exp.fvar xs) = .fvar xs
    rw [if_neg hax]
  show Exp.lam (Exp.close (.binop _ (Exp.subst (.fst (.fvar xs)) a u) _) xs) = _
  rw [h1]

theorem plProbNatRec_bodyE_subst {a xs ws : Var} {stepE u : Exp}
    (ha_xs : a ≠ xs) (ha_ws : a ≠ ws)
    (hxs_u : xs ∉ u.fv) (hws_u : ws ∉ u.fv) :
    Exp.subst (plProbNatRec_bodyE xs ws stepE) a u
      = plProbNatRec_bodyE xs ws (Exp.subst stepE a u) := by
  unfold plProbNatRec_bodyE
  rw [subst_lam_close ha_xs hxs_u, probLangBind_subst ha_ws hws_u]
  have hxs_subst : Exp.subst (Exp.fvar xs) a u = .fvar xs := by
    show (if a = xs then u else Exp.fvar xs) = _; rw [if_neg ha_xs]
  have hws_subst : Exp.subst (Exp.fvar ws) a u = .fvar ws := by
    show (if a = ws then u else Exp.fvar ws) = _; rw [if_neg ha_ws]
  show Exp.lam (Exp.close (probLangBind ws (Exp.subst _ a u) (Exp.subst _ a u)) xs) = _
  show Exp.lam (Exp.close (probLangBind ws
      (.app (.app (Exp.subst stepE a u) (.fst (Exp.subst (Exp.fvar xs) a u)))
            (.snd (Exp.subst (Exp.fvar xs) a u)))
      (.pair (.binop .plus (.fst (Exp.subst (Exp.fvar xs) a u)) (.lit (.int 1)))
             (Exp.subst (Exp.fvar ws) a u))) xs) = _
  rw [hxs_subst, hws_subst]

theorem plProbNatRec_loopE_subst {a f x v xs ws w : Var}
    {nE baseE stepE u : Exp}
    (ha_f : a ≠ f) (ha_x : a ≠ x) (ha_v : a ≠ v) (ha_w : a ≠ w)
    (ha_xs : a ≠ xs) (ha_ws : a ≠ ws)
    (hf_u : f ∉ u.fv) (hx_u : x ∉ u.fv) (hv_u : v ∉ u.fv) (hw_u : w ∉ u.fv)
    (hxs_u : xs ∉ u.fv) (hws_u : ws ∉ u.fv) :
    Exp.subst (plProbNatRec_loopE f x v xs ws w nE baseE stepE) a u
      = plProbNatRec_loopE f x v xs ws w
          (Exp.subst nE a u) (Exp.subst baseE a u) (Exp.subst stepE a u) := by
  unfold plProbNatRec_loopE
  rw [probLangBind_subst ha_w hw_u]
  -- Helpers for subst at fvar atoms.
  have hxsubst : Exp.subst (Exp.fvar x) a u = .fvar x := by
    show (if a = x then u else _) = _; rw [if_neg ha_x]
  have hfsubst : Exp.subst (Exp.fvar f) a u = .fvar f := by
    show (if a = f then u else _) = _; rw [if_neg ha_f]
  have hvsubst : Exp.subst (Exp.fvar v) a u = .fvar v := by
    show (if a = v then u else _) = _; rw [if_neg ha_v]
  have hwsubst : Exp.subst (Exp.fvar w) a u = .fvar w := by
    show (if a = w then u else _) = _; rw [if_neg ha_w]
  congr 1
  · unfold probLangWhile
    simp only [Exp.subst]
    rw [Exp.subst_close a f u _ ha_f hf_u]
    simp only [Exp.subst]
    rw [Exp.subst_close a x u _ ha_x hx_u]
    simp only [Exp.subst]
    rw [plProbNatRec_condE_subst ha_xs hxs_u, probLangBind_subst ha_v hv_u]
    simp only [Exp.subst]
    rw [plProbNatRec_bodyE_subst ha_xs ha_ws hxs_u hws_u]
    rw [if_neg ha_x, if_neg ha_f, if_neg ha_v]
  · show Exp.subst (.snd (.fvar w)) a u = .snd (.fvar w)
    show Exp.snd (Exp.subst (.fvar w) a u) = _
    rw [hwsubst]

/-- `IsEmbedding` is invariant under any deterministic head step on the ProbLang side. -/
theorem IsEmbedding.of_detHeadStep [SLangType T] [ProbLangEmbeddable T]
    {s : SLang T} {e e' : Exp}
    (hstep : ∀ σ, ¬ e.isValue ∧ DetHeadStep_discrete ⟨e, σ⟩ ⟨e', σ⟩)
    (h : IsEmbedding s e') : IsEmbedding s e := by
  intro σ
  obtain ⟨hnv, hd⟩ := hstep σ
  rw [limExec_detHeadStep hnv hd]; exact h σ

/-- `IsEmbedding` invariance under `limExec`-equality on the ProbLang side. -/
theorem IsEmbedding.of_limExec_eq [SLangType T] [ProbLangEmbeddable T]
    {s : SLang T} {e e' : Exp}
    (heq : ∀ σ, limExec ⟨e, σ⟩ = limExec ⟨e', σ⟩)
    (h : IsEmbedding s e') : IsEmbedding s e := by
  intro σ; rw [heq σ]; exact h σ

/-- β-reduce a closed lambda applied to an `as_expr`-encoded argument. Lifts an
    embedding of the substituted body to an embedding of the un-applied form.

    This is the key helper for **dynamic** embeddings: the user-facing closed
    sampler expression is a chain of lambdas (one per Nat/Bool/etc. parameter),
    and applying it to encoded arguments at runtime β-reduces back to the
    static-form body, whose embedding we can then prove inductively. -/
theorem probLangApp_isEmbedding [SLangType T] [ProbLangEmbeddable T]
    {A : Type} [ProbLangEmbeddable A]
    {body : Exp} {x : Var} (hbody : Exp.IsLocallyClosed body)
    {s : SLang T} {a : A}
    (h : IsEmbedding s (Exp.subst body x (as_expr a))) :
    IsEmbedding s (.app (.lam (Exp.close body x)) (as_expr a)) := by
  refine IsEmbedding.of_detHeadStep
    (e' := Exp.subst body x (as_expr a))
    (fun σ => ⟨?_, ?_⟩) h
  · intro ⟨h⟩; cases h
  · have hd := DetHeadStep_discrete.app_lam (as_expr_isVal a) σ
      (body := Exp.close body x)
    rw [Exp.open_close_subst_lc_gen x _ _ hbody (as_expr_lc a)] at hd
    exact hd

/-! ### Dynamic-embedding infrastructure

  Helpers for the per-sampler embedding proofs: each sampler is a chain of `λ`s
  that need to be β-reduced, then composed with `probLangBind_isEmbedding` etc.

  These helpers reduce the boilerplate from ~100s of LOC per sampler to ~50. -/

/-- LC of a `.lam (close body x)` form. -/
theorem Exp.IsLocallyClosed.lamClose {body : Exp} (x : Var) (hbody : Exp.IsLocallyClosed body) :
    Exp.IsLocallyClosed (Exp.lam (Exp.close body x)) := by
  refine Exp.IsLocallyClosed.lam ∅ _ (fun y _ => ?_)
  rw [Exp.open_close_subst_lc x y _ hbody]
  exact Exp.subst_lc hbody (.fvar _)

/-- `subst` commutes through `.lam (close body x)` when the target var differs from `x`
    and `x` is not free in the substituted value. -/
theorem Exp.subst_lamClose {body v : Exp} {x y : Var} (hxy : x ≠ y) (hxv : x ∉ v.fv) :
    Exp.subst (Exp.lam (Exp.close body x)) y v
    = Exp.lam (Exp.close (Exp.subst body y v) x) := by
  show Exp.lam _ = Exp.lam _
  congr 1
  rw [Exp.subst_close y x v body hxy.symm hxv]

/-- β-reduce a closed lambda applied to an *arbitrary* argument expression `argE`,
    given that `limExec` of the argument is `dirac (as_expr a, σ)` (i.e., `argE`
    deterministically reduces to `as_expr a`). -/
theorem probLangApp_argE_isEmbedding [SLangType T] [ProbLangEmbeddable T]
    {A : Type} [ProbLangEmbeddable A]
    {body argE : Exp} {x : Var} (hbody : Exp.IsLocallyClosed body)
    {s : SLang T} {a : A}
    (hargE : ∀ σ, limExec ⟨argE, σ⟩ = dirac ⟨as_expr a, σ⟩)
    (h : IsEmbedding s (Exp.subst body x (as_expr a))) :
    IsEmbedding s (.app (.lam (Exp.close body x)) argE) := by
  intro σ
  rw [limExec_app, hargE σ, Measure.dirac_bind Measurable.of_discrete]
  show limExec ⟨.app (.lam (.close body x)) (as_expr a), σ⟩ = _
  exact probLangApp_isEmbedding hbody h σ

/-- β-reduce TWO closed lambdas applied to two `as_expr`-encoded arguments.
    Specifically, the form `.app (.app (.lam (close (.lam (close body y)) x)) (as_expr a)) (as_expr b)`
    embeds `s` when the doubly-substituted body does. -/
theorem probLangApp2_isEmbedding [SLangType T] [ProbLangEmbeddable T]
    {A B : Type} [ProbLangEmbeddable A] [ProbLangEmbeddable B]
    {body : Exp} {x y : Var} (hxy : x ≠ y)
    (hbody : Exp.IsLocallyClosed body)
    (hxas : ∀ b : B, x ∉ (as_expr b).fv)
    (hyas : ∀ a : A, y ∉ (as_expr a).fv)
    {s : SLang T} {a : A} {b : B}
    (h : IsEmbedding s
      (Exp.subst (Exp.subst body y (as_expr b)) x (as_expr a))) :
    IsEmbedding s
      (.app (.app (.lam (Exp.close (Exp.lam (Exp.close body y)) x)) (as_expr a)) (as_expr b)) := by
  have hinner_lc : Exp.IsLocallyClosed (Exp.lam (Exp.close body y)) :=
    Exp.IsLocallyClosed.lamClose y hbody
  -- Step 1: peel outer λ x via det step under [appL (as_expr b)] ectx.
  have hstep : ∀ σ, DetStep_discrete
    ⟨.app (.app (.lam (.close (.lam (.close body y)) x)) (as_expr a)) (as_expr b), σ⟩
    ⟨.app (Exp.subst (Exp.lam (Exp.close body y)) x (as_expr a)) (as_expr b), σ⟩ := by
    intro σ
    have hbase : DetHeadStep_discrete
      ⟨.app (.lam (Exp.close (Exp.lam (Exp.close body y)) x)) (as_expr a), σ⟩
      ⟨Exp.subst (Exp.lam (Exp.close body y)) x (as_expr a), σ⟩ := by
      have h := DetHeadStep_discrete.app_lam (as_expr_isVal a) σ
        (body := Exp.close (Exp.lam (Exp.close body y)) x)
      rw [Exp.open_close_subst_lc_gen x _ _ hinner_lc (as_expr_lc a)] at h
      exact h
    have hfill := DetStep_discrete.fill [.appL ⟨as_expr b, as_expr_isVal b⟩] hbase.toDetStep
    simp only [Ectx.fill, List.foldl_cons, List.foldl_nil, flip,
               EctxItem.fillItem, Exp.ofVal] at hfill
    exact hfill
  refine IsEmbedding.of_limExec_eq (fun σ => limExec_detStep (hstep σ)) ?_
  -- After peeling: .app (subst (.lam (close body y)) x (as_expr a)) (as_expr b)
  -- = .app (.lam (close (subst body x (as_expr a)) y)) (as_expr b) by subst_lamClose
  -- (need x ∉ (as_expr a).fv, which is hxas a... wait no. subst_lamClose pushes subst at y
  -- through lam (close . x). The y here is x, and x_in_subst_lam is the binder. Wait let me re-read).
  -- subst_lamClose: subst (lam (close body x)) y v = lam (close (subst body y v) x) when x ≠ y, x ∉ v.fv.
  -- Here we want: subst (.lam (close body y)) x (as_expr a) = .lam (close (subst body x (as_expr a)) y)
  -- This requires y ≠ x AND y ∉ (as_expr a).fv.
  rw [Exp.subst_lamClose (Ne.symm hxy) (hyas a)]
  refine probLangApp_isEmbedding ?_ ?_
  · exact Exp.subst_lc hbody (as_expr_lc a)
  · -- IsEmbedding s (subst (subst body x (as_expr a)) y (as_expr b))
    -- Bridge to h via subst_subst_ne.
    have hcomm : Exp.subst (Exp.subst body x (as_expr a)) y (as_expr b)
        = Exp.subst (Exp.subst body y (as_expr b)) x (as_expr a) :=
      Exp.subst_subst_ne hxy (hxas b) (hyas a)
    rw [hcomm]
    exact h

/-! ### Det-step / `limExec` reduction toolkit

  Generic helpers that collapse the recurring pattern of
    `DetHeadStep_discrete.binop ... + DetStep_discrete.fill K + simp [Ectx.fill, ...] + limExec_detStep`
  into a single named call. -/

/-- Lift a deterministic head step under a single ectx item to a `limExec`
    equality. The step source must not already be a value. -/
theorem limExec_under_ectxItem (Ki : EctxItem) {e e' : Exp} {σ : State}
    (hnv : ¬ e.isValue) (h : DetHeadStep_discrete ⟨e, σ⟩ ⟨e', σ⟩) :
    limExec ⟨Ki.fillItem e, σ⟩ = limExec ⟨Ki.fillItem e', σ⟩ := by
  have hd : DetStep_discrete ⟨Ki.fillItem e, σ⟩ ⟨Ki.fillItem e', σ⟩ :=
    DetStep_discrete.fill [Ki] h.toDetStep
  exact limExec_detStep hd

/-- Lift a deterministic head step under a (composite) ectx to a `limExec` equality. -/
theorem limExec_under_ectx (K : Ectx) {e e' : Exp} {σ : State}
    (h : DetHeadStep_discrete ⟨e, σ⟩ ⟨e', σ⟩) :
    limExec ⟨K.fill e, σ⟩ = limExec ⟨K.fill e', σ⟩ :=
  limExec_detStep (DetStep_discrete.fill K h.toDetStep)

/-! Concrete variants for the syntactic shapes that appear in goals (without
    requiring `EctxItem.fillItem` sugar). Each takes an inner `DetStep_discrete` and lifts
    it under one ectx-item layer. They compose: chain them by `rw` to reduce
    arbitrary contexts. -/

theorem limExec_binopL_step {op : BinOp} {e e' : Exp} {v2 : Exp}
    (hv2 : IsVal v2) {σ σ' : State}
    (h : DetStep_discrete ⟨e, σ⟩ ⟨e', σ'⟩) :
    limExec ⟨.binop op e v2, σ⟩ = limExec ⟨.binop op e' v2, σ'⟩ :=
  limExec_detStep (DetStep_discrete.fill [.binopL op ⟨v2, hv2⟩] h)

theorem limExec_binopR_step {op : BinOp} {e1 e e' : Exp} {σ σ' : State}
    (h : DetStep_discrete ⟨e, σ⟩ ⟨e', σ'⟩) :
    limExec ⟨.binop op e1 e, σ⟩ = limExec ⟨.binop op e1 e', σ'⟩ :=
  limExec_detStep (DetStep_discrete.fill [.binopR op e1] h)

theorem limExec_pairL_step {e e' v2 : Exp} (hv2 : IsVal v2) {σ σ' : State}
    (h : DetStep_discrete ⟨e, σ⟩ ⟨e', σ'⟩) :
    limExec ⟨.pair e v2, σ⟩ = limExec ⟨.pair e' v2, σ'⟩ :=
  limExec_detStep (DetStep_discrete.fill [.pairL ⟨v2, hv2⟩] h)

theorem limExec_pairR_step {e1 e e' : Exp} {σ σ' : State}
    (h : DetStep_discrete ⟨e, σ⟩ ⟨e', σ'⟩) :
    limExec ⟨.pair e1 e, σ⟩ = limExec ⟨.pair e1 e', σ'⟩ :=
  limExec_detStep (DetStep_discrete.fill [.pairR e1] h)

theorem limExec_appL_step {e e' v2 : Exp} (hv2 : IsVal v2) {σ σ' : State}
    (h : DetStep_discrete ⟨e, σ⟩ ⟨e', σ'⟩) :
    limExec ⟨.app e v2, σ⟩ = limExec ⟨.app e' v2, σ'⟩ :=
  limExec_detStep (DetStep_discrete.fill [.appL ⟨v2, hv2⟩] h)

theorem limExec_appR_step {ef e e' : Exp} {σ σ' : State}
    (h : DetStep_discrete ⟨e, σ⟩ ⟨e', σ'⟩) :
    limExec ⟨.app ef e, σ⟩ = limExec ⟨.app ef e', σ'⟩ :=
  limExec_detStep (DetStep_discrete.fill [.appR ef] h)

theorem limExec_fst_step {e e' : Exp} {σ σ' : State}
    (h : DetStep_discrete ⟨e, σ⟩ ⟨e', σ'⟩) :
    limExec ⟨.fst e, σ⟩ = limExec ⟨.fst e', σ'⟩ :=
  limExec_detStep (DetStep_discrete.fill [.fst] h)

theorem limExec_snd_step {e e' : Exp} {σ σ' : State}
    (h : DetStep_discrete ⟨e, σ⟩ ⟨e', σ'⟩) :
    limExec ⟨.snd e, σ⟩ = limExec ⟨.snd e', σ'⟩ :=
  limExec_detStep (DetStep_discrete.fill [.snd] h)

/-- Generic reducer for a binop on two literals: a single `BinOp.eval` evaluation
    is enough to obtain the `limExec` equation. Subsumes the old `limExec_*_lit_lit`
    family (plus, minus, mult, div, mod, lt, le, shr, shl, eq, and, or, xor). -/
theorem limExec_binop_lit_lit (op : BinOp) {l1 l2 : BaseLit} {r : Exp} {σ : State}
    (heval : BinOp.eval op (.lit l1) (.lit l2) = some r) :
    limExec ⟨.binop op (.lit l1) (.lit l2), σ⟩ = limExec ⟨r, σ⟩ := by
  have hnv : ¬ (Exp.binop op (.lit l1) (.lit l2)).isValue := by intro ⟨h⟩; cases h
  exact limExec_detHeadStep hnv (DetHeadStep_discrete.binop .lit .lit heval σ)

theorem limExec_plus_lit_lit (a b : Int) (σ : State) :
    limExec ⟨.binop .plus (.lit (.int a)) (.lit (.int b)), σ⟩
    = limExec ⟨.lit (.int (a + b)), σ⟩ :=
  limExec_binop_lit_lit .plus rfl

theorem limExec_minus_lit_lit (a b : Int) (σ : State) :
    limExec ⟨.binop .minus (.lit (.int a)) (.lit (.int b)), σ⟩
    = limExec ⟨.lit (.int (a - b)), σ⟩ :=
  limExec_binop_lit_lit .minus rfl

theorem limExec_mult_lit_lit (a b : Int) (σ : State) :
    limExec ⟨.binop .mult (.lit (.int a)) (.lit (.int b)), σ⟩
    = limExec ⟨.lit (.int (a * b)), σ⟩ :=
  limExec_binop_lit_lit .mult rfl

theorem limExec_div_lit_lit (a b : Int) (σ : State) :
    limExec ⟨.binop .div (.lit (.int a)) (.lit (.int b)), σ⟩
    = limExec ⟨.lit (.int (a / b)), σ⟩ :=
  limExec_binop_lit_lit .div rfl

theorem limExec_mod_lit_lit (a b : Int) (σ : State) :
    limExec ⟨.binop .mod (.lit (.int a)) (.lit (.int b)), σ⟩
    = limExec ⟨.lit (.int (a % b)), σ⟩ :=
  limExec_binop_lit_lit .mod rfl

theorem limExec_shr_lit_lit (a b : Int) (σ : State) :
    limExec ⟨.binop .shr (.lit (.int a)) (.lit (.int b)), σ⟩
    = limExec ⟨.lit (.int (a / 2 ^ b.toNat)), σ⟩ :=
  limExec_binop_lit_lit .shr rfl

theorem limExec_lt_lit_lit (a b : Int) (σ : State) :
    limExec ⟨.binop .lt (.lit (.int a)) (.lit (.int b)), σ⟩
    = limExec ⟨.lit (.bool (decide (a < b))), σ⟩ :=
  limExec_binop_lit_lit .lt rfl

/-- Single-step reduction: `fst (pair v1 v2)` → `v1`. -/
theorem limExec_fst_pair {e1 e2 : Exp} (h1 : IsVal e1) (h2 : IsVal e2) (σ : State) :
    limExec ⟨.fst (.pair e1 e2), σ⟩ = limExec ⟨e1, σ⟩ := by
  have hnv : ¬ (Exp.fst (.pair e1 e2)).isValue := by intro ⟨h⟩; cases h
  exact limExec_detHeadStep hnv (DetHeadStep_discrete.fst_pair h1 h2 σ)

/-- Single-step reduction: `snd (pair v1 v2)` → `v2`. -/
theorem limExec_snd_pair {e1 e2 : Exp} (h1 : IsVal e1) (h2 : IsVal e2) (σ : State) :
    limExec ⟨.snd (.pair e1 e2), σ⟩ = limExec ⟨e2, σ⟩ := by
  have hnv : ¬ (Exp.snd (.pair e1 e2)).isValue := by intro ⟨h⟩; cases h
  exact limExec_detHeadStep hnv (DetHeadStep_discrete.snd_pair h1 h2 σ)

/-- Cond reduction: applying `plProbNatRec_condE xs n` to `as_expr (idx, acc)`
    reduces to `lit (bool (decide (idx < n)))`. -/
theorem limExec_plProbNatRec_condE [ProbLangEmbeddable T]
    (xs : Var) (n idx : Nat) (acc : T) (σ : State)
    (nE : Exp) (hxs_nE : xs ∉ nE.fv) (hnE_lc : Exp.IsLocallyClosed nE)
    (hnE_red : ∀ σ', limExec ⟨nE, σ'⟩ = dirac ⟨.lit (.int n), σ'⟩) :
    limExec ⟨.app (plProbNatRec_condE xs nE) (as_expr ((idx, acc) : Nat × T)), σ⟩
    = dirac ⟨.lit (.bool (decide ((idx : Int) < (n : Int)))), σ⟩ := by
  show limExec ⟨.app (plProbNatRec_condE xs nE) (.pair (.lit (.int idx)) (as_expr acc)), σ⟩ = _
  have hpairval : IsVal (.pair (.lit (.int idx)) (as_expr acc) : Exp) :=
    .pair .lit (as_expr_isVal acc)
  have hpair_lc : Exp.IsLocallyClosed
      (.pair (.lit (.int idx)) (as_expr acc) : Exp) := .pair (.lit _) (as_expr_lc _)
  have hbody_lc : Exp.IsLocallyClosed (.binop .lt (.fst (.fvar xs)) nE) :=
    .binop _ (.fst (.fvar _)) hnE_lc
  -- β-reduce, then push subst inside.
  unfold plProbNatRec_condE
  rw [limExec_beta hpairval, Exp.open_close_subst_lc_gen xs _ _ hbody_lc hpair_lc]
  have hsubst : Exp.subst (.binop .lt (.fst (.fvar xs)) nE) xs
        (.pair (.lit (.int idx)) (as_expr acc))
      = .binop .lt (.fst (.pair (.lit (.int idx)) (as_expr acc))) nE := by
    show Exp.binop _ _ _ = Exp.binop _ _ _
    simp [Exp.subst, Exp.subst_fresh xs nE _ hxs_nE]
  rw [hsubst]
  -- Reduce `nE` first (under `binopR .lt _`), giving `binop .lt (fst pair) (lit n)`.
  rw [show (Exp.binop .lt (.fst (.pair (.lit (.int idx)) (as_expr acc))) nE)
        = EctxItem.fillItem (.binopR .lt _) nE from rfl,
      limExec_fill_item, hnE_red σ, Measure.dirac_bind Measurable.of_discrete]
  show limExec ⟨.binop .lt (.fst (.pair (.lit (.int idx)) (as_expr acc))) (.lit (.int n)), σ⟩ = _
  -- Reduce `fst pair → lit idx`, then the final binop, then collapse to dirac.
  rw [limExec_binopL_step .lit
        (DetHeadStep_discrete.fst_pair .lit (as_expr_isVal acc) σ).toDetStep,
      limExec_lt_lit_lit, limExec_of_isVal IsVal.lit]

/-- Body-side embedding: `app bodyE (as_expr (idx, acc))` embeds `probNatRec_bodyUp step (idx, acc)`.
    This requires freshness conditions on `xs`, `ws` w.r.t. the value-form `as_expr`. -/
theorem plProbNatRec_bodyE_isEmbedding [SLangType T] [ProbLangEmbeddable T]
    {xs ws : Var} {stepE : Exp} {step : Nat → T → SLang T}
    (hxs_ws : xs ≠ ws)
    (hstepE_lc : Exp.IsLocallyClosed stepE)
    (hxs_step : xs ∉ stepE.fv) (hws_step : ws ∉ stepE.fv)
    (hxs_acc : ∀ a : T, xs ∉ (as_expr a).fv)
    (hws_acc : ∀ a : T, ws ∉ (as_expr a).fv)
    (hstep_emb : ∀ k a,
      IsEmbedding (step k a) (.app (.app stepE (as_expr k)) (as_expr a)))
    (idx : Nat) (acc : T) :
    IsEmbedding (probNatRec_bodyUp step (idx, acc))
                (.app (plProbNatRec_bodyE xs ws stepE) (as_expr ((idx, acc) : Nat × T))) := by
  -- Step 1: the SLang body unfolds.
  show IsEmbedding (probBind (step idx acc) (fun acc' => probPure ((idx + 1, acc') : Nat × T))) _
  -- Step 2: as_expr (idx, acc) = .pair (.lit (.int idx)) (as_expr acc).
  have has_expr_eq : (as_expr ((idx, acc) : Nat × T) : Exp)
      = .pair (.lit (.int idx)) (as_expr acc) := rfl
  rw [has_expr_eq]
  set pair_expr : Exp := .pair (.lit (.int idx)) (as_expr acc) with hpair_expr_def
  have hpair_isVal : IsVal pair_expr := .pair .lit (as_expr_isVal acc)
  have hpair_lc : Exp.IsLocallyClosed pair_expr := .pair (.lit _) (as_expr_lc _)
  have hxs_pair : xs ∉ pair_expr.fv := by
    simp only [hpair_expr_def, Exp.fv, Finset.mem_union, not_or]
    exact ⟨by simp [Exp.fv], hxs_acc acc⟩
  have hws_pair : ws ∉ pair_expr.fv := by
    simp only [hpair_expr_def, Exp.fv, Finset.mem_union, not_or]
    exact ⟨by simp [Exp.fv], hws_acc acc⟩
  -- Step 3: β-reduce. bodyE = .lam (close BodyInner xs).
  unfold plProbNatRec_bodyE
  set InnerArg : Exp := .app (.app stepE (.fst (.fvar xs))) (.snd (.fvar xs)) with hInnerArg_def
  set PairExp : Exp :=
    .pair (.binop .plus (.fst (.fvar xs)) (.lit (.int 1))) (.fvar ws) with hPairExp_def
  have hInnerArg_lc : Exp.IsLocallyClosed InnerArg :=
    .app (.app hstepE_lc (.fst (.fvar _))) (.snd (.fvar _))
  have hPairExp_lc : Exp.IsLocallyClosed PairExp :=
    .pair (.binop _ (.fst (.fvar _)) (.lit _)) (.fvar _)
  have hBodyInner_lc : Exp.IsLocallyClosed (probLangBind ws InnerArg PairExp) := by
    unfold probLangBind
    refine .app (Exp.IsLocallyClosed.lam (insert ws PairExp.fv) _ (fun y _ => ?_)) hInnerArg_lc
    rw [Exp.open_close_subst_lc ws y PairExp hPairExp_lc]
    exact Exp.subst_lc hPairExp_lc (.fvar _)
  -- One β step.
  refine IsEmbedding.of_detHeadStep
    (e' := Exp.subst (probLangBind ws InnerArg PairExp) xs pair_expr)
    (fun σ => ⟨?_, ?_⟩) ?_
  · -- ¬ isValue
    intro ⟨h⟩; cases h
  · -- DetHeadStep_discrete
    have h := DetHeadStep_discrete.app_lam hpair_isVal σ
      (body := Exp.close (probLangBind ws InnerArg PairExp) xs)
    rw [Exp.open_close_subst_lc_gen xs _ _ hBodyInner_lc hpair_lc] at h
    exact h
  -- Step 4: compute the substitution. subst (probLangBind ws E1 E2) xs pair_expr
  -- = probLangBind ws (subst E1 xs pair_expr) (subst E2 xs pair_expr).
  have hsubst_bind : Exp.subst (probLangBind ws InnerArg PairExp) xs pair_expr
      = probLangBind ws (Exp.subst InnerArg xs pair_expr) (Exp.subst PairExp xs pair_expr) := by
    unfold probLangBind
    show Exp.subst (.app _ _) xs _ = .app _ _
    simp only [Exp.subst]
    congr 1
    rw [Exp.subst_close xs ws pair_expr PairExp hxs_ws hws_pair]
  rw [hsubst_bind]
  -- Step 5: compute subst InnerArg xs pair_expr.
  have hsubst_innerArg : Exp.subst InnerArg xs pair_expr
      = .app (.app stepE (.fst pair_expr)) (.snd pair_expr) := by
    rw [hInnerArg_def]
    simp only [Exp.subst]
    rw [Exp.subst_fresh xs stepE pair_expr hxs_step]
    simp [Exp.subst]
  -- Step 6: compute subst PairExp xs pair_expr.
  have hsubst_pairExp : Exp.subst PairExp xs pair_expr
      = .pair (.binop .plus (.fst pair_expr) (.lit (.int 1))) (.fvar ws) := by
    rw [hPairExp_def]
    show Exp.pair _ _ = Exp.pair _ _
    simp only [Exp.subst, if_pos rfl, if_neg hxs_ws]
    simp
  rw [hsubst_innerArg, hsubst_pairExp]
  -- Step 7: apply probLangBind_isEmbedding.
  refine probLangBind_isEmbedding (x := ws) ?_ ?_ ?_
  · -- LC of the outer body (after subst).
    exact .pair (.binop _ (.fst hpair_lc) (.lit _)) (.fvar _)
  · -- IsEmbedding of inner: app (app stepE (fst pair)) (snd pair).
    -- Reduce snd-pair → as_expr acc (under appR), then fst-pair → lit idx (under appR · appL).
    refine IsEmbedding.of_limExec_eq (fun σ => ?_) (hstep_emb idx acc)
    have hstepFst : DetStep_discrete ⟨.app stepE (.fst pair_expr), σ⟩
                            ⟨.app stepE (.lit (.int idx)), σ⟩ := by
      rw [hpair_expr_def]
      exact DetStep_discrete.fill [.appR stepE]
        (DetHeadStep_discrete.fst_pair .lit (as_expr_isVal acc) σ).toDetStep
    rw [hpair_expr_def,
        limExec_appR_step (DetHeadStep_discrete.snd_pair .lit (as_expr_isVal acc) σ).toDetStep,
        ← hpair_expr_def,
        limExec_appL_step (as_expr_isVal acc) hstepFst]
    rfl
  · -- IsEmbedding of outer: subst (pair (binop plus (fst pair) (lit 1)) (fvar ws)) ws (as_expr t)
    --                        = pair (binop plus (fst pair) (lit 1)) (as_expr t).
    -- Need IsEmbedding (pure (idx+1, t)) (pair (binop plus (fst pair) (lit 1)) (as_expr t)).
    -- This det-reduces (under pairL ectx) to pair (lit (idx+1)) (as_expr t) = as_expr (idx+1, t).
    intro acc'
    -- Compute the substitution.
    have hsubst_outer : Exp.subst (.pair (.binop .plus (.fst pair_expr) (.lit (.int 1))) (.fvar ws))
                          ws (as_expr acc')
        = .pair (.binop .plus (.fst pair_expr) (.lit (.int 1))) (as_expr acc') := by
      simp only [Exp.subst]
      have h1 : Exp.subst pair_expr ws (as_expr acc') = pair_expr := by
        exact Exp.subst_fresh ws pair_expr (as_expr acc') hws_pair
      rw [h1]
      simp
    rw [hsubst_outer]
    -- Want: IsEmbedding (pure (idx+1, acc')) (pair (binop plus (fst pair) (lit 1)) (as_expr acc')).
    -- Apply IsEmbedding.of_limExec_eq + det reductions.
    show IsEmbedding (probPure ((idx + 1, acc') : Nat × T)) _
    refine IsEmbedding.of_limExec_eq (fun σ => ?_) probLangPure_isEmbedding
    -- Goal: limExec ⟨pair (binop plus (fst pair) (lit 1)) (as_expr acc'), σ⟩
    --     = limExec ⟨as_expr (idx+1, acc'), σ⟩, where as_expr (idx+1, acc') = pair (lit (idx+1)) (as_expr acc').
    rw [hpair_expr_def]
    -- Step 1: build the `DetStep_discrete` for `binop plus (fst pair) (lit 1) → binop plus (lit idx) (lit 1)`.
    have hFst : DetStep_discrete ⟨Exp.fst (.pair (.lit (.int idx)) (as_expr acc)), σ⟩
                        ⟨.lit (.int idx), σ⟩ :=
      (DetHeadStep_discrete.fst_pair .lit (as_expr_isVal acc) σ).toDetStep
    have hBinop : DetStep_discrete
        ⟨.binop .plus (.fst (.pair (.lit (.int idx)) (as_expr acc))) (.lit (.int 1)), σ⟩
        ⟨.binop .plus (.lit (.int idx)) (.lit (.int 1)), σ⟩ :=
      DetStep_discrete.fill [.binopL .plus (.int 1)] hFst
    rw [limExec_pairL_step (as_expr_isVal acc') hBinop]
    -- Step 2: binop plus → lit (idx+1), under pairL.
    rw [limExec_pairL_step (as_expr_isVal acc')
          (DetHeadStep_discrete.binop (op := .plus) (e1 := .lit (.int idx)) (e2 := .lit (.int 1))
             .lit .lit rfl σ).toDetStep]
    -- Final: pair (lit (idx+1)) (as_expr acc') = as_expr (idx+1, acc') (defeq up to Int cast).
    have hidx_plus : (idx : Int) + 1 = ((idx + 1 : Nat) : Int) := by push_cast; ring
    show limExec ⟨.pair (.lit (.int ((idx : Int) + 1))) (as_expr acc'), σ⟩ = _
    rw [hidx_plus]; rfl

/-! ### Main embedding theorem for the generic combinator

  Composes `probLangBind_isEmbedding` (outer projection) with
  `probLangWhile_isEmbedding` (inner loop) and the cond/body reductions above. -/
theorem plProbNatRec_loop_isEmbedding [SLangType T] [ProbLangEmbeddable T]
    {f x v xs ws w : Var} {n : Nat} {base : T} {step : Nat → T → SLang T} {stepE : Exp}
    {nE : Exp}
    (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    (hxs_ws : xs ≠ ws) (_hxs_w : xs ≠ w) (hws_w : ws ≠ w)
    (hxsf : xs ≠ f) (hxsx : xs ≠ x) (hxsv : xs ≠ v)
    (hwsf : ws ≠ f) (hwsx : ws ≠ x) (hwsv : ws ≠ v)
    (_hwf : w ≠ f) (_hwx : w ≠ x) (_hwv : w ≠ v)
    (hstepE_lc : Exp.IsLocallyClosed stepE)
    (hxs_step : xs ∉ stepE.fv) (hws_step : ws ∉ stepE.fv)
    (hf_step : f ∉ stepE.fv) (hx_step : x ∉ stepE.fv) (hv_step : v ∉ stepE.fv)
    (hnE_lc : Exp.IsLocallyClosed nE)
    (hnE_red : ∀ σ, limExec ⟨nE, σ⟩ = dirac ⟨.lit (.int n), σ⟩)
    (hxs_nE : xs ∉ nE.fv) (hf_nE : f ∉ nE.fv) (hx_nE : x ∉ nE.fv) (hv_nE : v ∉ nE.fv)
    (hxs_acc : ∀ a : (Nat × T), xs ∉ (as_expr a).fv)
    (hws_acc : ∀ a : (Nat × T), ws ∉ (as_expr a).fv)
    (hf_acc : ∀ a : (Nat × T), f ∉ (as_expr a).fv)
    (hx_acc : ∀ a : (Nat × T), x ∉ (as_expr a).fv)
    (hv_acc : ∀ a : (Nat × T), v ∉ (as_expr a).fv)
    (hw_acc : ∀ a : T, w ∉ (as_expr a).fv)
    (hstep_emb : ∀ k acc,
      IsEmbedding (step k acc) (.app (.app stepE (as_expr k)) (as_expr acc))) :
    IsEmbedding (probNatRec_loopUp base step n)
                (plProbNatRec_loop f x v xs ws w nE base stepE) := by
  unfold probNatRec_loopUp plProbNatRec_loop
  -- For the bind: `bind probWhile (fun s => pure s.2)` ↔ `probLangBind w probLangWhile (.snd (.fvar w))`.
  apply probLangBind_isEmbedding (x := w)
  · -- LC of .snd (.fvar w).
    exact .snd (.fvar _)
  · -- IsEmbedding (probWhile ...) (probLangWhile f x v condE bodyE init).
    -- Helpers: condE/bodyE freshness for any var fresh wrt xs/ws/stepE.
    have hcondE_fresh : ∀ a : Var, a ≠ xs → a ∉ nE.fv →
        a ∉ (plProbNatRec_condE xs nE).fv := by
      intro a ha ha_nE
      unfold plProbNatRec_condE
      simp only [Exp.fv]
      apply Exp.close_preserve_not_fvar
      simp only [Exp.fv, Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨ha, ha_nE⟩
    have hbodyE_fresh : ∀ a : Var, a ∉ stepE.fv → a ≠ xs → a ≠ ws →
        a ∉ (plProbNatRec_bodyE xs ws stepE).fv := by
      intro a ha_step ha_xs ha_ws
      unfold plProbNatRec_bodyE
      simp only [Exp.fv]
      apply Exp.close_preserve_not_fvar
      unfold probLangBind
      simp only [Exp.fv, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
                 false_or, or_false, not_or, not_false_iff]
      have hclose_pair : a ∉ ((Exp.pair (.binop .plus (.fst (.fvar xs)) (.lit (.int 1)))
            (.fvar ws)).close ws).fv := by
        apply Exp.close_preserve_not_fvar
        simp only [Exp.fv, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
                   false_or, or_false, not_or, not_false_iff]
        tauto
      tauto
    -- Apply probLangWhile_isEmbedding at type ℕ × T.
    refine probLangWhile_isEmbedding (T := Nat × T) (init := (0, base))
      hfx hfv hxv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · -- LC of condE = plProbNatRec_condE xs nE.
      unfold plProbNatRec_condE
      refine .lam ∅ _ (fun y _ => ?_)
      have hbody_lc : Exp.IsLocallyClosed (.binop .lt (.fst (.fvar xs)) nE) :=
        .binop _ (.fst (.fvar _)) hnE_lc
      rw [Exp.open_close_subst_lc xs y _ hbody_lc]
      exact Exp.subst_lc hbody_lc (.fvar _)
    · -- LC of bodyE.
      unfold plProbNatRec_bodyE probLangBind
      have hInner_lc : Exp.IsLocallyClosed
          (.app (.lam (Exp.close (.pair (.binop .plus (.fst (.fvar xs)) (.lit (.int 1))) (.fvar ws)) ws))
                (.app (.app stepE (.fst (.fvar xs))) (.snd (.fvar xs)))) := by
        refine .app ?_ (.app (.app hstepE_lc (.fst (.fvar _))) (.snd (.fvar _)))
        refine .lam ∅ _ (fun z _ => ?_)
        rw [Exp.open_close_subst_lc ws z _ (by exact .pair (.binop _ (.fst (.fvar _)) (.lit _)) (.fvar _))]
        exact Exp.subst_lc (.pair (.binop _ (.fst (.fvar _)) (.lit _)) (.fvar _)) (.fvar _)
      refine .lam ∅ _ (fun y _ => ?_)
      rw [Exp.open_close_subst_lc xs y _ hInner_lc]
      exact Exp.subst_lc hInner_lc (.fvar _)
    · exact hcondE_fresh f hxsf.symm hf_nE
    · exact hbodyE_fresh f hf_step hxsf.symm hwsf.symm
    · exact hcondE_fresh x hxsx.symm hx_nE
    · exact hbodyE_fresh x hx_step hxsx.symm hwsx.symm
    · exact hcondE_fresh v hxsv.symm hv_nE
    · exact hbodyE_fresh v hv_step hxsv.symm hwsv.symm
    · -- f ∉ as_expr.fv: we have hf_acc.
      exact hf_acc
    · -- x ∉ as_expr.fv: hx_acc.
      exact hx_acc
    · -- v ∉ as_expr.fv: hv_acc.
      exact hv_acc
    · -- hcond: ∀ s σ, limExec ⟨app condE (as_expr s), σ⟩ = dirac ⟨lit (bool (cond s)), σ⟩.
      intro ⟨idx, acc⟩ σ
      show limExec _ = dirac ⟨.lit (.bool (decide (idx < n))), σ⟩
      have h := limExec_plProbNatRec_condE (T := T) xs n idx acc σ nE hxs_nE hnE_lc hnE_red
      have hcast : decide ((idx : Int) < (n : Int)) = decide (idx < n) := by
        congr 1
        exact propext (by exact_mod_cast Iff.rfl)
      rw [hcast] at h
      exact h
    · -- hbody: ∀ s, IsEmbedding (probNatRec_bodyUp step s) (app bodyE (as_expr s)).
      intro ⟨idx, acc⟩
      exact plProbNatRec_bodyE_isEmbedding hxs_ws hstepE_lc hxs_step hws_step
        (fun a => by
          -- xs ∉ as_expr a.fv where a : T. We have hxs_acc for Nat × T.
          have := hxs_acc (0, a)
          simp only [as_expr, Exp.fv, Finset.mem_union, not_or] at this
          exact this.2)
        (fun a => by
          have := hws_acc (0, a)
          simp only [as_expr, Exp.fv, Finset.mem_union, not_or] at this
          exact this.2)
        hstep_emb idx acc
  · -- IsEmbedding of outer-bind body: ∀ s : Nat × T,
    --   IsEmbedding (pure s.2) (subst (.snd (.fvar w)) w (as_expr s)).
    intro ⟨idx, acc⟩
    -- subst (.snd (.fvar w)) w (as_expr (idx, acc)) = .snd (as_expr (idx, acc)) = .snd (pair (lit idx) (as_expr acc)).
    show IsEmbedding (probPure acc) (Exp.subst (.snd (.fvar w)) w (as_expr ((idx, acc) : Nat × T)))
    have hsubst : Exp.subst (.snd (.fvar w)) w (as_expr ((idx, acc) : Nat × T))
        = .snd (as_expr ((idx, acc) : Nat × T)) := by
      simp [Exp.subst]
    rw [hsubst]
    -- limExec ⟨snd (pair (lit idx) (as_expr acc)), σ⟩ = limExec ⟨as_expr acc, σ⟩ via det.
    refine IsEmbedding.of_limExec_eq (fun σ => ?_) probLangPure_isEmbedding
    show limExec ⟨.snd (.pair (.lit (.int idx)) (as_expr acc)), σ⟩ = _
    rw [limExec_snd_pair .lit (as_expr_isVal acc)]
    rfl

/-! ## Proof of concept: closed equivalence example -/

/-- SLang program: sample two random bytes, compare for equality, return the Bool result. -/
def twoByteEq : SLang Bool := do
  let a ← probUniformByte
  let b ← probUniformByte
  return (a == b)

-- Bool instances for embedding
instance : Countable Bool := inferInstance
instance : MeasurableSpace Bool := ⊤
instance : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

instance : ProbLangEmbeddable Bool where
  as_expr b := .lit (.bool b)
  as_expr_isVal _ := .lit
  as_expr_lc _ := .lit _
  as_expr_fv _ := rfl

/-- ProbLang translation: `let a := rand 255 (); let b := rand 255 (); a = b`. -/
def plTwoByteEq : Exp :=
  probLangBind "a" probLangUniformByte $
    probLangBind "b" probLangUniformByte $
      probLangEq (.fvar "a") (.fvar "b")

-- The ProbLang equality operator on embedded UInt8 values computes the same Bool.
-- After substitution, probLangEq (as_expr a) (as_expr b) = .binop .eq (.lit (.int a.toNat)) (.lit (.int b.toNat))
-- which steps to .lit (.bool (decide (a.toNat = b.toNat))), i.e. .lit (.bool (a == b)) = as_expr (a == b).

theorem probLangEq_uint8_isEmbedding (a b : UInt8) :
    IsEmbedding (probPure (a == b)) (probLangEq (as_expr a) (as_expr b)) := by
  intro σ
  show limExec ⟨.binop .eq (.lit (.int a.toNat)) (.lit (.int b.toNat)), σ⟩ = _
  have hnv : ¬ (Exp.binop .eq (.lit (.int ↑a.toNat)) (.lit (.int ↑b.toNat))).isValue := by
    intro ⟨h⟩; cases h
  rw [limExec_not_final hnv]
  set result := Exp.lit (.bool (decide (BaseLit.int ↑a.toNat = BaseLit.int ↑b.toNat))) with result_def
  have heval : BinOp.eval .eq (.lit (.int ↑a.toNat)) (.lit (.int ↑b.toNat)) = some result := by
    simp [BinOp.eval, result]
  have hred : ∃ ρ, 0 < headStep ⟨.binop .eq (.lit (.int ↑a.toNat)) (.lit (.int ↑b.toNat)), σ⟩ {ρ} :=
    ⟨⟨result, σ⟩, (DetHeadStep_discrete.binop .lit .lit heval σ).pos⟩
  rw [primStep_eq_headStep_discrete hred]
  show (headStep ⟨.binop .eq (.lit (.int ↑a.toNat)) (.lit (.int ↑b.toNat)), σ⟩).bind limExec = _
  simp only [headStep, Exp.isValM_some' IsVal.lit, heval, Option.unwrapM,
    Measure.dirac_bind Measurable.of_discrete]
  have beq_eq : decide (BaseLit.int ↑a.toNat = BaseLit.int ↑b.toNat) = (a == b) := by
    simp only [BaseLit.int.injEq, Nat.cast_inj]
    congr 1; exact propext ⟨UInt8.ext, congrArg _⟩
  show limExec ⟨.lit (.bool (decide (BaseLit.int ↑a.toNat = BaseLit.int ↑b.toNat))), σ⟩ = _
  rw [beq_eq]
  refine Eq.trans ?_ (probLangPure_isEmbedding σ)
  congr

/-- Main theorem: plTwoByteEq is an embedding of twoByteEq. -/
theorem twoByteEq_isEmbedding : IsEmbedding twoByteEq plTwoByteEq := by
  unfold twoByteEq plTwoByteEq
  show IsEmbedding (probBind probUniformByte fun a => probBind probUniformByte fun b => probPure (a == b)) _
  -- Outer bind: `let a := byte; <body>`
  apply probLangBind_isEmbedding
  · -- hbody : LC of the outer body = `probLangBind 1 byte (eq (fvar 0) (fvar 1))`
    -- This is `app (lam (close (eq (fvar 0) (fvar 1)) 1)) byte`. All literals + binops + lam → LC.
    unfold probLangBind probLangUniformByte probLangEq
    refine .app (.lam ∅ _ (fun _ _ => ?_)) (.rand (.lit _) (.lit _))
    -- After opening the lam at fresh y: open' (close (eq (fvar 0) (fvar 1)) 1) (fvar y)
    -- = subst (eq (fvar 0) (fvar 1)) 1 (fvar y) by open_close_subst_lc.
    -- = eq (fvar 0) (fvar y). Both args are fvar → LC.
    rw [Exp.open_close_subst_lc]
    · exact .binop _ (.fvar _) (.fvar _)
    · exact .binop _ (.fvar _) (.fvar _)
  · -- h1 : IsEmbedding probUniformByte probLangUniformByte
    exact probLangUniformByte_isEmbedding
  · -- h2 : ∀ a, IsEmbedding (...) (subst <body> "a" (as_expr a))
    intro a
    have hgoal : Exp.subst (probLangBind "b" probLangUniformByte
                              (probLangEq (.fvar "a") (.fvar "b"))) "a" (as_expr a)
        = probLangBind "b" probLangUniformByte (probLangEq (as_expr a) (.fvar "b")) := by
      unfold probLangBind probLangUniformByte probLangEq
      simp only [Exp.subst, Exp.close, Exp.closeRec]
      rfl
    rw [hgoal]
    apply probLangBind_isEmbedding
    · exact .binop _ (as_expr_lc a) (.fvar _)
    · exact probLangUniformByte_isEmbedding
    · intro b
      have ha_subst : Exp.subst (as_expr a) "b" (as_expr b) = as_expr a := by
        apply Exp.subst_fresh
        intro h; simp [Exp.fv] at h
      have hgoal2 : Exp.subst (probLangEq (as_expr a) (.fvar "b")) "b" (as_expr b)
          = probLangEq (as_expr a) (as_expr b) := by
        unfold probLangEq
        simp only [Exp.subst]
        rfl
      rw [hgoal2]
      exact probLangEq_uint8_isEmbedding a b

end EmbedSLang
end
