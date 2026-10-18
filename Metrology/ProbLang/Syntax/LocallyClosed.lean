module

public import Metrology.ProbLang.Syntax.Syntax
public meta import Lean.Elab.Tactic.Basic

@[expose] public section

/-!
# Locally-nameless theory for `Exp`

Mirrors `cslib/Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/Properties.lean`.
-/

namespace ProbLang

open Cslib Exp

namespace Exp

variable {rT : Type _}
variable {x y : Var} {e e' u t : Exp rT}

theorem openRec_aux (e : Exp rT) (j v i u) (neq : i ≠ j)
    (heq : openRec j v e = openRec i u (openRec j v e)) : e = openRec i u e := by
  induction e generalizing i j <;> grind

theorem openRec_openRec_comm (k n : Nat) (x y : Var) (e : Exp rT) (neq : k ≠ n) :
    openRec k (fvar x) (openRec n (fvar y) e) = openRec n (fvar y) (openRec k (fvar x) e) := by
  induction e generalizing k n <;> grind

@[scoped grind =]
theorem subst_fresh (x : Var) (e sub : Exp rT) (h : x ∉ e.fv) :
    subst e x sub = e := by
  induction e <;> grind

theorem closeRec_openRec (x : Var) (e : Exp rT) (k : Nat) (h : x ∉ e.fv) :
    e = closeRec k x (openRec k (fvar x) e) := by
  induction e generalizing k <;> grind

theorem close_open (x : Var) (e : Exp rT) (h : x ∉ e.fv) :
    e = close (open' e (fvar x)) x :=
  closeRec_openRec x e 0 h

theorem open_inj (x : Var) (e e' : Exp rT) (hx : x ∉ e.fv) (hx' : x ∉ e'.fv)
    (heq : open' e (fvar x) = open' e' (fvar x)) : e = e' := by
  grind [closeRec_openRec x e 0 hx, closeRec_openRec x e' 0 hx']

theorem swap_open_fvar_close (k n : Nat) (x y : Var) (e : Exp rT)
    (hk : k ≠ n) (hxy : x ≠ y) :
    closeRec k x (openRec n (fvar y) e)
      = openRec n (fvar y) (closeRec k x e) := by
  induction e generalizing k n <;> grind

theorem close_preserve_not_fvar {k x y} (e : Exp rT) (h : x ∉ e.fv) :
    x ∉ (closeRec k y e).fv := by
  induction e generalizing k <;> grind

theorem open_fresh_preserve_not_fvar {k x y} (e : Exp rT) (h : x ∉ e.fv) (hne : x ≠ y) :
    x ∉ (openRec k (fvar y) e).fv := by
  induction e generalizing k <;> grind

theorem open_preserve_not_fvar {k x} (e u : Exp rT) (he : x ∉ e.fv) (hu : x ∉ u.fv) :
    x ∉ (openRec k u e).fv := by
  induction e generalizing k <;> grind

theorem subst_preserve_not_fvar {x y : Var} (e u : Exp rT)
    (h : x ∉ e.fv ∪ u.fv) : x ∉ (subst e y u).fv := by
  induction e <;> grind

theorem fv_subst_subset (e : Exp rT) (x : Var) (v : Exp rT) :
    (subst e x v).fv ⊆ (e.fv \ {x}) ∪ v.fv := by
  intro z hz
  induction e with
  | fvar y =>
      by_cases hxy : x = y
      · subst hxy; simp [subst] at hz; exact Finset.mem_union_right _ hz
      · simp [subst, hxy] at hz; subst hz
        refine Finset.mem_union_left _ ?_
        simp; exact fun h => hxy h.symm
  | _ => simp [subst, fv] at * <;> tauto

@[scoped grind ←]
theorem close_var_not_fvar_rec (x) (k) (e : Exp rT) : x ∉ (closeRec k x e).fv := by
  induction e generalizing k <;> grind

theorem close_var_not_fvar (x : Var) (e : Exp rT) : x ∉ (close e x).fv :=
  close_var_not_fvar_rec x 0 e

@[scoped grind =_]
theorem open_lc (k : Nat) (t : Exp rT) (e : Exp rT) (he : e.IsLocallyClosed) :
    e = openRec k t e := by
  induction he generalizing k with
  | lam L e _ ih | fix L e _ ih =>
      obtain ⟨x, hx⟩ := HasFresh.fresh_exists L
      grind [openRec_aux e 0 (fvar x) (k+1) t]
  | _ => grind

@[scoped grind =]
theorem subst_openRec (x : Var) (t : Exp rT) (k : Nat) (u e : Exp rT) (hu : IsLocallyClosed t) :
    subst (openRec k u e) x t = openRec k (subst u x t) (subst e x t) := by
  induction e generalizing k with grind

theorem closeRec_fresh (x : Var) (e : Exp rT) (k : Nat) (h : x ∉ e.fv) :
    closeRec k x e = e := by
  induction e generalizing k <;> grind

@[scoped grind =]
theorem subst_closeRec (x y : Var) (t : Exp rT) (k : Nat) (e : Exp rT) (hxy : x ≠ y)
    (ht : y ∉ t.fv) :
    subst (closeRec k y e) x t = closeRec k y (subst e x t) := by
  induction e generalizing k with grind [closeRec_fresh]

theorem subst_close (x y : Var) (t : Exp rT) (e : Exp rT) (hxy : x ≠ y) (ht : y ∉ t.fv) :
    subst (close e y) x t = close (subst e x t) y :=
  subst_closeRec x y t 0 e hxy ht

theorem subst_open (x : Var) (t : Exp rT) (u e : Exp rT) (hu : IsLocallyClosed t) :
    subst (open' e u) x t = open' (subst e x t) (subst u x t) := by grind

theorem subst_open_var (x y : Var) (u e : Exp rT) (hne : y ≠ x) (hu : IsLocallyClosed u) :
    subst (open' e (fvar x)) y u = open' (subst e y u) (fvar x) := by grind

@[scoped grind ←]
theorem subst_lc {x : Var} {e u : Exp rT} (he : IsLocallyClosed e) (hu : IsLocallyClosed u)
    : IsLocallyClosed (subst e x u) := by
  induction he with
  | lam L e _ ih =>
      apply IsLocallyClosed.lam (free_union Var)
      intro y hy
      have hyL : y ∉ L := by grind
      have hyx : y ≠ x := by grind
      grind [subst_open_var]
  | fix L e _ ih =>
      apply IsLocallyClosed.fix (free_union Var)
      intro y hy
      have hyL : y ∉ L := by grind
      have hyx : y ≠ x := by grind
      grind [subst_open_var]
  | _ => grind

theorem subst_intro (x : Var) (t e : Exp rT) (mem : x ∉ e.fv) (t_lc : IsLocallyClosed t) :
    open' e t = subst (open' e (fvar x)) x t := by
  grind

theorem beta_lc (L : Finset Var) (e u : Exp rT)
    (he : ∀ x ∉ L, IsLocallyClosed (open' e (fvar x))) (hu : IsLocallyClosed u) :
    IsLocallyClosed (open' e u) := by
  obtain ⟨x, hx⟩ := HasFresh.fresh_exists (L ∪ e.fv)
  have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
  have hxfv : x ∉ e.fv := fun h => hx (Finset.mem_union_right _ h)
  grind [subst_intro x u e hxfv hu, subst_lc (he x hxL) hu]

private theorem openRec_closeRec_binder {L : Finset Var} {t : Exp rT} {x y : Var} {k : Nat}
    (ih : ∀ z ∉ L, ∀ k, openRec k (fvar y) (closeRec k x (open' t (fvar z)))
      = subst (open' t (fvar z)) x (fvar y)) :
    openRec (k+1) (fvar y) (closeRec (k+1) x t) = subst t x (fvar y) := by
  obtain ⟨z, hz⟩ := HasFresh.fresh_exists (L ∪ t.fv ∪ {x, y})
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨⟨hzL, hzt⟩, hzx, hzy⟩ := hz
  have hzL' : z ∉ (openRec (k+1) (fvar y) (closeRec (k+1) x t)).fv :=
    open_fresh_preserve_not_fvar _ (close_preserve_not_fvar _ hzt) hzy
  have hzR : z ∉ (subst t x (fvar y)).fv :=
    subst_preserve_not_fvar _ _ (by simp [fv, hzt, hzy])
  refine open_inj z _ _ hzL' hzR ?_
  calc open' (openRec (k+1) (fvar y) (closeRec (k+1) x t)) (fvar z)
      = openRec (k+1) (fvar y) (closeRec (k+1) x (open' t (fvar z))) := by
        simp only [open']
        rw [openRec_openRec_comm 0 (k+1) z y _ (by omega),
          swap_open_fvar_close (k+1) 0 x z t (by omega) (Ne.symm hzx)]
    _ = subst (open' t (fvar z)) x (fvar y) := ih z hzL (k+1)
    _ = open' (subst t x (fvar y)) (fvar z) := subst_open_var z x (fvar y) t (Ne.symm hzx) (.fvar y)

@[scoped grind =]
theorem open_close_to_subst (e : Exp rT) (x y : Var) (k : Nat) (he : IsLocallyClosed e) :
    openRec k (fvar y) (closeRec k x e) = subst e x (fvar y) := by
  induction he generalizing k with
  | lam L t _ ih | fix L t _ ih =>
      simp only [closeRec, openRec, subst]
      congr 1
      exact openRec_closeRec_binder ih
  | _ => grind

theorem open_close_subst_lc (x y : Var) (e : Exp rT) (he : IsLocallyClosed e) :
    open' (close e x) (fvar y) = subst e x (fvar y) :=
  open_close_to_subst e x y 0 he

/-- The shape `unpack` contexts produce: `CtxItem.fill (.unpackR x e₁) e = app (lam (close e x)) e₁`. -/
theorem open_close_isLocallyClosed {e : Exp rT} (x y : Var) (he : IsLocallyClosed e) :
    (Exp.open' (Exp.close e x) (Exp.fvar y)).IsLocallyClosed := by
  rw [open_close_subst_lc x y e he]
  exact subst_lc he (IsLocallyClosed.fvar y)

theorem open_close_subst_lc_gen (x : Var) (e v : Exp rT)
    (he : IsLocallyClosed e) (hv : IsLocallyClosed v) :
    open' (close e x) v = subst e x v := by
  obtain ⟨z, hz⟩ := HasFresh.fresh_exists (insert x (e.fv ∪ v.fv))
  have hzx : z ≠ x := fun h => hz (h ▸ Finset.mem_insert_self _ _)
  have hze : z ∉ e.fv := fun h => hz (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
  have hzv : z ∉ v.fv := fun h => hz (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
  have hzcl : z ∉ (close e x).fv := close_preserve_not_fvar e hze
  rw [subst_intro z v (close e x) hzcl hv, open_close_subst_lc x z e he]
  have subst_rename : ∀ e : Exp rT, z ∉ e.fv → subst (subst e x (fvar z)) z v = subst e x v := by
    intro e hze
    induction e with
    | fvar y =>
        by_cases hxy : x = y
        · subst hxy; simp [subst]
        · have hzy : z ≠ y := fun h => hze (by rw [h]; simp [fv])
          simp [subst, hxy, hzy]
    | bvar _ | lit _ | fail | urand => simp [subst]
    | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
    | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
        simp only [subst, fv] at hze ⊢
        rw [ih hze]
    | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
    | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
        simp only [subst, fv, Finset.mem_union, not_or] at hze ⊢
        rw [ih1 hze.1, ih2 hze.2]
    | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
        simp only [subst, fv, Finset.mem_union, not_or] at hze ⊢
        rw [ih0 hze.1.1, ih1 hze.1.2, ih2 hze.2]
  exact subst_rename e hze

/-- Locally closed with no free variables; usable before `ClosedCtx` exists in `Metatheory.lean`. -/
def isClosedEmpty (e : Exp rT) : Prop := IsLocallyClosed e ∧ e.fv = ∅

theorem isClosedEmpty.toFvSubsetEmpty {e : Exp rT} (h : e.isClosedEmpty) :
    e.IsLocallyClosed ∧ e.fv ⊆ (∅ : Finset Var) :=
  ⟨h.1, h.2.subset⟩

theorem lit_isClosedEmpty (b : BaseLit rT) : (Exp.lit b).isClosedEmpty :=
  ⟨IsLocallyClosed.lit b, by simp [Exp.fv]⟩

theorem open_isLocallyClosed {e : Exp rT} (t : Exp rT) (he : e.IsLocallyClosed) :
    (Exp.open' e t).IsLocallyClosed := by
  rw [open', ← open_lc 0 t e he]
  exact he

theorem fv_subset_openRec (k : Nat) (y : Var) (e : Exp rT) :
    e.fv ⊆ (openRec k (fvar y) e).fv := by
  induction e generalizing k <;> grind

theorem fv_subset_open (e : Exp rT) (y : Var) :
    e.fv ⊆ (open' e (fvar y)).fv :=
  fv_subset_openRec 0 y e

theorem fv_openRec_subset (k : Nat) (y : Var) (e : Exp rT) :
    (openRec k (fvar y) e).fv ⊆ e.fv ∪ {y} := by
  induction e generalizing k with grind

theorem fv_open_subset (e : Exp rT) (y : Var) :
    (open' e (fvar y)).fv ⊆ e.fv ∪ {y} :=
  fv_openRec_subset 0 y e

end Exp

/-! ## The `pl_step_simp` cleanup set

β/fix steps substitute through binders with `openRec`, and `pl%`-elaborated binders
carry `closeRec` wrappers; on an *opaque* leaf (an abstract `Val` projection or a
closed library constant) the recursion is stuck, so wrappers pile up in stepped
expressions and every later `whnf`-based defeq re-evaluates them over the whole leaf.
`@[pl_step_simp]` collects the propositional erasure lemmas — `openRec_val_fst` for
values, plus a per-library-constant `openRec`/`closeRec` identity pair (closed terms
are invariant) — and the step tactics run `simp only [pl_step_simp]` after each step. -/

register_simp_attr pl_step_simp

/-- Decide `Exp.lcb k e = true` (or any closed-form `a = b`) by *kernel* reduction and
close it with `Eq.refl`. On an inlined library closure the elaborator's `rfl`/`whnf`
re-evaluates `lcb` through every unfolded constant body (seconds per call, and it
recurs on every pure step); the kernel's cached reduction does the same check in
milliseconds. -/
public meta def Exp.kernelDecideEq (g : Lean.MVarId) : Lean.MetaM Unit := g.withContext do
  let ty ← Lean.instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq? | throwError "lcb_kernel: goal is not an equation"
  if ty.hasMVar then throwError "lcb_kernel: goal contains metavariables"
  unless ← Lean.ofExceptKernelException
      (Lean.Kernel.isDefEq (← Lean.getEnv) (← Lean.getLCtx) lhs rhs) do
    throwError "lcb_kernel: sides are not definitionally equal"
  g.assign (← Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl lhs) ty)

open Lean in
/-- Value check for a concrete `lam`/`fix` closure `e : Exp α` (possibly behind a library
constant), deciding its local closedness by kernel reduction instead of `whnf` of
`Exp.toVal?`. Returns `some (some v)` with `v.fst = e` for a closed closure,
`some none` for an open one, and `none` when `e` is not a `lam`/`fix` or the kernel
cannot decide (e.g. metavariables), so the caller falls back to `toVal?`. -/
public meta def Exp.closedFunVal? (α e : Expr) : MetaM (Option (Option Expr)) := do
  let eW ← Meta.whnf e
  let ctor ← if eW.isAppOfArity ``Exp.lam 2 then pure ``IsVal.lam
    else if eW.isAppOfArity ``Exp.fix 2 then pure ``IsVal.fix else return none
  let lcbTrue (x : Expr) : Expr :=
    mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp3 (mkConst ``Exp.lcb [0]) α (mkNatLit 0) x) (mkConst ``Bool.true)
  let some (_, lhs, rhs) := (lcbTrue e).eq? | return none
  let ok ← try ofExceptKernelException (Kernel.isDefEq (← getEnv) (← getLCtx) lhs rhs)
    catch _ => return none
  unless ok do return some none
  let rflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let lcOf (x : Expr) : MetaM Expr := do
    return mkApp3 (mkConst ``Exp.lcb_imp_lc [0]) α x
      (← Meta.mkExpectedTypeHint rflTrue (lcbTrue x))
  let snd := mkApp3 (mkConst ctor) α eW.appArg! (← lcOf eW)
  return some (some (mkApp4 (mkConst ``Val.mk) α e snd (← lcOf e)))

/-- `lcb_kernel` closes `Exp.lcb k e = true` by kernel reduction (see
`Exp.kernelDecideEq`). -/
syntax "lcb_kernel" : tactic
elab_rules : tactic
  | `(tactic| lcb_kernel) => Lean.Elab.Tactic.liftMetaFinishingTactic Exp.kernelDecideEq

/-- `kernel_rfl` closes a definitional equation `a = b` by kernel reduction when it is
metavariable-free (the step tactics' anchors `e_full = K.fill e`, `e.toVal? = some v`),
and falls back to the elaborator's `rfl` (which can unify metavariables) otherwise. -/
syntax "kernel_rfl" : tactic
elab_rules : tactic
  | `(tactic| kernel_rfl) => Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    if (← Lean.instantiateMVars (← g.getType)).hasMVar then g.refl
    else Exp.kernelDecideEq g

/-- `is_lc` discharges `Exp.IsLocallyClosed e` goals. Runtime values and program
fragments are locally closed; the proof is either a kernel computation of the decidable
checker (`Exp.lcb_imp_lc (by lcb_kernel)`, for fully concrete closed subterms such as source
`lam`/`fix` bodies), or a structural decomposition bottoming out at an abstract value's
`Val.lc` field (`exact Val.lc _`) or a closedness hypothesis already in context. -/
syntax "is_lc" : tactic
macro_rules
  | `(tactic| is_lc) =>
    `(tactic| first
        | assumption
        | exact Exp.lcb_imp_lc (by lcb_kernel)
        | repeat' (first
            | assumption
            | exact Exp.lcb_imp_lc (by lcb_kernel)
            | exact Val.lc _
            | exact Exp.IsLocallyClosed.fvar _
            | exact Exp.IsLocallyClosed.lit _
            | exact Exp.IsLocallyClosed.fail
            | exact Exp.IsLocallyClosed.urand
            -- Binders: open at a cofinite variable and reduce `open'`; this leaves
            -- `openRec _ _ e₀` stuck on each opaque leaf `e₀`, cleared by `← Exp.open_lc`.
            | (refine Exp.IsLocallyClosed.lam ∅ _ ?_ <;> intro _ _ <;>
                 simp only [Exp.open', Exp.openRec, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte])
            | (refine Exp.IsLocallyClosed.fix ∅ _ ?_ <;> intro _ _ <;>
                 simp only [Exp.open', Exp.openRec, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte])
            | rw [← Exp.open_lc]
            | apply Exp.IsLocallyClosed.app | apply Exp.IsLocallyClosed.unop
            | apply Exp.IsLocallyClosed.binop | apply Exp.IsLocallyClosed.cond
            | apply Exp.IsLocallyClosed.pair | apply Exp.IsLocallyClosed.fst
            | apply Exp.IsLocallyClosed.snd | apply Exp.IsLocallyClosed.inl
            | apply Exp.IsLocallyClosed.inr | apply Exp.IsLocallyClosed.case
            | apply Exp.IsLocallyClosed.alloc | apply Exp.IsLocallyClosed.load
            | apply Exp.IsLocallyClosed.store | apply Exp.IsLocallyClosed.tape
            | apply Exp.IsLocallyClosed.rand | apply Exp.IsLocallyClosed.scrut))

syntax "is_value" : tactic
macro_rules
  | `(tactic| is_value) =>
    `(tactic| first
        | trivial
        | repeat' (first
            | rfl
            | assumption
            | exact Val.snd _
            | exact Val.isValue _
            | exact Exp.lcb_imp_lc (by lcb_kernel)
            | exact Val.lc _
            | exact ProbLang.IsVal.lit
            | refine ProbLang.IsVal.lam ?_ | refine ProbLang.IsVal.fix ?_
            | apply ProbLang.IsVal.inl | apply ProbLang.IsVal.inr | apply ProbLang.IsVal.pair
            -- `lam`/`fix` bodies that are not closed: see `is_lc`.
            | (refine Exp.IsLocallyClosed.lam ∅ _ ?_ <;> intro _ _ <;>
                 simp only [Exp.open', Exp.openRec, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte])
            | (refine Exp.IsLocallyClosed.fix ∅ _ ?_ <;> intro _ _ <;>
                 simp only [Exp.open', Exp.openRec, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte])
            | rw [← Exp.open_lc]
            | apply Exp.IsLocallyClosed.fvar
            | apply Exp.IsLocallyClosed.lit | apply Exp.IsLocallyClosed.app
            | apply Exp.IsLocallyClosed.unop | apply Exp.IsLocallyClosed.binop
            | apply Exp.IsLocallyClosed.cond | apply Exp.IsLocallyClosed.pair
            | apply Exp.IsLocallyClosed.fst | apply Exp.IsLocallyClosed.snd
            | apply Exp.IsLocallyClosed.inl | apply Exp.IsLocallyClosed.inr
            | apply Exp.IsLocallyClosed.case | apply Exp.IsLocallyClosed.alloc
            | apply Exp.IsLocallyClosed.load | apply Exp.IsLocallyClosed.store
            | apply Exp.IsLocallyClosed.tape | apply Exp.IsLocallyClosed.rand
            | apply Exp.IsLocallyClosed.scrut
            | refine ⟨?_, ?_⟩
            | refine ⟨?_⟩))

/-! ## `toVal?` on value-shaped expressions -/

-- `rfl` by proof irrelevance on the `Val.lc` field.
@[simp] theorem Exp.toVal?_lit (b : BaseLit rT) :
    (Exp.lit b).toVal? = some ⟨.lit b, IsVal.lit, Exp.lcb_imp_lc rfl⟩ := rfl

-- `lam`/`fix` are values only when locally closed: `toVal?` gates on `lcb`.
@[simp] theorem Exp.toVal?_lam (e : Exp rT) (h : (Exp.lam e).IsLocallyClosed) :
    (Exp.lam e).toVal? = some ⟨.lam e, IsVal.lam h, h⟩ := by
  simp only [Exp.toVal?, IsVal.check?, dite_eq_left (Exp.lc_imp_lcb h)]

@[simp] theorem Exp.toVal?_fix (e : Exp rT) (h : (Exp.fix e).IsLocallyClosed) :
    (Exp.fix e).toVal? = some ⟨.fix e, IsVal.fix h, h⟩ := by
  simp only [Exp.toVal?, IsVal.check?, dite_eq_left (Exp.lc_imp_lcb h)]

end ProbLang
