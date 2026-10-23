module

public import Metrology.ProbLang.Syntax.Syntax
public meta import Lean.Elab.Tactic.Basic

@[expose] public section

/-!
# Locally-nameless facts for `Exp`

How `open'`, `close`, `subst` and `fv` interact with `IsLocallyClosed`, plus the `is_lc` and
`is_value` tactics. -/

namespace ProbLang

open Cslib Exp
open HasFresh (fresh_exists)
open Finset (mem_insert mem_insert_of_mem mem_insert_self mem_singleton mem_union mem_union_left
  mem_union_right)

namespace Exp

variable {rT : Type _}

/-! ## Opening at different indices

Bound variables are de Bruijn indices (`bvar`); free variables are names (`fvar`). -/

/-- If opening at `i` leaves `openRec j v e` unchanged for `i ≠ j`, it leaves `e` unchanged. -/
theorem openRec_aux (e : Exp rT) (j v i u) (neq : i ≠ j)
    (heq : openRec j v e = openRec i u (openRec j v e)) : e = openRec i u e := by
  induction e generalizing i j <;> grind

/-- Opening at two different indices with free variables commutes. -/
theorem openRec_openRec_comm (k n : Nat) (x y : Var) (e : Exp rT) (neq : k ≠ n) :
    openRec k (fvar x) (openRec n (fvar y) e) = openRec n (fvar y) (openRec k (fvar x) e) := by
  induction e generalizing k n <;> grind

/-! ## Closing, and `subst` away from fresh variables -/

section

variable (x : Var) (e : Exp rT)

/-- Substituting for a variable not free in `e` does nothing. -/
@[scoped grind =]
theorem subst_fresh (sub : Exp rT) (h : x ∉ e.fv) : subst e x sub = e := by
  induction e <;> grind

/-- Closing a freshly opened variable gives back the term. -/
theorem closeRec_openRec (k : Nat) (h : x ∉ e.fv) : e = closeRec k x (openRec k (fvar x) e) := by
  induction e generalizing k <;> grind

/-- Opening with the same fresh variable is injective. -/
theorem open_inj (e' : Exp rT) (hx : x ∉ e.fv) (hx' : x ∉ e'.fv)
    (heq : open' e (fvar x) = open' e' (fvar x)) : e = e' := by
  grind [closeRec_openRec x e 0 hx, closeRec_openRec x e' 0 hx']

/-- Closing a variable not free in `e` does nothing. -/
theorem closeRec_fresh (k : Nat) (h : x ∉ e.fv) : closeRec k x e = e := by
  induction e generalizing k <;> grind

end

/-- Closing at `k` and opening at a different index `n` with free variables commute. -/
theorem swap_open_fvar_close (k n : Nat) (x y : Var) (e : Exp rT) (hk : k ≠ n) (hxy : x ≠ y) :
    closeRec k x (openRec n (fvar y) e) = openRec n (fvar y) (closeRec k x e) := by
  induction e generalizing k n <;> grind

/-! ## Free variables under `close`, `open'`, `subst` -/

/-- Closing a term keeps a variable that was not free out of the free variables. -/
theorem close_preserve_not_fvar {k x y} (e : Exp rT) (h : x ∉ e.fv) :
    x ∉ (closeRec k y e).fv := by
  induction e generalizing k <;> grind

/-- Opening with a different free variable keeps a non-free variable non-free. -/
theorem open_fresh_preserve_not_fvar {k x y} (e : Exp rT) (h : x ∉ e.fv) (hne : x ≠ y) :
    x ∉ (openRec k (fvar y) e).fv := by
  induction e generalizing k <;> grind

/-- Substitution keeps a variable that is free in neither term out of the free variables. -/
theorem subst_preserve_not_fvar {x y : Var} (e u : Exp rT) (h : x ∉ e.fv ∪ u.fv) :
    x ∉ (subst e y u).fv := by
  induction e <;> grind

/-- The free variables of a substitution lie in those of `e` minus `x`, plus those of `v`. -/
theorem fv_subst_subset (e : Exp rT) (x : Var) (v : Exp rT) :
    (subst e x v).fv ⊆ (e.fv \ {x}) ∪ v.fv := by
  intro z hz
  induction e <;> grind

/-- A variable closed at any index is no longer free. -/
@[scoped grind ← ]
theorem close_var_not_fvar_rec (x : Var) (k : Nat) (e : Exp rT) : x ∉ (closeRec k x e).fv := by
  induction e generalizing k <;> grind

/-- A variable closed in `e` is no longer free in `close e x`. -/
theorem close_var_not_fvar (x : Var) (e : Exp rT) : x ∉ (close e x).fv :=
  close_var_not_fvar_rec x 0 e

/-! ## Local closedness

Main results: `open_lc` (opening a locally closed term is a no-op), `subst_lc` (`subst` preserves
local closedness), and `open_close_subst_lc_gen` (opening `close e x` with `v` substitutes `v`
for `x`). -/

-- Stated right-to-left so `rw [← open_lc]` erases a stuck `openRec` on an opaque leaf.
/-- Opening a locally closed term does nothing. -/
@[scoped grind =_]
theorem open_lc (k : Nat) (t e : Exp rT) (he : e.IsLocallyClosed) : e = openRec k t e := by
  induction he generalizing k with
  | lam L e _ ih | fix L e _ ih =>
      obtain ⟨x, hx⟩ := fresh_exists L
      grind [openRec_aux e 0 (fvar x) (k+1) t]
  | _ => grind

section

variable (x : Var)

/-- `subst` distributes over `openRec` when the substituted term is locally closed. -/
@[scoped grind =]
theorem subst_openRec (t : Exp rT) (k : Nat) (u e : Exp rT) (hu : IsLocallyClosed t) :
    subst (openRec k u e) x t = openRec k (subst u x t) (subst e x t) := by
  induction e generalizing k with grind

/-- `subst` commutes with `closeRec` at a different variable. -/
@[scoped grind =]
theorem subst_closeRec (y : Var) (t : Exp rT) (k : Nat) (e : Exp rT) (hxy : x ≠ y)
    (ht : y ∉ t.fv) : subst (closeRec k y e) x t = closeRec k y (subst e x t) := by
  induction e generalizing k with grind [closeRec_fresh]

/-- `subst` commutes with `close` at a different variable. -/
theorem subst_close (y : Var) (t e : Exp rT) (hxy : x ≠ y) (ht : y ∉ t.fv) :
    subst (close e y) x t = close (subst e x t) y :=
  subst_closeRec x y t 0 e hxy ht

/-- `subst` distributes over `open'` when the substituted term is locally closed. -/
theorem subst_open (t u e : Exp rT) (hu : IsLocallyClosed t) :
    subst (open' e u) x t = open' (subst e x t) (subst u x t) := by grind

theorem subst_open_var (y : Var) (u e : Exp rT) (hne : y ≠ x) (hu : IsLocallyClosed u) :
    subst (open' e (fvar x)) y u = open' (subst e y u) (fvar x) := by grind

/-- Opening with `t` is opening with a fresh variable `x` followed by substituting `t` for `x`. -/
theorem subst_intro (t e : Exp rT) (mem : x ∉ e.fv) (t_lc : IsLocallyClosed t) :
    open' e t = subst (open' e (fvar x)) x t := by
  grind

end

/-- Substituting a locally closed term into a locally closed term stays locally closed. -/
@[scoped grind ←]
theorem subst_lc {x : Var} {e u : Exp rT} (he : IsLocallyClosed e) (hu : IsLocallyClosed u) :
    IsLocallyClosed (subst e x u) := by
  induction he with
  | lam L e _ ih =>
      refine .lam (free_union Var) _ ?_
      intro y hy
      have hyL : y ∉ L := by grind
      have hyx : y ≠ x := by grind
      grind [subst_open_var]
  | fix L e _ ih =>
      refine .fix (free_union Var) _ ?_
      intro y hy
      have hyL : y ∉ L := by grind
      have hyx : y ≠ x := by grind
      grind [subst_open_var]
  | _ => grind

/-- The binder case of `open_close_to_subst`, from the induction hypothesis on the body. -/
private theorem openRec_closeRec_binder {L : Finset Var} {t : Exp rT} {x y : Var} {k : Nat}
    (ih : ∀ z ∉ L, ∀ k, openRec k (fvar y) (closeRec k x (open' t (fvar z))) =
      subst (open' t (fvar z)) x (fvar y)) :
    openRec (k+1) (fvar y) (closeRec (k+1) x t) = subst t x (fvar y) := by
  obtain ⟨z, hz⟩ := fresh_exists (L ∪ t.fv ∪ {x, y})
  simp only [mem_union, mem_insert, mem_singleton, not_or] at hz
  obtain ⟨⟨hzL, hzt⟩, hzx, hzy⟩ := hz
  have hzL' : z ∉ (openRec (k+1) (fvar y) (closeRec (k+1) x t)).fv :=
    open_fresh_preserve_not_fvar _ (close_preserve_not_fvar _ hzt) hzy
  have hzR : z ∉ (subst t x (fvar y)).fv := subst_preserve_not_fvar _ _ (by simp [fv, hzt, hzy])
  refine open_inj z _ _ hzL' hzR ?_
  calc open' (openRec (k+1) (fvar y) (closeRec (k+1) x t)) (fvar z)
      = openRec (k+1) (fvar y) (closeRec (k+1) x (open' t (fvar z))) := by
        simp only [open']
        rw [openRec_openRec_comm 0 (k+1) z y _ (by omega),
          swap_open_fvar_close (k+1) 0 x z t (by omega) (Ne.symm hzx)]
    _ = subst (open' t (fvar z)) x (fvar y) := ih z hzL (k+1)
    _ = open' (subst t x (fvar y)) (fvar z) := subst_open_var z x (fvar y) t (Ne.symm hzx) (.fvar y)

/-- Closing `x` then opening with `fvar y` renames `x` to `y` (`subst`) on locally closed terms. -/
@[scoped grind =]
theorem open_close_to_subst (e : Exp rT) (x y : Var) (k : Nat) (he : IsLocallyClosed e) :
    openRec k (fvar y) (closeRec k x e) = subst e x (fvar y) := by
  induction he generalizing k with
  | lam L t _ ih | fix L t _ ih =>
      simp only [closeRec, openRec, subst]
      congr 1
      exact openRec_closeRec_binder ih
  | _ => grind

/-- Closing `x` then opening with `fvar y` is substituting `fvar y` for `x`. -/
theorem open_close_subst_lc (x y : Var) (e : Exp rT) (he : IsLocallyClosed e) :
    open' (close e x) (fvar y) = subst e x (fvar y) :=
  open_close_to_subst e x y 0 he

/-- The body of an `unpack` context (`app (lam (close e x)) e₁`) opens to a locally closed term. -/
theorem open_close_isLocallyClosed {e : Exp rT} (x y : Var) (he : IsLocallyClosed e) :
    (open' (close e x) (fvar y)).IsLocallyClosed := by
  rw [open_close_subst_lc x y e he]
  exact subst_lc he (.fvar y)

/-- `e[x ↦ y][y ↦ w] = e[x ↦ w]` for `y` fresh in `e`. -/
theorem subst_subst_fvar_id (e w : Exp α) (x y : Var) (hyv : y ∉ e.fv) :
    subst (subst e x (.fvar y)) y w = subst e x w := by
  induction e with
  | fvar z =>
    by_cases h1 : x = z
    · subst h1
      simp [subst]
    · have hyz : y ≠ z := fun h => hyv (h ▸ by simp [fv])
      simp [subst, h1, hyz]
  | bvar _ | lit _ | fail | urand => rfl
  | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
    have hyv' : y ∉ e.fv := fun h => hyv (by simpa [fv] using h)
    simp [subst, ih hyv']
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
    have hyv1 : y ∉ e1.fv := fun h => hyv (by simp [fv]; exact Or.inl h)
    have hyv2 : y ∉ e2.fv := fun h => hyv (by simp [fv]; exact Or.inr h)
    simp [subst, ih1 hyv1, ih2 hyv2]
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
    have hyv0 : y ∉ e0.fv := fun h => hyv (by simp [fv]; exact Or.inl h)
    have hyv1 : y ∉ e1.fv := fun h => hyv (by simp [fv]; exact Or.inr (Or.inl h))
    have hyv2 : y ∉ e2.fv := fun h => hyv (by simp [fv]; exact Or.inr (Or.inr h))
    simp [subst, ih0 hyv0, ih1 hyv1, ih2 hyv2]

/-- Opening `close e x` with any locally closed `v` substitutes `v` for `x`. -/
theorem open_close_subst_lc_gen (x : Var) (e v : Exp rT)
    (he : IsLocallyClosed e) (hv : IsLocallyClosed v) :
    open' (close e x) v = subst e x v := by
  obtain ⟨z, hz⟩ := fresh_exists (insert x (e.fv ∪ v.fv))
  have hzx : z ≠ x := fun h => hz (h ▸ mem_insert_self _ _)
  have hze : z ∉ e.fv := fun h => hz (mem_insert_of_mem (mem_union_left _ h))
  have hzv : z ∉ v.fv := fun h => hz (mem_insert_of_mem (mem_union_right _ h))
  have hzcl : z ∉ (close e x).fv := close_preserve_not_fvar e hze
  rw [subst_intro z v (close e x) hzcl hv, open_close_subst_lc x z e he]
  -- Rename `x` to the fresh `z`, then substitute `v` for `z`.
  exact subst_subst_fvar_id e v x z hze

/-- `e` is locally closed and has no free variables. -/
def IsClosedEmpty (e : Exp rT) : Prop := IsLocallyClosed e ∧ e.fv = ∅

/-- A closed term is locally closed with free variables inside the empty set. -/
theorem IsClosedEmpty.toFvSubsetEmpty {e : Exp rT} (h : e.IsClosedEmpty) :
    e.IsLocallyClosed ∧ e.fv ⊆ (∅ : Finset Var) :=
  ⟨h.1, h.2.subset⟩

/-- Literals are closed. -/
theorem lit_isClosedEmpty (b : BaseLit rT) : (lit b).IsClosedEmpty :=
  ⟨.lit b, by simp [fv]⟩

/-! ## Free variables of `open'` -/

/-- Opening with a free variable at any index only adds free variables. -/
theorem fv_subset_openRec (k : Nat) (y : Var) (e : Exp rT) :
    e.fv ⊆ (openRec k (fvar y) e).fv := by
  induction e generalizing k <;> grind

/-- Opening with a free variable only adds free variables. -/
theorem fv_subset_open (e : Exp rT) (y : Var) : e.fv ⊆ (open' e (fvar y)).fv :=
  fv_subset_openRec 0 y e

end Exp

/-! ## Free variables of `close` -/

/-- Closing a term at an atom introduces no new free variables. -/
theorem closeRec_fv_subset (e : Exp α) (x : Var) (k : Nat) (y : Var)
    (hy : y ∈ (closeRec k x e).fv) : y ∈ e.fv := by
  induction e generalizing k with
  | bvar _ => simp [closeRec, fv] at hy
  | fvar z =>
      simp [closeRec] at hy
      by_cases hxz : x = z
      · rw [ite_eq_left hxz] at hy; simp [fv] at hy
      · rw [ite_eq_right hxz] at hy; exact hy
  | lit _ | fail | urand => simp [closeRec, fv] at hy
  | lam e ih | fix e ih =>
      simp only [closeRec, fv] at hy ⊢
      exact ih (k+1) hy
  | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
      simp only [closeRec, fv] at hy ⊢
      exact ih k hy
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
      simp only [closeRec, fv, mem_union] at hy ⊢
      exact hy.imp (ih1 k) (ih2 k)
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
      simp only [closeRec, fv, mem_union] at hy ⊢
      exact hy.imp (Or.imp (ih0 k) (ih1 k)) (ih2 k)

/-- Closing a term introduces no new free variables. -/
theorem close_fv_subset (e : Exp α) (x : Var) : (close e x).fv ⊆ e.fv :=
  fun y hy => closeRec_fv_subset e x 0 y hy

/-! ## The `pl_step_simp` cleanup set

On an opaque leaf, the `openRec`/`closeRec` wrappers from β/fix steps get stuck and pile up.
`@[pl_step_simp]` collects the lemmas that erase them, and the step tactics run
`simp only [pl_step_simp]` after each step. -/

register_simp_attr pl_step_simp

/-! ## Closedness and value tactics

The kernel helpers below serve these tactics and `Micrometer/WpTactics.lean`. -/

section

open Lean Meta
open Lean.Elab.Tactic (liftMetaFinishingTactic)
open Nat (reduceAdd reduceEqDiff)
open Val (isValue lc)
open Kernel (isDefEq)

/-- Closes `Exp.lcb k e = true` (or any metavariable-free `a = b`) by kernel reduction. -/
public meta def Exp.kernelDecideEq (g : MVarId) : MetaM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq? | throwError "lcb_kernel: goal is not an equation"
  if ty.hasMVar then throwError "lcb_kernel: goal contains metavariables"
  unless ← ofExceptKernelException (isDefEq (← getEnv) (← getLCtx) lhs rhs) do
    throwError "lcb_kernel: sides are not definitionally equal"
  g.assign (← mkExpectedTypeHint (← mkEqRefl lhs) ty)

-- Returns `some (some v)` for a closed closure, `some none` for an open one, and `none` when
-- `e` is not a `lam`/`fix` or the kernel cannot decide, so the caller falls back to `toVal?`.
/-- Decides by kernel reduction whether a concrete `lam`/`fix` closure `e : Exp α` is a value. -/
public meta def Exp.closedFunVal? (α e : Expr) : MetaM (Option (Option Expr)) := do
  let eW ← whnf e
  let ctor ← if eW.isAppOfArity ``Exp.lam 2 then pure ``IsVal.lam
    else if eW.isAppOfArity ``Exp.fix 2 then pure ``IsVal.fix else return none
  let lcbTrue (x : Expr) : Expr :=
    mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkApp3 (mkConst ``Exp.lcb [0]) α (mkNatLit 0) x)
      (mkConst ``Bool.true)
  let some (_, lhs, rhs) := (lcbTrue e).eq? | return none
  let ok ← try ofExceptKernelException (isDefEq (← getEnv) (← getLCtx) lhs rhs)
    catch _ => return none
  unless ok do return some none
  let rflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let lcOf (x : Expr) : MetaM Expr := do
    return mkApp3 (mkConst ``Exp.lcb_imp_lc [0]) α x (← mkExpectedTypeHint rflTrue (lcbTrue x))
  let snd := mkApp3 (mkConst ctor) α eW.appArg! (← lcOf eW)
  return some (some (mkApp4 (mkConst ``Val.mk) α e snd (← lcOf e)))

/-- Closes `Exp.lcb k e = true` by kernel reduction (see `Exp.kernelDecideEq`). -/
syntax "lcb_kernel" : tactic
elab_rules : tactic
  | `(tactic| lcb_kernel) => liftMetaFinishingTactic kernelDecideEq

/-- Closes a definitional equation by kernel reduction if it has no metavariables, else by `rfl`. -/
syntax "kernel_rfl" : tactic
elab_rules : tactic
  | `(tactic| kernel_rfl) => liftMetaFinishingTactic fun g => do
    if (← instantiateMVars (← g.getType)).hasMVar then g.refl
    else kernelDecideEq g

/-- Discharges `Exp.IsLocallyClosed e`, by kernel computation for concrete terms or by structural
decomposition down to `Val.lc` fields and hypotheses. -/
syntax "is_lc" : tactic
macro_rules
  | `(tactic| is_lc) =>
    `(tactic| first
        | assumption
        | exact lcb_imp_lc (by lcb_kernel)
        | repeat' (first
            | assumption
            | exact lcb_imp_lc (by lcb_kernel)
            | exact lc _
            | exact IsLocallyClosed.fvar _
            | exact IsLocallyClosed.lit _
            | exact IsLocallyClosed.fail
            | exact IsLocallyClosed.urand
            -- Binders: open at a cofinite variable and reduce `open'`; this leaves
            -- `openRec _ _ e₀` stuck on each opaque leaf `e₀`, cleared by `← Exp.open_lc`.
            | (refine IsLocallyClosed.lam ∅ _ ?_ <;> intro _ _ <;>
                 simp only [open', openRec, reduceAdd, reduceEqDiff, ↓reduceIte])
            | (refine IsLocallyClosed.fix ∅ _ ?_ <;> intro _ _ <;>
                 simp only [open', openRec, reduceAdd, reduceEqDiff, ↓reduceIte])
            | rw [← open_lc]
            | apply IsLocallyClosed.app | apply IsLocallyClosed.unop
            | apply IsLocallyClosed.binop | apply IsLocallyClosed.cond
            | apply IsLocallyClosed.pair | apply IsLocallyClosed.fst
            | apply IsLocallyClosed.snd | apply IsLocallyClosed.inl
            | apply IsLocallyClosed.inr | apply IsLocallyClosed.case
            | apply IsLocallyClosed.alloc | apply IsLocallyClosed.load
            | apply IsLocallyClosed.store | apply IsLocallyClosed.tape
            | apply IsLocallyClosed.rand | apply IsLocallyClosed.scrut))

/-- Discharges `IsVal e` and `IsLocallyClosed e` goals, like `is_lc`. -/
syntax "is_value" : tactic
macro_rules
  | `(tactic| is_value) =>
    `(tactic| first
        | trivial
        | repeat' (first
            | rfl
            | assumption
            | exact Val.snd _
            | exact isValue _
            | exact lcb_imp_lc (by lcb_kernel)
            | exact lc _
            | exact IsVal.lit
            | refine IsVal.lam ?_ | refine IsVal.fix ?_
            | apply IsVal.inl | apply IsVal.inr | apply IsVal.pair
            -- `lam`/`fix` bodies that are not closed: see `is_lc`.
            | (refine IsLocallyClosed.lam ∅ _ ?_ <;> intro _ _ <;>
                 simp only [open', openRec, reduceAdd, reduceEqDiff, ↓reduceIte])
            | (refine IsLocallyClosed.fix ∅ _ ?_ <;> intro _ _ <;>
                 simp only [open', openRec, reduceAdd, reduceEqDiff, ↓reduceIte])
            | rw [← open_lc]
            | apply IsLocallyClosed.fvar
            | apply IsLocallyClosed.lit | apply IsLocallyClosed.app
            | apply IsLocallyClosed.unop | apply IsLocallyClosed.binop
            | apply IsLocallyClosed.cond | apply IsLocallyClosed.pair
            | apply IsLocallyClosed.fst | apply IsLocallyClosed.snd
            | apply IsLocallyClosed.inl | apply IsLocallyClosed.inr
            | apply IsLocallyClosed.case | apply IsLocallyClosed.alloc
            | apply IsLocallyClosed.load | apply IsLocallyClosed.store
            | apply IsLocallyClosed.tape | apply IsLocallyClosed.rand
            | apply IsLocallyClosed.scrut
            | refine ⟨?_, ?_⟩
            | refine ⟨?_⟩))

end

/-! ## `toVal?` on value-shaped expressions -/

namespace Exp

-- `rfl` by proof irrelevance on the `Val.lc` field.
/-- `toVal?` sends a literal to the literal value. -/
@[simp] theorem toVal?_lit (b : BaseLit rT) :
    (lit b).toVal? = some ⟨.lit b, IsVal.lit, lcb_imp_lc rfl⟩ := rfl

-- `lam`/`fix` are values only when locally closed: `toVal?` gates on `lcb`.
/-- `toVal?` sends a locally closed `lam` to the lambda value. -/
@[simp] theorem toVal?_lam (e : Exp rT) (h : (lam e).IsLocallyClosed) :
    (lam e).toVal? = some ⟨.lam e, IsVal.lam h, h⟩ := by
  simp only [toVal?, IsVal.check?, dite_eq_left (lc_imp_lcb h)]

/-- `toVal?` sends a locally closed `fix` to the fixpoint value. -/
@[simp] theorem toVal?_fix (e : Exp rT) (h : (fix e).IsLocallyClosed) :
    (fix e).toVal? = some ⟨.fix e, IsVal.fix h, h⟩ := by
  simp only [toVal?, IsVal.check?, dite_eq_left (lc_imp_lcb h)]

end Exp

end ProbLang
