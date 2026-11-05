module

public import Metrology.ProbLang.Syntax.Syntax
public meta import Lean.Elab.Tactic.Basic
public meta import Qq

@[expose] public section

/-! # Locally-nameless facts for `Exp`
How `open'`, `close`, `subst` and `fv` interact with `IsLocallyClosed`, plus the tactics `is_lc`
and `is_value`. -/

namespace ProbLang

variable {rT : Type _}

open Cslib Exp
open HasFresh (fresh_exists)
open Finset (mem_insert mem_insert_of_mem mem_insert_self mem_singleton mem_union mem_union_left
  mem_union_right notMem_empty notMem_singleton notMem_union)

namespace Exp

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

/-- Closing at `k` and opening at a different index `n` with free variables commute. -/
theorem swap_open_fvar_close (k n : Nat) (x y : Var) (e : Exp rT) (hk : k ≠ n) (hxy : x ≠ y) :
    closeRec k x (openRec n (fvar y) e) = openRec n (fvar y) (closeRec k x e) := by
  induction e generalizing k n <;> grind

/-! ## Free variables under `close`, `open'`, `subst` -/

/-- Closing a term keeps any variable not free in it out of its free variables. -/
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

/-- Opening with the variable `x` commutes with substituting for a different variable `y`. -/
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
theorem subst_subst_fvar_id {α : Type _} (e w : Exp α) (x y : Var) (hyv : y ∉ e.fv) :
    subst (subst e x (.fvar y)) y w = subst e x w := by
  induction e with
  | fvar z =>
    by_cases h1 : x = z
    · subst h1
      simp [subst]
    · have hyz : y ≠ z := fun h => hyv (h ▸ by simp [fv])
      simp [subst, h1, hyz]
  | bvar _ | lit _ | fail => rfl
  | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape _ e ih | ffi e ih
  | scrut e _ ih | randvar _ e ih =>
    have hyv' : y ∉ e.fv := fun h => hyv (by simpa [fv] using h)
    simp [subst, ih hyv']
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | allocN e1 e2 ih1 ih2 | sample _ e1 e2 ih1 ih2 | test _ e1 e2 ih1 ih2 =>
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

/-- Closing at index `k` introduces no new free variables. -/
theorem closeRec_fv_subset {α : Type _} (e : Exp α) (x : Var) (k : Nat) (y : Var)
    (hy : y ∈ (closeRec k x e).fv) : y ∈ e.fv := by
  induction e generalizing k with
  | bvar _ => simp [closeRec, fv] at hy
  | fvar z =>
      simp only [closeRec] at hy
      by_cases hxz : x = z
      · rw [ite_eq_left hxz] at hy; simp [fv] at hy
      · rw [ite_eq_right hxz] at hy; exact hy
  | lit _ | fail => simp [closeRec, fv] at hy
  | lam e ih | fix e ih =>
      simp only [closeRec, fv] at hy ⊢
      exact ih (k+1) hy
  | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape _ e ih | ffi e ih
  | scrut e _ ih | randvar _ e ih =>
      simp only [closeRec, fv] at hy ⊢
      exact ih k hy
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | allocN e1 e2 ih1 ih2 | sample _ e1 e2 ih1 ih2 | test _ e1 e2 ih1 ih2 =>
      simp only [closeRec, fv, mem_union] at hy ⊢
      exact hy.imp (ih1 k) (ih2 k)
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
      simp only [closeRec, fv, mem_union] at hy ⊢
      exact hy.imp (Or.imp (ih0 k) (ih1 k)) (ih2 k)

/-- Closing a term introduces no new free variables. -/
theorem close_fv_subset {α : Type _} (e : Exp α) (x : Var) : (close e x).fv ⊆ e.fv :=
  fun y hy => closeRec_fv_subset e x 0 y hy

/-! ## Certificates for `lcb`

The lemmas of the structural closedness check `Exp.lcbProof?`. -/

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

/-- A value passes `lcb` at every bound. -/
theorem lcb_ofVal {α : Type} (k : Nat) (v : Val α) : lcb k (ofVal v) = true :=
  lcb_mono (lc_imp_lcb v.lc) k.zero_le

section

variable {j k : Nat} {x : Var} {v e : Exp rT}

/-- Opening at `k` with a term passing `lcb k` lowers the bound from `k + 1` to `k`. -/
theorem lcb_openRec (hv : lcb k v = true) (he : lcb (k + 1) e = true) :
    lcb k (openRec k v e) = true := by
  induction e generalizing k with
  | bvar j =>
      simp only [lcb, decide_eq_true_eq] at he
      simp only [openRec]
      split
      · exact hv
      · simp only [lcb, decide_eq_true_eq]; omega
  | lam e ih | fix e ih => exact ih (lcb_succ v k hv) he
  | _ => simp_all [lcb, openRec]

/-- Opening at an index the term does not reach leaves it unchanged. -/
theorem openRec_of_lcb (he : lcb j e = true) : openRec j v e = e := by
  induction e generalizing j <;> grind [lcb]

/-- Opening at or above the bound keeps a term within the bound. -/
theorem lcb_openRec_of_le (hkj : k ≤ j) (he : lcb k e = true) : lcb k (openRec j v e) = true := by
  rwa [openRec_of_lcb (lcb_mono he hkj)]

/-- Closing at an index below the bound keeps a term within the bound. -/
theorem lcb_closeRec (hj : j < k) (he : lcb k e = true) : lcb k (closeRec j x e) = true := by
  induction e generalizing j k with
  | fvar y =>
      simp only [closeRec]
      split <;> simp [lcb, hj]
  | lam e ih | fix e ih => exact ih (by omega) he
  | _ => simp_all [lcb, closeRec]

/-- Closing a variable that does not occur keeps a term within the bound. -/
theorem lcb_closeRec_of_notMem (hx : x ∉ e.fv) (he : lcb k e = true) :
    lcb k (closeRec j x e) = true := by
  rwa [closeRec_fresh x e j hx]

theorem notMem_fv_closeRec {y : Var} (h : x ∉ e.fv) : x ∉ (closeRec k y e).fv :=
  fun hx => h (closeRec_fv_subset e y k x hx)

theorem notMem_fv_closeRec_self : x ∉ (closeRec k x e).fv := by
  induction e generalizing k <;> grind

theorem notMem_fv_openRec (hv : x ∉ v.fv) (he : x ∉ e.fv) : x ∉ (openRec k v e).fv := by
  induction e generalizing k <;> grind

end

end Exp

/-! ## The `pl_step_simp` cleanup set

On an opaque leaf, the `openRec`/`closeRec` wrappers from β/fix steps get stuck and pile up.
`@[pl_step_simp]` collects the lemmas that erase them, and the step tactics run
`simp only [pl_step_simp]` after each step. -/

register_simp_attr pl_step_simp

/-! ## Closedness and value tactics

The helpers below serve these tactics and the `wp_value` tactics. -/

section

open Lean Meta Qq
open Lean.Elab.Tactic (liftMetaFinishingTactic)
open Nat (reduceAdd reduceEqDiff)
open Val (isValue lc)
open Kernel (isDefEq)

/-- Closes a metavariable-free `a = b` by kernel reduction. -/
public meta def Exp.kernelDecideEq (g : MVarId) : MetaM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq? | throwError "kernel_rfl: goal is not an equation"
  if ty.hasMVar then throwError "kernel_rfl: goal contains metavariables"
  unless ← ofExceptKernelException (isDefEq (← getEnv) (← getLCtx) lhs rhs) do
    throwError "kernel_rfl: sides are not definitionally equal"
  g.assign (← mkExpectedTypeHint (← mkEqRefl lhs) ty)

/-- The equation lemmas of `f` by constructor of `Exp`, each with the argument position of each
of its binders. -/
public meta def Exp.eqnTable (f : Name) : MetaM (NameMap (Name × Array Nat)) := do
  let some eqns ← getEqnsFor? f | throwError "{f} has no equation lemmas"
  eqns.foldlM (init := {}) fun m eqn => do
    let ty := (← getConstInfo eqn).type
    let some (_, lhs, _) := ty.getForallBody.eq? | return m
    let some c := lhs.appArg!.getAppFn.constName? | return m
    let args := lhs.appFn!.getAppArgs ++ lhs.appArg!.getAppArgs
    let n := ty.getForallArity
    let some pos := (List.range n).toArray.mapM fun j => args.findIdx? (· == .bvar (n - 1 - j))
      | return m
    return m.insert c (eqn, pos)

/-- The equation of `f` at a constructor application, as its proof and right side. -/
public meta def Exp.unfoldCtor? (tbl : NameMap (Name × Array Nat)) (fArgs e : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let .const c us := e.getAppFn | return none
  let some (eqn, pos) := tbl.find? c | return none
  let args := fArgs.getAppArgs ++ e.getAppArgs
  let xs := pos.map (args[·]!)
  let some (_, _, rhs) := (← instantiateForall
    ((← getConstInfo eqn).instantiateTypeLevelParams us) xs).eq? | return none
  return some (mkAppN (mkConst eqn us) xs, rhs)

/-- Whether the kernel reduces the boolean `b` to `true`. -/
public meta def Exp.kernelTrue (b : Expr) : MetaM Bool :=
  return (← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) b)).isConstOf ``true

/-- Proves `p` by `decide` if the kernel reduces it to `true`. -/
public meta def Exp.decideProof? (p : Expr) : MetaM (Option Expr) := do
  let d ← mkDecide p
  unless ← kernelTrue d do return none
  return some (mkApp3 (mkConst ``of_decide_eq_true) p d.appArg! (← mkEqRefl q(true)))

/-- Proves `Exp.lcb k e = true` (`e : Exp α`) by kernel reduction. -/
public meta def Exp.kernelLcb? (α k e : Expr) : MetaM (Option Expr) := do
  let lhs := mkApp3 (.const ``Exp.lcb [← getDecLevel α]) α k e
  unless ← (try ofExceptKernelException (isDefEq (← getEnv) (← getLCtx) lhs q(true))
    catch _ => pure false) do return none
  return some (← mkExpectedTypeHint (← mkEqRefl q(true)) (← mkEq lhs q(true)))

/-- Proves `Exp.lcb k e = true` structurally, by the equation lemmas of `lcb` and the
certificates above. -/
public meta partial def Exp.lcbProof? (eqns fvEqns : NameMap (Name × Array Nat)) (k e : Expr) :
    MetaM (Option Expr) := do
  let e := e.consumeMData
  if let some (α, v) ← valLeaf? e then return some (mkApp3 (mkConst ``Exp.lcb_ofVal) α k v)
  if let some pf? ← binderOp? e then return pf?
  let eW ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) e)
  if let some (α, v) ← valLeaf? eW then return some (mkApp3 (mkConst ``Exp.lcb_ofVal) α k v)
  let .const _ us := eW.getAppFn | return none
  let some (eqnPf, rhs) ← unfoldCtor? eqns (mkApp2 (.const ``Exp.lcb us) eW.getAppArgs[0]! k) eW
    | return none
  let some rhsPf ← rhsProof? rhs | return none
  have rhs : Q(Bool) := rhs
  have rhsPf : Q($rhs = true) := rhsPf
  have lhs : Q(Bool) := mkApp3 (.const ``Exp.lcb us) eW.getAppArgs[0]! k eW
  have eqnPf : Q($lhs = $rhs) := eqnPf
  return some q(Eq.trans $eqnPf $rhsPf)
where
  /-- The value `(α, v)` of a value leaf `ofVal v`, `v.fst` or `v.1`. -/
  valLeaf? (e : Expr) : MetaM (Option (Expr × Expr)) := do
    match_expr e with
    | Exp.ofVal α v => return some (α, v)
    | Val.fst α v => return some (α, v)
    | _ =>
      let .proj ``Val 0 v := e | return none
      return some ((← whnf (← inferType v)).appArg!, v)
  /-- For a closing or opening `e`, a proof of `lcb k e = true` from its parts, if any. -/
  binderOp? (e : Expr) : MetaM (Option (Option Expr)) := do
    let some (close?, α, j, s, b) := match_expr e with
      | Exp.close α b x => some (true, α, mkNatLit 0, x, b)
      | Exp.closeRec α j x b => some (true, α, j, x, b)
      | Exp.open' α b v => some (false, α, mkNatLit 0, v, b)
      | Exp.openRec α j v b => some (false, α, j, v, b)
      | _ => none
      | return none
    let (some j', some k') := (← evalNat j, ← evalNat k) | return none
    binderCert (u := e.getAppFn.constLevels![0]!) α close? j j' k' s b e
  /-- `binderOp?` once `e` is split into the index `j` (value `j'`), the variable or term `s` and
  the body `b`. -/
  binderCert {u : Level} (α : Q(Type u)) (close? : Bool) (j : Q(Nat)) (j' k' : Nat) (s : Expr)
      (b : Q(Exp $α)) (e : Expr) : MetaM (Option (Option Expr)) := do
    have k : Q(Nat) := k
    if close? then
      have s : Q(Var) := s
      let some hb ← lcbProof? eqns fvEqns k b | return some none
      have hb : Q(Exp.lcb $k $b = true) := hb
      if j' < k' then
        let some hj ← decideProof? q($j < $k) | return some none
        have hj : Q($j < $k) := hj
        return some q(Exp.lcb_closeRec (x := $s) $hj $hb)
      -- A wrapper left by a step: `s` does not occur, so closing it changes nothing.
      let some hs ← freshProof? s b | return some (← kernelLcb? α k e)
      have hs : Q($s ∉ Exp.fv $b) := hs
      return some q(Exp.lcb_closeRec_of_notMem (j := $j) $hs $hb)
    have s : Q(Exp $α) := s
    if j' < k' then return some (← kernelLcb? α k e)
    if k' < j' then
      let some hb ← lcbProof? eqns fvEqns k b | return some none
      have hb : Q(Exp.lcb $k $b = true) := hb
      let some hkj ← decideProof? q($k ≤ $j) | return some none
      have hkj : Q($k ≤ $j) := hkj
      return some q(Exp.lcb_openRec_of_le (v := $s) $hkj $hb)
    let some hs ← lcbProof? eqns fvEqns k s | return some none
    have hs : Q(Exp.lcb $k $s = true) := hs
    let some hb ← lcbProof? eqns fvEqns q($k + 1) b | return some none
    have hb : Q(Exp.lcb ($k + 1) $b = true) := hb
    return some q(Exp.lcb_openRec $hs $hb)
  /-- Proves `x ∉ e.fv`, through the same wrappers and constructors as `lcbProof?`. -/
  freshProof? (x e : Expr) : MetaM (Option Expr) := do
    let e := e.consumeMData
    let some (close?, α, j, s, b) := match_expr e with
      | Exp.close α b y => some (true, α, mkNatLit 0, y, b)
      | Exp.closeRec α j y b => some (true, α, j, y, b)
      | Exp.open' α b v => some (false, α, mkNatLit 0, v, b)
      | Exp.openRec α j v b => some (false, α, j, v, b)
      | _ => none
      | ctorFresh? x e
    freshCert (u := e.getAppFn.constLevels![0]!) α x close? j s b
  /-- `freshProof?` once `e` is split into the index `j`, the variable or term `s` and the body
  `b`. -/
  freshCert {u : Level} (α : Q(Type u)) (x : Q(Var)) (close? : Bool) (j : Q(Nat)) (s : Expr)
      (b : Q(Exp $α)) : MetaM (Option Expr) := do
    if close? then
      have s : Q(Var) := s
      if x == s || (← decideProof? q($x = $s)).isSome then
        return some q(Exp.notMem_fv_closeRec_self (k := $j) (x := $s) (e := $b))
      let some h ← freshProof? x b | return none
      have h : Q($x ∉ Exp.fv $b) := h
      return some q(Exp.notMem_fv_closeRec (k := $j) (y := $s) $h)
    have s : Q(Exp $α) := s
    let some hs ← freshProof? x s | return none
    have hs : Q($x ∉ Exp.fv $s) := hs
    let some hb ← freshProof? x b | return none
    have hb : Q($x ∉ Exp.fv $b) := hb
    return some q(Exp.notMem_fv_openRec (k := $j) $hs $hb)
  /-- Proves `x ∉ e.fv` by the equation of `fv` at the constructor of `e`. -/
  ctorFresh? (x e : Expr) : MetaM (Option Expr) := do
    let eW ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) e)
    let .const _ us := eW.getAppFn | return none
    let some (eqnPf, rhs) ← unfoldCtor? fvEqns (mkApp (.const ``Exp.fv us) eW.getAppArgs[0]!) eW
      | return none
    let some h ← notMemProof? x rhs | return none
    have x : Q(Var) := x
    have rhs : Q(Finset Var) := rhs
    have lhs : Q(Finset Var) := mkApp2 (.const ``Exp.fv us) eW.getAppArgs[0]! eW
    have eqnPf : Q($lhs = $rhs) := eqnPf
    have h : Q($x ∉ $rhs) := h
    return some q(Eq.mpr (congrArg (fun s => $x ∉ s) $eqnPf) $h)
  /-- Proves `x ∉ s` for the right side `s` of an `fv` equation. -/
  notMemProof? (x s : Expr) : MetaM (Option Expr) := do
    have x : Q(Var) := x
    match_expr s with
    | EmptyCollection.emptyCollection _ _ => return some q(notMem_empty $x)
    | Singleton.singleton _ _ _ y =>
      have y : Q(Var) := y
      let some h ← decideProof? q($x ≠ $y) | return none
      have h : Q($x ≠ $y) := h
      return some q(notMem_singleton.mpr $h)
    | Union.union _ _ s₁ s₂ =>
      let some h₁ ← notMemProof? x s₁ | return none
      let some h₂ ← notMemProof? x s₂ | return none
      have s₁ : Q(Finset Var) := s₁
      have s₂ : Q(Finset Var) := s₂
      have h₁ : Q($x ∉ $s₁) := h₁
      have h₂ : Q($x ∉ $s₂) := h₂
      return some q(notMem_union.mpr ⟨$h₁, $h₂⟩)
    | Exp.fv _ e => freshProof? x e
    | _ => return none
  /-- Proves `b = true` for the right side `b` of an `lcb` equation. -/
  rhsProof? (b : Expr) : MetaM (Option Expr) := do
    match_expr b with
    | Bool.true => return some (← mkEqRefl b)
    | and b₁ b₂ =>
      let some h₁ ← rhsProof? b₁ | return none
      let some h₂ ← rhsProof? b₂ | return none
      have b₁ : Q(Bool) := b₁
      have b₂ : Q(Bool) := b₂
      have h₁ : Q($b₁ = true) := h₁
      have h₂ : Q($b₂ = true) := h₂
      return some q(Bool.and_eq_true_iff.mpr ⟨$h₁, $h₂⟩)
    | Exp.lcb _ k' e' => lcbProof? eqns fvEqns k' e'
    | decide _ _ =>
      unless ← kernelTrue b do return none
      return some (← mkExpectedTypeHint (← mkEqRefl q(true)) (← mkEq b q(true)))
    | _ => return none

/-- Proves `Exp.lcb k e = true` (`e : Exp α`) by `lcbProof?`, else by kernel reduction. -/
public meta def Exp.lcbClosed? (α k e : Expr) : MetaM (Option Expr) := do
  let h? ← try lcbProof? (← eqnTable ``Exp.lcb) (← eqnTable ``Exp.fv) k e catch _ => pure none
  if let some h := h? then return h
  kernelLcb? α k e

-- Returns `some (some v)` for a closed closure, `some none` for an open one, and `none` when
-- `e` is not a `lam`/`fix` or has metavariables, so the caller falls back to `toVal?`.
/-- Decides structurally whether a concrete `lam`/`fix` closure `e : Exp α` is a value. -/
public meta def Exp.closedFunVal? (α e : Expr) : MetaM (Option (Option Expr)) := do
  let e ← instantiateMVars e
  if e.hasExprMVar then return none
  let eW ← whnf e
  let ctor ← if eW.isAppOfArity ``Exp.lam 2 then pure ``IsVal.lam
    else if eW.isAppOfArity ``Exp.fix 2 then pure ``IsVal.fix else return none
  let some h ← lcbClosed? α (mkNatLit 0) eW | return some none
  let lc := mkApp3 (mkConst ``Exp.lcb_imp_lc [0]) α eW h
  let snd := mkApp3 (mkConst ctor) α eW.appArg! lc
  return some (some (mkApp4 (mkConst ``Val.mk) α e snd lc))

/-- Closes `Exp.lcb k e = true` for a concrete closed `e` (see `Exp.lcbProof?`). -/
syntax "lcb_decide" : tactic
elab_rules : tactic
  | `(tactic| lcb_decide) => liftMetaFinishingTactic fun g => g.withContext do
    let ty ← instantiateMVars (← g.getType)
    if ty.hasExprMVar then throwError "lcb_decide: goal contains metavariables"
    let_expr Eq _ lhs rhs := ty | throwError "lcb_decide: goal is not an equation"
    let_expr Exp.lcb α k e := lhs | throwError "lcb_decide: goal is not `Exp.lcb k e = true`"
    unless rhs.isConstOf ``Bool.true do throwError "lcb_decide: goal is not `Exp.lcb k e = true`"
    let some h ← lcbClosed? α k e | throwError "lcb_decide: {e} is not closed"
    g.assign (← mkExpectedTypeHint h ty)

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
        | exact lcb_imp_lc (by lcb_decide)
        | repeat' (first
            | assumption
            | exact lcb_imp_lc (by lcb_decide)
            | exact lc _
            | exact IsLocallyClosed.fvar _
            | exact IsLocallyClosed.lit _
            | exact IsLocallyClosed.fail
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
            | apply IsLocallyClosed.allocN
            | apply IsLocallyClosed.ffi
            | apply IsLocallyClosed.sample | apply IsLocallyClosed.scrut
            | apply IsLocallyClosed.randvar | apply IsLocallyClosed.test))

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
            | exact lcb_imp_lc (by lcb_decide)
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
            | apply IsLocallyClosed.allocN
            | apply IsLocallyClosed.tape
            | apply IsLocallyClosed.ffi | apply IsLocallyClosed.sample
            | apply IsLocallyClosed.scrut | apply IsLocallyClosed.randvar
            | apply IsLocallyClosed.test
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
