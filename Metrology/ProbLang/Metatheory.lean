module

public import Metrology.ProbLang.DetStep
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Syntax.LocallyClosed

@[expose] public section

/-! # ProbLang metatheory

Port of Clutch `metatheory.v`: closedness, substitution maps, head-step trichotomy, tape updates. -/

namespace ProbLang
open Cslib Exp Cfg State MeasureTheory Finset
open Std (ExtTreeMap)

variable {rT : Type _}
variable {α : Type _}

/-! ## Closed contexts and `isClosed`

Port of Clutch's `is_closed` to locally-nameless syntax. -/

/-- A finite set of atoms the free variables may range over. -/
abbrev ClosedCtx := Finset Var

namespace ClosedCtx

/-- The empty set of atoms. -/
def empty : ClosedCtx := ∅

end ClosedCtx

/-- `e` is locally closed with free variables in `X`. -/
def Exp.isClosed (X : ClosedCtx) (e : Exp rT) : Prop := e.IsLocallyClosed ∧ e.fv ⊆ X

/-- A closed expression has no free variables. -/
theorem Exp.notMem_fv_of_isClosed_empty {e : Exp α} (h : e.isClosed .empty) (x : Var) :
    x ∉ e.fv :=
  fun hx => by simpa [ClosedCtx.empty] using h.2 hx

/-- A closed expression has an empty set of free variables. -/
theorem Exp.fv_eq_empty_of_isClosed_empty {e : Exp α} (h : e.isClosed .empty) : e.fv = ∅ :=
  eq_empty_iff_forall_notMem.mpr (notMem_fv_of_isClosed_empty h)

/-! ## Substitution maps -/

/-- A list of `(variable, value)` pairs to substitute. -/
abbrev SubstMap (rT : Type _) := List (Var × Exp rT)

namespace SubstMap

/-- The empty substitution map. -/
def empty : SubstMap rT := []

/-- Cons a pair on the left; it does not shadow an existing binding. -/
def insert (vs : SubstMap rT) (x : Var) (v : Exp rT) : SubstMap rT := (x, v) :: vs

/-- Remove every binding of `x` from the map. -/
def delete (vs : SubstMap rT) (x : Var) : SubstMap rT :=
  vs.filter (fun p => p.1 ≠ x)

/-- Look up a variable; the rightmost binding wins, matching `Exp.substMap`. -/
def lookup : SubstMap rT → Var → Option (Exp rT)
  | [], _ => none
  | (y, v) :: rest, x =>
    match lookup rest x with
    | some w => some w
    | none => if x = y then some v else none

/-- Looking up a variable after `insert` finds an older binding first, then the new one. -/
@[simp] theorem lookup_insert (vs : SubstMap rT) (x y : Var) (v : Exp rT) :
    (vs.insert x v).lookup y =
      match vs.lookup y with
        | some w => some w
        | none => if y = x then some v else none := rfl

end SubstMap
open SubstMap

/-- Substitutes the pairs of `vs` sequentially, rightmost pair first (`SubstMap.AllClosed` makes
this agree with simultaneous substitution). -/
def Exp.substMap (vs : SubstMap rT) (e : Exp rT) : Exp rT :=
  vs.foldr (fun p acc => subst acc p.1 p.2) e

/-- The empty substitution map leaves an expression unchanged. -/
@[simp] theorem Exp.substMap_empty (e : Exp rT) : e.substMap .empty = e := rfl

/-- Substituting an inserted pair substitutes it after the rest of the map. -/
@[simp] theorem Exp.substMap_insert (vs : SubstMap rT) (x : Var) (v e : Exp rT) :
    e.substMap (vs.insert x v) = subst (e.substMap vs) x v := rfl

/-- Substituting a cons-ed pair substitutes it after the rest of the map. -/
@[simp] theorem Exp.substMap_cons (p : Var × Exp rT) (vs : SubstMap rT) (e : Exp rT) :
    e.substMap (p :: vs) = subst (e.substMap vs) p.1 p.2 := rfl

/-! ### Substitution and closedness -/

/-! ### Commutation of substitutions -/

/-- Substitutions at different variables commute when `v'` has no `x` free. -/
theorem Exp.subst_subst {e v v' : Exp α} {x : Var} {y : Var}
    (hne : x ≠ y) (hv' : x ∉ v'.fv) :
    subst (subst e x v) y v' =
      subst (subst e y v') x (subst v y v') := by
  induction e with
  | fvar z =>
      by_cases h1 : x = z <;> by_cases h2 : y = z
      · subst h1; exact absurd h2 hne.symm
      · subst h1
        simp [subst, h2]
      · subst h2
        simp [subst, h1, subst_fresh _ _ _ hv']
      · simp [subst, h1, h2]
  | bvar _ | lit _ | fail | urand => rfl
  | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
      simp [subst, ih]
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
      simp [subst, ih1, ih2]
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
      simp [subst, ih0, ih1, ih2]

/-- Independence of substitutions at distinct, mutually-fresh variables. -/
theorem Exp.subst_subst_ne {e v v' : Exp α} {x y : Var}
    (hne : x ≠ y) (hxv' : x ∉ v'.fv) (hyv : y ∉ v.fv) :
    subst (subst e x v) y v' = subst (subst e y v') x v := by
  rw [subst_subst hne hxv', subst_fresh y v v' hyv]

/-! ### Closed substitution maps -/

/-- Every value in `vs` is closed. -/
def SubstMap.AllClosed (vs : SubstMap rT) : Prop :=
  ∀ p ∈ vs, p.2.isClosed .empty

/-- The empty substitution map has only closed values. -/
theorem SubstMap.allClosed_nil : AllClosed ([] : SubstMap rT) :=
  fun _ hp => nomatch hp

/-- A cons-ed map has only closed values iff its head value and its tail do. -/
theorem SubstMap.allClosed_cons {x : Var} {v : Exp rT} {vs : SubstMap rT} :
    AllClosed ((x, v) :: vs) ↔ v.isClosed .empty ∧ AllClosed vs := by
  constructor
  · intro h
    exact ⟨h (x, v) List.mem_cons_self, fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
  · rintro ⟨hv, hvs⟩ p hp
    rcases List.mem_cons.mp hp with rfl | hpm
    · exact hv
    · exact hvs p hpm

/-- Filtering a map with only closed values leaves only closed values. -/
theorem SubstMap.allClosed_filter (vs : SubstMap rT) (P : Var × Exp rT → Bool)
    (h : AllClosed vs) :
    AllClosed (vs.filter P) :=
  fun p hp => h p (List.mem_filter.mp hp).1

/-- Filtering out a variable outside the domain leaves the map unchanged. -/
theorem SubstMap.filter_notMem_dom (vs : SubstMap rT) {y : Var}
    (h : y ∉ (vs.map (·.1)).toFinset) :
    vs.filter (fun p => !decide (p.1 = y)) = vs := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, w⟩ := p
    have hky : k ≠ y := by intro hk; apply h; rw [hk]; simp
    have hyRest : y ∉ (rest.map (·.1)).toFinset := fun h' => h (by simp at h' ⊢; exact Or.inr h')
    simp [hky, ih hyRest]

/-- The pair returned by `lookup` is the rightmost matching member. -/
theorem SubstMap.mem_of_lookup_eq_some {vs : SubstMap rT} {y : Var} {w : Exp rT}
    (h : vs.lookup y = some w) : (y, w) ∈ vs := by
  induction vs with
  | nil => simp [lookup] at h
  | cons p rest ih =>
    obtain ⟨z, v⟩ := p
    simp only [lookup] at h
    cases hr : lookup rest y with
    | some w' =>
      obtain rfl : w' = w := by simpa [hr] using h
      exact List.mem_cons_of_mem _ (ih hr)
    | none =>
      rw [hr] at h
      split_ifs at h with hyz
      obtain rfl := Option.some.inj h
      exact hyz ▸ List.mem_cons_self

/-- A variable in the domain has some binding. -/
theorem SubstMap.lookup_isSome_of_mem_dom {vs : SubstMap rT} {y : Var}
    (h : y ∈ (vs.map (·.1)).toFinset) : (vs.lookup y).isSome := by
  simp only [List.mem_toFinset, List.mem_map] at h
  obtain ⟨q, hqmem, hqeq⟩ := h
  induction vs with
  | nil => exact absurd hqmem (by simp)
  | cons p rest ih =>
    obtain ⟨z, v⟩ := p
    rcases List.mem_cons.mp hqmem with rfl | hpm
    · obtain rfl : z = y := hqeq
      simp only [lookup]
      cases lookup rest z <;> simp
    · simp only [lookup]
      cases hrr : lookup rest y with
      | some _ => simp
      | none => simpa [hrr] using ih hpm

/-- `substMap` commutes with `subst _ x (.fvar y)` when `x`, `y` avoid `vs`'s domain. -/
theorem Exp.substMap_subst_fvar_comm
    (vs : SubstMap rT) (E : Exp rT) (x y : Var)
    (hxNotDom : x ∉ (vs.map (·.1)).toFinset)
    (hyNotDom : y ∉ (vs.map (·.1)).toFinset)
    (hvs : AllClosed vs) :
    substMap vs (subst E x (.fvar y)) =
      subst (substMap vs E) x (.fvar y) := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    have hzx : z ≠ x := fun h => hxNotDom (h ▸ by simp)
    have hzy : z ≠ y := fun h => hyNotDom (h ▸ by simp)
    have hxNotRest : x ∉ (rest.map (·.1)).toFinset := fun h => hxNotDom (by simp [h])
    have hyNotRest : y ∉ (rest.map (·.1)).toFinset := fun h => hyNotDom (by simp [h])
    obtain ⟨hw_closed, hvs_rest⟩ := allClosed_cons.mp hvs
    have hzNotFvY : z ∉ (fvar (rT := rT) y).fv := by simpa [fv] using hzy
    rw [substMap_cons, substMap_cons, ih hxNotRest hyNotRest hvs_rest,
      ← subst_subst_ne hzx hzNotFvY (notMem_fv_of_isClosed_empty hw_closed x)]

/-! ### `substMap` through constructors

The `substMap_hom*` lemmas lift "`subst` commutes with this constructor" along the fold.
(Clutch gets these by `simpl`, since its `subst_map` is simultaneous.) -/

/-- `substMap` goes through a constant constructor. -/
theorem Exp.substMap_hom₀ (C : Exp rT) (hC : ∀ x v, subst C x v = C)
    (vs : SubstMap rT) : C.substMap vs = C := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => simp only [substMap_cons, ih, hC]

/-- `substMap` goes through a unary constructor. -/
theorem Exp.substMap_hom₁ (C : Exp rT → Exp rT)
    (hC : ∀ e x v, subst (C e) x v = C (subst e x v))
    (vs : SubstMap rT) (e : Exp rT) :
    (C e).substMap vs = C (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => simp only [substMap_cons, ih, hC]

/-- `substMap` goes through a binary constructor. -/
theorem Exp.substMap_hom₂ (C : Exp rT → Exp rT → Exp rT)
    (hC : ∀ e1 e2 x v, subst (C e1 e2) x v = C (subst e1 x v) (subst e2 x v))
    (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (C e1 e2).substMap vs = C (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => simp only [substMap_cons, ih, hC]

/-- `substMap` goes through a ternary constructor. -/
theorem Exp.substMap_hom₃ (C : Exp rT → Exp rT → Exp rT → Exp rT)
    (hC : ∀ e0 e1 e2 x v, subst (C e0 e1 e2) x v = C (subst e0 x v) (subst e1 x v) (subst e2 x v))
    (vs : SubstMap rT) (e0 e1 e2 : Exp rT) :
    (C e0 e1 e2).substMap vs =
      C (e0.substMap vs) (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => simp only [substMap_cons, ih, hC]

/-- `substMap` goes through `lit`. -/
@[simp] theorem Exp.substMap_lit (vs : SubstMap rT) (b : BaseLit rT) :
    (lit b).substMap vs = .lit b :=
  substMap_hom₀ _ (by intros; simp [subst]) vs

/-- `substMap` goes through `bvar`. -/
@[simp] theorem Exp.substMap_bvar (vs : SubstMap rT) (j : Nat) :
    (bvar j).substMap vs = .bvar j :=
  substMap_hom₀ _ (by intros; simp [subst]) vs

/-- `substMap` goes through `fail`. -/
@[simp] theorem Exp.substMap_fail (vs : SubstMap rT) :
    fail.substMap vs = .fail :=
  substMap_hom₀ _ (by intros; simp [subst]) vs

/-- `substMap` goes through `urand`. -/
@[simp] theorem Exp.substMap_urand (vs : SubstMap rT) :
    urand.substMap vs = .urand :=
  substMap_hom₀ _ (by intros; simp [subst]) vs

/-- `substMap` goes through `pair`. -/
@[simp] theorem Exp.substMap_pair (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (pair e1 e2).substMap vs = .pair (e1.substMap vs) (e2.substMap vs) :=
  substMap_hom₂ _ (by intros; simp [subst]) vs e1 e2

/-- `substMap` goes through `fst`. -/
@[simp] theorem Exp.substMap_fst (vs : SubstMap rT) (e : Exp rT) :
    (fst e).substMap vs = .fst (e.substMap vs) :=
  substMap_hom₁ _ (by intros; simp [subst]) vs e

/-- `substMap` goes through `snd`. -/
@[simp] theorem Exp.substMap_snd (vs : SubstMap rT) (e : Exp rT) :
    (snd e).substMap vs = .snd (e.substMap vs) :=
  substMap_hom₁ _ (by intros; simp [subst]) vs e

/-- `substMap` goes through `inl`. -/
@[simp] theorem Exp.substMap_inl (vs : SubstMap rT) (e : Exp rT) :
    (inl e).substMap vs = .inl (e.substMap vs) :=
  substMap_hom₁ _ (by intros; simp [subst]) vs e

/-- `substMap` goes through `inr`. -/
@[simp] theorem Exp.substMap_inr (vs : SubstMap rT) (e : Exp rT) :
    (inr e).substMap vs = .inr (e.substMap vs) :=
  substMap_hom₁ _ (by intros; simp [subst]) vs e

/-- `substMap` goes through `case`. -/
@[simp] theorem Exp.substMap_case (vs : SubstMap rT) (e0 e1 e2 : Exp rT) :
    (case e0 e1 e2).substMap vs =
      .case (e0.substMap vs) (e1.substMap vs) (e2.substMap vs) :=
  substMap_hom₃ _ (by intros; simp [subst]) vs e0 e1 e2

/-- `substMap` goes through `cond`. -/
@[simp] theorem Exp.substMap_cond (vs : SubstMap rT) (e0 e1 e2 : Exp rT) :
    (cond e0 e1 e2).substMap vs =
      .cond (e0.substMap vs) (e1.substMap vs) (e2.substMap vs) :=
  substMap_hom₃ _ (by intros; simp [subst]) vs e0 e1 e2

/-- `substMap` goes through `app`. -/
@[simp] theorem Exp.substMap_app (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (app e1 e2).substMap vs = .app (e1.substMap vs) (e2.substMap vs) :=
  substMap_hom₂ _ (by intros; simp [subst]) vs e1 e2

/-- `substMap` goes through `lam`. -/
@[simp] theorem Exp.substMap_lam (vs : SubstMap rT) (e : Exp rT) :
    (lam e).substMap vs = .lam (e.substMap vs) :=
  substMap_hom₁ _ (by intros; simp [subst]) vs e

/-- `substMap` goes through `fix`. -/
@[simp] theorem Exp.substMap_fix (vs : SubstMap rT) (e : Exp rT) :
    (fix e).substMap vs = .fix (e.substMap vs) :=
  substMap_hom₁ _ (by intros; simp [subst]) vs e

/-- `substMap` goes through `unop`. -/
@[simp] theorem Exp.substMap_unop (vs : SubstMap rT) (op : UnOp) (e : Exp rT) :
    (unop op e).substMap vs = .unop op (e.substMap vs) :=
  substMap_hom₁ (unop op) (by intros; simp [subst]) vs e

/-- `substMap` goes through `binop`. -/
@[simp] theorem Exp.substMap_binop (vs : SubstMap rT) (op : BinOp) (e1 e2 : Exp rT) :
    (binop op e1 e2).substMap vs =
      .binop op (e1.substMap vs) (e2.substMap vs) :=
  substMap_hom₂ (binop op) (by intros; simp [subst]) vs e1 e2

/-- `substMap` goes through `alloc`. -/
@[simp] theorem Exp.substMap_alloc (vs : SubstMap rT) (e : Exp rT) :
    (alloc e).substMap vs = .alloc (e.substMap vs) :=
  substMap_hom₁ _ (by intros; simp [subst]) vs e

/-- `substMap` goes through `load`. -/
@[simp] theorem Exp.substMap_load (vs : SubstMap rT) (e : Exp rT) :
    (load e).substMap vs = .load (e.substMap vs) :=
  substMap_hom₁ _ (by intros; simp [subst]) vs e

/-- `substMap` goes through `store`. -/
@[simp] theorem Exp.substMap_store (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (store e1 e2).substMap vs = .store (e1.substMap vs) (e2.substMap vs) :=
  substMap_hom₂ _ (by intros; simp [subst]) vs e1 e2

/-- `substMap` goes through `tape`. -/
@[simp] theorem Exp.substMap_tape (vs : SubstMap rT) (e : Exp rT) :
    (tape e).substMap vs = .tape (e.substMap vs) :=
  substMap_hom₁ _ (by intros; simp [subst]) vs e

/-- `substMap` goes through `rand`. -/
@[simp] theorem Exp.substMap_rand (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (rand e1 e2).substMap vs = .rand (e1.substMap vs) (e2.substMap vs) :=
  substMap_hom₂ _ (by intros; simp [subst]) vs e1 e2

/-- `substMap` goes through `scrut`. -/
@[simp] theorem Exp.substMap_scrut (vs : SubstMap rT) (e : Exp rT) (p : Pat rT) :
    (scrut e p).substMap vs = .scrut (e.substMap vs) p :=
  substMap_hom₁ (scrut · p) (by intros; simp [subst]) vs e

/-- A closed substitution map commutes with `openRec`. -/
theorem Exp.substMap_openRec (vs : SubstMap rT) (k : Nat) (u e : Exp rT)
    (hClosed : AllClosed vs) :
    substMap vs (openRec k u e) =
      openRec k (substMap vs u) (substMap vs e) := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    obtain ⟨hwClosed, hRestClosed⟩ := allClosed_cons.mp hClosed
    rw [substMap_cons, ih hRestClosed, substMap_cons, substMap_cons]
    exact subst_openRec y w k _ _ hwClosed.1

/-- A closed substitution map commutes with `open'`. -/
theorem Exp.substMap_open (vs : SubstMap rT) (u e : Exp rT)
    (hClosed : AllClosed vs) :
    substMap vs (open' e u) =
      open' (substMap vs e) (substMap vs u) :=
  substMap_openRec vs 0 u e hClosed

section

variable {vs : SubstMap rT} {e : Exp rT} {x : Var} {v : Exp rT}

/-- A closed substitution map introduces no new free variables. -/
theorem Exp.notFv_substMap
    (hClosed : AllClosed vs) (hx : x ∉ e.fv) :
    x ∉ (substMap vs e).fv := by
  induction vs with
  | nil => exact hx
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    obtain ⟨hwClosed, hRestClosed⟩ := allClosed_cons.mp hClosed
    rw [substMap_cons]
    intro hmem
    rcases mem_union.mp (fv_subst_subset (substMap rest e) y w hmem) with h1 | h2
    · exact ih hRestClosed (mem_sdiff.mp h1).1
    · exact notMem_fv_of_isClosed_empty hwClosed x h2

/-- Substituting a variable outside the map's domain leaves it unchanged. -/
theorem Exp.substMap_fvar_lookup_none
    (hv : lookup vs x = none) :
    substMap vs (.fvar x) = .fvar x := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    simp only [lookup] at hv
    cases hr : lookup rest x with
    | some w' => rw [hr] at hv; cases hv
    | none =>
      rw [hr] at hv
      simp only at hv
      split_ifs at hv with hxy
      rw [substMap_cons, ih hr]
      simp [subst, Ne.symm hxy]

/-- A value found by `lookup` in a map with only closed values is closed. -/
theorem SubstMap.lookup_closed
    (hv : lookup vs x = some v) (hClosed : AllClosed vs) :
    v.isClosed .empty := by
  induction vs with
  | nil => simp [lookup] at hv
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    rw [allClosed_cons] at hClosed
    simp only [lookup] at hv
    cases hr : lookup rest x with
    | some w' =>
      rw [hr] at hv
      injection hv with hw'v
      subst hw'v
      exact ih hr hClosed.2
    | none =>
      rw [hr] at hv
      simp only at hv
      split_ifs at hv with hxy
      injection hv with hwv
      subst hwv
      exact hClosed.1

/-- Opening a body at a fresh atom `x`, then binding `x ↦ v`, opens the substituted body at `v`. -/
theorem Exp.substMap_open_fresh
    (hClosed : AllClosed vs) (hxFv : x ∉ e.fv)
    (hxDom : lookup vs x = none) (hvLC : v.IsLocallyClosed) :
    substMap ((x, v) :: vs) (open' e (.fvar x)) =
      open' (substMap vs e) v := by
  show subst (substMap vs (open' e (.fvar x))) x v =
    open' (substMap vs e) v
  rw [substMap_open _ _ _ hClosed, substMap_fvar_lookup_none hxDom,
    subst_intro x v _ (notFv_substMap hClosed hxFv) hvLC]

/-- A closed substitution map preserves local closedness. -/
theorem Exp.substMap_lc
    (hClosed : AllClosed vs) (he : e.IsLocallyClosed) :
    (substMap vs e).IsLocallyClosed := by
  induction vs with
  | nil => exact he
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    obtain ⟨hwClosed, hRestClosed⟩ := allClosed_cons.mp hClosed
    exact subst_lc (ih hRestClosed) hwClosed.1

/-- Substituting closed values into the body of a locally closed `lam` keeps it locally closed. -/
theorem Exp.lam_substMap_isLocallyClosed {σ : SubstMap rT} {L D : Finset Var}
    (hσ : AllClosed σ) (hdom : ∀ y ∉ D, lookup σ y = none)
    (he : ∀ x ∉ L, (open' e (.fvar x)).IsLocallyClosed) :
    (lam (substMap σ e)).IsLocallyClosed := by
  refine IsLocallyClosed.lam (L ∪ D) _ ?_
  intro y hy
  have hyL : y ∉ L := fun h => hy (mem_union_left _ h)
  have hyD : y ∉ D := fun h => hy (mem_union_right _ h)
  have hbridge : substMap σ (open' e (.fvar y)) =
      open' (substMap σ e) (.fvar y) := by
    rw [substMap_open _ _ _ hσ, substMap_fvar_lookup_none (hdom y hyD)]
  rw [← hbridge]
  exact substMap_lc hσ (he y hyL)

/-- Substituting closed values into the body of a locally closed `fix` keeps it locally closed. -/
theorem Exp.fix_substMap_isLocallyClosed {σ : SubstMap rT} {L D : Finset Var}
    (hσ : AllClosed σ) (hdom : ∀ y ∉ D, lookup σ y = none)
    (he : ∀ x ∉ L, (open' e (.fvar x)).IsLocallyClosed) :
    (fix (substMap σ e)).IsLocallyClosed := by
  refine IsLocallyClosed.fix (L ∪ D) _ ?_
  intro y hy
  have hbridge : substMap σ (open' e (.fvar y)) =
      open' (substMap σ e) (.fvar y) := by
    rw [substMap_open _ _ _ hσ,
      substMap_fvar_lookup_none (hdom y fun h => hy (mem_union_right _ h))]
  rw [← hbridge]
  exact substMap_lc hσ (he y fun h => hy (mem_union_left _ h))

/-- After a closed substitution map, the free variables lie outside its domain. -/
theorem Exp.fv_substMap_sdiff_dom
    (hClosed : AllClosed vs) :
    (substMap vs e).fv ⊆ e.fv \ (vs.map (·.1)).toFinset := by
  induction vs generalizing e with
  | nil =>
    simp [substMap]
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    obtain ⟨hwClosed, hRestClosed⟩ := allClosed_cons.mp hClosed
    rw [substMap_cons]
    intro y hy
    rcases mem_union.mp (fv_subst_subset (substMap rest e) z w hy) with hL | hR
    · obtain ⟨hyRest, hyNeZ⟩ := mem_sdiff.mp hL
      obtain ⟨hyE, hyDom⟩ := mem_sdiff.mp (ih hRestClosed hyRest)
      simp only [mem_sdiff, List.map_cons, List.toFinset_cons, mem_insert,
        not_or]
      exact ⟨hyE, fun h => hyNeZ (by simp [h]), hyDom⟩
    · exact absurd hR (notMem_fv_of_isClosed_empty hwClosed y)

/-- A closed substitution map whose domain covers the free variables gives a closed result. -/
theorem Exp.substMap_fv_eq_empty
    (hClosed : AllClosed vs)
    (hsub : e.fv ⊆ (vs.map (·.1)).toFinset) :
    (substMap vs e).fv = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  obtain ⟨hyE, hyDom⟩ := mem_sdiff.mp (fv_substMap_sdiff_dom hClosed hy)
  exact hyDom (hsub hyE)

end

/-- `substMap` commutes with renaming `x` to a variable `y` that the map binds. -/
theorem Exp.substMap_subst_fvar_lookup
    (vs : SubstMap rT) (E : Exp rT) (x y : Var) (w : Exp rT)
    (hxNotDom : x ∉ (vs.map (·.1)).toFinset)
    (hvs : AllClosed vs)
    (hyLookup : vs.lookup y = some w)
    (hyFvE : y ∉ E.fv) :
    substMap vs (subst E x (.fvar y)) =
      subst (substMap (vs.filter (fun p => !decide (p.1 = y))) E) x w := by
  have hw_closed : w.isClosed .empty :=
    hvs (y, w) (mem_of_lookup_eq_some hyLookup)
  induction vs with
  | nil => simp [lookup] at hyLookup
  | cons p rest ih =>
    obtain ⟨z, v⟩ := p
    have hcons1 : substMap ((z, v) :: rest) (subst E x (.fvar y)) =
        subst (substMap rest (subst E x (.fvar y))) z v := rfl
    have hzx : z ≠ x := fun h => hxNotDom (h ▸ by simp)
    have hxNotRest : x ∉ (rest.map (·.1)).toFinset := fun h => hxNotDom (by simp [h])
    obtain ⟨hv_closed, hvs_rest⟩ := allClosed_cons.mp hvs
    rw [hcons1]
    by_cases hzy : z = y
    · simp only [hzy, lookup] at hyLookup
      cases hr : lookup rest y with
      | some w' =>
        -- z = y and rest also binds y: the head binding is shadowed (rightmost wins); the filter
        -- drops it and y is not free
        rw [hr] at hyLookup
        have hw'eq : w' = w := by injection hyLookup
        rw [hw'eq] at hr
        rw [ih hxNotRest hvs_rest hr]
        have hfilter_cons :
            ((z, v) :: rest).filter (fun p => !decide (p.1 = y)) =
              rest.filter (fun p => !decide (p.1 = y)) := by simp [hzy]
        rw [hfilter_cons]
        rw [hzy]
        have hfilter_closed : AllClosed (rest.filter (fun p => !decide (p.1 = y))) :=
          allClosed_filter rest _ hvs_rest
        have hyNotFinner : y ∉ (substMap (rest.filter (fun p => !decide (p.1 = y))) E).fv :=
          notFv_substMap hfilter_closed hyFvE
        have hyNotFsubst :
            y ∉ (subst (substMap (rest.filter (fun p => !decide (p.1 = y))) E) x w).fv := by
          intro hy
          have := fv_subst_subset _ x w hy
          rcases mem_union.mp this with h1 | h2
          · exact hyNotFinner (mem_sdiff.mp h1).1
          · exact notMem_fv_of_isClosed_empty hw_closed y h2
        rw [subst_fresh y _ v hyNotFsubst]
      | none =>
        -- z = y is the binding of y: rename x ↦ y ↦ v with `substMap_subst_fvar_comm` and
        -- `subst_subst_fvar_id`
        rw [hr] at hyLookup
        simp at hyLookup
        subst hyLookup
        have hfilter_cons :
            ((z, v) :: rest).filter (fun p => !decide (p.1 = y)) =
              rest.filter (fun p => !decide (p.1 = y)) := by simp [hzy]
        rw [hfilter_cons]
        have hyNotRest : y ∉ (rest.map (·.1)).toFinset := by
          intro h
          have := lookup_isSome_of_mem_dom h
          rw [hr] at this
          cases this
        have hcomm := substMap_subst_fvar_comm rest E x y hxNotRest hyNotRest hvs_rest
        rw [hcomm]
        have hyNotInner : y ∉ (substMap rest E).fv :=
          notFv_substMap hvs_rest hyFvE
        rw [filter_notMem_dom rest hyNotRest, hzy]
        exact subst_subst_fvar_id (substMap rest E) v x y hyNotInner
    · -- z ≠ y: commute the head substitution past `subst _ x w`
      simp only [lookup] at hyLookup
      cases hr : lookup rest y with
      | some w' =>
        rw [hr] at hyLookup
        have hw'eq : w' = w := by injection hyLookup
        rw [hw'eq] at hr
        rw [ih hxNotRest hvs_rest hr]
        have hfilter_cons :
            ((z, v) :: rest).filter (fun p => !decide (p.1 = y)) =
              (z, v) :: rest.filter (fun p => !decide (p.1 = y)) := by simp [hzy]
        rw [hfilter_cons]
        rw [subst_subst_ne (Ne.symm hzx) (notMem_fv_of_isClosed_empty hv_closed x)
          (notMem_fv_of_isClosed_empty hw_closed z)]
        rfl
      | none =>
        rw [hr] at hyLookup
        simp [Ne.symm hzy] at hyLookup

/-- Substituting a variable bound in a closed map gives its value. -/
theorem Exp.substMap_fvar_lookup_some (vs : SubstMap rT) (x : Var)
    (hClosed : AllClosed vs) :
    ∀ {v : Exp rT}, lookup vs x = some v → substMap vs (.fvar x) = v := by
  induction vs with
  | nil => intro v hv; simp [lookup] at hv
  | cons p rest ih =>
    intro v hv
    obtain ⟨y, w⟩ := p
    rw [allClosed_cons] at hClosed
    obtain ⟨hwClosed, hRestClosed⟩ := hClosed
    rw [substMap_cons]
    simp only [lookup] at hv
    cases hr : lookup rest x with
    | some w' =>
      rw [hr] at hv
      injection hv with hw'v
      subst hw'v
      rw [ih hRestClosed hr]
      exact subst_fresh _ _ _
        (notMem_fv_of_isClosed_empty (lookup_closed hr hRestClosed) y)
    | none =>
      rw [hr] at hv
      simp only at hv
      split_ifs at hv with hxy
      injection hv with hwv
      subst hwv
      subst hxy
      rw [substMap_fvar_lookup_none hr]
      show (fvar x).subst x w = w
      simp [subst]

variable [MeasurableSpace rT]

/-! ## `Cfg.uniform` -/

variable {z : Int}

/-- A non-positive bound makes `Cfg.uniform` the Dirac at `-1`. -/
theorem Cfg.uniform_nonpos_eq {σ : State rT} (hz : ¬ 0 < z) :
    uniform z σ = Measure.dirac ⟨.lit (.int (-1)), σ⟩ := by
  unfold uniform Int.isPos
  rw [dite_eq_right hz]

/-- `Cfg.uniform` is never the zero measure. -/
theorem Cfg.uniform_ne_zero
    (z : Int) (σ : State rT) : uniform z σ ≠ 0 :=
  IsProbabilityMeasure.ne_zero _

/-- Reindex a sum over `Ico 0 z` along a map that restricts to a bijection on it. -/
theorem _root_.Finset.sum_Ico_comp_of_bijOn {M : Type _} [AddCommMonoid M]
    {f : Int → Int}
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (g : Int → M) :
    ∑ n ∈ Ico (0 : Int) z, g (f n) = ∑ m ∈ Ico (0 : Int) z, g m := by
  refine sum_bij (fun n _ => f n) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_Ico] at hn ⊢
    exact hdom n hn.1 hn.2
  · intro n₁ hn₁ n₂ hn₂ h
    simp only [mem_Ico] at hn₁ hn₂
    obtain ⟨n₀, -, huniq⟩ := hbij (f n₁) (hdom n₁ hn₁.1 hn₁.2).1 (hdom n₁ hn₁.1 hn₁.2).2
    exact (huniq n₁ ⟨hn₁, rfl⟩).trans (huniq n₂ ⟨hn₂, h.symm⟩).symm
  · intro m hm
    simp only [mem_Ico] at hm
    obtain ⟨n₀, ⟨hn₀, hfn₀⟩, -⟩ := hbij m hm.1 hm.2
    exact ⟨n₀, by simp only [mem_Ico]; exact hn₀, hfn₀⟩
  · intro n _; rfl

/-- For `0 < z`, `Cfg.uniform` is the uniform measure on `Ico 0 z` as configurations. -/
theorem Cfg.uniform_eq_map_uniformOfFinset (hz : 0 < z) (σ : State rT) :
    uniform z σ = (PMF.uniformOfFinset (Ico (0 : Int) z) (nonempty_Ico.mpr hz)).toMeasure.map
      (fun n : Int => (⟨.lit (.int n), σ⟩ : Cfg rT)) := by
  unfold uniform Int.isPos; simp only [dite_eq_left hz]

/-- The integral of a measurable `φ` against `Cfg.uniform z σ` is its average over `Ico 0 z`. -/
theorem Cfg.lintegral_uniform
    (Hz : 0 < z) (σ : State rT)
    {φ : Cfg rT → ENNReal} (hφ : Measurable φ) :
    ∫⁻ c, φ c ∂(uniform z σ) =
      ((z.toNat : ENNReal)⁻¹) * ∑ n ∈ Ico (0 : Int) z,
          φ (⟨.lit (.int n), σ⟩ : Cfg rT) := by
  have hcard : (Ico (0 : Int) z).card = z.toNat := by rw [Int.card_Ico]; omega
  rw [uniform_eq_map_uniformOfFinset Hz σ,
      lintegral_map hφ Measurable.of_discrete,
      lintegral_countable',
      tsum_eq_sum (s := Ico (0 : Int) z) fun n hn => by
        rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
            PMF.uniformOfFinset_apply_of_notMem _ hn, mul_zero],
      mul_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
      PMF.uniformOfFinset_apply_of_mem _ hn, hcard, mul_comm]

variable [LawfulProbLangℝ rT]

/-! ## Deterministic and probabilistic head steps

Clutch's `metatheory.v` ~1448–1713, minus Laplace/Tick. The export is `det_or_prob_or_zero`. -/

/-- Non-sampling head redexes; the step is a Dirac but may read the heap or tapes. -/
inductive DetHeadStepPred : Exp rT → State rT → Prop
  | betaLam {e1 e2 σ} : e2.isValue →
      DetHeadStepPred (.app (.lam e1) e2) σ
  | betaFix {e1 e2 σ} : e2.isValue →
      DetHeadStepPred (.app (.fix e1) e2) σ
  | unop {op e σ e'} : e.isValue → op.eval e = some e' →
      DetHeadStepPred (.unop op e) σ
  | binop {op e1 e2 σ e'} : e1.isValue → e2.isValue → op.eval e1 e2 = some e' →
      DetHeadStepPred (.binop op e1 e2) σ
  | ifTrue {et ef σ} : DetHeadStepPred (.cond (.lit (.bool true)) et ef) σ
  | ifFalse {et ef σ} : DetHeadStepPred (.cond (.lit (.bool false)) et ef) σ
  | fst {e1 e2 σ} : e1.isValue → e2.isValue →
      DetHeadStepPred (.fst (.pair e1 e2)) σ
  | snd {e1 e2 σ} : e1.isValue → e2.isValue →
      DetHeadStepPred (.snd (.pair e1 e2)) σ
  | caseL {e el er σ} : e.isValue →
      DetHeadStepPred (.case (.inl e) el er) σ
  | caseR {e el er σ} : e.isValue →
      DetHeadStepPred (.case (.inr e) el er) σ
  | alloc {ed σ} : ed.isValue → DetHeadStepPred (.alloc ed) σ
  | load {ℓ v σ} : σ.heap[ℓ]? = some v →
      DetHeadStepPred (.load (.lit (.loc ℓ))) σ
  | store {ℓ e σ} : e.isValue → σ.heap[ℓ]?.isSome →
      DetHeadStepPred (.store (.lit (.loc ℓ)) e) σ
  | tape {z σ} : DetHeadStepPred (.tape (.lit (.int z))) σ
  | scrutSuccess {e p σ bindings} : e.isValue → Pat.tryMatch p e = some bindings →
      DetHeadStepPred (.scrut e p) σ
  | scrutFailure {e p σ} : e.isValue → Pat.tryMatch p e = none →
      DetHeadStepPred (.scrut e p) σ

/-- `rand` redexes, split by tape situation (including non-positive bounds, which step to `-1`),
and `urand`. -/
inductive ProbHeadStepPred : Exp rT → State rT → Prop
/-- Tapeless `rand` with `z > 0`: uniform. -/
  | randNoTape {z σ} : 0 < z →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit .unit)) σ
/-- A tape of bound `z` with a head `n`: pop `n`. -/
  | randTape {z α σ N nn ns} : σ.tapes[α]? = some ⟨N, nn :: ns⟩ → z = N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
/-- An empty tape of bound `z`: uniform. -/
  | randTapeEmpty {z α σ N} : 0 < z → σ.tapes[α]? = some ⟨N, []⟩ → z = N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
/-- A tape whose bound is not `z`: ignore the tape, uniform. -/
  | randTapeOther {z α σ N L} : 0 < z → σ.tapes[α]? = some ⟨N, L⟩ → z ≠ N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
/-- Tapeless `rand` with `z ≤ 0`: Dirac at `-1`. -/
  | randNonpos {z σ} : ¬ 0 < z →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit .unit)) σ
/-- `z ≤ 0` on an empty tape of bound `z`: Dirac at `-1`. -/
  | randTapeNonposEmpty {z α σ N} : ¬ 0 < z → σ.tapes[α]? = some ⟨N, []⟩ → z = N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
/-- `z ≤ 0` on a tape whose bound is not `z`: Dirac at `-1`. -/
  | randTapeNonposOther {z α σ N L} : ¬ 0 < z → σ.tapes[α]? = some ⟨N, L⟩ → z ≠ N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
  | urand {σ} : ProbHeadStepPred urand σ

/-- `e` is a head redex in state `σ`. -/
def HeadStepPred (e : Exp rT) (σ : State rT) : Prop :=
  DetHeadStepPred e σ ∨ ProbHeadStepPred e σ

/-- `HeadStepPred` holds iff the head step has some support point. -/
theorem headStepPred_iff_exists_support (e : Exp rT) (σ : State rT) :
    HeadStepPred e σ ↔ ∃ ρ', HeadStepSupport ⟨e, σ⟩ ρ' := by
  constructor
  · rintro (hdet | hprob)
    · cases hdet with
      | betaLam hv => exact ⟨_, .BetaLamS hv rfl⟩
      | betaFix hv => exact ⟨_, .BetaFixS hv rfl⟩
      | unop hv heval => exact ⟨_, .UnOpS hv heval.symm⟩
      | binop hv1 hv2 heval => exact ⟨_, .BinOpS hv1 hv2 heval.symm⟩
      | ifTrue => exact ⟨_, .IfTrueS⟩
      | ifFalse => exact ⟨_, .IfFalseS⟩
      | fst hv1 hv2 => exact ⟨_, .FstS hv1 hv2⟩
      | snd hv1 hv2 => exact ⟨_, .SndS hv1 hv2⟩
      | caseL hv => exact ⟨_, .CaseLS hv⟩
      | caseR hv => exact ⟨_, .CaseRS hv⟩
      | @alloc ed σ hv =>
          have : ed.toVal?.isSome := by
            rw [Option.isSome_iff_ne_none]
            intro h
            exact (toVal?_eq_none.mp h) hv
          obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp this
          exact ⟨_, .AllocS hv' rfl rfl⟩
      | load hlook => exact ⟨_, .LoadS hlook rfl⟩
      | @store ℓ e σ hv hsome =>
          have : e.toVal?.isSome := by
            rw [Option.isSome_iff_ne_none]
            intro h
            exact (toVal?_eq_none.mp h) hv
          obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp this
          exact ⟨_, .StoreS hv' hsome rfl⟩
      | tape => exact ⟨_, .TapeS rfl rfl⟩
      | scrutSuccess hv hm => exact ⟨_, .ScrutSuccessS hv hm⟩
      | scrutFailure hv hm => exact ⟨_, .ScrutFailureS hv hm⟩
    · cases hprob with
      | randNoTape hz => exact ⟨_, .RandNoTapeS hz (le_refl 0) hz⟩
      | randTape htape hzN =>
          exact ⟨_, .RandTapeS htape hzN rfl rfl⟩
      | randTapeEmpty hz htape hzN =>
          exact ⟨_, .RandTapeEmptyS hz htape hzN (le_refl 0) hz rfl⟩
      | randTapeOther hz htape hzN =>
          exact ⟨_, .RandTapeOtherS hz htape hzN (le_refl 0) hz rfl⟩
      | randNonpos hz => exact ⟨_, .RandNonposS hz⟩
      | randTapeNonposEmpty hz htape hzN =>
          exact ⟨_, .RandTapeNonposEmptyS hz htape hzN⟩
      | randTapeNonposOther hz htape hzN =>
          exact ⟨_, .RandTapeNonposOtherS hz htape hzN⟩
      | urand =>
          obtain ⟨r, hr⟩ := LawfulProbLangℝ.unifUnitSupport_nonempty rT
          exact ⟨_, .UrandS hr⟩
  · rintro ⟨ρ', hsupp⟩
    cases hsupp with
    | BetaLamS hv _ => exact .inl (.betaLam hv)
    | BetaFixS hv _ => exact .inl (.betaFix hv)
    | UnOpS hv heval => exact .inl (.unop hv heval.symm)
    | BinOpS hv1 hv2 heval => exact .inl (.binop hv1 hv2 heval.symm)
    | IfTrueS => exact .inl .ifTrue
    | IfFalseS => exact .inl .ifFalse
    | FstS hv1 hv2 => exact .inl (.fst hv1 hv2)
    | SndS hv1 hv2 => exact .inl (.snd hv1 hv2)
    | CaseLS hv => exact .inl (.caseL hv)
    | CaseRS hv => exact .inl (.caseR hv)
    | AllocS htoval _ _ =>
        exact .inl (.alloc (toVal?_isValue htoval))
    | LoadS hlook _ => exact .inl (.load hlook)
    | StoreS htoval hsome _ =>
        exact .inl (.store (toVal?_isValue htoval) hsome)
    | TapeS _ _ => exact .inl .tape
    | ScrutSuccessS hv hm => exact .inl (.scrutSuccess hv hm)
    | ScrutFailureS hv hm => exact .inl (.scrutFailure hv hm)
    | RandNoTapeS hz _ _ => exact .inr (.randNoTape hz)
    | RandTapeS htape hzN _ _ => exact .inr (.randTape htape hzN)
    | RandTapeEmptyS hz htape hzN _ _ _ => exact .inr (.randTapeEmpty hz htape hzN)
    | RandTapeOtherS hz htape hzN _ _ _ => exact .inr (.randTapeOther hz htape hzN)
    | RandNonposS hz => exact .inr (.randNonpos hz)
    | RandTapeNonposEmptyS hz htape hzN => exact .inr (.randTapeNonposEmpty hz htape hzN)
    | RandTapeNonposOtherS hz htape hzN => exact .inr (.randTapeNonposOther hz htape hzN)
    | UrandS _ => exact .inr .urand

/-- No head redex exists iff the head step is the zero measure. -/
theorem not_HeadStepPred_iff_zero
    (e : Exp rT) (σ : State rT) :
    ¬ HeadStepPred e σ ↔ headStep ⟨e, σ⟩ = 0 := by
  rw [headStepPred_iff_exists_support]
  constructor
  · intro hns
    by_contra h0
    exact hns (headStep_exists_support_of_ne_zero h0)
  · rintro h0 ⟨ρ', hsupp⟩
    exact HeadStepSupport.ne_zero hsupp h0

/-- Every head redex is deterministic (Dirac), sampling, or stuck; the case split of the erasure
proof. -/
theorem det_or_prob_or_zero
    (e : Exp rT) (σ : State rT) :
    DetHeadStepPred e σ ∨ ProbHeadStepPred e σ ∨ headStep ⟨e, σ⟩ = 0 := by
  by_cases hpred : HeadStepPred e σ
  · exact hpred.imp_right .inl
  · exact .inr (.inr ((not_HeadStepPred_iff_zero e σ).mp hpred))

/-! ## Tape and fresh-location updates -/

/-- Reading the tape just written returns it. -/
theorem State.upd_tape_some {rT : Type _} (σ : State rT) (α : Loc) (t : Tape) :
    (σ.update_tapes (·.insert α t)).tapes[α]? = some t := by
  simp [update_tapes]

/-- Writes to distinct tapes commute. -/
theorem State.upd_diff_tape_comm {rT : Type _} {σ : State rT} {α β : Loc} {bs bs' : Tape}
    (hne : α ≠ β) :
    ((σ.update_tapes (·.insert β bs)).update_tapes (·.insert α bs')) =
      ((σ.update_tapes (·.insert α bs')).update_tapes (·.insert β bs)) := by
  unfold update_tapes
  congr 2
  apply ExtTreeMap.ext_getElem?
  intro k
  simp [ExtTreeMap.getElem?_insert]
  by_cases hαk : α = k
  · subst hαk
    simp [Ne.symm hne]
  · by_cases hβk : β = k
    · subst hβk
      simp [hαk]
    · simp [hαk, hβk]

/-- Writing tape `β` leaves the lookup at `α ≠ β` unchanged. -/
theorem State.upd_diff_tape_tot {rT : Type _} {σ : State rT} {α β : Loc} {bs : Tape}
    (hne : α ≠ β) :
    (σ.update_tapes (·.insert β bs)).tapes[α]? = σ.tapes[α]? := by
  simp [update_tapes, ExtTreeMap.getElem?_insert, Ne.symm hne]

/-- Inserting at an existing key keeps `fresh`. -/
theorem _root_.Std.ExtTreeMap.fresh_insert_of_mem
    {V : Type*} (t : ExtTreeMap Int V compare) {α : Int} {v w : V}
    (h : t[α]? = some v) :
    (t.insert α w).fresh = t.fresh := by
  -- inserting at an existing key does not change `maxKey?`
  unfold ExtTreeMap.fresh
  have hkeys : (t.insert α w).maxKey? = t.maxKey? := by
    rw [ExtTreeMap.maxKey?_insert]
    have hmem : α ∈ t := ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [h]; rfl)
    have hsome : t.maxKey?.isSome := ExtTreeMap.isSome_maxKey?_of_mem hmem
    obtain ⟨km, hkm⟩ : ∃ km, t.maxKey? = some km := ⟨_, Option.eq_some_of_isSome hsome⟩
    rw [hkm]
    simp only [Option.elim, Option.some.injEq]
    have hle_αkm : (compare α km).isLE := by
      have hget : t.maxKey?.get (ExtTreeMap.isSome_maxKey?_of_mem hmem) = km :=
        Option.get_of_eq_some _ hkm
      exact ExtTreeMap.le_maxKey?_of_mem hmem hget
    have hα_le_km : α ≤ km := by
      simp [compare, compareOfLessAndEq] at hle_αkm
      split at hle_αkm
      · omega
      · split at hle_αkm
        · omega
        · simp [Ordering.isLE] at hle_αkm
    by_cases heq : α = km
    · have hcmp : compare km α = .eq := by
        simp [compare, compareOfLessAndEq, heq.symm]
      simp [Ordering.isLE, heq.symm]
    · have hlt : α < km := lt_of_le_of_ne hα_le_km heq
      have hcmp : compare km α = .gt := by
        show compareOfLessAndEq km α = .gt
        unfold compareOfLessAndEq
        have h1 : ¬ (km < α) := by omega
        have h2 : km ≠ α := by omega
        simp [h1, h2]
      simp [hcmp, Ordering.isLE]
  rw [hkeys]

/-- Overwriting an existing tape keeps `tapes.fresh`. -/
theorem State.fresh_loc_upd_some {rT : Type _} {σ : State rT} {α : Loc} {bs bs' : Tape}
    (h : σ.tapes[α]? = some bs) :
    (σ.tapes.insert α bs').fresh = σ.tapes.fresh :=
  ExtTreeMap.fresh_insert_of_mem σ.tapes h

/-- The fresh key is never a key of the map. -/
theorem _root_.Std.ExtTreeMap.elem_fresh_ne
    {V : Type*} {t : ExtTreeMap Int V compare} {k : Int} {v : V}
    (h : t[k]? = some v) : t.fresh ≠ k := by
  intro heq
  have hfresh := ExtTreeMap.fresh_get? t
  rw [heq, h] at hfresh
  simp at hfresh

/-! ## Tape updates preserve head-step shape -/

-- The `simpa` below runs under `all_goals try`: the linter sees one branch where the
-- goal-side `simp` is idle, but other branches need it.
set_option linter.unnecessarySimpa false in
/-- Overwriting an existing tape cannot unstick a stuck head redex. -/
theorem State.head_step_dzero_upd_tapes
    {e : Exp rT} {σ : State rT} {α : Loc} {bs bs' : Tape}
    (hmem : σ.tapes[α]? = some bs)
    (h0 : ProbLang.headStep ⟨e, σ⟩ = 0) :
    ProbLang.headStep ⟨e, σ.update_tapes (·.insert α bs')⟩ = 0 := by
  revert h0
  head_case
  all_goals try (intro h0; simpa using h0)
  all_goals try (intro h0; simp_all)
  case unop.redex h0 =>
    unfold Option.unwrapM at h0 ⊢
    split <;> rename_i hopt
    · rw [hopt] at h0
      exact absurd h0 Measure.dirac_ne_zero
    · rfl
  case binop.redex h0 =>
    unfold Option.unwrapM at h0 ⊢
    split <;> rename_i hopt
    · rw [hopt] at h0
      exact absurd h0 Measure.dirac_ne_zero
    · rfl
  case alloc.no_redex hned =>
    simp [toVal?_eq_none.mpr hned]
  case load.segfault hheap =>
    have hnotmem : ‹Loc› ∉ (σ.update_tapes (·.insert α bs')).heap := hheap
    have hnone := Option.not_isSome_iff_eq_none.mp
      (fun hsome => hnotmem (ExtTreeMap.mem_iff_isSome_getElem?.mpr hsome))
    rw [hnone]
  case store.no_redex hned =>
    simp [toVal?_eq_none.mpr hned]
  case store.segfault hv hheap =>
    have hnotmem : ‹Loc› ∉ (σ.update_tapes (·.insert α bs')).heap := hheap
    have hnone := Option.not_isSome_iff_eq_none.mp
      (fun hsome => hnotmem (ExtTreeMap.mem_iff_isSome_getElem?.mpr hsome))
    rw [hnone]
  case rand.plain h0 =>
    exact absurd h0 (uniform_ne_zero _ _)
  case rand.tape.unalloc hnotin =>
    have hne : α ≠ ‹Lbl› := by
      intro he
      exact hnotin (he ▸ ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hmem]; rfl))
    have hnone : σ.tapes[‹Lbl›]? = none :=
      Option.not_isSome_iff_eq_none.mp
        (fun hsome => hnotin (ExtTreeMap.mem_iff_isSome_getElem?.mpr hsome))
    rw [upd_diff_tape_tot (Ne.symm hne), hnone]
  case rand.tape.mismatch =>
    exact absurd h0 (uniform_ne_zero _ _)
  case rand.tape.empty =>
    exact absurd h0 (uniform_ne_zero _ _)
  case urand h0 =>
    exact absurd h0 (IsProbabilityMeasure.ne_zero _)

end ProbLang
