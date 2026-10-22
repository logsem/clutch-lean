module

public import Metrology.ProbLang.DetStep
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Syntax.LocallyClosed

@[expose] public section

/-! # ProbLang metatheory

Port of Clutch `metatheory.v`: closedness, sequential substitution maps, the Det/Prob/stuck
head-step trichotomy `det_or_prob_or_zero` used by erasure, and tape-update lemmas. -/

namespace ProbLang
open Cslib Exp

variable {rT : Type _} [LawfulProbLangℝ rT]

/-! ## Closed contexts and `isClosed`

Port of Clutch's `is_closed` to locally-nameless syntax. -/

/-- A finite set of atoms the free variables may range over. -/
abbrev ClosedCtx := Finset Var

namespace ClosedCtx

def empty : ClosedCtx := ∅

end ClosedCtx

/-- `e` is locally closed with free variables in `X`. -/
def Exp.isClosed (X : ClosedCtx) (e : Exp rT) : Prop := e.IsLocallyClosed ∧ e.fv ⊆ X

theorem Exp.notMem_fv_of_isClosed_empty {e : Exp α} (h : e.isClosed .empty) (x : Var) :
    x ∉ e.fv :=
  fun hx => by simpa [ClosedCtx.empty] using h.2 hx

theorem Exp.fv_eq_empty_of_isClosed_empty {e : Exp α} (h : e.isClosed .empty) : e.fv = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr (Exp.notMem_fv_of_isClosed_empty h)

/-! ## Substitution maps -/

/-- A list of `(variable, value)` pairs to substitute. -/
abbrev SubstMap (rT : Type _) [LawfulProbLangℝ rT] := List (Var × Exp rT)

namespace SubstMap

def empty : SubstMap rT := []

/-- Cons a pair on the left; it does not shadow an existing binding. -/
def insert (vs : SubstMap rT) (x : Var) (v : Exp rT) : SubstMap rT := (x, v) :: vs

def delete (vs : SubstMap rT) (x : Var) : SubstMap rT :=
  vs.filter (fun p => p.1 ≠ x)

/-- Look up a variable; the rightmost binding wins, matching `Exp.substMap`. -/
def lookup : SubstMap rT → Var → Option (Exp rT)
  | [], _ => none
  | (y, v) :: rest, x =>
    match lookup rest x with
    | some w => some w
    | none => if x = y then some v else none

@[simp] theorem lookup_insert (vs : SubstMap rT) (x y : Var) (v : Exp rT) :
    (vs.insert x v).lookup y =
      match vs.lookup y with
        | some w => some w
        | none => if y = x then some v else none := rfl

end SubstMap

/-- Substitute sequentially, rightmost pair first:
`substMap [(x,u), (y,w)] e = subst (subst e y w) x u`. Since this is sequential, not
simultaneous, lemmas need `SubstMap.AllClosed` for the two readings to agree. -/
def Exp.substMap (vs : SubstMap rT) (e : Exp rT) : Exp rT :=
  vs.foldr (fun p acc => Exp.subst acc p.1 p.2) e

@[simp] theorem Exp.substMap_empty (e : Exp rT) : e.substMap .empty = e := rfl

@[simp] theorem Exp.substMap_insert (vs : SubstMap rT) (x : Var) (v e : Exp rT) :
    e.substMap (vs.insert x v) = Exp.subst (e.substMap vs) x v := rfl

@[simp] theorem Exp.substMap_cons (p : Var × Exp rT) (vs : SubstMap rT) (e : Exp rT) :
    e.substMap (p :: vs) = Exp.subst (e.substMap vs) p.1 p.2 := rfl

/-! ### Substitution and closedness -/

/-! ### Commutation of substitutions -/

/-- Substitutions at different variables commute when `v'` has no `x` free. -/
theorem Exp.subst_subst {e v v' : Exp α} {x : Var} {y : Var}
    (hne : x ≠ y) (hv' : x ∉ v'.fv) :
    Exp.subst (Exp.subst e x v) y v' =
      Exp.subst (Exp.subst e y v') x (Exp.subst v y v') := by
  induction e with
  | fvar z =>
      by_cases h1 : x = z <;> by_cases h2 : y = z
      · subst h1; exact absurd h2 hne.symm
      · subst h1
        simp [Exp.subst, h2]
      · subst h2
        simp [Exp.subst, h1, Exp.subst_fresh _ _ _ hv']
      · simp [Exp.subst, h1, h2]
  | bvar _ | lit _ | fail | urand => rfl
  | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
      simp [Exp.subst, ih]
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
      simp [Exp.subst, ih1, ih2]
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
      simp [Exp.subst, ih0, ih1, ih2]

/-- Independence of substitutions at distinct, mutually-fresh variables. -/
theorem Exp.subst_subst_ne {e v v' : Exp α} {x y : Var}
    (hne : x ≠ y) (hxv' : x ∉ v'.fv) (hyv : y ∉ v.fv) :
    Exp.subst (Exp.subst e x v) y v' = Exp.subst (Exp.subst e y v') x v := by
  rw [Exp.subst_subst hne hxv', Exp.subst_fresh y v v' hyv]

/-! ### α-renaming

Used by the binder cases of the Soundness precongruence to rename an atom `x ↦ .fvar y`. -/

/-- `e[x ↦ y][y ↦ w] = e[x ↦ w]` for `y` fresh in `e`. -/
theorem Exp.subst_subst_fvar_id (e w : Exp α) (x y : Var) (hyv : y ∉ e.fv) :
    Exp.subst (Exp.subst e x (.fvar y)) y w = Exp.subst e x w := by
  induction e with
  | fvar z =>
    by_cases h1 : x = z
    · subst h1
      simp [Exp.subst]
    · have hyz : y ≠ z := fun h => hyv (h ▸ by simp [Exp.fv])
      simp [Exp.subst, h1, hyz]
  | bvar _ | lit _ | fail | urand => rfl
  | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
    have hyv' : y ∉ e.fv := fun h => hyv (by simpa [Exp.fv] using h)
    simp [Exp.subst, ih hyv']
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
    have hyv1 : y ∉ e1.fv := fun h => hyv (by simp [Exp.fv]; exact Or.inl h)
    have hyv2 : y ∉ e2.fv := fun h => hyv (by simp [Exp.fv]; exact Or.inr h)
    simp [Exp.subst, ih1 hyv1, ih2 hyv2]
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
    have hyv0 : y ∉ e0.fv := fun h => hyv (by simp [Exp.fv]; exact Or.inl h)
    have hyv1 : y ∉ e1.fv := fun h => hyv (by simp [Exp.fv]; exact Or.inr (Or.inl h))
    have hyv2 : y ∉ e2.fv := fun h => hyv (by simp [Exp.fv]; exact Or.inr (Or.inr h))
    simp [Exp.subst, ih0 hyv0, ih1 hyv1, ih2 hyv2]

/-! ### Closed substitution maps -/

/-- Every value in `vs` is closed. -/
def SubstMap.AllClosed (vs : SubstMap rT) : Prop :=
  ∀ p ∈ vs, p.2.isClosed .empty

theorem SubstMap.AllClosed_nil : SubstMap.AllClosed ([] : SubstMap rT) :=
  fun _ hp => nomatch hp

theorem SubstMap.AllClosed_cons {x : Var} {v : Exp rT} {vs : SubstMap rT} :
    SubstMap.AllClosed ((x, v) :: vs) ↔ v.isClosed .empty ∧ SubstMap.AllClosed vs := by
  constructor
  · intro h
    exact ⟨h (x, v) List.mem_cons_self, fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
  · rintro ⟨hv, hvs⟩ p hp
    rcases List.mem_cons.mp hp with rfl | hpm
    · exact hv
    · exact hvs p hpm

theorem SubstMap.AllClosed_filter (vs : SubstMap rT) (P : Var × Exp rT → Bool)
    (h : SubstMap.AllClosed vs) :
    SubstMap.AllClosed (vs.filter P) :=
  fun p hp => h p (List.mem_filter.mp hp).1

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
  | nil => simp [SubstMap.lookup] at h
  | cons p rest ih =>
    obtain ⟨z, v⟩ := p
    simp only [SubstMap.lookup] at h
    cases hr : SubstMap.lookup rest y with
    | some w' =>
      obtain rfl : w' = w := by simpa [hr] using h
      exact List.mem_cons_of_mem _ (ih hr)
    | none =>
      rw [hr] at h
      split_ifs at h with hyz
      obtain rfl := Option.some.inj h
      exact hyz ▸ List.mem_cons_self

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
      simp only [SubstMap.lookup]
      cases SubstMap.lookup rest z <;> simp
    · simp only [SubstMap.lookup]
      cases hrr : SubstMap.lookup rest y with
      | some _ => simp
      | none => simpa [hrr] using ih hpm

/-- `substMap` commutes with `subst _ x (.fvar y)` when `x`, `y` avoid `vs`'s domain. -/
theorem Exp.substMap_subst_fvar_comm
    (vs : SubstMap rT) (E : Exp rT) (x y : Var)
    (hxNotDom : x ∉ (vs.map (·.1)).toFinset)
    (hyNotDom : y ∉ (vs.map (·.1)).toFinset)
    (hvs : SubstMap.AllClosed vs) :
    Exp.substMap vs (Exp.subst E x (.fvar y)) =
      Exp.subst (Exp.substMap vs E) x (.fvar y) := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    have hzx : z ≠ x := fun h => hxNotDom (h ▸ by simp)
    have hzy : z ≠ y := fun h => hyNotDom (h ▸ by simp)
    have hxNotRest : x ∉ (rest.map (·.1)).toFinset := fun h => hxNotDom (by simp [h])
    have hyNotRest : y ∉ (rest.map (·.1)).toFinset := fun h => hyNotDom (by simp [h])
    obtain ⟨hw_closed, hvs_rest⟩ := SubstMap.AllClosed_cons.mp hvs
    have hzNotFvY : z ∉ (Exp.fvar (rT := rT) y).fv := by simpa [Exp.fv] using hzy
    rw [Exp.substMap_cons, Exp.substMap_cons, ih hxNotRest hyNotRest hvs_rest,
      ← Exp.subst_subst_ne hzx hzNotFvY (Exp.notMem_fv_of_isClosed_empty hw_closed x)]

/-! ### `substMap` through constructors

The `substMap_hom*` lemmas lift "`subst` commutes with this constructor" along the fold.
(Clutch gets these by `simpl`, since its `subst_map` is simultaneous.) -/

theorem Exp.substMap_hom₀ (C : Exp rT) (hC : ∀ x v, Exp.subst C x v = C)
    (vs : SubstMap rT) : C.substMap vs = C := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => simp only [Exp.substMap_cons, ih, hC]

theorem Exp.substMap_hom₁ (C : Exp rT → Exp rT)
    (hC : ∀ e x v, Exp.subst (C e) x v = C (Exp.subst e x v))
    (vs : SubstMap rT) (e : Exp rT) :
    (C e).substMap vs = C (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => simp only [Exp.substMap_cons, ih, hC]

theorem Exp.substMap_hom₂ (C : Exp rT → Exp rT → Exp rT)
    (hC : ∀ e1 e2 x v, Exp.subst (C e1 e2) x v = C (Exp.subst e1 x v) (Exp.subst e2 x v))
    (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (C e1 e2).substMap vs = C (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => simp only [Exp.substMap_cons, ih, hC]

theorem Exp.substMap_hom₃ (C : Exp rT → Exp rT → Exp rT → Exp rT)
    (hC : ∀ e0 e1 e2 x v, Exp.subst (C e0 e1 e2) x v =
      C (Exp.subst e0 x v) (Exp.subst e1 x v) (Exp.subst e2 x v))
    (vs : SubstMap rT) (e0 e1 e2 : Exp rT) :
    (C e0 e1 e2).substMap vs =
      C (e0.substMap vs) (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => simp only [Exp.substMap_cons, ih, hC]

@[simp] theorem Exp.substMap_lit (vs : SubstMap rT) (b : BaseLit rT) :
    (Exp.lit b).substMap vs = .lit b :=
  Exp.substMap_hom₀ _ (by intros; simp [Exp.subst]) vs

@[simp] theorem Exp.substMap_bvar (vs : SubstMap rT) (j : Nat) :
    (Exp.bvar j).substMap vs = .bvar j :=
  Exp.substMap_hom₀ _ (by intros; simp [Exp.subst]) vs

@[simp] theorem Exp.substMap_fail (vs : SubstMap rT) :
    Exp.fail.substMap vs = .fail :=
  Exp.substMap_hom₀ _ (by intros; simp [Exp.subst]) vs

@[simp] theorem Exp.substMap_urand (vs : SubstMap rT) :
    Exp.urand.substMap vs = .urand :=
  Exp.substMap_hom₀ _ (by intros; simp [Exp.subst]) vs

@[simp] theorem Exp.substMap_pair (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (Exp.pair e1 e2).substMap vs = .pair (e1.substMap vs) (e2.substMap vs) :=
  Exp.substMap_hom₂ _ (by intros; simp [Exp.subst]) vs e1 e2

@[simp] theorem Exp.substMap_fst (vs : SubstMap rT) (e : Exp rT) :
    (Exp.fst e).substMap vs = .fst (e.substMap vs) :=
  Exp.substMap_hom₁ _ (by intros; simp [Exp.subst]) vs e

@[simp] theorem Exp.substMap_snd (vs : SubstMap rT) (e : Exp rT) :
    (Exp.snd e).substMap vs = .snd (e.substMap vs) :=
  Exp.substMap_hom₁ _ (by intros; simp [Exp.subst]) vs e

@[simp] theorem Exp.substMap_inl (vs : SubstMap rT) (e : Exp rT) :
    (Exp.inl e).substMap vs = .inl (e.substMap vs) :=
  Exp.substMap_hom₁ _ (by intros; simp [Exp.subst]) vs e

@[simp] theorem Exp.substMap_inr (vs : SubstMap rT) (e : Exp rT) :
    (Exp.inr e).substMap vs = .inr (e.substMap vs) :=
  Exp.substMap_hom₁ _ (by intros; simp [Exp.subst]) vs e

@[simp] theorem Exp.substMap_case (vs : SubstMap rT) (e0 e1 e2 : Exp rT) :
    (Exp.case e0 e1 e2).substMap vs =
      .case (e0.substMap vs) (e1.substMap vs) (e2.substMap vs) :=
  Exp.substMap_hom₃ _ (by intros; simp [Exp.subst]) vs e0 e1 e2

@[simp] theorem Exp.substMap_cond (vs : SubstMap rT) (e0 e1 e2 : Exp rT) :
    (Exp.cond e0 e1 e2).substMap vs =
      .cond (e0.substMap vs) (e1.substMap vs) (e2.substMap vs) :=
  Exp.substMap_hom₃ _ (by intros; simp [Exp.subst]) vs e0 e1 e2

@[simp] theorem Exp.substMap_app (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (Exp.app e1 e2).substMap vs = .app (e1.substMap vs) (e2.substMap vs) :=
  Exp.substMap_hom₂ _ (by intros; simp [Exp.subst]) vs e1 e2

@[simp] theorem Exp.substMap_lam (vs : SubstMap rT) (e : Exp rT) :
    (Exp.lam e).substMap vs = .lam (e.substMap vs) :=
  Exp.substMap_hom₁ _ (by intros; simp [Exp.subst]) vs e

@[simp] theorem Exp.substMap_fix (vs : SubstMap rT) (e : Exp rT) :
    (Exp.fix e).substMap vs = .fix (e.substMap vs) :=
  Exp.substMap_hom₁ _ (by intros; simp [Exp.subst]) vs e

@[simp] theorem Exp.substMap_unop (vs : SubstMap rT) (op : UnOp) (e : Exp rT) :
    (Exp.unop op e).substMap vs = .unop op (e.substMap vs) :=
  Exp.substMap_hom₁ (Exp.unop op) (by intros; simp [Exp.subst]) vs e

@[simp] theorem Exp.substMap_binop (vs : SubstMap rT) (op : BinOp) (e1 e2 : Exp rT) :
    (Exp.binop op e1 e2).substMap vs =
      .binop op (e1.substMap vs) (e2.substMap vs) :=
  Exp.substMap_hom₂ (Exp.binop op) (by intros; simp [Exp.subst]) vs e1 e2

@[simp] theorem Exp.substMap_alloc (vs : SubstMap rT) (e : Exp rT) :
    (Exp.alloc e).substMap vs = .alloc (e.substMap vs) :=
  Exp.substMap_hom₁ _ (by intros; simp [Exp.subst]) vs e

@[simp] theorem Exp.substMap_load (vs : SubstMap rT) (e : Exp rT) :
    (Exp.load e).substMap vs = .load (e.substMap vs) :=
  Exp.substMap_hom₁ _ (by intros; simp [Exp.subst]) vs e

@[simp] theorem Exp.substMap_store (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (Exp.store e1 e2).substMap vs = .store (e1.substMap vs) (e2.substMap vs) :=
  Exp.substMap_hom₂ _ (by intros; simp [Exp.subst]) vs e1 e2

@[simp] theorem Exp.substMap_tape (vs : SubstMap rT) (e : Exp rT) :
    (Exp.tape e).substMap vs = .tape (e.substMap vs) :=
  Exp.substMap_hom₁ _ (by intros; simp [Exp.subst]) vs e

@[simp] theorem Exp.substMap_rand (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (Exp.rand e1 e2).substMap vs = .rand (e1.substMap vs) (e2.substMap vs) :=
  Exp.substMap_hom₂ _ (by intros; simp [Exp.subst]) vs e1 e2

@[simp] theorem Exp.substMap_scrut (vs : SubstMap rT) (e : Exp rT) (p : Pat rT) :
    (Exp.scrut e p).substMap vs = .scrut (e.substMap vs) p :=
  Exp.substMap_hom₁ (Exp.scrut · p) (by intros; simp [Exp.subst]) vs e

theorem Exp.substMap_openRec (vs : SubstMap rT) (k : Nat) (u e : Exp rT)
    (hClosed : SubstMap.AllClosed vs) :
    Exp.substMap vs (Exp.openRec k u e) =
      Exp.openRec k (Exp.substMap vs u) (Exp.substMap vs e) := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    obtain ⟨hwClosed, hRestClosed⟩ := SubstMap.AllClosed_cons.mp hClosed
    rw [Exp.substMap_cons, ih hRestClosed, Exp.substMap_cons, Exp.substMap_cons]
    exact Exp.subst_openRec y w k _ _ hwClosed.1

theorem Exp.substMap_open (vs : SubstMap rT) (u e : Exp rT)
    (hClosed : SubstMap.AllClosed vs) :
    Exp.substMap vs (Exp.open' e u) =
      Exp.open' (Exp.substMap vs e) (Exp.substMap vs u) :=
  Exp.substMap_openRec vs 0 u e hClosed

theorem Exp.notFv_substMap {vs : SubstMap rT} {e : Exp rT} {x : Var}
    (hClosed : SubstMap.AllClosed vs) (hx : x ∉ e.fv) :
    x ∉ (Exp.substMap vs e).fv := by
  induction vs with
  | nil => exact hx
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    obtain ⟨hwClosed, hRestClosed⟩ := SubstMap.AllClosed_cons.mp hClosed
    rw [Exp.substMap_cons]
    intro hmem
    rcases Finset.mem_union.mp (fv_subst_subset (substMap rest e) y w hmem) with h1 | h2
    · exact ih hRestClosed (Finset.mem_sdiff.mp h1).1
    · exact Exp.notMem_fv_of_isClosed_empty hwClosed x h2

theorem Exp.substMap_fvar_lookup_none {vs : SubstMap rT} {x : Var}
    (hv : SubstMap.lookup vs x = none) :
    Exp.substMap vs (.fvar x) = .fvar x := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    simp only [SubstMap.lookup] at hv
    cases hr : SubstMap.lookup rest x with
    | some w' => rw [hr] at hv; cases hv
    | none =>
      rw [hr] at hv
      simp only at hv
      split_ifs at hv with hxy
      rw [Exp.substMap_cons, ih hr]
      simp [Exp.subst, Ne.symm hxy]

theorem SubstMap.lookup_closed {vs : SubstMap rT} {x : Var} {v : Exp rT}
    (hv : SubstMap.lookup vs x = some v) (hClosed : SubstMap.AllClosed vs) :
    v.isClosed .empty := by
  induction vs with
  | nil => simp [SubstMap.lookup] at hv
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    rw [SubstMap.AllClosed_cons] at hClosed
    simp only [SubstMap.lookup] at hv
    cases hr : SubstMap.lookup rest x with
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
theorem Exp.substMap_open_fresh {vs : SubstMap rT} {e v : Exp rT} {x : Var}
    (hClosed : SubstMap.AllClosed vs) (hxFv : x ∉ e.fv)
    (hxDom : SubstMap.lookup vs x = none) (hvLC : v.IsLocallyClosed) :
    Exp.substMap ((x, v) :: vs) (Exp.open' e (.fvar x)) =
      Exp.open' (Exp.substMap vs e) v := by
  show Exp.subst (Exp.substMap vs (Exp.open' e (.fvar x))) x v =
    Exp.open' (Exp.substMap vs e) v
  rw [Exp.substMap_open _ _ _ hClosed, Exp.substMap_fvar_lookup_none hxDom,
    Exp.subst_intro x v _ (Exp.notFv_substMap hClosed hxFv) hvLC]

theorem Exp.substMap_lc {vs : SubstMap rT} {e : Exp rT}
    (hClosed : SubstMap.AllClosed vs) (he : e.IsLocallyClosed) :
    (Exp.substMap vs e).IsLocallyClosed := by
  induction vs with
  | nil => exact he
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    obtain ⟨hwClosed, hRestClosed⟩ := SubstMap.AllClosed_cons.mp hClosed
    exact subst_lc (ih hRestClosed) hwClosed.1

/-- Substituting closed values into the body of a locally closed `lam` keeps it locally closed. -/
theorem Exp.lam_substMap_isLocallyClosed {e : Exp rT} {σ : SubstMap rT} {L D : Finset Var}
    (hσ : SubstMap.AllClosed σ) (hdom : ∀ y ∉ D, SubstMap.lookup σ y = none)
    (he : ∀ x ∉ L, (Exp.open' e (.fvar x)).IsLocallyClosed) :
    (Exp.lam (Exp.substMap σ e)).IsLocallyClosed := by
  refine Exp.IsLocallyClosed.lam (L ∪ D) _ ?_
  intro y hy
  have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
  have hyD : y ∉ D := fun h => hy (Finset.mem_union_right _ h)
  have hbridge : Exp.substMap σ (Exp.open' e (.fvar y)) =
      Exp.open' (Exp.substMap σ e) (.fvar y) := by
    rw [Exp.substMap_open _ _ _ hσ, Exp.substMap_fvar_lookup_none (hdom y hyD)]
  rw [← hbridge]
  exact Exp.substMap_lc hσ (he y hyL)

/-- Substituting closed values into the body of a locally closed `fix` keeps it locally closed. -/
theorem Exp.fix_substMap_isLocallyClosed {e : Exp rT} {σ : SubstMap rT} {L D : Finset Var}
    (hσ : SubstMap.AllClosed σ) (hdom : ∀ y ∉ D, SubstMap.lookup σ y = none)
    (he : ∀ x ∉ L, (Exp.open' e (.fvar x)).IsLocallyClosed) :
    (Exp.fix (Exp.substMap σ e)).IsLocallyClosed := by
  refine Exp.IsLocallyClosed.fix (L ∪ D) _ ?_
  intro y hy
  have hbridge : Exp.substMap σ (Exp.open' e (.fvar y)) =
      Exp.open' (Exp.substMap σ e) (.fvar y) := by
    rw [Exp.substMap_open _ _ _ hσ,
      Exp.substMap_fvar_lookup_none (hdom y fun h => hy (Finset.mem_union_right _ h))]
  rw [← hbridge]
  exact Exp.substMap_lc hσ (he y fun h => hy (Finset.mem_union_left _ h))

theorem Exp.fv_substMap_sdiff_dom {vs : SubstMap rT} {e : Exp rT}
    (hClosed : SubstMap.AllClosed vs) :
    (Exp.substMap vs e).fv ⊆ e.fv \ (vs.map (·.1)).toFinset := by
  induction vs generalizing e with
  | nil =>
    simp [Exp.substMap]
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    obtain ⟨hwClosed, hRestClosed⟩ := SubstMap.AllClosed_cons.mp hClosed
    rw [Exp.substMap_cons]
    intro y hy
    rcases Finset.mem_union.mp (fv_subst_subset (substMap rest e) z w hy) with hL | hR
    · obtain ⟨hyRest, hyNeZ⟩ := Finset.mem_sdiff.mp hL
      obtain ⟨hyE, hyDom⟩ := Finset.mem_sdiff.mp (ih (e := e) hRestClosed hyRest)
      simp only [Finset.mem_sdiff, List.map_cons, List.toFinset_cons, Finset.mem_insert,
        not_or]
      exact ⟨hyE, fun h => hyNeZ (by simp [h]), hyDom⟩
    · exact absurd hR (Exp.notMem_fv_of_isClosed_empty hwClosed y)

theorem Exp.substMap_fv_eq_empty {vs : SubstMap rT} {e : Exp rT}
    (hClosed : SubstMap.AllClosed vs)
    (hsub : e.fv ⊆ (vs.map (·.1)).toFinset) :
    (Exp.substMap vs e).fv = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  obtain ⟨hyE, hyDom⟩ := Finset.mem_sdiff.mp (Exp.fv_substMap_sdiff_dom hClosed hy)
  exact hyDom (hsub hyE)

theorem Exp.substMap_subst_fvar_lookup
    (vs : SubstMap rT) (E : Exp rT) (x y : Var) (w : Exp rT)
    (hxNotDom : x ∉ (vs.map (·.1)).toFinset)
    (hvs : SubstMap.AllClosed vs)
    (hyLookup : vs.lookup y = some w)
    (hyFvE : y ∉ E.fv) :
    Exp.substMap vs (Exp.subst E x (.fvar y)) =
      Exp.subst (Exp.substMap (vs.filter (fun p => !decide (p.1 = y))) E) x w := by
  have hw_closed : w.isClosed .empty :=
    hvs (y, w) (SubstMap.mem_of_lookup_eq_some hyLookup)
  induction vs with
  | nil => simp [SubstMap.lookup] at hyLookup
  | cons p rest ih =>
    obtain ⟨z, v⟩ := p
    have hcons1 : Exp.substMap ((z, v) :: rest) (Exp.subst E x (.fvar y)) =
        Exp.subst (Exp.substMap rest (Exp.subst E x (.fvar y))) z v := rfl
    have hzx : z ≠ x := fun h => hxNotDom (h ▸ by simp)
    have hxNotRest : x ∉ (rest.map (·.1)).toFinset := fun h => hxNotDom (by simp [h])
    obtain ⟨hv_closed, hvs_rest⟩ := SubstMap.AllClosed_cons.mp hvs
    rw [hcons1]
    by_cases hzy : z = y
    · simp only [hzy, SubstMap.lookup] at hyLookup
      cases hr : SubstMap.lookup rest y with
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
        have hfilter_closed : SubstMap.AllClosed (rest.filter (fun p => !decide (p.1 = y))) :=
          SubstMap.AllClosed_filter rest _ hvs_rest
        have hyNotFinner : y ∉ (Exp.substMap (rest.filter (fun p => !decide (p.1 = y))) E).fv :=
          Exp.notFv_substMap hfilter_closed hyFvE
        have hyNotFsubst :
            y ∉ (Exp.subst (Exp.substMap (rest.filter (fun p => !decide (p.1 = y))) E) x w).fv := by
          intro hy
          have := Exp.fv_subst_subset _ x w hy
          rcases Finset.mem_union.mp this with h1 | h2
          · exact hyNotFinner (Finset.mem_sdiff.mp h1).1
          · exact Exp.notMem_fv_of_isClosed_empty hw_closed y h2
        rw [Exp.subst_fresh y _ v hyNotFsubst]
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
          have := SubstMap.lookup_isSome_of_mem_dom h
          rw [hr] at this
          cases this
        have hcomm := Exp.substMap_subst_fvar_comm rest E x y hxNotRest hyNotRest hvs_rest
        rw [hcomm]
        have hyNotInner : y ∉ (Exp.substMap rest E).fv :=
          Exp.notFv_substMap hvs_rest hyFvE
        rw [SubstMap.filter_notMem_dom rest hyNotRest, hzy]
        exact Exp.subst_subst_fvar_id (Exp.substMap rest E) v x y hyNotInner
    · -- z ≠ y: commute the head substitution past `subst _ x w`
      simp only [SubstMap.lookup] at hyLookup
      cases hr : SubstMap.lookup rest y with
      | some w' =>
        rw [hr] at hyLookup
        have hw'eq : w' = w := by injection hyLookup
        rw [hw'eq] at hr
        rw [ih hxNotRest hvs_rest hr]
        have hfilter_cons :
            ((z, v) :: rest).filter (fun p => !decide (p.1 = y)) =
              (z, v) :: rest.filter (fun p => !decide (p.1 = y)) := by simp [hzy]
        rw [hfilter_cons]
        rw [Exp.subst_subst_ne (Ne.symm hzx) (Exp.notMem_fv_of_isClosed_empty hv_closed x)
          (Exp.notMem_fv_of_isClosed_empty hw_closed z)]
        rfl
      | none =>
        rw [hr] at hyLookup
        simp [Ne.symm hzy] at hyLookup

theorem Exp.substMap_fvar_lookup_some (vs : SubstMap rT) (x : Var)
    (hClosed : SubstMap.AllClosed vs) :
    ∀ {v : Exp rT}, SubstMap.lookup vs x = some v → Exp.substMap vs (.fvar x) = v := by
  induction vs with
  | nil => intro v hv; simp [SubstMap.lookup] at hv
  | cons p rest ih =>
    intro v hv
    obtain ⟨y, w⟩ := p
    rw [SubstMap.AllClosed_cons] at hClosed
    obtain ⟨hwClosed, hRestClosed⟩ := hClosed
    rw [Exp.substMap_cons]
    simp only [SubstMap.lookup] at hv
    cases hr : SubstMap.lookup rest x with
    | some w' =>
      rw [hr] at hv
      injection hv with hw'v
      subst hw'v
      rw [ih hRestClosed hr]
      exact Exp.subst_fresh _ _ _
        (Exp.notMem_fv_of_isClosed_empty (SubstMap.lookup_closed hr hRestClosed) y)
    | none =>
      rw [hr] at hv
      simp only at hv
      split_ifs at hv with hxy
      injection hv with hwv
      subst hwv
      subst hxy
      rw [Exp.substMap_fvar_lookup_none hr]
      show (Exp.fvar x).subst x w = w
      simp [Exp.subst]

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
  | urand {σ} : ProbHeadStepPred Exp.urand σ

/-- `e` is a head redex in state `σ`. -/
def HeadStepPred (e : Exp rT) (σ : State rT) : Prop :=
  DetHeadStepPred e σ ∨ ProbHeadStepPred e σ

theorem HeadStepPred_iff_exists_support (e : Exp rT) (σ : State rT) :
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
            exact (Exp.toVal?_eq_none.mp h) hv
          obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp this
          exact ⟨_, .AllocS hv' rfl rfl⟩
      | load hlook => exact ⟨_, .LoadS hlook rfl⟩
      | @store ℓ e σ hv hsome =>
          have : e.toVal?.isSome := by
            rw [Option.isSome_iff_ne_none]
            intro h
            exact (Exp.toVal?_eq_none.mp h) hv
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
          exact ⟨_, .UrandS (r := r) hr⟩
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
        exact .inl (.alloc (Exp.toVal?_isValue htoval))
    | LoadS hlook _ => exact .inl (.load hlook)
    | StoreS htoval hsome _ =>
        exact .inl (.store (Exp.toVal?_isValue htoval) hsome)
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

theorem not_HeadStepPred_iff_zero
    (e : Exp rT) (σ : State rT) :
    ¬ HeadStepPred e σ ↔ headStep ⟨e, σ⟩ = 0 := by
  rw [HeadStepPred_iff_exists_support]
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
  simp [State.update_tapes]

/-- Writes to distinct tapes commute. -/
theorem State.upd_diff_tape_comm {rT : Type _} {σ : State rT} {α β : Loc} {bs bs' : Tape}
    (hne : α ≠ β) :
    ((σ.update_tapes (·.insert β bs)).update_tapes (·.insert α bs')) =
      ((σ.update_tapes (·.insert α bs')).update_tapes (·.insert β bs)) := by
  unfold State.update_tapes
  congr 2
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp [Std.ExtTreeMap.getElem?_insert]
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
  simp [State.update_tapes, Std.ExtTreeMap.getElem?_insert, Ne.symm hne]

theorem _root_.Std.ExtTreeMap.fresh_insert_of_mem
    {V : Type*} (t : Std.ExtTreeMap Int V compare) {α : Int} {v w : V}
    (h : t[α]? = some v) :
    (t.insert α w).fresh = t.fresh := by
  -- inserting at an existing key does not change `maxKey?`
  unfold Std.ExtTreeMap.fresh
  have hkeys : (t.insert α w).maxKey? = t.maxKey? := by
    rw [Std.ExtTreeMap.maxKey?_insert]
    have hmem : α ∈ t := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [h]; rfl)
    have hsome : t.maxKey?.isSome := Std.ExtTreeMap.isSome_maxKey?_of_mem hmem
    obtain ⟨km, hkm⟩ : ∃ km, t.maxKey? = some km := ⟨_, Option.eq_some_of_isSome hsome⟩
    rw [hkm]
    simp only [Option.elim, Option.some.injEq]
    have hle_αkm : (compare α km).isLE := by
      have hget : t.maxKey?.get (Std.ExtTreeMap.isSome_maxKey?_of_mem hmem) = km :=
        Option.get_of_eq_some _ hkm
      exact Std.ExtTreeMap.le_maxKey?_of_mem hmem hget
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
  Std.ExtTreeMap.fresh_insert_of_mem σ.tapes h

theorem _root_.Std.ExtTreeMap.elem_fresh_ne
    {V : Type*} {t : Std.ExtTreeMap Int V compare} {k : Int} {v : V}
    (h : t[k]? = some v) : t.fresh ≠ k := by
  intro heq
  have hfresh := Std.ExtTreeMap.fresh_get? t
  rw [heq, h] at hfresh
  simp at hfresh

/-! ## `Cfg.uniform` -/

theorem Cfg.uniform_nonpos_eq {z : Int} {σ : State rT} (hz : ¬ 0 < z) :
    Cfg.uniform z σ = MeasureTheory.Measure.dirac ⟨.lit (.int (-1)), σ⟩ := by
  unfold Cfg.uniform Int.isPos
  rw [dite_eq_right hz]

theorem Cfg.uniform_ne_zero
    (z : Int) (σ : State rT) : Cfg.uniform z σ ≠ 0 :=
  MeasureTheory.IsProbabilityMeasure.ne_zero _

/-- Reindex a sum over `Ico 0 z` along a map that restricts to a bijection on it. -/
theorem _root_.Finset.sum_Ico_comp_of_bijOn {M : Type _} [AddCommMonoid M]
    {z : Int} {f : Int → Int}
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (g : Int → M) :
    ∑ n ∈ Finset.Ico (0 : Int) z, g (f n) = ∑ m ∈ Finset.Ico (0 : Int) z, g m := by
  refine Finset.sum_bij (fun n _ => f n) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Ico] at hn ⊢
    exact hdom n hn.1 hn.2
  · intro n₁ hn₁ n₂ hn₂ h
    simp only [Finset.mem_Ico] at hn₁ hn₂
    obtain ⟨n₀, -, huniq⟩ := hbij (f n₁) (hdom n₁ hn₁.1 hn₁.2).1 (hdom n₁ hn₁.1 hn₁.2).2
    exact (huniq n₁ ⟨hn₁, rfl⟩).trans (huniq n₂ ⟨hn₂, h.symm⟩).symm
  · intro m hm
    simp only [Finset.mem_Ico] at hm
    obtain ⟨n₀, ⟨hn₀, hfn₀⟩, -⟩ := hbij m hm.1 hm.2
    exact ⟨n₀, by simp only [Finset.mem_Ico]; exact hn₀, hfn₀⟩
  · intro n _; rfl

theorem Cfg.uniform_eq_map_uniformOfFinset {z : Int} (hz : 0 < z) (σ : State rT) :
    Cfg.uniform z σ = (PMF.uniformOfFinset (Finset.Ico (0 : Int) z)
        (Finset.nonempty_Ico.mpr hz)).toMeasure.map
      (fun n : Int => (⟨.lit (.int n), σ⟩ : Cfg rT)) := by
  unfold Cfg.uniform Int.isPos; simp only [dite_eq_left hz]

/-- The integral of a measurable `φ` against `Cfg.uniform z σ` is its average over `Ico 0 z`. -/
theorem Cfg.lintegral_uniform
    {z : Int} (Hz : 0 < z) (σ : State rT)
    {φ : Cfg rT → ENNReal} (hφ : Measurable φ) :
    ∫⁻ c, φ c ∂(Cfg.uniform z σ) =
      ((z.toNat : ENNReal)⁻¹) * ∑ n ∈ Finset.Ico (0 : Int) z,
          φ (⟨.lit (.int n), σ⟩ : Cfg rT) := by
  have hcard : (Finset.Ico (0 : Int) z).card = z.toNat := by rw [Int.card_Ico]; omega
  rw [Cfg.uniform_eq_map_uniformOfFinset Hz σ,
      MeasureTheory.lintegral_map hφ Measurable.of_discrete,
      MeasureTheory.lintegral_countable',
      tsum_eq_sum (s := Finset.Ico (0 : Int) z) fun n hn => by
        rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
            PMF.uniformOfFinset_apply_of_notMem _ hn, mul_zero],
      Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
      PMF.uniformOfFinset_apply_of_mem _ hn, hcard, mul_comm]

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
      exact absurd h0 MeasureTheory.Measure.dirac_ne_zero
    · rfl
  case binop.redex h0 =>
    unfold Option.unwrapM at h0 ⊢
    split <;> rename_i hopt
    · rw [hopt] at h0
      exact absurd h0 MeasureTheory.Measure.dirac_ne_zero
    · rfl
  case alloc.no_redex hned =>
    simp [Exp.toVal?_eq_none.mpr hned]
  case load.segfault hheap =>
    have hnotmem : ‹Loc› ∉ (σ.update_tapes (·.insert α bs')).heap := hheap
    have hnone := Option.not_isSome_iff_eq_none.mp
      (fun hsome => hnotmem (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr hsome))
    rw [hnone]
  case store.no_redex hned =>
    simp [Exp.toVal?_eq_none.mpr hned]
  case store.segfault hv hheap =>
    have hnotmem : ‹Loc› ∉ (σ.update_tapes (·.insert α bs')).heap := hheap
    have hnone := Option.not_isSome_iff_eq_none.mp
      (fun hsome => hnotmem (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr hsome))
    rw [hnone]
  case rand.plain h0 =>
    exact absurd h0 (Cfg.uniform_ne_zero _ _)
  case rand.tape.unalloc hnotin =>
    have hne : α ≠ ‹Lbl› := by
      intro he
      exact hnotin (he ▸ Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hmem]; rfl))
    have hnone : σ.tapes[‹Lbl›]? = none :=
      Option.not_isSome_iff_eq_none.mp
        (fun hsome => hnotin (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr hsome))
    rw [State.upd_diff_tape_tot (Ne.symm hne), hnone]
  case rand.tape.mismatch =>
    exact absurd h0 (Cfg.uniform_ne_zero _ _)
  case rand.tape.empty =>
    exact absurd h0 (Cfg.uniform_ne_zero _ _)
  case urand h0 =>
    exact absurd h0 (MeasureTheory.IsProbabilityMeasure.ne_zero _)

end ProbLang
