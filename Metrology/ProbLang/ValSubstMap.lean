module

public import Metrology.ProbLang.Metatheory

/-! # Paired value substitutions

Association lists of value pairs, with projections to `SubstMap` for the left and right sides. -/

@[expose] public section

namespace ProbLang

/-- A substitution assigning a pair of values (left, right) to each variable. -/
abbrev ValSubstMap (rT : Type _) := List (Var × (Val rT × Val rT))

namespace ValSubstMap
variable {rT : Type _}

/-- The pair assigned to `x`, preferring the entry nearest the end of the list. -/
def lookup : ValSubstMap rT → Var → Option (Val rT × Val rT)
  | [], _ => none
  | (y, p) :: rest, x =>
    match lookup rest x with
    | some q => some q
    | none => if x = y then some p else none

theorem lookup_eq_none_of_not_mem {y : Var} : ∀ (vs : ValSubstMap rT),
    y ∉ (vs.map (·.1)).toFinset → vs.lookup y = none
  | [], _ => rfl
  | (z, _) :: rest, hyNot => by
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at hyNot
    simp only [ValSubstMap.lookup, lookup_eq_none_of_not_mem rest hyNot.2]
    simp [hyNot.1]

theorem mem_of_lookup_eq_some {vs : ValSubstMap rT} {y : Var} {w1 w2 : Val rT}
    (h : vs.lookup y = some (w1, w2)) : (y, (w1, w2)) ∈ vs := by
  induction vs with
  | nil => simp [ValSubstMap.lookup] at h
  | cons p rest ih =>
    obtain ⟨z, ⟨v1, v2⟩⟩ := p
    simp only [ValSubstMap.lookup] at h
    cases hr : ValSubstMap.lookup rest y with
    | some q =>
      rw [hr] at h
      obtain rfl : q = (w1, w2) := by injection h
      exact List.mem_cons.mpr (.inr (ih hr))
    | none =>
      rw [hr] at h
      split_ifs at h with hyz
      · subst hyz
        obtain ⟨rfl, rfl⟩ : v1 = w1 ∧ v2 = w2 := by simpa using h
        exact List.mem_cons.mpr (.inl rfl)

theorem mem_of_lookup_isSome {vs : ValSubstMap rT} {x : Var}
    (h : (vs.lookup x).isSome) : ∃ p ∈ vs, p.1 = x := by
  obtain ⟨⟨w1, w2⟩, hw⟩ := Option.isSome_iff_exists.mp h
  exact ⟨(x, (w1, w2)), mem_of_lookup_eq_some hw, rfl⟩

theorem lookup_isSome_of_mem {vs : ValSubstMap rT} {x : Var}
    (hmem : ∃ w, (x, w) ∈ vs) : (vs.lookup x).isSome := by
  obtain ⟨w, hmem⟩ := hmem
  induction vs with
  | nil => simp at hmem
  | cons q rest ih =>
    obtain ⟨k, v⟩ := q
    simp only [ValSubstMap.lookup]
    cases hr : ValSubstMap.lookup rest x with
    | some _ => rfl
    | none =>
      rcases List.mem_cons.mp hmem with hq | hm
      · injection hq with hkx _
        simp [hkx]
      · rw [hr] at ih
        exact absurd (ih hm) (by simp)

/-- Remove every entry for `x`. -/
def delete (vs : ValSubstMap rT) (x : Var) : ValSubstMap rT :=
  vs.filter fun p => !decide (p.1 = x)

theorem delete_cons (z : Var) (w : Val rT × Val rT) (rest : ValSubstMap rT) (x : Var) :
    ValSubstMap.delete ((z, w) :: rest) x =
      if z = x then rest.delete x else (z, w) :: rest.delete x := by
  by_cases hzx : z = x <;> simp [ValSubstMap.delete, hzx]

theorem lookup_delete_self (vs : ValSubstMap rT) (x : Var) :
    (vs.delete x).lookup x = none := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    rw [delete_cons]
    split_ifs with hzx
    · exact ih
    · simp [ValSubstMap.lookup, ih, Ne.symm hzx]

theorem lookup_delete_other (vs : ValSubstMap rT) (x z : Var) (hxz : z ≠ x) :
    (vs.delete x).lookup z = vs.lookup z := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨w, v⟩ := p
    rw [delete_cons]
    split_ifs with hwx
    · subst hwx
      simp only [ValSubstMap.lookup, ih]
      cases ValSubstMap.lookup rest z <;> simp [hxz]
    · simp [ValSubstMap.lookup, ih]

theorem mem_delete (vs : ValSubstMap rT) (x : Var) (p : Var × (Val rT × Val rT)) :
    p ∈ vs.delete x ↔ p ∈ vs ∧ p.1 ≠ x := by
  simp [delete, List.mem_filter]

theorem proj_dom (f : Val rT × Val rT → Val rT) (vs : ValSubstMap rT) :
    ((vs.map fun p => (p.1, (f p.2).1)).map (·.1)).toFinset = (vs.map (·.1)).toFinset := by
  simp only [List.map_map]; rfl

theorem proj_delete (f : Val rT × Val rT → Val rT) (vs : ValSubstMap rT) (x : Var) :
    (vs.delete x).map (fun p => (p.1, (f p.2).1)) =
      (vs.map fun p => (p.1, (f p.2).1)).filter fun p => !decide (p.1 = x) := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    rw [delete_cons, List.map_cons, List.filter_cons]
    by_cases hzx : z = x <;> simp [hzx, ih]

variable [LawfulProbLangℝ rT]

/-- The substitution of left values. -/
def fst (vs : ValSubstMap rT) : SubstMap rT := vs.map fun p => (p.1, p.2.1.1)

/-- The substitution of right values. -/
def snd (vs : ValSubstMap rT) : SubstMap rT := vs.map fun p => (p.1, p.2.2.1)

/-! Lemmas for any projection `f` of the value pair; `fst_*`/`snd_*` below instantiate `f`. -/

section proj
variable (f : Val rT × Val rT → Val rT)

theorem proj_lookup : ∀ (vs : ValSubstMap rT) (x : Var),
    SubstMap.lookup (vs.map fun p => (p.1, (f p.2).1)) x = (vs.lookup x).map fun q => (f q).1
  | [], _ => rfl
  | (y, w) :: rest, x => by
    simp only [List.map_cons, SubstMap.lookup, ValSubstMap.lookup, proj_lookup rest x]
    cases ValSubstMap.lookup rest x <;> simp

theorem proj_allClosed {vs : ValSubstMap rT} (h : ∀ p ∈ vs, (f p.2).1.isClosed .empty) :
    SubstMap.AllClosed (vs.map fun p => (p.1, (f p.2).1)) := by
  intro p hp
  obtain ⟨q, hmem, rfl⟩ := List.mem_map.mp hp
  exact h q hmem

end proj

theorem fst_lookup (vs : ValSubstMap rT) (x : Var) :
    SubstMap.lookup vs.fst x = (vs.lookup x).map fun p => p.1.1 :=
  proj_lookup Prod.fst vs x

theorem fst_lookup_eq_none_of_not_mem {vs : ValSubstMap rT} {y : Var}
    (hy : y ∉ (vs.map (·.1)).toFinset) : SubstMap.lookup vs.fst y = none := by
  rw [fst_lookup, lookup_eq_none_of_not_mem vs hy]; rfl

theorem snd_lookup (vs : ValSubstMap rT) (x : Var) :
    SubstMap.lookup vs.snd x = (vs.lookup x).map fun p => p.2.1 :=
  proj_lookup Prod.snd vs x

theorem snd_lookup_eq_none_of_not_mem {vs : ValSubstMap rT} {y : Var}
    (hy : y ∉ (vs.map (·.1)).toFinset) : SubstMap.lookup vs.snd y = none := by
  rw [snd_lookup, lookup_eq_none_of_not_mem vs hy]; rfl

theorem fst_dom (vs : ValSubstMap rT) :
    (vs.fst.map (·.1)).toFinset = (vs.map (·.1)).toFinset :=
  proj_dom Prod.fst vs

theorem snd_dom (vs : ValSubstMap rT) :
    (vs.snd.map (·.1)).toFinset = (vs.map (·.1)).toFinset :=
  proj_dom Prod.snd vs

theorem fst_delete (vs : ValSubstMap rT) (x : Var) :
    (vs.delete x).fst = vs.fst.filter fun p => !decide (p.1 = x) :=
  proj_delete Prod.fst vs x

theorem snd_delete (vs : ValSubstMap rT) (x : Var) :
    (vs.delete x).snd = vs.snd.filter fun p => !decide (p.1 = x) :=
  proj_delete Prod.snd vs x

end ValSubstMap

end ProbLang
