module

public import Metrology.Micrometer.Interp
import Metrology.Iris.LocalBI

/-! # The semantic typing judgement

Relational contexts `RelCtx`, related closing substitutions `env_ltyped2`, and the open-term
judgement `bin_log_related` (`E; Δ; Γ ⊨[L] e ≤log≤ e' : τ`), with its variable-renaming lemma. -/

@[expose] public section

open Option (isSome_iff_exists not_isSome_iff_eq_none)
open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

variable {rT : Type} {GF : BundledGFunctors}

open List (mem_cons mem_toFinset mem_map forall_mem_cons)
open Exp

/-! ## Relational contexts -/

/-- A relational typing context assigns a logical relation to each variable. -/
abbrev RelCtx (rT : Type) (GF : BundledGFunctors) := List (Var × lrel rT GF)

namespace RelCtx

/-- The relation of the deepest entry for `x` in the list, as in `ValSubstMap.lookup`; callers
only cons fresh variables, so the order never matters. -/
def lookup : RelCtx rT GF → Var → Option (lrel rT GF)
  | [], _ => none
  | (y, A) :: rest, x =>
    match lookup rest x with
    | some B => some B
    | none => if x = y then some A else none

variable {Γ : RelCtx rT GF}

theorem lookup_isSome_of_mem {p : Var × lrel rT GF} (h : p ∈ Γ) : (Γ.lookup p.1).isSome := by
  induction Γ with
  | nil => cases h
  | cons q rest ih =>
    simp only [lookup]
    rcases mem_cons.mp h with rfl | hRest
    · cases lookup rest p.1 <;> simp
    · have := ih hRest
      cases hr : lookup rest p.1 <;> simp_all

variable {y : Var}

theorem mem_of_lookup_isSome (h : (Γ.lookup y).isSome) : y ∈ (Γ.map (·.1)).toFinset := by
  induction Γ with
  | nil => simp [lookup] at h
  | cons q rest ih =>
    obtain ⟨k, B⟩ := q
    simp only [lookup] at h
    cases hr : lookup rest y with
    | some _ => simp [ih (by rw [hr]; rfl)]
    | none => rw [hr] at h; split_ifs at h <;> simp_all

theorem lookup_cons (y : Var) (A : lrel rT GF) (Γ : RelCtx rT GF) (z : Var) :
    RelCtx.lookup ((y, A) :: Γ) z = match Γ.lookup z with
      | some B => some B
      | none => if z = y then some A else none := rfl

theorem lookup_eq_none_of_not_mem (hyNotDom : y ∉ (Γ.map (·.1)).toFinset) : Γ.lookup y = none := by
  cases hΓ : Γ.lookup y with
  | none => rfl
  | some _ => exact absurd (mem_of_lookup_isSome (by rw [hΓ]; rfl)) hyNotDom

end RelCtx

/-! ## Related closing substitutions -/

section env_typed
local bi IProp GF

open RelCtx ValSubstMap

section
variable (Γ : RelCtx rT GF) (vs : ValSubstMap rT)

/-- `vs` maps the variables of `Γ` to pairs of closed values related at their relations; the
closedness conjunct also covers shadowed entries, as `SubstMap.AllClosed` needs. -/
noncomputable def env_ltyped2 : IProp GF := iprop%
  ⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝ ∗
  ⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝ ∗
  (∀ x A v1 v2, ⌜Γ.lookup x = some A⌝ -∗ ⌜vs.lookup x = some (v1, v2)⌝ -∗ A v1 v2)

instance env_ltyped2_persistent : Persistent (env_ltyped2 Γ vs) := by
  unfold env_ltyped2
  infer_instance

theorem env_ltyped2_domEq : env_ltyped2 Γ vs ⊢ ⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝ :=
  sep_elim_left

theorem env_ltyped2_allClosed :
    env_ltyped2 Γ vs ⊢ ⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝ :=
  sep_elim_right.trans sep_elim_left

theorem env_ltyped2_fst_allClosed [LawfulProbLangℝ rT] :
    env_ltyped2 Γ vs ⊢ ⌜SubstMap.AllClosed vs.fst⌝ :=
  (env_ltyped2_allClosed Γ vs).trans <| pure_mono fun hc =>
    proj_allClosed (·.fst) fun p hp => (hc p hp).1

theorem env_ltyped2_snd_allClosed [LawfulProbLangℝ rT] :
    env_ltyped2 Γ vs ⊢ ⌜SubstMap.AllClosed vs.snd⌝ :=
  (env_ltyped2_allClosed Γ vs).trans <| pure_mono fun hc =>
    proj_allClosed (·.snd) fun p hp => (hc p hp).2

theorem env_ltyped2_domSubset :
    env_ltyped2 Γ vs ⊢ ⌜(Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset⌝ := by
  iintro Hvs
  ihave %hDom := env_ltyped2_domEq Γ vs $$ Hvs
  ipureintro
  intro y hy
  simp only [mem_toFinset, mem_map] at hy ⊢
  obtain ⟨p, hp, rfl⟩ := hy
  exact mem_of_lookup_isSome ((hDom p.1).mp (lookup_isSome_of_mem hp))

variable (x : Var) (A : lrel rT GF)

theorem env_ltyped2_lookup (hΓ : Γ.lookup x = some A) :
    env_ltyped2 Γ vs ⊢ ∃ v1 v2, ⌜vs.lookup x = some (v1, v2)⌝ ∗ A v1 v2 := by
  unfold env_ltyped2
  iintro ⟨%Hdom, -, Hall⟩
  obtain ⟨⟨v1, v2⟩, hvs_eq⟩ := isSome_iff_exists.mp ((Hdom x).mp (by rw [hΓ]; rfl))
  iexists v1, v2
  iframe %hvs_eq
  iapply Hall $$ %x %A %v1 %v2 %hΓ %hvs_eq

/-- Extend a related substitution by a variable bound to closed related values. -/
theorem env_ltyped2_insert
    (v1 v2) (hv1c : v1.1.isClosed .empty) (hv2c : v2.1.isClosed .empty) : iprop%
    A v1 v2 ∗ env_ltyped2 Γ vs ⊢ env_ltyped2 ((x, A) :: Γ) ((x, (v1, v2)) :: vs) := by
  unfold env_ltyped2
  iintro ⟨HA, %Hdom, %Hclosed, #Hall⟩
  isplitr
  · ipureintro
    intro y
    simp only [RelCtx.lookup, ValSubstMap.lookup]
    cases hΓy : Γ.lookup y with
    | some B =>
      obtain ⟨_, hvy⟩ := isSome_iff_exists.mp ((Hdom y).mp (by rw [hΓy]; rfl))
      rw [hvy]; simp
    | none =>
      rw [show vs.lookup y = none from
        not_isSome_iff_eq_none.mp fun h => by simpa [hΓy] using (Hdom y).mpr h]
      simp
  isplitr
  · ipureintro
    exact forall_mem_cons.mpr ⟨⟨hv1c, hv2c⟩, Hclosed⟩
  iintro %y %B %w1 %w2 %hΓ' %hvs'
  simp only [RelCtx.lookup, ValSubstMap.lookup] at hΓ' hvs'
  cases hΓy : Γ.lookup y with
  | some Bold =>
    obtain rfl : Bold = B := by simpa [hΓy] using hΓ'
    obtain ⟨⟨w1', w2'⟩, hvy⟩ := isSome_iff_exists.mp ((Hdom y).mp (by rw [hΓy]; rfl))
    obtain ⟨rfl, rfl⟩ : w1' = w1 ∧ w2' = w2 := by simpa [hvy] using hvs'
    iapply Hall $$ %y %Bold %w1' %w2' %hΓy %hvy
  | none =>
    rw [hΓy] at hΓ'
    simp only at hΓ'
    split_ifs at hΓ' with hxy
    injection hΓ' with hBeq; subst hBeq hxy
    cases hvy : vs.lookup y with
    | some _ => exact absurd ((Hdom y).mpr (by rw [hvy]; rfl)) (by simp [hΓy])
    | none =>
      obtain ⟨rfl, rfl⟩ : v1 = w1 ∧ v2 = w2 := by simpa [hvy] using hvs'
      iexact HA

/-- Drop a fresh head variable from both the context and the substitution. -/
theorem env_ltyped2_drop_head (y : Var) (A : lrel rT GF)
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset) :
    env_ltyped2 ((y, A) :: Γ) vs ⊢ env_ltyped2 Γ (vs.delete y) := by
  unfold env_ltyped2
  iintro ⟨%Hdom, %Hclosed, #Hall⟩
  isplitr
  · ipureintro
    intro z
    by_cases hzy : z = y
    · subst hzy
      rw [lookup_eq_none_of_not_mem hyNotDom, lookup_delete_self]
      simp
    · rw [lookup_delete_other vs y z hzy]
      have heq := Hdom z
      rw [lookup_cons] at heq
      cases hΓz : Γ.lookup z <;> simpa [hΓz, hzy] using heq
  isplitr
  · ipureintro; exact fun p hp => Hclosed p ((mem_delete _ _ _).mp hp).1
  iintro %z %B %v1 %v2 %hΓz %hvsz
  have hzy : z ≠ y := by
    rintro rfl
    rw [lookup_delete_self] at hvsz
    cases hvsz
  rw [lookup_delete_other vs y z hzy] at hvsz
  have hΓhead : lookup ((y, A) :: Γ) z = some B := by rw [lookup_cons, hΓz]
  iapply Hall $$ %z %B %v1 %v2 %hΓhead %hvsz

end

theorem env_ltyped2_empty : ⊢ env_ltyped2 ([] : RelCtx rT GF) [] := by
  unfold env_ltyped2
  isplitr
  · ipureintro; simp [RelCtx.lookup, ValSubstMap.lookup]
  isplitr
  · ipureintro; simp
  iintro %x %A %v1 %v2 %hΓ
  simp [RelCtx.lookup] at hΓ

theorem env_ltyped2_empty_inv (vs : ValSubstMap rT) :
    env_ltyped2 ([] : RelCtx rT GF) vs ⊢ ⌜vs = []⌝ := by
  unfold env_ltyped2
  iintro ⟨%Hdom, -, -⟩ !%
  cases vs with
  | nil => rfl
  | cons p rest =>
    exfalso
    have hsome : (ValSubstMap.lookup (p :: rest) p.1).isSome := by
      simp only [ValSubstMap.lookup]
      cases ValSubstMap.lookup rest p.1 <;> simp
    simpa [RelCtx.lookup] using (Hdom p.1).mpr hsome

end env_typed

/-! ## The semantic typing judgement -/

section bin_log_related
variable [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]
local bi IProp GF

open RelCtx ValSubstMap

variable (L) in
/-- The semantic typing judgement: related substitutions give related expressions. -/
noncomputable def bin_log_related (E : CoPset) (Γ : RelCtx rT GF) (e e' : Exp rT)
    (A : lrel rT GF) : IProp GF := iprop%
  ∀ vs, env_ltyped2 Γ vs -∗ refines L E (substMap vs.fst e) (substMap vs.snd e') A

variable (L) in
/-- The semantic typing judgement at a syntactic type. -/
noncomputable abbrev bin_log_related_ty (E : CoPset) (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) (e e' : Exp rT) (τ : Ty) : IProp GF :=
  bin_log_related L E Γ e e' (interp L τ Δ)

/-- `E; Δ; Γ ⊨[L] e ≤log≤ e' : τ` is `bin_log_related_ty L E Δ Γ e e' τ`. -/
scoped notation:100 E "; " Δ "; " Γ " ⊨[" L "] " e " ≤log≤ " e' " : " τ =>
  bin_log_related_ty L E Δ Γ e e' τ

/-- `Δ; Γ ⊨[L] e ≤log≤ e' : τ` is the judgement at the full mask `⊤`. -/
scoped notation:100 Δ "; " Γ " ⊨[" L "] " e " ≤log≤ " e' " : " τ =>
  bin_log_related_ty L ⊤ Δ Γ e e' τ

/-! ## The empty context and renaming -/

section
variable {E : CoPset} {Γ : RelCtx rT GF} {A : lrel rT GF} {e e' : Exp rT}

/-- At the empty context, the semantic typing judgement is a closed refinement. -/
theorem bin_log_related_nil_elim : bin_log_related L E [] e e' A ⊢ refines L E e e' A := by
  show bin_log_related L E [] e e' A ⊢ refines L E (substMap (fst []) e)
    (substMap (snd []) e') A
  unfold bin_log_related
  iintro H
  iapply H $$ %([] : _)
  iapply env_ltyped2_empty

/-- A closed refinement is the semantic typing judgement at the empty context. -/
theorem bin_log_related_nil_intro : refines L E e e' A ⊢ bin_log_related L E [] e e' A := by
  unfold bin_log_related
  iintro H %vs Hvs
  ihave ⟨%hvs_nil⟩ := env_ltyped2_empty_inv vs $$ Hvs
  subst hvs_nil
  rw [show substMap (fst ([] : ValSubstMap rT)) e = e from rfl,
    show substMap (snd ([] : ValSubstMap rT)) e' = e' from rfl]
  iexact H

variable {x y : Var}
variable {τE τE' : Exp rT}

/-- Renaming the innermost relational variable `x` to a fresh `y`. -/
theorem bin_log_related_rename {B : lrel rT GF} (hxy : x ≠ y)
    (hxNotDom : x ∉ (Γ.map (·.1)).toFinset) (hyNotDom : y ∉ (Γ.map (·.1)).toFinset)
    (hyFvE : y ∉ τE.fv) (hyFvE' : y ∉ τE'.fv) :
    bin_log_related L E ((x, A) :: Γ) τE τE' B ⊢
    bin_log_related L E ((y, A) :: Γ) (τE.subst x (.fvar y)) (τE'.subst x (.fvar y)) B := by
  -- From `vs` related at `(y, A) :: Γ`, build `vs' := (x ↦ vs y) :: vs.delete y`, related at
  -- `(x, A) :: Γ`; substituting `vs'` into `τE` equals substituting `vs` into `τE[y/x]`.
  unfold bin_log_related
  iintro Hold %vs #Hvs
  have hyHeadLookup : lookup ((y, A) :: Γ) y = some A := by
    rw [lookup_cons, lookup_eq_none_of_not_mem hyNotDom]; simp
  icases env_ltyped2_lookup _ vs _ _ hyHeadLookup $$ Hvs with ⟨%w1, %w2, %hvsLookupY, HAw⟩
  ihave %hvsClosed := env_ltyped2_allClosed _ vs $$ Hvs
  obtain ⟨hw1c, hw2c⟩ := hvsClosed _ (mem_of_lookup_eq_some hvsLookupY)
  ihave HvsDrop := env_ltyped2_drop_head Γ vs y A hyNotDom $$ Hvs
  ihave Hvs' := env_ltyped2_insert Γ (vs.delete y) x A _ _ hw1c hw2c $$ [$HAw $HvsDrop]
  set vs' : ValSubstMap rT := (x, (w1, w2)) :: vs.delete y
  ihave Hrefines := Hold $$ %vs' Hvs'
  ihave %hvsDom := env_ltyped2_domEq _ vs $$ Hvs
  have hvsLookupX : vs.lookup x = none := by
    have hΓheadX : lookup ((y, A) :: Γ) x = none := by
      rw [lookup_cons, lookup_eq_none_of_not_mem hxNotDom]; simp [hxy]
    cases hvs : vs.lookup x with
    | none => rfl
    | some _ => simpa [hΓheadX] using (hvsDom x).mpr (by rw [hvs]; rfl)
  have hxNotVsDom : x ∉ (vs.map (·.1)).toFinset := by
    intro h
    simp only [mem_toFinset, mem_map] at h
    obtain ⟨p, hpmem, rfl⟩ := h
    simpa [hvsLookupX] using lookup_isSome_of_mem ⟨p.2, hpmem⟩
  have hswapFst :=
    substMap_subst_fvar_lookup vs.fst τE x y w1.1 (by rwa [fst_dom])
      (proj_allClosed (·.fst) fun p hp => (hvsClosed p hp).1)
      (by rw [fst_lookup, hvsLookupY]; rfl) hyFvE
  have hswapSnd :=
    substMap_subst_fvar_lookup vs.snd τE' x y w2.1 (by rwa [snd_dom])
      (proj_allClosed (·.snd) fun p hp => (hvsClosed p hp).2)
      (by rw [snd_lookup, hvsLookupY]; rfl) hyFvE'
  rw [← fst_delete] at hswapFst
  rw [← snd_delete] at hswapSnd
  rw [show substMap vs.fst (τE.subst x (.fvar y)) = substMap vs'.fst τE from hswapFst,
    show substMap vs.snd (τE'.subst x (.fvar y)) = substMap vs'.snd τE' from hswapSnd]
  iexact Hrefines

/-- `bin_log_related_rename` for the type-level judgement. -/
theorem bin_log_related_ty_rename {Δ : TyEnv rT GF} {τ : Ty}
    (hxy : x ≠ y)
    (hxNotDom : x ∉ (Γ.map (·.1)).toFinset) (hyNotDom : y ∉ (Γ.map (·.1)).toFinset)
    (hyFvE : y ∉ τE.fv) (hyFvE' : y ∉ τE'.fv) :
    bin_log_related_ty L E Δ ((x, A) :: Γ) τE τE' τ ⊢
    bin_log_related_ty L E Δ ((y, A) :: Γ) (τE.subst x (.fvar y)) (τE'.subst x (.fvar y)) τ :=
  bin_log_related_rename hxy hxNotDom hyNotDom hyFvE hyFvE'

end

end bin_log_related

end ProbLang
