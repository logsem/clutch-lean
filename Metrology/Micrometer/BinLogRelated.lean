module

public import Metrology.Micrometer.Interp

/-! Relational contexts and the semantic typing judgement `bin_log_related`. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

variable {rT : Type}

/-! ## Relational environment typing -/

/-- A relational typing context assigns a logical relation to each variable. -/
abbrev RelCtx (rT : Type) (GF : BundledGFunctors) := List (Var × lrel rT GF)

namespace RelCtx

/-- The relation of the last entry for `x` in the list.

Same order as `ValSubstMap.lookup`; callers only cons fresh variables, so shadowing never arises. -/
def lookup : RelCtx rT GF → Var → Option (lrel rT GF)
  | [], _ => none
  | (y, A) :: rest, x =>
    match lookup rest x with
    | some B => some B
    | none => if x = y then some A else none

theorem lookup_isSome_of_mem {Γ : RelCtx rT GF} {p : Var × lrel rT GF}
    (h : p ∈ Γ) : (Γ.lookup p.1).isSome := by
  induction Γ with
  | nil => cases h
  | cons q rest ih =>
    simp only [lookup]
    rcases List.mem_cons.mp h with rfl | hRest
    · cases lookup rest p.1 <;> simp
    · have := ih hRest
      cases hr : lookup rest p.1 <;> simp_all

theorem mem_of_lookup_isSome {Γ : RelCtx rT GF} {y : Var}
    (h : (Γ.lookup y).isSome) : y ∈ (Γ.map (·.1)).toFinset := by
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

theorem lookup_eq_none_of_not_mem {Γ : RelCtx rT GF} {y : Var}
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset) : Γ.lookup y = none := by
  cases hΓ : Γ.lookup y with
  | none => rfl
  | some _ => exact absurd (mem_of_lookup_isSome (by rw [hΓ]; rfl)) hyNotDom

end RelCtx

section env_typed
variable {GF : BundledGFunctors}

/-- `vs` maps the variables of `Γ` to pairs of closed values related at their relations. The
closedness conjunct covers every entry of `vs`, including shadowed ones that `lookup` cannot
reach; `substMap` lemmas need it (`SubstMap.AllClosed`). -/
noncomputable def env_ltyped2 (Γ : RelCtx rT GF) (vs : ValSubstMap rT) : IProp GF := iprop%
  ⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝ ∗
  ⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝ ∗
  (∀ x A v1 v2, ⌜Γ.lookup x = some A⌝ -∗ ⌜vs.lookup x = some (v1, v2)⌝ -∗ A v1 v2)

/-- `env_ltyped2` is persistent. -/
instance env_ltyped2_persistent (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    Persistent (env_ltyped2 Γ vs) := by
  unfold env_ltyped2
  infer_instance

theorem env_ltyped2_domEq (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝ :=
  sep_elim_left

theorem env_ltyped2_allClosed (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝ :=
  sep_elim_right.trans sep_elim_left

theorem env_ltyped2_fst_allClosed [LawfulProbLangℝ rT] (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜SubstMap.AllClosed vs.fst⌝ :=
  (env_ltyped2_allClosed Γ vs).trans <| pure_mono fun hc =>
    ValSubstMap.proj_allClosed Prod.fst fun p hp => (hc p hp).1

theorem env_ltyped2_snd_allClosed [LawfulProbLangℝ rT] (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜SubstMap.AllClosed vs.snd⌝ :=
  (env_ltyped2_allClosed Γ vs).trans <| pure_mono fun hc =>
    ValSubstMap.proj_allClosed Prod.snd fun p hp => (hc p hp).2

theorem env_ltyped2_domSubset (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜(Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset⌝ := by
  iintro Hvs
  ihave %hDom := env_ltyped2_domEq Γ vs $$ Hvs
  ipureintro
  intro y hy
  simp only [List.mem_toFinset, List.mem_map] at hy ⊢
  obtain ⟨p, hp, rfl⟩ := hy
  exact ValSubstMap.mem_of_lookup_isSome ((hDom p.1).mp (RelCtx.lookup_isSome_of_mem hp))

theorem env_ltyped2_lookup (Γ : RelCtx rT GF) (vs : ValSubstMap rT) (x : Var) (A : lrel rT GF)
    (hΓ : Γ.lookup x = some A) :
    env_ltyped2 Γ vs ⊢ ∃ v1 v2, ⌜vs.lookup x = some (v1, v2)⌝ ∗ A v1 v2 := by
  unfold env_ltyped2
  iintro ⟨%Hdom, -, Hall⟩
  obtain ⟨⟨v1, v2⟩, hvs_eq⟩ := Option.isSome_iff_exists.mp ((Hdom x).mp (by rw [hΓ]; rfl))
  iexists v1, v2
  iframe %hvs_eq
  iapply Hall $$ %x %A %v1 %v2 %hΓ %hvs_eq

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

theorem env_ltyped2_insert (Γ : RelCtx rT GF) (vs : ValSubstMap rT) (x : Var) (A : lrel rT GF)
    (v1 v2 : Val rT) (hv1c : v1.1.isClosed .empty) (hv2c : v2.1.isClosed .empty) : iprop%
    A v1 v2 ∗ env_ltyped2 Γ vs ⊢ env_ltyped2 ((x, A) :: Γ) ((x, (v1, v2)) :: vs) := by
  unfold env_ltyped2
  iintro ⟨HA, %Hdom, %Hclosed, #Hall⟩
  isplitr
  · ipureintro
    intro y
    simp only [RelCtx.lookup, ValSubstMap.lookup]
    cases hΓy : Γ.lookup y with
    | some B =>
      obtain ⟨_, hvy⟩ := Option.isSome_iff_exists.mp ((Hdom y).mp (by rw [hΓy]; rfl))
      rw [hvy]; simp
    | none =>
      rw [show vs.lookup y = none from
        Option.not_isSome_iff_eq_none.mp fun h => by simpa [hΓy] using (Hdom y).mpr h]
      simp
  isplitr
  · ipureintro
    exact List.forall_mem_cons.mpr ⟨⟨hv1c, hv2c⟩, Hclosed⟩
  iintro %y %B %w1 %w2 %hΓ' %hvs'
  simp only [RelCtx.lookup, ValSubstMap.lookup] at hΓ' hvs'
  cases hΓy : Γ.lookup y with
  | some Bold =>
    obtain rfl : Bold = B := by simpa [hΓy] using hΓ'
    obtain ⟨⟨w1', w2'⟩, hvy⟩ := Option.isSome_iff_exists.mp ((Hdom y).mp (by rw [hΓy]; rfl))
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

theorem env_ltyped2_drop_head (Γ : RelCtx rT GF) (vs : ValSubstMap rT) (y : Var) (A : lrel rT GF)
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset) :
    env_ltyped2 ((y, A) :: Γ) vs ⊢ env_ltyped2 Γ (vs.delete y) := by
  unfold env_ltyped2
  iintro ⟨%Hdom, %Hclosed, #Hall⟩
  isplitr
  · ipureintro
    intro z
    by_cases hzy : z = y
    · subst hzy
      rw [RelCtx.lookup_eq_none_of_not_mem hyNotDom, ValSubstMap.lookup_delete_self]
      simp
    · rw [ValSubstMap.lookup_delete_other vs y z hzy]
      have heq := Hdom z
      rw [RelCtx.lookup_cons] at heq
      cases hΓz : Γ.lookup z <;> simpa [hΓz, hzy] using heq
  isplitr
  · ipureintro; exact fun p hp => Hclosed p ((ValSubstMap.mem_delete _ _ _).mp hp).1
  iintro %z %B %v1 %v2 %hΓz %hvsz
  have hzy : z ≠ y := by
    rintro rfl
    rw [ValSubstMap.lookup_delete_self] at hvsz
    cases hvsz
  rw [ValSubstMap.lookup_delete_other vs y z hzy] at hvsz
  have hΓhead : RelCtx.lookup ((y, A) :: Γ) z = some B := by rw [RelCtx.lookup_cons, hΓz]
  iapply Hall $$ %z %B %v1 %v2 %hΓhead %hvsz

end env_typed

/-! ## The semantic typing judgement -/

section bin_log_related
variable [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

variable (L) in
/-- The semantic typing judgement: related substitutions give related expressions. -/
noncomputable def bin_log_related (E : CoPset) (Γ : RelCtx rT GF) (e e' : Exp rT)
    (A : lrel rT GF) : IProp GF := iprop%
  ∀ vs, env_ltyped2 Γ vs -∗ refines L E (Exp.substMap vs.fst e) (Exp.substMap vs.snd e') A

variable (L) in
/-- The semantic typing judgement at a syntactic type. -/
noncomputable abbrev bin_log_related_ty (E : CoPset) (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) (e e' : Exp rT) (τ : Ty) : IProp GF :=
  bin_log_related L E Γ e e' (interp L τ Δ)

/-- At the empty context, the semantic typing judgement is a closed refinement. -/
theorem bin_log_related_nil_elim {E : CoPset} {e e' : Exp rT} {A : lrel rT GF} :
    bin_log_related L E [] e e' A ⊢ refines L E e e' A := by
  show bin_log_related L E [] e e' A ⊢ refines L E (Exp.substMap (ValSubstMap.fst []) e)
    (Exp.substMap (ValSubstMap.snd []) e') A
  unfold bin_log_related
  iintro H
  iapply H $$ %([] : ValSubstMap rT)
  iapply env_ltyped2_empty

/-- A closed refinement is the semantic typing judgement at the empty context. -/
theorem bin_log_related_nil_intro {E : CoPset} {e e' : Exp rT} {A : lrel rT GF} :
    refines L E e e' A ⊢ bin_log_related L E [] e e' A := by
  unfold bin_log_related
  iintro H %vs Hvs
  ihave ⟨%hvs_nil⟩ := env_ltyped2_empty_inv vs $$ Hvs
  subst hvs_nil
  rw [show Exp.substMap (ValSubstMap.fst ([] : ValSubstMap rT)) e = e from rfl,
    show Exp.substMap (ValSubstMap.snd ([] : ValSubstMap rT)) e' = e' from rfl]
  iexact H

/-- Rename the innermost relational variable `x` to a fresh `y` (used for named context binders,
`bin_log_related_close_cofinite`). -/
theorem bin_log_related_rename {E : CoPset} {Γ : RelCtx rT GF} {x y : Var} {A : lrel rT GF}
    {τE τE' : Exp rT} {B : lrel rT GF} (hxy : x ≠ y) (hxNotDom : x ∉ (Γ.map (·.1)).toFinset)
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset) (hyFvE : y ∉ τE.fv) (hyFvE' : y ∉ τE'.fv) :
    bin_log_related L E ((x, A) :: Γ) τE τE' B ⊢
    bin_log_related L E ((y, A) :: Γ) (τE.subst x (.fvar y)) (τE'.subst x (.fvar y)) B := by
  unfold bin_log_related
  iintro Hold %vs #Hvs
  have hyHeadLookup : RelCtx.lookup ((y, A) :: Γ) y = some A := by
    rw [RelCtx.lookup_cons, RelCtx.lookup_eq_none_of_not_mem hyNotDom]; simp
  icases env_ltyped2_lookup _ vs _ _ hyHeadLookup $$ Hvs with ⟨%w1, %w2, %hvsLookupY, HAw⟩
  ihave %hvsClosed := env_ltyped2_allClosed _ vs $$ Hvs
  obtain ⟨hw1c, hw2c⟩ := hvsClosed _ (ValSubstMap.mem_of_lookup_eq_some hvsLookupY)
  ihave HvsDrop := env_ltyped2_drop_head Γ vs y A hyNotDom $$ Hvs
  ihave Hvs' := env_ltyped2_insert Γ (vs.delete y) x A _ _ hw1c hw2c $$ [$HAw $HvsDrop]
  set vs' : ValSubstMap rT := (x, (w1, w2)) :: vs.delete y
  ihave Hrefines := Hold $$ %vs' Hvs'
  ihave %hvsDom := env_ltyped2_domEq _ vs $$ Hvs
  have hvsLookupX : vs.lookup x = none := by
    have hΓheadX : RelCtx.lookup ((y, A) :: Γ) x = none := by
      rw [RelCtx.lookup_cons, RelCtx.lookup_eq_none_of_not_mem hxNotDom]; simp [hxy]
    cases hvs : vs.lookup x with
    | none => rfl
    | some _ => simpa [hΓheadX] using (hvsDom x).mpr (by rw [hvs]; rfl)
  have hxNotVsDom : x ∉ (vs.map (·.1)).toFinset := by
    intro h
    simp only [List.mem_toFinset, List.mem_map] at h
    obtain ⟨p, hpmem, rfl⟩ := h
    simpa [hvsLookupX] using ValSubstMap.lookup_isSome_of_mem ⟨p.2, hpmem⟩
  -- substituting vs after renaming x↦y equals substituting (x ↦ vs(y)) :: vs.delete y
  have hswapFst :=
    Exp.substMap_subst_fvar_lookup vs.fst τE x y w1.1 (by rwa [ValSubstMap.fst_dom])
      (ValSubstMap.proj_allClosed Prod.fst fun p hp => (hvsClosed p hp).1)
      (by rw [ValSubstMap.fst_lookup, hvsLookupY]; rfl) hyFvE
  have hswapSnd :=
    Exp.substMap_subst_fvar_lookup vs.snd τE' x y w2.1 (by rwa [ValSubstMap.snd_dom])
      (ValSubstMap.proj_allClosed Prod.snd fun p hp => (hvsClosed p hp).2)
      (by rw [ValSubstMap.snd_lookup, hvsLookupY]; rfl) hyFvE'
  rw [← ValSubstMap.fst_delete] at hswapFst
  rw [← ValSubstMap.snd_delete] at hswapSnd
  rw [show Exp.substMap vs.fst (τE.subst x (.fvar y)) = Exp.substMap vs'.fst τE from hswapFst,
    show Exp.substMap vs.snd (τE'.subst x (.fvar y)) = Exp.substMap vs'.snd τE' from hswapSnd]
  iexact Hrefines

/-- `bin_log_related_rename` for the type-level judgement. -/
theorem bin_log_related_ty_rename {E : CoPset} {Δ : TyEnv rT GF} {Γ : RelCtx rT GF} {x y : Var}
    {A : lrel rT GF} {τE τE' : Exp rT} {τ : Ty} (hxy : x ≠ y)
    (hxNotDom : x ∉ (Γ.map (·.1)).toFinset) (hyNotDom : y ∉ (Γ.map (·.1)).toFinset)
    (hyFvE : y ∉ τE.fv) (hyFvE' : y ∉ τE'.fv) :
    bin_log_related_ty L E Δ ((x, A) :: Γ) τE τE' τ ⊢
    bin_log_related_ty L E Δ ((y, A) :: Γ) (τE.subst x (.fvar y)) (τE'.subst x (.fvar y)) τ :=
  bin_log_related_rename hxy hxNotDom hyNotDom hyFvE hyFvE'

end bin_log_related

/-! ## Notation for the semantic typing judgement -/

scoped notation:100 E "; " Δ "; " Γ " ⊨[" L "] " e " ≤log≤ " e' " : " τ =>
  bin_log_related_ty L E Δ Γ e e' τ

scoped notation:100 Δ "; " Γ " ⊨[" L "] " e " ≤log≤ " e' " : " τ =>
  bin_log_related_ty L (⊤ : CoPset) Δ Γ e e' τ

end ProbLang
