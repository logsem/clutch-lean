module

public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.Model
public import Metrology.ProbLang.Metatheory
public import Metrology.ProbLang.ValSubstMap
public import Metrology.ProbLang.Syntax.Types

@[expose] public section

/-! # Type Interpretation -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

section TyEnvSetup
variable {GF : BundledGFunctors}

abbrev TyEnv (rT : Type _) (GF : BundledGFunctors) := Nat → lrel rT GF

def TyEnv.cons (X : lrel rT GF) (Δ : TyEnv rT GF) : TyEnv rT GF
  | 0 => X
  | n + 1 => Δ n

omit [LawfulProbLangℝ rT] in
theorem TyEnv.cons_ne_head {n : Nat} {X Y : lrel rT GF} {Δ : TyEnv rT GF} (h : X ≡{n}≡ Y) :
    TyEnv.cons X Δ ≡{n}≡ TyEnv.cons Y Δ
  | 0 => h
  | _ + 1 => Dist.rfl

omit [LawfulProbLangℝ rT] in
theorem TyEnv.cons_ne_tail {n : Nat} {X : lrel rT GF} {Δ Δ' : TyEnv rT GF} (h : Δ ≡{n}≡ Δ') :
    TyEnv.cons X Δ ≡{n}≡ TyEnv.cons X Δ'
  | 0 => Dist.rfl
  | m + 1 => h m

@[reducible] def ctxLookup (x : Nat) (Δ : TyEnv rT GF) : lrel rT GF := Δ x

end TyEnvSetup

section interp
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

structure NEFun (rT : Type _) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (GF : BundledGFunctors) where
  fn : TyEnv rT GF → lrel rT GF
  ne : ∀ {n : Nat} {Δ Δ' : TyEnv rT GF}, Δ ≡{n}≡ Δ' → fn Δ ≡{n}≡ fn Δ'

namespace NEFun
variable {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

@[reducible] noncomputable def const (L : lrel rT GF) : NEFun rT GF :=
  { fn := fun _ => L, ne := fun _ => Dist.rfl }

@[reducible] def ofCtx (x : Nat) : NEFun rT GF :=
  { fn := fun Δ => ctxLookup x Δ, ne := fun h => h x }

@[reducible] noncomputable def map2 (F : lrel rT GF → lrel rT GF → lrel rT GF)
    [OFE.NonExpansive₂ F] (A B : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => F (A.fn Δ) (B.fn Δ)
    ne := fun h => OFE.NonExpansive₂.ne (A.ne h) (B.ne h) }

@[reducible] noncomputable def map1 (F : lrel rT GF → lrel rT GF)
    [OFE.NonExpansive F] (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => F (A.fn Δ)
    ne := fun h => OFE.NonExpansive.ne (A.ne h) }

@[reducible] noncomputable def rec' (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => lrel_rec
      { f := fun X => A.fn (TyEnv.cons X Δ)
        ne := ⟨fun {_ _ _} hXY => A.ne (TyEnv.cons_ne_head hXY)⟩ }
    ne := fun h => lrel_rec_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

@[reducible] noncomputable def forall' (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => lrel_forall (fun X => A.fn (TyEnv.cons X Δ))
    ne := fun h => lrel_forall_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

@[reducible] noncomputable def exists' (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => lrel_exists (fun X => A.fn (TyEnv.cons X Δ))
    ne := fun h => lrel_exists_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

end NEFun

noncomputable def interpNE : Ty → NEFun rT GF
  | .unit         => NEFun.const lrel_unit
  | .int          => NEFun.const lrel_int
  | .bool         => NEFun.const lrel_bool
  | .real         => NEFun.const lrel_real
  | .tape         => NEFun.const lrel_tape
  | .var x        => NEFun.ofCtx x
  | .prod τ1 τ2   => NEFun.map2 lrel_prod (interpNE τ1) (interpNE τ2)
  | .sum  τ1 τ2   => NEFun.map2 lrel_sum  (interpNE τ1) (interpNE τ2)
  | .arrow τ1 τ2  => NEFun.map2 lrel_arr  (interpNE τ1) (interpNE τ2)
  | .ref τ        => NEFun.map1 lrel_ref (interpNE τ)
  | .rec' τ'      => NEFun.rec'    (interpNE τ')
  | .forall' τ'   => NEFun.forall' (interpNE τ')
  | .exists' τ'   => NEFun.exists' (interpNE τ')

noncomputable def interp (τ : Ty) (Δ : TyEnv rT GF) : lrel rT GF :=
  (interpNE τ).fn Δ

theorem interp_ne_env (τ : Ty) {n : Nat} {Δ Δ' : TyEnv rT GF} (h : Δ ≡{n}≡ Δ') :
    interp τ Δ ≡{n}≡ interp τ Δ' := (interpNE τ).ne h

/-! ### `interp` head-shape equations -/

@[simp] theorem interp_unit (Δ : TyEnv rT GF) : interp Ty.unit Δ = lrel_unit := rfl
@[simp] theorem interp_int  (Δ : TyEnv rT GF) : interp Ty.int  Δ = lrel_int  := rfl
@[simp] theorem interp_bool (Δ : TyEnv rT GF) : interp Ty.bool Δ = lrel_bool := rfl
@[simp] theorem interp_real (Δ : TyEnv rT GF) : interp Ty.real Δ = lrel_real := rfl
@[simp] theorem interp_tape (Δ : TyEnv rT GF) : interp Ty.tape Δ = lrel_tape := rfl

theorem interp_prod (Δ : TyEnv rT GF) (τ1 τ2 : Ty) :
    interp (Ty.prod τ1 τ2) Δ = lrel_prod (interp τ1 Δ) (interp τ2 Δ) := rfl

theorem interp_sum (Δ : TyEnv rT GF) (τ1 τ2 : Ty) :
    interp (Ty.sum τ1 τ2) Δ = lrel_sum (interp τ1 Δ) (interp τ2 Δ) := rfl

theorem interp_arrow (Δ : TyEnv rT GF) (τ1 τ2 : Ty) :
    interp (Ty.arrow τ1 τ2) Δ = lrel_arr (interp τ1 Δ) (interp τ2 Δ) := rfl

theorem interp_ref (Δ : TyEnv rT GF) (τ : Ty) :
    interp (Ty.ref τ) Δ = lrel_ref (interp τ Δ) := rfl

end interp

/-! ## Closedness of related values -/

section interp_closed
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

theorem interp_closed {Δ : TyEnv rT GF} (τ : Ty) (v v' : Val rT) :
    (interp τ Δ).car v v' ⊢ ⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ :=
  (interp τ Δ).closed v v'

end interp_closed

/-! ## Unboxed-value predicate -/

@[simp] def Exp.isUnboxedV : Exp rT → Prop
  | .lit _ => True
  | .inl (.lit _) => True
  | .inr (.lit _) => True
  | _ => False

@[reducible] def Val.isUnboxed (v : Val rT) : Prop := v.1.isUnboxedV

/-! ## Soundness of the semantic type interpretation -/

section interp_sound
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

theorem unboxed_type_lit_shape {τ : Ty} {Δ : TyEnv rT GF} {v v' : Val rT} (H : UnboxedType τ) :
    (interp τ Δ).car v v' ⊢ ⌜∃ l l', v.1 = .lit l ∧ v'.1 = .lit l'⌝ := by
  cases H
  · show iprop(⌜_⌝) ⊢ _
    iintro ⟨%h1, %h2⟩ !%
    exact ⟨_, _, Val.ext_iff.mp h1, Val.ext_iff.mp h2⟩
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%n, %h1, %h2⟩ !%
    exact ⟨_, _, Val.ext_iff.mp h1, Val.ext_iff.mp h2⟩
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%b, %h1, %h2⟩ !%
    exact ⟨_, _, Val.ext_iff.mp h1, Val.ext_iff.mp h2⟩
  · show iprop(∃ _ _, _) ⊢ _
    iintro ⟨%l1, %l2, %h1, %h2, -⟩ !%
    exact ⟨_, _, Val.ext_iff.mp h1, Val.ext_iff.mp h2⟩

theorem unboxed_type_sound {τ : Ty} {Δ : TyEnv rT GF} {v v' : Val rT} (H : UnboxedType τ) :
    (interp τ Δ).car v v' ⊢ ⌜Val.isUnboxed v ∧ Val.isUnboxed v'⌝ := by
  refine (unboxed_type_lit_shape H).trans (pure_mono ?_)
  rintro ⟨_, _, h1, h2⟩
  exact ⟨by simp [Val.isUnboxed, h1], by simp [Val.isUnboxed, h2]⟩

theorem eq_type_sound {τ : Ty} {Δ : TyEnv rT GF} {v v' : Val rT} (H : EqType τ) :
    (interp τ Δ).car v v' ⊢ ⌜v = v'⌝ := by
  induction H generalizing v v'
  · show iprop(⌜_⌝) ⊢ _
    iintro ⟨%h1, %h2⟩ !%
    rw [h1, h2]
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%n, %h1, %h2⟩ !%
    rw [h1, h2]
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%b, %h1, %h2⟩ !%
    rw [h1, h2]
  · rename_i _ _ _ _ ih1 ih2
    unfold interp at ih1 ih2
    show iprop(∃ _ _ _ _, _) ⊢ _
    iintro ⟨%a1, %a2, %b1, %b2, %h1, %h2, HA, HB⟩
    ihave %heq1 := ih1 $$ HA
    ihave %heq2 := ih2 $$ HB
    ipureintro
    apply Val.ext
    rw [h1, h2, heq1, heq2]
  · rename_i _ _ _ _ ih1 ih2
    unfold interp at ih1 ih2
    show iprop(∃ _ _, _) ⊢ _
    iintro ⟨%w1, %w2, ⟨%h1, %h2, HA⟩ | ⟨%h1, %h2, HB⟩⟩
    · ihave %heq := ih1 $$ HA
      ipureintro
      apply Val.ext
      rw [h1, h2, heq]
    · ihave %heq := ih2 $$ HB
      ipureintro
      apply Val.ext
      rw [h1, h2, heq]

theorem eq_type_eq_iff {τ : Ty} {Δ : TyEnv rT GF} {v1 v2 w1 w2 : Val rT} (H : EqType τ) :
    (interp τ Δ).car v1 v2 ⊢ (interp τ Δ).car w1 w2 -∗ |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝ := by
  iintro H1 H2
  ihave %heq1 := eq_type_sound H $$ H1
  ihave %heq2 := eq_type_sound H $$ H2
  imodintro
  ipureintro
  subst heq1 heq2
  exact .rfl

private theorem lrel_ref_shape (A : lrel rT GF) (v1 v2 : Val rT) :
    (lrel_ref A).car v1 v2 ⊢ ⌜∃ l1 l2 : Loc, v1 = .loc l1 ∧ v2 = .loc l2⌝ := by
  unfold lrel_ref
  iintro ⟨%l1, %l2, %h1, %h2, -⟩ !%
  exact ⟨l1, l2, h1, h2⟩

theorem unboxed_type_eq {τ : Ty} {Δ : TyEnv rT GF} {v1 v2 w1 w2 : Val rT} (H : UnboxedType τ) :
    (interp τ Δ).car v1 v2 ⊢ (interp τ Δ).car w1 w2 -∗ |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝ := by
  cases H
  · exact eq_type_eq_iff .unit
  · exact eq_type_eq_iff .int
  · exact eq_type_eq_iff .bool
  · rename_i τ'
    rw [interp_ref]
    iintro H1 H2
    ihave %hs1 := lrel_ref_shape _ _ _ $$ H1
    ihave %hs2 := lrel_ref_shape _ _ _ $$ H2
    obtain ⟨l1, l2, rfl, rfl⟩ := hs1
    obtain ⟨r1, r2, rfl, rfl⟩ := hs2
    have hloc : ∀ a b : Loc, ((.loc a : Val rT) = .loc b) ↔ a = b := fun a b =>
      ⟨fun h => by injection Val.ext_iff.mp h with h; injection h, (· ▸ rfl)⟩
    simp only [hloc]
    by_cases hl : l1 = r1
    · subst hl
      imod interp_ref_funct (interp τ' Δ) l1 l2 r2 CoPset.subseteq_top $$ H1 H2 with %h
      imodintro
      ipureintro
      simp [h]
    · by_cases hr : l2 = r2
      · subst hr
        imod interp_ref_inj (interp τ' Δ) l2 l1 r1 CoPset.subseteq_top $$ H1 H2 with %h
        exact (hl h).elim
      · imodintro
        ipureintro
        exact iff_of_false hl hr

end interp_sound

/-! ## Relational environment typing -/

abbrev RelCtx (rT : Type _) (GF : BundledGFunctors) := List (Var × lrel rT GF)

namespace RelCtx
variable {rT : Type _} [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors}

def lookup : RelCtx rT GF → Var → Option (lrel rT GF)
  | [], _ => none
  | (y, A) :: rest, x =>
    match lookup rest x with
    | some B => some B
    | none => if x = y then some A else none

omit [LawfulProbLangℝ rT] in
theorem lookup_isSome_of_mem {Γ : RelCtx rT GF} {p : Var × lrel rT GF}
    (h : p ∈ Γ) : (Γ.lookup p.1).isSome := by
  induction Γ with
  | nil => cases h
  | cons q rest ih =>
    simp only [RelCtx.lookup]
    rcases List.mem_cons.mp h with rfl | hRest
    · cases RelCtx.lookup rest p.1 <;> simp
    · have := ih hRest
      cases hr : RelCtx.lookup rest p.1 <;> simp_all

omit [LawfulProbLangℝ rT] in
theorem mem_of_lookup_isSome {Γ : RelCtx rT GF} {y : Var}
    (h : (Γ.lookup y).isSome) : y ∈ (Γ.map (·.1)).toFinset := by
  induction Γ with
  | nil => simp [RelCtx.lookup] at h
  | cons q rest ih =>
    obtain ⟨k, B⟩ := q
    simp only [RelCtx.lookup] at h
    cases hr : RelCtx.lookup rest y with
    | some _ => simp [ih (by rw [hr]; rfl)]
    | none => rw [hr] at h; split_ifs at h <;> simp_all

omit [LawfulProbLangℝ rT] in
theorem lookup_cons (y : Var) (A : lrel rT GF) (Γ : RelCtx rT GF) (z : Var) :
    RelCtx.lookup ((y, A) :: Γ) z = match Γ.lookup z with
      | some B => some B
      | none => if z = y then some A else none := rfl

omit [LawfulProbLangℝ rT] in
theorem lookup_eq_none_of_not_mem {Γ : RelCtx rT GF} {y : Var}
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset) : Γ.lookup y = none := by
  cases hΓ : Γ.lookup y with
  | none => rfl
  | some _ => exact absurd (RelCtx.mem_of_lookup_isSome (by rw [hΓ]; rfl)) hyNotDom

end RelCtx

section env_typed
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

noncomputable def env_ltyped2 (Γ : RelCtx rT GF) (vs : ValSubstMap rT) : IProp GF := iprop%
  ⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝ ∗
  ⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝ ∗
  (∀ x A v1 v2, ⌜Γ.lookup x = some A⌝ -∗ ⌜vs.lookup x = some (v1, v2)⌝ -∗ A v1 v2)

instance env_ltyped2_persistent (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    Persistent (env_ltyped2 Γ vs) := by
  unfold env_ltyped2
  infer_instance

omit [LawfulProbLangℝ rT] in
theorem env_ltyped2_domEq (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝ := by
  unfold env_ltyped2
  iintro ⟨%H, -, -⟩ !%
  exact H

omit [LawfulProbLangℝ rT] in
theorem env_ltyped2_allClosed (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝ := by
  unfold env_ltyped2
  iintro ⟨-, %Hc, -⟩ !%
  exact Hc

theorem env_ltyped2_fst_allClosed (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜SubstMap.AllClosed vs.fst⌝ :=
  (env_ltyped2_allClosed Γ vs).trans <| pure_mono fun hc =>
    ValSubstMap.proj_allClosed Prod.fst fun p hp => (hc p hp).1

theorem env_ltyped2_snd_allClosed (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜SubstMap.AllClosed vs.snd⌝ :=
  (env_ltyped2_allClosed Γ vs).trans <| pure_mono fun hc =>
    ValSubstMap.proj_allClosed Prod.snd fun p hp => (hc p hp).2

omit [LawfulProbLangℝ rT] in
theorem env_ltyped2_domSubset (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜(Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset⌝ := by
  iintro Hvs
  ihave %hDom := env_ltyped2_domEq Γ vs $$ Hvs
  ipureintro
  intro y hy
  simp only [List.mem_toFinset, List.mem_map] at hy
  obtain ⟨p, hpmem, rfl⟩ := hy
  obtain ⟨q, hqmem, hqeq⟩ :=
    ValSubstMap.mem_of_lookup_isSome ((hDom p.1).mp (RelCtx.lookup_isSome_of_mem hpmem))
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨q, hqmem, hqeq⟩

omit [LawfulProbLangℝ rT] in
theorem env_ltyped2_lookup (Γ : RelCtx rT GF) (vs : ValSubstMap rT) (x : Var) (A : lrel rT GF)
    (hΓ : Γ.lookup x = some A) :
    env_ltyped2 Γ vs ⊢ ∃ v1 v2, ⌜vs.lookup x = some (v1, v2)⌝ ∗ A v1 v2 := by
  unfold env_ltyped2
  iintro ⟨%Hdom, -, Hall⟩
  obtain ⟨⟨v1, v2⟩, hvs_eq⟩ := Option.isSome_iff_exists.mp ((Hdom x).mp (by rw [hΓ]; rfl))
  iexists v1, v2
  iframe %hvs_eq
  iapply Hall $$ %x %A %v1 %v2 %hΓ %hvs_eq

omit [LawfulProbLangℝ rT] in
theorem env_ltyped2_empty : ⊢ env_ltyped2 ([] : RelCtx rT GF) [] := by
  unfold env_ltyped2
  isplitr
  · ipureintro; simp [RelCtx.lookup, ValSubstMap.lookup]
  isplitr
  · ipureintro; simp
  iintro %x %A %v1 %v2 %hΓ
  simp [RelCtx.lookup] at hΓ

omit [LawfulProbLangℝ rT] in
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

omit [LawfulProbLangℝ rT] in
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

omit [LawfulProbLangℝ rT] in
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
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

noncomputable def bin_log_related (E : CoPset) (Γ : RelCtx rT GF) (e e' : Exp rT)
    (A : lrel rT GF) : IProp GF := iprop%
  ∀ vs, env_ltyped2 Γ vs -∗ refines E (Exp.substMap vs.fst e) (Exp.substMap vs.snd e') A

noncomputable abbrev bin_log_related_ty (E : CoPset) (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) (e e' : Exp rT) (τ : Ty) : IProp GF :=
  bin_log_related E Γ e e' (interp τ Δ)

theorem bin_log_related_rename {E : CoPset} {Γ : RelCtx rT GF} {x y : Var} {A : lrel rT GF}
    {τE τE' : Exp rT} {B : lrel rT GF} (hxy : x ≠ y) (hxNotDom : x ∉ (Γ.map (·.1)).toFinset)
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset) (hyFvE : y ∉ τE.fv) (hyFvE' : y ∉ τE'.fv) :
    bin_log_related E ((x, A) :: Γ) τE τE' B ⊢
    bin_log_related E ((y, A) :: Γ) (τE.subst x (.fvar y)) (τE'.subst x (.fvar y)) B := by
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
  have hswapFst :=
    Exp.substMap_subst_fvar_lookup vs.fst τE x y w1.1 hxy (by rwa [ValSubstMap.fst_dom])
      (ValSubstMap.proj_allClosed Prod.fst fun p hp => (hvsClosed p hp).1)
      (by rw [ValSubstMap.fst_lookup, hvsLookupY]; rfl) hyFvE
  have hswapSnd :=
    Exp.substMap_subst_fvar_lookup vs.snd τE' x y w2.1 hxy (by rwa [ValSubstMap.snd_dom])
      (ValSubstMap.proj_allClosed Prod.snd fun p hp => (hvsClosed p hp).2)
      (by rw [ValSubstMap.snd_lookup, hvsLookupY]; rfl) hyFvE'
  rw [← ValSubstMap.fst_delete] at hswapFst
  rw [← ValSubstMap.snd_delete] at hswapSnd
  rw [show Exp.substMap vs.fst (τE.subst x (.fvar y)) = Exp.substMap vs'.fst τE from hswapFst,
    show Exp.substMap vs.snd (τE'.subst x (.fvar y)) = Exp.substMap vs'.snd τE' from hswapSnd]
  iexact Hrefines

theorem bin_log_related_ty_rename {E : CoPset} {Δ : TyEnv rT GF} {Γ : RelCtx rT GF} {x y : Var}
    {A : lrel rT GF} {τE τE' : Exp rT} {τ : Ty} (hxy : x ≠ y)
    (hxNotDom : x ∉ (Γ.map (·.1)).toFinset) (hyNotDom : y ∉ (Γ.map (·.1)).toFinset)
    (hyFvE : y ∉ τE.fv) (hyFvE' : y ∉ τE'.fv) :
    bin_log_related_ty E Δ ((x, A) :: Γ) τE τE' τ ⊢
    bin_log_related_ty E Δ ((y, A) :: Γ) (τE.subst x (.fvar y)) (τE'.subst x (.fvar y)) τ :=
  bin_log_related_rename hxy hxNotDom hyNotDom hyFvE hyFvE'

end bin_log_related

/-! ## Notation for the semantic typing judgement -/

scoped notation:100 E "; " Δ "; " Γ " ⊨ " e " ≤log≤ " e' " : " τ =>
  bin_log_related_ty E Δ Γ e e' τ

scoped notation:100 Δ "; " Γ " ⊨ " e " ≤log≤ " e' " : " τ =>
  bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ

/-! ## Substitution lemmas on `interp` -/

section interp_subst
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

@[reducible] def TyEnv.comp (Δ : TyEnv rT GF) (ξ : Nat → Nat) : TyEnv rT GF :=
  fun n => Δ (ξ n)

omit [LawfulProbLangℝ rT] in
theorem TyEnv.comp_upren (X : lrel rT GF) (Δ : TyEnv rT GF) (ξ : Nat → Nat) :
    TyEnv.cons X (TyEnv.comp Δ ξ) = TyEnv.comp (TyEnv.cons X Δ) (Renaming.under ξ) := by
  funext n; cases n <;> rfl

private theorem interp_rename_under {τ' : Ty} {ξ : Nat → Nat} {Δ : TyEnv rT GF}
    (ih : ∀ (ξ : Nat → Nat) (Δ : TyEnv rT GF), interp (τ'.rename ξ) Δ = interp τ' (TyEnv.comp Δ ξ))
    (X : lrel rT GF) :
    interp (τ'.rename (Renaming.under ξ)) (TyEnv.cons X Δ) =
      interp τ' (TyEnv.cons X (TyEnv.comp Δ ξ)) :=
  (ih _ _).trans (congrArg (interp τ') (TyEnv.comp_upren X Δ ξ).symm)

theorem interp_rename (τ : Ty) (ξ : Nat → Nat) (Δ : TyEnv rT GF) :
    interp (τ.rename ξ) Δ = interp τ (TyEnv.comp Δ ξ) := by
  induction τ generalizing ξ Δ with
  | prod τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_prod (ih1 ξ Δ) (ih2 ξ Δ)
  | sum τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_sum (ih1 ξ Δ) (ih2 ξ Δ)
  | arrow τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_arr (ih1 ξ Δ) (ih2 ξ Δ)
  | ref τ ih => exact congrArg lrel_ref (ih ξ Δ)
  | rec' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_rec_ne fun X => (interp_rename_under ih X).dist
  | forall' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_forall_ne fun X => (interp_rename_under ih X).dist
  | exists' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_exists_ne fun X => (interp_rename_under ih X).dist
  | _ => rfl

theorem interp_ren (τ : Ty) (X : lrel rT GF) (Δ : TyEnv rT GF) :
    interp (Ty.shift τ) (TyEnv.cons X Δ) = interp τ Δ :=
  interp_rename τ (· + 1) (TyEnv.cons X Δ)

@[reducible] noncomputable def semSubst (σ : Nat → Ty) (Δ : TyEnv rT GF) : TyEnv rT GF :=
  fun n => interp (σ n) Δ

theorem semSubst_up (σ : Nat → Ty) (X : lrel rT GF) (Δ : TyEnv rT GF) :
    ∀ n, semSubst (up σ) (TyEnv.cons X Δ) n = TyEnv.cons X (semSubst σ Δ) n
  | 0 => rfl
  | k + 1 => interp_ren (σ k) X Δ

private theorem interp_substG_under {τ' : Ty} {σ : Nat → Ty} {Δ : TyEnv rT GF}
    (ih : ∀ (σ : Nat → Ty) (Δ : TyEnv rT GF), interp (τ'.subst σ) Δ = interp τ' (semSubst σ Δ))
    (X : lrel rT GF) :
    interp (τ'.subst (up σ)) (TyEnv.cons X Δ) = interp τ' (TyEnv.cons X (semSubst σ Δ)) :=
  (ih _ _).trans <| OFE.eq_dist.mpr fun _ => interp_ne_env τ' fun k => (semSubst_up σ X Δ k).dist

theorem interp_substG (τ : Ty) (σ : Nat → Ty) (Δ : TyEnv rT GF) :
    interp (τ.subst σ) Δ = interp τ (semSubst σ Δ) := by
  induction τ generalizing σ Δ with
  | prod τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_prod (ih1 σ Δ) (ih2 σ Δ)
  | sum τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_sum (ih1 σ Δ) (ih2 σ Δ)
  | arrow τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_arr (ih1 σ Δ) (ih2 σ Δ)
  | ref τ ih => exact congrArg lrel_ref (ih σ Δ)
  | rec' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_rec_ne fun X => (interp_substG_under ih X).dist
  | forall' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_forall_ne fun X => (interp_substG_under ih X).dist
  | exists' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_exists_ne fun X => (interp_substG_under ih X).dist
  | _ => rfl

theorem interp_subst (τ' τ : Ty) (Δ : TyEnv rT GF) :
    interp (Ty.single τ τ') Δ = interp τ (TyEnv.cons (interp τ' Δ) Δ) := by
  unfold Ty.single
  refine (interp_substG τ _ Δ).trans (congrArg (interp τ) ?_)
  funext n; cases n <;> rfl

end interp_subst

end ProbLang
