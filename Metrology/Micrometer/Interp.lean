module

public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Micrometer.Model
public import Metrology.ProbLang.Metatheory
public import Metrology.ProbLang.ValSubstMap
public import Metrology.ProbLang.Syntax.Types

@[expose] public section

/-! Semantic interpretation of types and the semantic typing judgement. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

variable {rT : Type}

section TyEnvSetup
variable {GF : BundledGFunctors}

/-- A semantic type environment assigns a logical relation to each type variable. -/
abbrev TyEnv (rT : Type) (GF : BundledGFunctors) := Nat → lrel rT GF

/-- Extend a type environment with a new innermost variable. -/
def TyEnv.cons (X : lrel rT GF) (Δ : TyEnv rT GF) : TyEnv rT GF
  | 0 => X
  | n + 1 => Δ n

theorem TyEnv.cons_ne_head {n : Nat} {X Y : lrel rT GF} {Δ : TyEnv rT GF} (h : X ≡{n}≡ Y) :
    TyEnv.cons X Δ ≡{n}≡ TyEnv.cons Y Δ
  | 0 => h
  | _ + 1 => Dist.rfl

theorem TyEnv.cons_ne_tail {n : Nat} {X : lrel rT GF} {Δ Δ' : TyEnv rT GF} (h : Δ ≡{n}≡ Δ') :
    TyEnv.cons X Δ ≡{n}≡ TyEnv.cons X Δ'
  | 0 => Dist.rfl
  | m + 1 => h m

/-- The relation bound to type variable `x`. -/
@[reducible] def ctxLookup (x : Nat) (Δ : TyEnv rT GF) : lrel rT GF := Δ x

/-- Precompose a type environment with a renaming. -/
@[reducible] def TyEnv.comp (Δ : TyEnv rT GF) (ξ : Nat → Nat) : TyEnv rT GF :=
  fun n => Δ (ξ n)

theorem TyEnv.comp_upren (X : lrel rT GF) (Δ : TyEnv rT GF) (ξ : Nat → Nat) :
    TyEnv.cons X (TyEnv.comp Δ ξ) = TyEnv.comp (TyEnv.cons X Δ) (Renaming.under ξ) := by
  funext n; cases n <;> rfl

end TyEnvSetup

section interp
variable [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

/-- A non-expansive map from type environments to logical relations. -/
structure NEFun (rT : Type) [LawfulProbLangℝ rT] (GF : BundledGFunctors) where
  fn : TyEnv rT GF → lrel rT GF
  ne : ∀ {n : Nat} {Δ Δ' : TyEnv rT GF}, Δ ≡{n}≡ Δ' → fn Δ ≡{n}≡ fn Δ'

namespace NEFun

/-- The constant map to `L`. -/
@[reducible] noncomputable def const (L : lrel rT GF) : NEFun rT GF :=
  { fn := fun _ => L, ne := fun _ => Dist.rfl }

/-- The map looking up type variable `x`. -/
@[reducible] def ofCtx (x : Nat) : NEFun rT GF :=
  { fn := fun Δ => ctxLookup x Δ, ne := fun h => h x }

/-- Apply a binary relation constructor pointwise. -/
@[reducible] noncomputable def map2 (F : lrel rT GF → lrel rT GF → lrel rT GF)
    [OFE.NonExpansive₂ F] (A B : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => F (A.fn Δ) (B.fn Δ)
    ne := fun h => OFE.NonExpansive₂.ne (A.ne h) (B.ne h) }

/-- Apply a unary relation constructor pointwise. -/
@[reducible] noncomputable def map1 (F : lrel rT GF → lrel rT GF)
    [OFE.NonExpansive F] (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => F (A.fn Δ)
    ne := fun h => OFE.NonExpansive.ne (A.ne h) }

/-- The recursive relation binding the innermost type variable. -/
@[reducible] noncomputable def rec' (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => lrel_rec
      { f := fun X => A.fn (TyEnv.cons X Δ)
        ne := ⟨fun {_ _ _} hXY => A.ne (TyEnv.cons_ne_head hXY)⟩ }
    ne := fun h => lrel_rec_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

variable (L) in
/-- The universal relation binding the innermost type variable. -/
@[reducible] noncomputable def forall' (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => lrel_forall L (fun X => A.fn (TyEnv.cons X Δ))
    ne := fun h => lrel_forall_ne L (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

/-- The existential relation binding the innermost type variable. -/
@[reducible] noncomputable def exists' (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => lrel_exists (fun X => A.fn (TyEnv.cons X Δ))
    ne := fun h => lrel_exists_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

end NEFun

variable (L) in
/-- Interpret a type as a non-expansive function of the type environment. -/
noncomputable def interpNE : Ty → NEFun rT GF
  | .unit         => NEFun.const lrel_unit
  | .int          => NEFun.const lrel_int
  | .bool         => NEFun.const lrel_bool
  | .real         => NEFun.const lrel_real
  | .tape         => NEFun.const lrel_tape
  | .var x        => NEFun.ofCtx x
  | .prod τ1 τ2   => NEFun.map2 lrel_prod (interpNE τ1) (interpNE τ2)
  | .sum  τ1 τ2   => NEFun.map2 lrel_sum  (interpNE τ1) (interpNE τ2)
  | .arrow τ1 τ2  => NEFun.map2 (lrel_arr L) (interpNE τ1) (interpNE τ2)
  | .ref τ        => NEFun.map1 lrel_ref (interpNE τ)
  | .rec' τ'      => NEFun.rec'    (interpNE τ')
  | .forall' τ'   => NEFun.forall' L (interpNE τ')
  | .exists' τ'   => NEFun.exists' (interpNE τ')

variable (L) in
/-- The logical relation interpreting type `τ` in the type environment `Δ`. -/
noncomputable def interp (τ : Ty) (Δ : TyEnv rT GF) : lrel rT GF :=
  (interpNE L τ).fn Δ

theorem interp_ne_env (τ : Ty) {n : Nat} {Δ Δ' : TyEnv rT GF} (h : Δ ≡{n}≡ Δ') :
    interp L τ Δ ≡{n}≡ interp L τ Δ' := (interpNE L τ).ne h

/-! ### `interp` head-shape equations -/

@[simp] theorem interp_unit (Δ : TyEnv rT GF) : interp L Ty.unit Δ = lrel_unit := rfl
@[simp] theorem interp_int  (Δ : TyEnv rT GF) : interp L Ty.int  Δ = lrel_int  := rfl
@[simp] theorem interp_bool (Δ : TyEnv rT GF) : interp L Ty.bool Δ = lrel_bool := rfl
@[simp] theorem interp_real (Δ : TyEnv rT GF) : interp L Ty.real Δ = lrel_real := rfl
@[simp] theorem interp_tape (Δ : TyEnv rT GF) : interp L Ty.tape Δ = lrel_tape := rfl

theorem interp_prod (Δ : TyEnv rT GF) (τ1 τ2 : Ty) :
    interp L (Ty.prod τ1 τ2) Δ = lrel_prod (interp L τ1 Δ) (interp L τ2 Δ) := rfl

theorem interp_sum (Δ : TyEnv rT GF) (τ1 τ2 : Ty) :
    interp L (Ty.sum τ1 τ2) Δ = lrel_sum (interp L τ1 Δ) (interp L τ2 Δ) := rfl

theorem interp_arrow (Δ : TyEnv rT GF) (τ1 τ2 : Ty) :
    interp L (Ty.arrow τ1 τ2) Δ = lrel_arr L (interp L τ1 Δ) (interp L τ2 Δ) := rfl

theorem interp_ref (Δ : TyEnv rT GF) (τ : Ty) :
    interp L (Ty.ref τ) Δ = lrel_ref (interp L τ Δ) := rfl

end interp

/-! ## Closedness of related values -/

section interp_closed
variable [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

theorem interp_closed {Δ : TyEnv rT GF} (τ : Ty) (v v' : Val rT) :
    (interp L τ Δ).car v v' ⊢ ⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ :=
  (interp L τ Δ).closed v v'

end interp_closed

/-! ## Unboxed-value predicate -/

/-- Unboxed expressions are literals, possibly under a sum injection. -/
@[simp] def Exp.isUnboxedV : Exp rT → Prop
  | .lit _ => True
  | .inl (.lit _) => True
  | .inr (.lit _) => True
  | _ => False

/-- A value is unboxed when its underlying expression is. -/
@[reducible] def Val.isUnboxed (v : Val rT) : Prop := v.1.isUnboxedV

/-! ## Soundness of the semantic type interpretation -/

section interp_sound
variable [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

theorem unboxed_type_lit_shape {τ : Ty} {Δ : TyEnv rT GF} {v v' : Val rT} (H : UnboxedType τ) :
    (interp L τ Δ).car v v' ⊢ ⌜∃ l l', v.1 = .lit l ∧ v'.1 = .lit l'⌝ := by
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
    (interp L τ Δ).car v v' ⊢ ⌜Val.isUnboxed v ∧ Val.isUnboxed v'⌝ := by
  refine (unboxed_type_lit_shape H).trans (pure_mono ?_)
  rintro ⟨_, _, h1, h2⟩
  exact ⟨by simp [Val.isUnboxed, h1], by simp [Val.isUnboxed, h2]⟩

theorem eq_type_sound {τ : Ty} {Δ : TyEnv rT GF} {v v' : Val rT} (H : EqType τ) :
    (interp L τ Δ).car v v' ⊢ ⌜v = v'⌝ := by
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
    (interp L τ Δ).car v1 v2 ⊢ (interp L τ Δ).car w1 w2 -∗ |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝ := by
  iintro H1 H2
  ihave %heq1 := eq_type_sound H $$ H1
  ihave %heq2 := eq_type_sound H $$ H2
  imodintro
  ipureintro
  subst heq1 heq2
  exact .rfl

/-- Related values of a reference relation are both locations. -/
theorem lrel_ref_shape (A : lrel rT GF) (v1 v2 : Val rT) :
    (lrel_ref A).car v1 v2 ⊢ ⌜∃ l1 l2 : Loc, v1 = .loc l1 ∧ v2 = .loc l2⌝ := by
  unfold lrel_ref
  iintro ⟨%l1, %l2, %h1, %h2, -⟩ !%
  exact ⟨l1, l2, h1, h2⟩

theorem unboxed_type_eq {τ : Ty} {Δ : TyEnv rT GF} {v1 v2 w1 w2 : Val rT} (H : UnboxedType τ) :
    (interp L τ Δ).car v1 v2 ⊢ (interp L τ Δ).car w1 w2 -∗ |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝ := by
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
    simp only [Val.ext_iff, Exp.lit.injEq, BaseLit.loc.injEq]
    by_cases hl : l1 = r1
    · subst hl
      imod interp_ref_funct (interp L τ' Δ) l1 l2 r2 CoPset.subseteq_top $$ H1 H2 with %h
      imodintro
      ipureintro
      simp [h]
    · by_cases hr : l2 = r2
      · subst hr
        imod interp_ref_inj (interp L τ' Δ) l2 l1 r1 CoPset.subseteq_top $$ H1 H2 with %h
        exact (hl h).elim
      · imodintro
        ipureintro
        exact iff_of_false hl hr

end interp_sound

/-! ## Relational environment typing -/

/-- A relational typing context assigns a logical relation to each variable. -/
abbrev RelCtx (rT : Type) (GF : BundledGFunctors) := List (Var × lrel rT GF)

namespace RelCtx

/-- The relation of the last entry for `x` in the list. -/
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

/-- `vs` maps the variables of `Γ` to pairs of closed values related at their relations. -/
noncomputable def env_ltyped2 (Γ : RelCtx rT GF) (vs : ValSubstMap rT) : IProp GF := iprop%
  ⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝ ∗
  ⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝ ∗
  (∀ x A v1 v2, ⌜Γ.lookup x = some A⌝ -∗ ⌜vs.lookup x = some (v1, v2)⌝ -∗ A v1 v2)

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
    bin_log_related_ty L E Δ ((x, A) :: Γ) τE τE' τ ⊢
    bin_log_related_ty L E Δ ((y, A) :: Γ) (τE.subst x (.fvar y)) (τE'.subst x (.fvar y)) τ :=
  bin_log_related_rename hxy hxNotDom hyNotDom hyFvE hyFvE'

end bin_log_related

/-! ## Notation for the semantic typing judgement -/

scoped notation:100 E "; " Δ "; " Γ " ⊨[" L "] " e " ≤log≤ " e' " : " τ =>
  bin_log_related_ty L E Δ Γ e e' τ

scoped notation:100 Δ "; " Γ " ⊨[" L "] " e " ≤log≤ " e' " : " τ =>
  bin_log_related_ty L (⊤ : CoPset) Δ Γ e e' τ

/-! ## Substitution lemmas on `interp` -/

section interp_subst
variable [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

/-- The renaming hypothesis for a type body extends under a new relation binder. -/
theorem interp_rename_under {τ' : Ty} {ξ : Nat → Nat} {Δ : TyEnv rT GF}
    (ih : ∀ (ξ : Nat → Nat) (Δ : TyEnv rT GF),
      interp L (τ'.rename ξ) Δ = interp L τ' (TyEnv.comp Δ ξ))
    (X : lrel rT GF) :
    interp L (τ'.rename (Renaming.under ξ)) (TyEnv.cons X Δ) =
      interp L τ' (TyEnv.cons X (TyEnv.comp Δ ξ)) :=
  (ih _ _).trans (congrArg (interp L τ') (TyEnv.comp_upren X Δ ξ).symm)

theorem interp_rename (τ : Ty) (ξ : Nat → Nat) (Δ : TyEnv rT GF) :
    interp L (τ.rename ξ) Δ = interp L τ (TyEnv.comp Δ ξ) := by
  induction τ generalizing ξ Δ with
  | prod τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_prod (ih1 ξ Δ) (ih2 ξ Δ)
  | sum τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_sum (ih1 ξ Δ) (ih2 ξ Δ)
  | arrow τ1 τ2 ih1 ih2 => exact congrArg₂ (lrel_arr L) (ih1 ξ Δ) (ih2 ξ Δ)
  | ref τ ih => exact congrArg lrel_ref (ih ξ Δ)
  | rec' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_rec_ne fun X => (interp_rename_under ih X).dist
  | forall' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_forall_ne L fun X => (interp_rename_under ih X).dist
  | exists' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_exists_ne fun X => (interp_rename_under ih X).dist
  | _ => rfl

theorem interp_ren (τ : Ty) (X : lrel rT GF) (Δ : TyEnv rT GF) :
    interp L (Ty.shift τ) (TyEnv.cons X Δ) = interp L τ Δ :=
  interp_rename τ (· + 1) (TyEnv.cons X Δ)

variable (L) in
/-- Interpret each type of a substitution in the type environment `Δ`. -/
@[reducible] noncomputable def semSubst (σ : Nat → Ty) (Δ : TyEnv rT GF) : TyEnv rT GF :=
  fun n => interp L (σ n) Δ

theorem semSubst_up (σ : Nat → Ty) (X : lrel rT GF) (Δ : TyEnv rT GF) :
    ∀ n, semSubst L (up σ) (TyEnv.cons X Δ) n = TyEnv.cons X (semSubst L σ Δ) n
  | 0 => rfl
  | k + 1 => interp_ren (σ k) X Δ

/-- The substitution hypothesis for a type body extends under a new relation binder. -/
theorem interp_substG_under {τ' : Ty} {σ : Nat → Ty} {Δ : TyEnv rT GF}
    (ih : ∀ (σ : Nat → Ty) (Δ : TyEnv rT GF),
      interp L (τ'.subst σ) Δ = interp L τ' (semSubst L σ Δ))
    (X : lrel rT GF) :
    interp L (τ'.subst (up σ)) (TyEnv.cons X Δ) = interp L τ' (TyEnv.cons X (semSubst L σ Δ)) :=
  (ih _ _).trans <| OFE.eq_dist.mpr fun _ => interp_ne_env τ' fun k => (semSubst_up σ X Δ k).dist

theorem interp_substG (τ : Ty) (σ : Nat → Ty) (Δ : TyEnv rT GF) :
    interp L (τ.subst σ) Δ = interp L τ (semSubst L σ Δ) := by
  induction τ generalizing σ Δ with
  | prod τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_prod (ih1 σ Δ) (ih2 σ Δ)
  | sum τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_sum (ih1 σ Δ) (ih2 σ Δ)
  | arrow τ1 τ2 ih1 ih2 => exact congrArg₂ (lrel_arr L) (ih1 σ Δ) (ih2 σ Δ)
  | ref τ ih => exact congrArg lrel_ref (ih σ Δ)
  | rec' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_rec_ne fun X => (interp_substG_under ih X).dist
  | forall' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_forall_ne L fun X => (interp_substG_under ih X).dist
  | exists' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_exists_ne fun X => (interp_substG_under ih X).dist
  | _ => rfl

theorem interp_subst (τ' τ : Ty) (Δ : TyEnv rT GF) :
    interp L (Ty.single τ τ') Δ = interp L τ (TyEnv.cons (interp L τ' Δ) Δ) := by
  unfold Ty.single
  refine (interp_substG τ _ Δ).trans (congrArg (interp L τ) ?_)
  funext n; cases n <;> rfl

end interp_subst

end ProbLang
