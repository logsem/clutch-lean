module

public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Micrometer.Model
public import Metrology.ProbLang.Metatheory
public import Metrology.ProbLang.ValSubstMap
public import Metrology.ProbLang.Syntax.Types

/-! Semantic interpretation of types: `interp`, closedness, soundness and substitution. -/

@[expose] public section

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

/-! ## Unboxed-value predicate -/

/-- Unboxed expressions are literals, possibly under a sum injection. -/
@[simp] def Exp.isUnboxedV : Exp rT → Prop
  | .lit _ => True
  | .inl (.lit _) => True
  | .inr (.lit _) => True
  | _ => False

/-- A value is unboxed when its underlying expression is. -/
@[reducible] def Val.isUnboxed (v : Val rT) : Prop := v.1.isUnboxedV

section interp
variable [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]
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


/-! ## Closedness of related values -/


theorem interp_closed {Δ : TyEnv rT GF} (τ : Ty) (v v' : Val rT) :
    (interp L τ Δ).car v v' ⊢ ⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ :=
  (interp L τ Δ).closed v v'


/-! ## Soundness of the semantic type interpretation -/


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
      imod lrel_ref_funct (interp L τ' Δ) l1 l2 r2 CoPset.subseteq_top $$ H1 H2 with %h
      imodintro
      ipureintro
      simp [h]
    · by_cases hr : l2 = r2
      · subst hr
        imod lrel_ref_inj (interp L τ' Δ) l2 l1 r1 CoPset.subseteq_top $$ H1 H2 with %h
        exact (hl h).elim
      · imodintro
        ipureintro
        exact iff_of_false hl hr


/-! ## Substitution lemmas on `interp` -/


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

end interp

end ProbLang
