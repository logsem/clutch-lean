module

public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Micrometer.Model
public import Metrology.ProbLang.Metatheory
public import Metrology.ProbLang.ValSubstMap
public import Metrology.ProbLang.Syntax.Types
import Metrology.Iris.LocalBI

/-! # Interpretation of types

`interp L τ Δ`: each type as a value relation (`lrel`) under a type environment `Δ`, with the
substitution lemma `interp_subst` and the facts the equality operator needs (`unboxed_type_eq`). -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang.MicrometerWpGS GradedLifting

namespace ProbLang

variable {rT : Type}

/-! ## Type environments -/

section TyEnvSetup
variable {GF : BundledGFunctors}

/-- A semantic type environment assigns a logical relation to each type variable. -/
abbrev TyEnv (rT : Type) (GF : BundledGFunctors) := Nat → lrel rT GF

variable {n : Nat} {X : lrel rT GF} {Δ Δ' : TyEnv rT GF}

namespace TyEnv

/-- Extend a type environment with a new innermost variable. -/
def cons (X : lrel rT GF) (Δ : TyEnv rT GF) : TyEnv rT GF
  | 0 => X
  | n + 1 => Δ n

/-- Extending with `n`-close relations gives `n`-close environments. -/
theorem cons_ne_head {Y : lrel rT GF} (h : X ≡{n}≡ Y) : cons X Δ ≡{n}≡ cons Y Δ
  | 0 => h
  | _ + 1 => .rfl

/-- Extending `n`-close environments with the same relation gives `n`-close environments. -/
theorem cons_ne_tail (h : Δ ≡{n}≡ Δ') : cons X Δ ≡{n}≡ cons X Δ'
  | 0 => .rfl
  | m + 1 => h m

/-- Precompose a type environment with a renaming. -/
@[reducible] def comp (Δ : TyEnv rT GF) (ξ : Nat → Nat) : TyEnv rT GF :=
  fun n => Δ (ξ n)

/-- Extending then renaming agrees with renaming under a binder, then extending. -/
theorem comp_upren (X : lrel rT GF) (Δ : TyEnv rT GF) (ξ : Nat → Nat) :
    cons X (comp Δ ξ) = comp (cons X Δ) (Renaming.under ξ) := by
  funext n; cases n <;> rfl

end TyEnv

end TyEnvSetup

-- The sum cases are unused here because `UnboxedType` has no sums; the equality proof uses
-- `unboxed_type_lit_shape` instead.
/-- Unboxed expressions are literals, possibly under a sum injection (Rocq's `val_is_unboxed`). -/
@[simp] def Exp.isUnboxedV : Exp rT → Prop
  | .lit _ => True
  | .inl (.lit _) => True
  | .inr (.lit _) => True
  | _ => False

/-- A value is unboxed when its underlying expression is. -/
@[reducible] def Val.isUnboxed (v : Val rT) : Prop := v.1.isUnboxedV

section interp
open TyEnv
open Val (ext ext_iff isUnboxed)
open CoPset (subseteq_top)
variable [MeasurableSpace rT] [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B]
    [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF] {n : Nat} {Δ Δ' : TyEnv rT GF}
local bi IProp GF

/-! ## Interpreting types -/

/-- A non-expansive map from type environments to logical relations. -/
structure NEFun (rT : Type) [MeasurableSpace rT] [LawfulProbLangℝ rT] (GF : BundledGFunctors) where
  /-- The underlying map. -/
  fn : TyEnv rT GF → lrel rT GF
  /-- The map is non-expansive. -/
  ne : ∀ {n : Nat} {Δ Δ' : TyEnv rT GF}, Δ ≡{n}≡ Δ' → fn Δ ≡{n}≡ fn Δ'

namespace NEFun

/-- The constant map to the relation `A`. -/
@[reducible] noncomputable def const (A : lrel rT GF) : NEFun rT GF :=
  { fn := fun _ => A, ne := fun _ => .rfl }

/-- The map looking up type variable `x`. -/
@[reducible] def ofCtx (x : Nat) : NEFun rT GF :=
  { fn := fun Δ => Δ x, ne := fun h => h x }

/-- Apply a binary relation constructor pointwise. -/
@[reducible] noncomputable def map2 (F : lrel rT GF → lrel rT GF → lrel rT GF)
    [NonExpansive₂ F] (A B : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => F (A.fn Δ) (B.fn Δ)
    ne := fun h => NonExpansive₂.ne (A.ne h) (B.ne h) }

/-- Apply a unary relation constructor pointwise. -/
@[reducible] noncomputable def map1 (F : lrel rT GF → lrel rT GF)
    [NonExpansive F] (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => F (A.fn Δ)
    ne := fun h => NonExpansive.ne (A.ne h) }

section
variable (A : NEFun rT GF)

/-- The recursive relation binding the innermost type variable. -/
@[reducible] noncomputable def rec' : NEFun rT GF :=
  { fn := fun Δ => lrel_rec
      { f := fun X => A.fn (cons X Δ)
        ne := ⟨fun {_ _ _} hXY => A.ne (cons_ne_head hXY)⟩ }
    ne := fun h => lrel_rec_ne (fun _ => A.ne (cons_ne_tail h)) }

variable (L) in
/-- The universal relation binding the innermost type variable. -/
@[reducible] noncomputable def forall' : NEFun rT GF :=
  { fn := fun Δ => lrel_forall L (fun X => A.fn (cons X Δ))
    ne := fun h => lrel_forall_ne L (fun _ => A.ne (cons_ne_tail h)) }

/-- The existential relation binding the innermost type variable. -/
@[reducible] noncomputable def exists' : NEFun rT GF :=
  { fn := fun Δ => lrel_exists (fun X => A.fn (cons X Δ))
    ne := fun h => lrel_exists_ne (fun _ => A.ne (cons_ne_tail h)) }

end

end NEFun

open NEFun

variable (L) in
/-- Interpret a type as a non-expansive function of the type environment. -/
noncomputable def interpNE : Ty → NEFun rT GF
  | .unit => const lrel_unit
  | .int => const lrel_int
  | .bool => const lrel_bool
  | .real => const lrel_real
  | .tape => const lrel_tape
  | .var x => ofCtx x
  | .prod τ1 τ2 => map2 lrel_prod (interpNE τ1) (interpNE τ2)
  | .sum τ1 τ2 => map2 lrel_sum (interpNE τ1) (interpNE τ2)
  | .arrow τ1 τ2 => map2 (lrel_arr L) (interpNE τ1) (interpNE τ2)
  | .ref τ => map1 lrel_ref (interpNE τ)
  | .rec' τ' => rec' (interpNE τ')
  | .forall' τ' => forall' L (interpNE τ')
  | .exists' τ' => exists' (interpNE τ')

variable (L) in
/-- The logical relation interpreting type `τ` in the type environment `Δ`. -/
noncomputable def interp (τ : Ty) (Δ : TyEnv rT GF) : lrel rT GF :=
  (interpNE L τ).fn Δ

/-- `interp` is non-expansive in the type environment. -/
theorem interp_ne_env (τ : Ty) (h : Δ ≡{n}≡ Δ') :
    interp L τ Δ ≡{n}≡ interp L τ Δ' := (interpNE L τ).ne h

/-! ### `interp` head-shape equations -/

section HeadShape
variable (Δ : TyEnv rT GF)

/-- The `unit` type is interpreted as `lrel_unit`. -/
@[simp] theorem interp_unit : interp L .unit Δ = lrel_unit := rfl
/-- The `int` type is interpreted as `lrel_int`. -/
@[simp] theorem interp_int : interp L .int Δ = lrel_int := rfl
/-- The `bool` type is interpreted as `lrel_bool`. -/
@[simp] theorem interp_bool : interp L .bool Δ = lrel_bool := rfl
/-- The `real` type is interpreted as `lrel_real`. -/
@[simp] theorem interp_real : interp L .real Δ = lrel_real := rfl
/-- The `tape` type is interpreted as `lrel_tape`. -/
@[simp] theorem interp_tape : interp L .tape Δ = lrel_tape := rfl

section
variable (τ1 τ2 : Ty)

/-- Products are interpreted as `lrel_prod`. -/
theorem interp_prod : interp L (.prod τ1 τ2) Δ = lrel_prod (interp L τ1 Δ) (interp L τ2 Δ) := rfl

/-- Sums are interpreted as `lrel_sum`. -/
theorem interp_sum : interp L (.sum τ1 τ2) Δ = lrel_sum (interp L τ1 Δ) (interp L τ2 Δ) := rfl

/-- Arrows are interpreted as `lrel_arr`. -/
theorem interp_arrow : interp L (.arrow τ1 τ2) Δ = lrel_arr L (interp L τ1 Δ) (interp L τ2 Δ) := rfl

end

section
variable (τ : Ty)

/-- References are interpreted as `lrel_ref`. -/
theorem interp_ref : interp L (.ref τ) Δ = lrel_ref (interp L τ Δ) := rfl

variable (v v' : Val rT)

/-- `⟦μX.τ⟧` unfolds once, with the recursive occurrence under `▷`. -/
theorem interp_rec_car :
    (interp L (.rec' τ) Δ).car v v' = iprop(⌜v.1.IsClosedEmpty ∧ v'.1.IsClosedEmpty⌝ ∗
      ▷ (interp L τ (cons (interp L (.rec' τ) Δ) Δ)).car v v') :=
  congrArg (fun A => A.car v v') (lrel_rec_unfold
    { f := fun X => interp L τ (cons X Δ)
      ne := ⟨fun {_ _ _} hXY => (interpNE L τ).ne (cons_ne_head hXY)⟩ })

/-- `⟦∃X.τ⟧` relates closed values related at some instance. -/
theorem interp_exists_car :
    (interp L (.exists' τ) Δ).car v v' = iprop(⌜v.1.IsClosedEmpty ∧ v'.1.IsClosedEmpty⌝ ∗
      ∃ A, (interp L τ (cons A Δ)).car v v') :=
  rfl

end

end HeadShape

/-- Related values are closed. -/
theorem interp_closed (τ : Ty) (v v' : Val rT) :
    (interp L τ Δ).car v v' ⊢ ⌜v.1.IsClosedEmpty ∧ v'.1.IsClosedEmpty⌝ :=
  (interp L τ Δ).closed v v'

/-! ## Substitution lemmas -/

variable {τ' : Ty}

/-- The renaming hypothesis for a type body extends under a new relation binder. -/
theorem interp_rename_under {ξ : Nat → Nat}
    (ih : ∀ (ξ : Nat → Nat) (Δ : TyEnv rT GF),
      interp L (τ'.rename ξ) Δ = interp L τ' (comp Δ ξ))
    (X : lrel rT GF) :
    interp L (τ'.rename (Renaming.under ξ)) (cons X Δ) = interp L τ' (cons X (comp Δ ξ)) :=
  (ih _ _).trans (congrArg (interp L τ') (comp_upren X Δ ξ).symm)

/-- Renaming a type's variables equals precomposing its environment with the renaming. -/
theorem interp_rename (τ : Ty) (ξ : Nat → Nat) (Δ : TyEnv rT GF) :
    interp L (τ.rename ξ) Δ = interp L τ (comp Δ ξ) := by
  induction τ generalizing ξ Δ with
  | prod τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_prod (ih1 ξ Δ) (ih2 ξ Δ)
  | sum τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_sum (ih1 ξ Δ) (ih2 ξ Δ)
  | arrow τ1 τ2 ih1 ih2 => exact congrArg₂ (lrel_arr L) (ih1 ξ Δ) (ih2 ξ Δ)
  | ref τ ih => exact congrArg lrel_ref (ih ξ Δ)
  -- Binder cases: the bodies agree for every X, so equality follows from being n-close at every n
  -- (eq_dist) via the constructor's _ne lemma.
  | rec' τ' ih =>
    exact eq_dist.mpr fun _ => lrel_rec_ne fun X => (interp_rename_under ih X).dist
  | forall' τ' ih =>
    exact eq_dist.mpr fun _ => lrel_forall_ne L fun X => (interp_rename_under ih X).dist
  | exists' τ' ih =>
    exact eq_dist.mpr fun _ => lrel_exists_ne fun X => (interp_rename_under ih X).dist
  | _ => rfl

/-- Shifting `τ` past a new type variable does not change its interpretation. -/
theorem interp_ren (τ : Ty) (X : lrel rT GF) (Δ : TyEnv rT GF) :
    interp L τ.shift (cons X Δ) = interp L τ Δ :=
  interp_rename τ (· + 1) (cons X Δ)

variable (L) in
/-- The type environment sending variable `n` to `⟦σ n⟧Δ`. -/
@[reducible] noncomputable def semSubst (σ : Nat → Ty) (Δ : TyEnv rT GF) : TyEnv rT GF :=
  fun n => interp L (σ n) Δ

/-- Extending a semantic substitution matches substituting under a binder. -/
theorem semSubst_up (σ : Nat → Ty) (X : lrel rT GF) (Δ : TyEnv rT GF) :
    ∀ n, semSubst L (up σ) (cons X Δ) n = cons X (semSubst L σ Δ) n
  | 0 => rfl
  | k + 1 => interp_ren (σ k) X Δ

/-- The substitution hypothesis for a type body extends under a new relation binder. -/
theorem interp_substG_under {σ : Nat → Ty}
    (ih : ∀ (σ : Nat → Ty) (Δ : TyEnv rT GF),
      interp L (τ'.subst σ) Δ = interp L τ' (semSubst L σ Δ))
    (X : lrel rT GF) :
    interp L (τ'.subst (up σ)) (cons X Δ) = interp L τ' (cons X (semSubst L σ Δ)) :=
  (ih _ _).trans <| eq_dist.mpr fun _ => interp_ne_env τ' fun k => (semSubst_up σ X Δ k).dist

/-- Substituting into a type equals interpreting the substitution into the environment. -/
theorem interp_substG (τ : Ty) (σ : Nat → Ty) (Δ : TyEnv rT GF) :
    interp L (τ.subst σ) Δ = interp L τ (semSubst L σ Δ) := by
  induction τ generalizing σ Δ with
  | prod τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_prod (ih1 σ Δ) (ih2 σ Δ)
  | sum τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_sum (ih1 σ Δ) (ih2 σ Δ)
  | arrow τ1 τ2 ih1 ih2 => exact congrArg₂ (lrel_arr L) (ih1 σ Δ) (ih2 σ Δ)
  | ref τ ih => exact congrArg lrel_ref (ih σ Δ)
  -- Binder cases: as in `interp_rename`.
  | rec' τ' ih =>
    exact eq_dist.mpr fun _ => lrel_rec_ne fun X => (interp_substG_under ih X).dist
  | forall' τ' ih =>
    exact eq_dist.mpr fun _ => lrel_forall_ne L fun X => (interp_substG_under ih X).dist
  | exists' τ' ih =>
    exact eq_dist.mpr fun _ => lrel_exists_ne fun X => (interp_substG_under ih X).dist
  | _ => rfl

/-- Substituting `τ'` for the innermost variable interprets it as `⟦τ'⟧Δ`. -/
theorem interp_subst (τ' τ : Ty) (Δ : TyEnv rT GF) :
    interp L (.single τ τ') Δ = interp L τ (cons (interp L τ' Δ) Δ) := by
  unfold Ty.single
  refine (interp_substG τ _ Δ).trans (congrArg (interp L τ) ?_)
  funext n; cases n <;> rfl

/-! ## Equality on `EqType` and `UnboxedType` -/

variable {τ : Ty} {v v' v1 v2 w1 w2 : Val rT}

/-- Related values at an unboxed type are both literals. -/
theorem unboxed_type_lit_shape (H : UnboxedType τ) :
    (interp L τ Δ).car v v' ⊢ ⌜∃ l l', v.1 = .lit l ∧ v'.1 = .lit l'⌝ := by
  cases H
  · -- unit
    show iprop(⌜_⌝) ⊢ _
    iintro ⟨%h1, %h2⟩ !%
    exact ⟨_, _, ext_iff.mp h1, ext_iff.mp h2⟩
  · -- int
    show iprop(∃ _, _) ⊢ _
    iintro ⟨%n, %h1, %h2⟩ !%
    exact ⟨_, _, ext_iff.mp h1, ext_iff.mp h2⟩
  · -- bool
    show iprop(∃ _, _) ⊢ _
    iintro ⟨%b, %h1, %h2⟩ !%
    exact ⟨_, _, ext_iff.mp h1, ext_iff.mp h2⟩
  · -- ref
    show iprop(∃ _ _, _) ⊢ _
    iintro ⟨%l1, %l2, %h1, %h2, -⟩ !%
    exact ⟨_, _, ext_iff.mp h1, ext_iff.mp h2⟩

/-- Related values at an unboxed type are both unboxed. -/
theorem unboxed_type_sound (H : UnboxedType τ) :
    (interp L τ Δ).car v v' ⊢ ⌜v.isUnboxed ∧ v'.isUnboxed⌝ := by
  refine (unboxed_type_lit_shape H).trans (pure_mono ?_)
  rintro ⟨_, _, h1, h2⟩
  exact ⟨by simp [isUnboxed, h1], by simp [isUnboxed, h2]⟩

/-- Related values at an `EqType` are equal. -/
theorem eq_type_sound (H : EqType τ) : (interp L τ Δ).car v v' ⊢ ⌜v = v'⌝ := by
  induction H generalizing v v'
  · -- unit
    show iprop(⌜_⌝) ⊢ _
    iintro ⟨%h1, %h2⟩ !%
    rw [h1, h2]
  · -- int
    show iprop(∃ _, _) ⊢ _
    iintro ⟨%n, %h1, %h2⟩ !%
    rw [h1, h2]
  · -- bool
    show iprop(∃ _, _) ⊢ _
    iintro ⟨%b, %h1, %h2⟩ !%
    rw [h1, h2]
  · -- prod
    rename_i _ _ _ _ ih1 ih2
    unfold interp at ih1 ih2
    show iprop(∃ _ _ _ _, _) ⊢ _
    iintro ⟨%a1, %a2, %b1, %b2, %h1, %h2, HA, HB⟩
    ihave %heq1 := ih1 $$ HA
    ihave %heq2 := ih2 $$ HB
    ipureintro
    apply ext
    rw [h1, h2, heq1, heq2]
  · -- sum
    rename_i _ _ _ _ ih1 ih2
    unfold interp at ih1 ih2
    show iprop(∃ _ _, _) ⊢ _
    iintro ⟨%w1, %w2, ⟨%h1, %h2, HA⟩ | ⟨%h1, %h2, HB⟩⟩
    · ihave %heq := ih1 $$ HA
      ipureintro
      apply ext
      rw [h1, h2, heq]
    · ihave %heq := ih2 $$ HB
      ipureintro
      apply ext
      rw [h1, h2, heq]

/-- On an `EqType`, two related pairs agree on equality, `v1 = w1 ↔ v2 = w2`. -/
theorem eq_type_eq_iff (H : EqType τ) :
    (interp L τ Δ).car v1 v2 ⊢ (interp L τ Δ).car w1 w2 -∗ |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝ := by
  iintro H1 H2
  ihave %heq1 := eq_type_sound H $$ H1
  ihave %heq2 := eq_type_sound H $$ H2
  imodintro
  ipureintro
  subst heq1 heq2
  exact .rfl

/-- On an unboxed type, two related pairs agree on equality, `v1 = w1 ↔ v2 = w2`; this makes `=`
compatible (`bin_log_related_unboxed_eq`). -/
theorem unboxed_type_eq (H : UnboxedType τ) :
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
    simp only [ext_iff, Exp.lit.injEq, BaseLit.loc.injEq]
    -- Locations: `lrel_ref` is functional (same left ⇒ same right) and injective.
    by_cases hl : l1 = r1
    · subst hl
      imod lrel_ref_funct (interp L τ' Δ) l1 l2 r2 subseteq_top $$ H1 H2 with %h
      imodintro
      ipureintro
      simp [h]
    · by_cases hr : l2 = r2
      · subst hr
        imod lrel_ref_inj (interp L τ' Δ) l2 l1 r1 subseteq_top $$ H1 H2 with %h
        exact (hl h).elim
      · imodintro
        ipureintro
        exact iff_of_false hl hr

end interp

end ProbLang
