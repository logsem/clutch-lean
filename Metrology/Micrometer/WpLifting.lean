module

public import Metrology.Micrometer.WpRules
import Metrology.Iris.LocalBI

/-! # Lifting lemmas for `wp`

Reduce `wp` to one coupled step (Rocq `approxis/lifting.v`); main: `wp_lift_prim_steps_coupl`. -/

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode GradedLifting

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]

section Wp
variable [BudgetGS B GF] {E E1 E2 : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
local bi IProp GF
open SpecUpdateGS BIFUpdate
open LawfulSet (empty_subset subset_refl)
open BindLaw

/-! ## Unfolding `wp` -/

/-- `wp_unfold` read right to left: the body of `wpPre` proves `wp`. -/
theorem wp_lift_step_couple : iprop%
    (∀ σ₁ e₁' σ₁' (b₁ : B), stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗
      budgetInterp b₁ -∗
      |={E, ∅}=> specCoupl L ∅ σ₁ e₁' σ₁' b₁ fun σ₂ ρ' b₂ =>
        match e₁.toVal? with
        | some v => iprop(|={∅, E}=> stateInterp σ₂ ∗ specInterp ρ' ∗
            budgetInterp b₂ ∗ Φ v)
        | none => progCoupl L e₁ σ₂ ρ'.expr ρ'.state b₂ fun e₃ σ₃ e₃' σ₃' b₃ => iprop%
            ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E}=>
              stateInterp σ₄ ∗ specInterp ρ'' ∗ budgetInterp b₄ ∗
                wp L E e₃ Φ)) ⊢ wp L E e₁ Φ := by
  rw [wp_unfold]
  exact .rfl

/-- Run a spec phase only, then re-enter `wp` at the same program expression. -/
theorem wp_lift_step_spec_couple [Add B] [L.IsLawful] [L.IsTopAbsorbing] : iprop%
    (∀ (σ₁ : State rT) e₁' σ₁' (b₁ : B), stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗
        budgetInterp b₁ -∗ |={E, ∅}=>
        specCoupl L ∅ σ₁ e₁' σ₁' b₁ fun σ₂ ρ' b₂ => iprop(|={∅, E}=>
          stateInterp σ₂ ∗ specInterp ρ' ∗ budgetInterp b₂ ∗ wp L E e₁ Φ)) ⊢
      wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb]
  imodintro
  iapply specCoupl_bind subset_refl
  iframe H
  iintro %σ₂ %ρ₂ %b₂ HInner
  iapply fupd_specCoupl
  imod HInner with ⟨Hσ', Hs', Hb', HW⟩
  imod wp_unfold_mp $$ HW %σ₂ %ρ₂.expr %ρ₂.state %b₂ [$Hσ' $Hs' $Hb'] with HW'
  imodintro
  iexact HW'

section Coupling
variable (Hv : e₁.toVal? = none)
include Hv

/-- For a non-value, skip both spec phases: a program coupling straight into `wp`. -/
theorem wp_lift_step_prog_couple : iprop%
    (∀ σ₁ e₁' σ₁' (b₁ : B), stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗
      budgetInterp b₁ -∗ |={E, ∅}=>
      progCoupl L e₁ σ₁ e₁' σ₁' b₁ fun e₂ σ₂ e₂' σ₂' b₂ => iprop% ▷ |={∅, E}=>
        stateInterp σ₂ ∗ specInterp ⟨e₂', σ₂'⟩ ∗ budgetInterp b₂ ∗
          wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb]
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_mono
  iframe H
  iintro %e₂ %σ₂ %e₂' %σ₂' %b₂ HL !>
  iapply specCoupl_ret
  iexact HL

/-! ## Coupling a program step with a spec step -/

/-- Couple one program step against one spec step by a head of `law`, each related pair continuing
with the leftover `R` as budget. -/
theorem wp_lift_prim_steps_coupl_of_head (law : L.BindLaw) : iprop%
    (∀ σ₁ e₁' σ₁' (b : B),
      stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗ budgetInterp b -∗
      |={E, ∅}=> ∃ R : Cfg rT → Cfg rT → B,
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜Reducible e₁' σ₁'⌝ ∗
        ⌜law.head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R b⌝ ∗
        ⌜law.SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R id⌝ ∗
        (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=> ▷ |={∅, E}=>
          stateInterp σ₂ ∗ specInterp ⟨e₂', σ₂'⟩ ∗
            budgetInterp (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) ∗ wp L E e₂ Φ)) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_prog_couple Hv
  iintro %σ₁ %e₁' %σ₁' %b Hres
  imod H $$ %σ₁ %e₁' %σ₁' %b Hres with ⟨%R, %Hred, %Hred', %Hhead, %Hside, H⟩
  imodintro
  iapply progCoupl_steps_law law Hred Hred' Hhead Hside
  iexact H

/-- `wp_lift_prim_steps_coupl_of_head` for a law whose heads shift: the head is at `b₁` and `b₂`
rides along on every leftover (Rocq `wp_couple_spend`). -/
theorem wp_lift_prim_steps_coupl_law [Add B] (law : L.BindLaw) [law.HeadShift] : iprop%
    (∀ σ₁ e₁' σ₁' (b : B),
      stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗ budgetInterp b -∗
      |={E, ∅}=> ∃ (R : Cfg rT → Cfg rT → B) (b₁ b₂ : B),
        ⌜b₁ + b₂ ≤ b⌝ ∗
        ⌜b₂ < (⊤ : B)⌝ ∗
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜Reducible e₁' σ₁'⌝ ∗
        ⌜law.head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R b₁⌝ ∗
        ⌜law.SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) (fun ρ ρ' => R ρ ρ' + b₂) id⌝ ∗
        (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂ < (⊤ : B)⌝ -∗ |={∅}=> ▷ |={∅, E}=>
          stateInterp σ₂ ∗ specInterp ⟨e₂', σ₂'⟩ ∗
            budgetInterp (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂) ∗ wp L E e₂ Φ)) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_prim_steps_coupl_of_head Hv law
  iintro %σ₁ %e₁' %σ₁' %b Hres
  imod H $$ %σ₁ %e₁' %σ₁' %b Hres with
    ⟨%R, %b₁, %b₂, %hb, %hb₂, %Hred, %Hred', %Hhead, %Hside, H⟩
  have Hhead' := law.mono_out (HeadShift.shift hb₂ Hhead) hb
  imodintro
  iexists fun ρ ρ' => R ρ ρ' + b₂
  iframe %Hred %Hred' %Hhead' %Hside H

/-- Couple a program step against a spec step within `b₁`, leaving `b₂` to the continuation out
of the budget `b` (Rocq `wp_couple`). -/
theorem wp_lift_prim_steps_coupl [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] : iprop%
    (∀ σ₁ e₁' σ₁' (b : B),
      stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗ budgetInterp b -∗
      |={E, ∅}=> ∃ (S : Cfg rT → Cfg rT → Prop) (b₁ b₂ : B),
        ⌜b₁ + b₂ ≤ b⌝ ∗
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜Reducible e₁' σ₁'⌝ ∗
        ⌜L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
        (∀ e₂ σ₂ e₂' σ₂', ⌜S ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ -∗ |={∅}=> ▷ |={∅, E}=>
          stateInterp σ₂ ∗ specInterp ⟨e₂', σ₂'⟩ ∗ budgetInterp b₂ ∗
            wp L E e₂ Φ)) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_prim_steps_coupl_of_head Hv (canonical L)
  iintro %σ₁ %e₁' %σ₁' %b Hres
  imod H $$ %σ₁ %e₁' %σ₁' %b Hres with ⟨%S, %b₁, %b₂, %hb, %Hred, %Hred', %Hcpl, H⟩
  have Hhead : (canonical L).head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)
      (fun ρ ρ' => relCost S ρ ρ' + b₂) b :=
    -- frame `b₂` onto the coupling at `b₁`, then weaken `b₁ + b₂` to `b`
    IsLawful.mono (IsTopAbsorbing.frame Hcpl) hb le_rfl
  have Hside : (canonical L).SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)
      (fun ρ ρ' => relCost S ρ ρ' + b₂) id :=
    SideForExec.of_forall fun _ _ => trivial
  imodintro
  iexists fun ρ ρ' => relCost S ρ ρ' + b₂
  iframe %Hred %Hred' %Hhead %Hside
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  -- a finite leftover means the pair is in `S`, where the leftover is `0 + b₂ = b₂`
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hR
  simp only [relCost_of hS, zero_add]
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂' %hS

/-- Couple a program step against an erasable presampling of the spec state, leaving the spec
expression in place. -/
theorem wp_lift_prim_step_l_erasable [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] : iprop%
    (∀ σ₁ e₁' σ₁' (b : B),
      stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗ budgetInterp b -∗
      |={E, ∅}=> ∃ (S : Cfg rT → State rT → Prop) (μ₁' : MeasureTheory.Measure (State rT))
        (b₁ b₂ : B),
        ⌜b₁ + b₂ ≤ b⌝ ∗
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜ErasableExpr μ₁' σ₁'⌝ ∗
        ⌜L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) μ₁'⌝ ∗
        (∀ e₂ σ₂ σ₂', ⌜S ⟨e₂, σ₂⟩ σ₂'⌝ -∗ |={∅}=> ▷ |={∅, E}=>
          stateInterp σ₂ ∗ specInterp ⟨e₁', σ₂'⟩ ∗ budgetInterp b₂ ∗
            wp L E e₂ Φ)) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b Hres
  imod H $$ %σ₁ %e₁' %σ₁' %b Hres with ⟨%S, %μ₁', %b₁, %b₂, %hb, %Hred, %Heras, %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_step_l_erasable hb Hred Hcpl Heras
  iintro %e₂ %σ₂ %σ₂' %HS
  imod H $$ %e₂ %σ₂ %σ₂' %HS
  iintro !> !>
  iapply specCoupl_ret
  iexact H

/-! ## Program steps that leave the spec in place

Program steps coupled against a Dirac at the spec configuration, leaving the budget unchanged.
`_concentrated` rules take any measurable set carrying the step; `@[discrete]` rules use the
support of a non-`urand` step. -/

section ConcentratedRules
variable [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive]
  [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] {S : State rT → Set (Cfg rT)}

section Concentrated
variable (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
  (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁))
include hSmeas hSconc

/-- A program step concentrated on `S σ₁`, with the spec untouched; the base of this section. -/
theorem wp_lift_step_later_concentrated : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=> ⌜Reducible e₁ σ₁⌝ ∗ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗
      |={∅}=> ▷ |={∅, E}=> stateInterp σ₂ ∗ wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_step_l_concentrated Hred (hSmeas σ₁) (hSconc σ₁)
  iintro %e₂ %σ₂ %Hmem
  imod H $$ %e₂ %σ₂ %Hmem
  iintro !> !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', HwpNew⟩
  imodintro
  iframe

/-- `wp_lift_step_later_concentrated` with the later taken before the continuation. -/
theorem wp_lift_step_concentrated : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=> ⌜Reducible e₁ σ₁⌝ ∗ ▷ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗
      |={∅, E}=> stateInterp σ₂ ∗ wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_later_concentrated Hv hSmeas hSconc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

/-- An atomic program step concentrated on `S σ₁`: every successor is a value satisfying `Φ`. -/
theorem wp_lift_atomic_step_fupd_concentrated : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E1}=> ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗ |={E1}[E2]▷=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E1 e₁ Φ := by
  iintro H
  iapply wp_lift_step_later_concentrated Hv hSmeas hSconc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imod subset empty_subset with Hclose
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hmem
  imod Hclose
  imod H $$ %e₂ %σ₂ %Hmem
  imod subset empty_subset with Hclose
  iintro !> !>
  imod Hclose
  cases htv : e₂.toVal? with
  | some v =>
    imod H with ⟨Hσ', HΦ⟩
    imodintro
    iframe Hσ'
    iapply wp_value_of_toVal htv $$ HΦ
  | none =>
    imod H with ⟨Hσ', HΦ⟩
    iexfalso
    iexact HΦ

/-- `wp_lift_atomic_step_fupd_concentrated` with a later in place of a step-update. -/
theorem wp_lift_atomic_step_concentrated : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=> ⌜Reducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗ |={E}=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd_concentrated Hv hSmeas hSconc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

end Concentrated

/-- `wp_lift_step_later_concentrated` on the support of a non-`urand` step. -/
@[discrete]
theorem wp_lift_step_later
    (hne : e₁.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=> ⌜Discrete.Reducible e₁ σ₁⌝ ∗ ∀ e₂ σ₂,
      ⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝ -∗ |={∅}=> ▷ |={∅, E}=> stateInterp σ₂ ∗ wp L E e₂ Φ) ⊢
    wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_later_concentrated Hv (measurableSet_primStep_support e₁)
    (concentrated_primStep_support e₁ · hne)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  have := Hred.toReducible
  iframe %this
  iintro %e₂ %σ₂ %Hmem
  iapply H $$ %e₂ %σ₂ %Hmem

/-- `wp_lift_atomic_step_fupd_concentrated` on the support of a non-`urand` step. -/
@[discrete]
theorem wp_lift_atomic_step_fupd
    (hne : e₁.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E1}=> ⌜Discrete.Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝ -∗ |={E1}[E2]▷=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E1 e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd_concentrated Hv (measurableSet_primStep_support e₁)
    (concentrated_primStep_support e₁ · hne)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  have := Hred.toReducible
  iframe %this
  iintro %e₂ %σ₂ %Hpstep
  iapply H $$ %e₂ %σ₂ %Hpstep

/-- `wp_lift_atomic_step_concentrated` on the support of a non-`urand` step. -/
@[discrete]
theorem wp_lift_atomic_step
    (hne : e₁.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=> ⌜Discrete.Reducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂, ⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝ -∗ |={E}=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd Hv hne
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hpstep !> !>
  iapply H $$ %e₂ %σ₂ %Hpstep

end ConcentratedRules

end Coupling

/-! ## Pure steps

Pure steps, stated on the measure-theoretic `PureStep` and `PureExec`, so they hold for a diffuse
`rT`. -/

section PureSteps
variable [Add B] [L.IsLawful] [L.IsTopAbsorbing] {e₂ : Exp rT} {φ : Prop} {n : Nat}
  {E' : CoPset}

/-- A pure step under a step-update proves `wp` (Rocq `wp_lift_pure_det_step`). -/
theorem wp_lift_pure_det_step (Hpure : PureStep e₁ e₂) :
    (|={E}[E']▷=> wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wpFor_lift_det_step (Exp.toVal?_eq_none.mpr (val_stuck (Hpure.safe default)))
  iintro %σ Hσ
  imod H
  imod subset empty_subset with Hclose
  imodintro
  iexists ⟨e₂, σ⟩
  have hdet := Hpure.det σ
  iframe %hdet
  iintro !>
  imod Hclose
  imod H
  imodintro
  iframe

/-- One pure step under a later. -/
theorem wp_pure_step_one (Hstep : PureStep e₁ e₂) : ▷ wp L E e₂ Φ ⊢ wp L E e₁ Φ :=
  wpFor_pure_step (Exp.toVal?_eq_none.mpr (val_stuck (Hstep.safe default))) Hstep.det

variable [Hex : PureExec φ n e₁ e₂]

/-- `n` pure steps given by a `PureExec` instance, each under a step-update. -/
theorem wp_pure_step_fupd (Hφ : φ) :
    (|={E}[E']▷=>^[n] wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  have Hsteps := Hex.pure_exec Hφ
  clear Hex
  induction n generalizing e₁ with
  | zero =>
    simp only [nsteps] at Hsteps
    subst Hsteps
    exact .rfl
  | succ n IH =>
    obtain ⟨c, Hstep, Hrest⟩ := Hsteps
    simp only [step_fupdN]
    iintro H
    iapply wp_lift_pure_det_step Hstep
    imod H
    imodintro
    iintro !>
    imod H
    imodintro
    iapply IH Hrest $$ H

/-- `n` pure steps under `n` laters, given by a `PureExec` instance. -/
theorem wp_pure_step_later (Hφ : φ) : ▷^[n] wp L E e₂ Φ ⊢ wp L E e₁ Φ :=
  (step_fupdN_intro subset_refl).trans (wp_pure_step_fupd (E' := E) (e₂ := e₂) Hφ)

end PureSteps

end Wp

end MicrometerWpGS

end ProbLang
