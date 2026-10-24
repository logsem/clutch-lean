module

public import Metrology.Micrometer.WpLifting
import Metrology.Iris.LocalBI

/-! # Head-step lifting rules of `wp`

The step-lifting rules of `WpLifting` restated for `headStep` (Rocq `approxis/ectx_lifting.v`). -/

@[expose] public section

open Iris

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]

section Wp
variable [BudgetGS B GF] {E E1 E2 : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
local bi IProp GF
open SpecUpdateGS
open Exp (decompItem_none_of_lc_headReducible)
open Set (univ)

/-- Head-step form of `wp_lift_step_prog_couple` (Rocq `wp_lift_head_step_prog_couple`). -/
theorem wp_lift_head_step_prog_couple (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' b₁, stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗
      budgetInterp b₁ -∗ |={E, ∅}=>
      ⌜∃ ρ : Cfg rT, 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝ ∗
      progCoupl L e₁ σ₁ e₁' σ₁' b₁ fun e₂ σ₂ e₂' σ₂' b₂ => iprop% ▷ |={∅, E}=>
        stateInterp σ₂ ∗ specInterp ⟨e₂', σ₂'⟩ ∗ budgetInterp b₂ ∗
          wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_prog_couple Hv
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with ⟨-, H⟩
  imodintro
  iexact H

section HeadRules
variable [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive]
  [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] {S : State rT → Set (Cfg rT)}

/-- Atomic head step, discrete form: reducibility and outcomes are read off the support of
`headStep`. -/
@[discrete]
theorem wp_lift_atomic_head_step (Hv : e₁.toVal? = none) (Hlc : e₁.IsLocallyClosed := by is_lc)
    (hne : e₁.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=> ⌜∃ ρ, 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝ ∗
      ▷ ∀ e₂ σ₂, ⌜0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝ -∗ |={E}=> stateInterp σ₂ ∗
        (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step Hv hne
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hhred, H⟩
  imodintro
  have Hhr : HeadReducible e₁ σ₁ := fun hz => by
    obtain ⟨ρ, hρ⟩ := Hhred
    simp [hz] at hρ
  isplitr
  · ipureintro; exact Reducible.toDiscrete hne (reducible_of_headReducible Hlc Hhr)
  iintro !> %e₂ %σ₂ %Hpstep
  have hpos : 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩} :=
    primStep_eq_headStep (decompItem_none_of_lc_headReducible Hlc Hhr) ▸ Hpstep
  iapply H $$ %e₂ %σ₂ %hpos

/-! ## Head-step rules over a carrying set

The carrying set is padded to `Set.univ` off the head-reducible states. -/

open scoped Classical in
/-- The carrying set `S σ₁` at head-reducible states, `univ` elsewhere, is measurable. -/
theorem measurableSet_headPad (hSmeas : ∀ σ₁, MeasurableSet (S σ₁)) (σ₁ : State rT) :
    MeasurableSet (if HeadReducible e₁ σ₁ then S σ₁ else univ) := by
  split_ifs; exacts [hSmeas σ₁, MeasurableSet.univ]

open scoped Classical in
/-- The carrying set `S σ₁` at head-reducible states, `univ` elsewhere, carries `primStep`. -/
theorem concentrated_headPad (Hlc : e₁.IsLocallyClosed)
    (hSconc : ∀ σ₁, HeadReducible e₁ σ₁ → Concentrated (headStep ⟨e₁, σ₁⟩) (S σ₁))
    (σ₁ : State rT) :
    Concentrated (primStep ⟨e₁, σ₁⟩) (if HeadReducible e₁ σ₁ then S σ₁ else univ) := by
  split_ifs with hhr
  · rw [primStep_eq_headStep (decompItem_none_of_lc_headReducible Hlc hhr)]
    exact hSconc σ₁ hhr
  · exact Concentrated.univ

section
variable (Hv : e₁.toVal? = none)
  (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
  (hSconc : ∀ σ₁, HeadReducible e₁ σ₁ → Concentrated (headStep ⟨e₁, σ₁⟩) (S σ₁))
include Hv hSmeas hSconc

/-- Head step, for any `rT`: outcomes range over a measurable set `S σ₁` carrying `headStep`. -/
theorem wp_lift_head_step_concentrated (Hlc : e₁.IsLocallyClosed := by is_lc) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=> ⌜HeadReducible e₁ σ₁⌝ ∗ ▷ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗
      |={∅, E}=> stateInterp σ₂ ∗ wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_concentrated Hv (measurableSet_headPad hSmeas)
    (concentrated_headPad Hlc hSconc)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hhred, H⟩
  imodintro
  isplitr
  · ipureintro; exact reducible_of_headReducible Hlc Hhred
  iintro !> %e₂ %σ₂ %Hmem
  rw [ite_eq_left Hhred] at Hmem
  iapply H $$ %e₂ %σ₂ %Hmem

/-- Atomic head step with a mask change `E1`/`E2`, over a measurable set carrying `headStep`. -/
theorem wp_lift_atomic_head_step_fupd_concentrated (Hlc : e₁.IsLocallyClosed := by is_lc) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E1}=> ⌜HeadReducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗ |={E1}[E2]▷=> stateInterp σ₂ ∗
        (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E1 e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd_concentrated Hv (measurableSet_headPad hSmeas)
    (concentrated_headPad Hlc hSconc)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hhred, H⟩
  imodintro
  isplitr
  · ipureintro; exact reducible_of_headReducible Hlc Hhred
  iintro %e₂ %σ₂ %Hmem
  rw [ite_eq_left Hhred] at Hmem
  iapply H $$ %e₂ %σ₂ %Hmem

/-- Atomic head step over a measurable set carrying `headStep`, from the mask-changing rule. -/
theorem wp_lift_atomic_head_step_concentrated (Hlc : e₁.IsLocallyClosed := by is_lc) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=> ⌜HeadReducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗ |={E}=> stateInterp σ₂ ∗
        (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_head_step_fupd_concentrated Hv hSmeas hSconc Hlc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hhred, H⟩
  imodintro
  iframe %Hhred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

end

end HeadRules

end Wp

end MicrometerWpGS

end ProbLang
