module

public import Metrology.Micrometer.ProgramKernel
import Metrology.Iris.LocalBI

/-! # The program-step modality `progCoupl`

`progCoupl` couples one program step with spec steps through a bind law, in the shape the
one-step adequacy lemma consumes. -/

@[expose] public section

open Std Iris Iris.BI Iris.ProofMode OFE ProbLang GradedLifting
open MeasureTheory (Measure measure_univ)
open MeasureTheory.Measure ErasableExpr BindLaw BindLaw.HeadDiag IsLawful IsTopAbsorbing

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]
local bi IProp GF

/-! ## The `progCoupl` modality -/

variable (L) in
/-- One program step coupled with some number of spec steps from an erasable spec-state
distribution by a bind law: both runs are images of the law's head measures under `f` and `f'`,
and `Z` continues at each pair whose leftover is finite (Rocq `prog_coupl`). -/
noncomputable abbrev progCoupl (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (b : B)
    (Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF) :=
  progCouplFor primStep L e₁ σ₁ e₁' σ₁' b Z

section Steps
variable {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT} {b : B}
  {Z Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {n : Nat}
  {μ₁' : Measure (State rT)} {R : Cfg rT → Cfg rT → B}

/-! ### Basic properties -/

/-- `progCoupl` is non-expansive in its continuation. -/
theorem progCoupl_ne (HZ : ∀ e₂ σ₂ e₂' σ₂' b', Z₁ e₂ σ₂ e₂' σ₂' b' ≡{n}≡ Z₂ e₂ σ₂ e₂' σ₂' b') :
    progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ≡{n}≡ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ :=
  progCouplFor_ne HZ

/-- `progCoupl` is monotone in its continuation. -/
theorem progCoupl_mono : iprop%
    (∀ e₂ σ₂ e₂' σ₂' b', Z₁ e₂ σ₂ e₂' σ₂' b' -∗ Z₂ e₂ σ₂ e₂' σ₂' b') ∗
      progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ :=
  progCouplFor_mono

/-- A `progCoupl` step is only possible from a reducible program configuration. -/
theorem progCoupl_reducible : progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢ ⌜Reducible e₁ σ₁⌝ :=
  progCouplFor_step_ne_zero

/-! ## Introducing `progCoupl` -/

/-- Introduce a program coupling by a step of any bind law, whose program and spec distributions
are images of the law's head measures under `f` and `f'` (Rocq `prog_coupl_intro_map`). -/
theorem progCoupl_intro_map (law : L.BindLaw) {μ₀ ν₀ : Measure (Cfg rT)} {f f' : Cfg rT → Cfg rT}
    (Hred : Reducible e₁ σ₁) (hf : Measurable f) (hprog : primStep ⟨e₁, σ₁⟩ = μ₀.map f)
    (hf' : Measurable f') (hspec : (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₀ ν₀ R b) (hside : law.SideForExec μ₀ ν₀ R f')
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ ρ ρ', ⌜R ρ ρ' < (⊤ : B)⌝ -∗ |={∅}=>
        Z (f ρ).expr (f ρ).state (f' ρ').expr (f' ρ').state (R ρ ρ')) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCouplFor_intro_map law Hred hf hprog hf' hspec hhead hside Heras

/-- `progCoupl_intro_map` with `f = f' = id`: the law's head is stated directly on the program
step and the spec run (Rocq `prog_coupl_intro`). -/
theorem progCoupl_intro_law (law : L.BindLaw) (Hred : Reducible e₁ σ₁)
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R b)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R id)
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
        Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCouplFor_intro_law law Hred hhead hside Heras

/-! ## Structural rules -/

variable {S : Set (Cfg rT)}

/-- Continuations need only cover a set carrying the program step (via the law's `head_supp`). -/
theorem progCoupl_strong_mono (hSmeas : MeasurableSet S)
    (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) : iprop%
    (∀ e₂ σ₂ e₂' σ₂' b', ⌜⟨e₂, σ₂⟩ ∈ S⌝ ∗ Z₁ e₂ σ₂ e₂' σ₂' b' -∗ Z₂ e₂ σ₂ e₂' σ₂' b') ∗
      progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ :=
  progCouplFor_strong_mono hSmeas hSconc

/-- The continuation may assume the program landed in `S` (Rocq `prog_coupl_strengthen`). -/
theorem progCoupl_strengthen (hSmeas : MeasurableSet S)
    (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
    progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b fun e₂ σ₂ e₂' σ₂' b' =>
        iprop(⌜⟨e₂, σ₂⟩ ∈ S⌝ ∧ Z e₂ σ₂ e₂' σ₂' b') := by
  iintro HCpl
  iapply progCoupl_strong_mono hSmeas hSconc
  iframe HCpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %b' ⟨%Hmem, HZ⟩
  isplit
  · ipureintro
    exact Hmem
  iexact HZ

/-- A program step under an evaluation context, for any bind law: the program-side map is
composed with `K.fill` (Rocq `prog_coupl_ctx_bind`). -/
theorem progCoupl_ctx_bind {K : Ectx rT} (hv : ¬ e₁.isValue) :
    progCoupl L e₁ σ₁ e₁' σ₁' b (fun e₂ => Z (K.fill e₂)) ⊢
      progCoupl L (K.fill e₁) σ₁ e₁' σ₁' b Z :=
  progCouplFor_ctx_bind (fun _ _ _ hv => primStep_fill hv) hv

/-! ## Steps for a given law -/

/-- One spec step from a reducible configuration, written as a `pexecN 1` run from `dirac σ₁'`. -/
theorem dirac_bind_pexecN_one (Hred' : Reducible e₁' σ₁') :
    (dirac σ₁').bind (fun σ => pexecN 1 ⟨e₁', σ⟩) = primStep ⟨e₁', σ₁'⟩ := by
  rw [dirac_bind (by fun_prop), pexecN_one, stepOrFinal_not_isValue (val_stuck Hred')]

variable (law : L.BindLaw)

/-- Couple one program step against one spec step by a step of any bind law (Rocq
`prog_coupl_one_step_top`). -/
theorem progCoupl_steps_law (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R b)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R id) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
        Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_intro_law law Hred (dirac_bind_pexecN_one Hred' ▸ hhead)
    (dirac_bind_pexecN_one Hred' ▸ hside) (dret σ₁')

variable {b₁ b₂ : B}

/-- `progCoupl_steps_law` spending `b₁` of the budget `b` on the step and carrying `b₂` through
it, for a law whose heads shift (Rocq `wp_couple_spend`, `gbl_head_shift`). -/
theorem progCoupl_steps_spend_law [Add B] [law.HeadShift]
    (hb : b₁ + b₂ ≤ b) (hb₂ : b₂ < (⊤ : B)) (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R b₁)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)
      (fun ρ ρ' => R ρ ρ' + b₂) id) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂ < (⊤ : B)⌝ -∗ |={∅}=>
        Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂)) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  -- `HeadShift.shift` needs both primitive steps to be probability measures
  have := prim_step_mass Hred
  have := prim_step_mass Hred'
  progCoupl_steps_law law Hred Hred' (law.mono_out (HeadShift.shift hb₂ hhead) hb) hside

/-- A deterministic program step with the spec in place, by a step of the unit law (Rocq
`prog_coupl_det_step`). -/
theorem progCoupl_det_step [Add B] [L.IsLawful] {e₂ : Exp rT} {σ₂ : State rT} (hb : b < (⊤ : B))
    (Hred : Reducible e₁ σ₁) (Hdet : primStep ⟨e₁, σ₁⟩ = dirac ⟨e₂, σ₂⟩) :
    iprop(|={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCouplFor_det_step hb Hred Hdet

/-- A finite leftover plus a slack `c` forces the pair into the relation and leaves just `c`. -/
private theorem relCost_add_of_lt_top [AddZeroClass B] [CanonicallyOrderedAdd B] {T U : Type}
    {S' : T → U → Prop} {x : T} {y : U} {c : B} (h : relCost S' x y + c < (⊤ : B)) :
    S' x y ∧ relCost S' x y + c = c :=
  have hS := (relCost_add_lt_top_iff.1 h).1
  ⟨hS, by rw [relCost_of hS, zero_add]⟩

/-- A program step that leaves the spec in place, by a step of any law with diagonal heads: the
program step against itself, mapped to the spec configuration (Rocq `prog_coupl_step_l`). -/
theorem progCoupl_step_l_law [AddZeroClass B] [CanonicallyOrderedAdd B] (law : L.BindLaw)
    [law.HeadDiag] (hb : b < (⊤ : B)) (Hred : Reducible e₁ σ₁) :
    iprop(∀ e₂ σ₂, |={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  have := prim_step_mass Hred
  iintro H
  -- couple the step with itself (`HeadDiag.diag`: leftover `relCost (· = ·) ρ ρ' + b`), with `f'`
  -- sending the right copy to `⟨e₁', σ₁'⟩`; a finite leftover forces `ρ = ρ'`, so `b` is left
  iapply progCoupl_intro_map (n := 0) (μ₁' := dirac σ₁') (f' := fun _ => ⟨e₁', σ₁'⟩) law Hred
    measurable_id map_id.symm measurable_const
    (by rw [dirac_bind (by fun_prop), pexecN_zero, Measure.map_const, measure_univ, one_smul])
    (diag _ hb) (fun _ _ _ _ => side_diag _ _ _ _) (dret σ₁')
  iintro %ρ %ρ' %hR
  obtain ⟨rfl, hc⟩ := relCost_add_of_lt_top hR
  rw [hc]
  simp only [id]
  iapply H $$ %ρ.expr %ρ.state

/-! ## Steps for the canonical law -/

section Canonical
variable [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal] (Hred : Reducible e₁ σ₁)
include Hred

/-- Couple a program step with `n` spec steps from an erasable distribution, by the canonical law
with per-pair leftover `R`. -/
theorem progCoupl_intro (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩))
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
        Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_intro_law (canonical L) Hred Hcpl (.of_forall fun _ _ => trivial) Heras

/-- `progCoupl_steps_law` for the canonical law: a lifting with per-pair leftover `R` at the whole
budget `b`. -/
theorem progCoupl_steps_adv' (Hred' : Reducible e₁' σ₁')
    (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
        Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_steps_law (canonical L) Hred Hred' Hcpl (.of_forall fun _ _ => trivial)

/-- A program step against an erasable spec-state distribution, spec expression fixed, with
per-pair leftover `R`. -/
theorem progCoupl_step_l_erasable_adv {R : Cfg rT → State rT → B} (Heras : ErasableExpr μ₁' σ₁')
    (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) μ₁') : iprop%
    (∀ e₂ σ₂ σ₂', ⌜R ⟨e₂, σ₂⟩ σ₂' < (⊤ : B)⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₂' (R ⟨e₂, σ₂⟩ σ₂')) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  classical
  iintro Hcnt
  -- read `μ₁'` as a 0-step spec run from `e₁'`; leftover `⊤` off that expression
  have Hcpl' : L b (fun ρ₁ ρ₂ => if ρ₂.expr = e₁' then R ρ₁ ρ₂.state else (⊤ : B))
      (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN 0 ⟨e₁', σ⟩) := by
    simp only [pexecN_zero]
    rw [bind_dirac_eq_map _ (by fun_prop), ← map_id (μ := primStep ⟨e₁, σ₁⟩)]
    exact map measurable_id (by fun_prop) (by simpa using Hcpl)
  iapply progCoupl_intro Hred Hcpl' Heras
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  by_cases he : e₂' = e₁'
  · subst he
    simp only [↓reduceIte] at hR ⊢
    iapply Hcnt $$ %e₂ %σ₂ %σ₂' %hR
  · simp [he] at hR

end Canonical

section SplitBudget
variable [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsTopAbsorbing] [L.HasBind]
  [L.IsSupportLocal]

/-- Couple one program step against one spec step within `b₁`, adding `b₂` to every
leftover. -/
theorem progCoupl_steps_adv (hb : b₁ + b₂ ≤ b)
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : L b₁ R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂ < (⊤ : B)⌝ -∗ |={∅}=>
        Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂)) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  -- `IsTopAbsorbing.frame` needs both primitive steps to be probability measures
  have := prim_step_mass Hred
  have := prim_step_mass Hred'
  progCoupl_steps_adv' Hred Hred' (mono (frame Hcpl) hb le_rfl)

/-- Couple one program step against one spec step by a relational lifting within `b₁`, leaving
`b₂` to the continuation: the step spends `b₁` out of the budget `b`. -/
theorem progCoupl_steps {S : Cfg rT → Cfg rT → Prop} (hb : b₁ + b₂ ≤ b)
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜S ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ -∗ |={∅}=> Z e₂ σ₂ e₂' σ₂' b₂) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  iintro Hcnt
  iapply progCoupl_steps_adv hb Hred Hred' Hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  obtain ⟨hS, hc⟩ := relCost_add_of_lt_top hR
  rw [hc]
  iapply Hcnt $$ %e₂ %σ₂ %e₂' %σ₂' %hS

/-- `progCoupl_step_l_erasable_adv` with a relational lifting within `b₁`, leaving `b₂` to the
continuation. -/
theorem progCoupl_step_l_erasable {S : Cfg rT → State rT → Prop}
    (hb : b₁ + b₂ ≤ b) (Hred : Reducible e₁ σ₁) (Hcpl : L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) μ₁')
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ σ₂', ⌜S ⟨e₂, σ₂⟩ σ₂'⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₂' b₂) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  have := Heras.isProbabilityMeasure
  have := prim_step_mass Hred
  iintro Hcnt
  iapply progCoupl_step_l_erasable_adv Hred Heras (mono (frame Hcpl) hb le_rfl)
  iintro %e₂ %σ₂ %σ₂' %hR
  obtain ⟨hS, hc⟩ := relCost_add_of_lt_top hR
  rw [hc]
  iapply Hcnt $$ %e₂ %σ₂ %σ₂' %hS

/-- A program step that leaves the spec in place, continuing on any set carrying the step. -/
theorem progCoupl_step_l_concentrated [L.IsReflexive] {S : Set (Cfg rT)}
    (Hred : Reducible e₁ σ₁) (hSmeas : MeasurableSet S)
    (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) : iprop%
    (∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢
      progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  iintro H
  have := prim_step_mass Hred
  iapply progCoupl_step_l_erasable (zero_add b).le Hred
    (rel_dirac_right _ hSmeas hSconc σ₁') (dret σ₁')
  iintro %e₂ %σ₂ %σ₂' %HS
  obtain ⟨Hmem, rfl⟩ := HS
  iapply H $$ %e₂ %σ₂ %Hmem

end SplitBudget

end Steps

end MicrometerWpGS

end ProbLang
