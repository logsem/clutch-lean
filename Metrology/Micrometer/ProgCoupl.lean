module

public import Metrology.Micrometer.SpecCoupl
import Metrology.Iris.LocalBI

/-! # The program-step modality `progCoupl`

`progCoupl` couples one program step with spec steps through a bind law, in the shape adequacy's
one-step lemma `lift_erasure_erasable_exp_lhs_kanto_law` consumes. -/

@[expose] public section

open Std Iris Iris.BI Iris.ProofMode OFE COFE ProbLang GradedLifting
open MeasureTheory (Measure measure_univ)
open MeasureTheory.Measure ErasableExpr BindLaw BindLaw.HeadDiag IsLawful IsTopAbsorbing
open Set BIFUpdate

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]
local bi IProp GF

/-! ## The `progCoupl` modality -/

variable (L) in
/-- One program step coupled with `n` spec steps from an erasable spec-state distribution by a
bind law: both runs are images of the law's head measures under `f` and `f'`, and `Z` continues at
each pair whose leftover is finite (Rocq `prog_coupl`). -/
abbrev progCoupl (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (b : B)
    (Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF) : IProp GF := iprop%
  (∃ (law : L.BindLaw) (n : Nat) (μ₁' : Measure (State rT))
      (μ₀ ν₀ : Measure (Cfg rT)) (f f' : Cfg rT → Cfg rT)
      (R : Cfg rT → Cfg rT → B),
      ⌜Reducible e₁ σ₁⌝ ∗
      ⌜Measurable f ∧ primStep ⟨e₁, σ₁⟩ = μ₀.map f⌝ ∗
      ⌜Measurable f' ∧ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f'⌝ ∗
      ⌜law.head μ₀ ν₀ R b⌝ ∗
      ⌜law.SideForExec μ₀ ν₀ R f'⌝ ∗
      ⌜ErasableExpr μ₁' σ₁'⌝ ∗
      (∀ ρ ρ', ⌜R ρ ρ' < (⊤ : B)⌝ -∗ |={∅}=>
        Z (f ρ).expr (f ρ).state (f' ρ').expr (f' ρ').state (R ρ ρ')))

section Steps
variable {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT} {b : B}
  {Z Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {n : Nat}
  {μ₁' : Measure (State rT)} {R : Cfg rT → Cfg rT → B}

/-! ### Basic properties -/

/-- `progCoupl` is non-expansive in its continuation. -/
theorem progCoupl_ne
    (HZ : ∀ e₂ σ₂ e₂' σ₂' b', Z₁ e₂ σ₂ e₂' σ₂' b' ≡{n}≡ Z₂ e₂ σ₂ e₂' σ₂' b') :
    progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ≡{n}≡ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ := by
  refine exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ =>
    exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => ?_
  refine sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
    sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) ?_
  exact forall_ne fun _ => forall_ne fun _ =>
    wand_ne.ne (.of_eq rfl) (ne.ne (HZ _ _ _ _ _))

/-- `progCoupl` is monotone in its continuation. -/
theorem progCoupl_mono : iprop%
    (∀ e₂ σ₂ e₂' σ₂' b', Z₁ e₂ σ₂ e₂' σ₂' b' -∗ Z₂ e₂ σ₂ e₂' σ₂' b') ∗
    progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ := by
  iintro ⟨HZ, HCpl⟩
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  iexists law, n, μ₁', μ₀, ν₀, f, f', R
  iframe %
  iintro %ρ %ρ' %hR
  imod HCont $$ %ρ %ρ' %hR with HZ'
  imodintro
  iapply HZ $$ HZ'

/-- A `progCoupl` step is only possible from a reducible program configuration. -/
theorem progCoupl_reducible : progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢ ⌜Reducible e₁ σ₁⌝ := by
  iintro ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, -⟩
  ipureintro; exact Hred

/-! ## Introducing `progCoupl` -/

/-- Introduce a program coupling by a step of any bind law, whose program and spec distributions
are images of the law's head measures under `f` and `f'` (Rocq `prog_coupl_intro_map`). -/
theorem progCoupl_intro_map (law : L.BindLaw) {μ₀ ν₀ : Measure (Cfg rT)}
    {f f' : Cfg rT → Cfg rT} (Hred : Reducible e₁ σ₁) (hf : Measurable f)
    (hprog : primStep ⟨e₁, σ₁⟩ = μ₀.map f) (hf' : Measurable f')
    (hspec : (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₀ ν₀ R b) (hside : law.SideForExec μ₀ ν₀ R f')
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ ρ ρ', ⌜R ρ ρ' < (⊤ : B)⌝ -∗ |={∅}=>
      Z (f ρ).expr (f ρ).state (f' ρ').expr (f' ρ').state (R ρ ρ')) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  -- paired up so that `iframe %` closes the two `⌜Measurable _ ∧ _ = _.map _⌝` conjuncts
  have hF := (⟨hf, hprog⟩ : _ ∧ _)
  have hF' := (⟨hf', hspec⟩ : _ ∧ _)
  iintro H
  iexists law, n, μ₁', μ₀, ν₀, f, f', R
  iframe %
  iexact H

/-- `progCoupl_intro_map` with `f = f' = id`: the law's head is stated directly on the program
step and the spec run (Rocq `prog_coupl_intro`). -/
theorem progCoupl_intro_law (law : L.BindLaw) (Hred : Reducible e₁ σ₁)
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R b)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R id)
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  iintro H
  iapply progCoupl_intro_map law Hred measurable_id map_id.symm
    measurable_id map_id.symm hhead hside Heras
  iintro %⟨e₂, σ₂⟩ %⟨e₂', σ₂'⟩ %hR
  simp only [id]
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂' %hR

/-! ## Structural rules -/

/-- Continuations need only cover a set carrying the program step (via the law's `head_supp`). -/
theorem progCoupl_strong_mono {S : Set (Cfg rT)} (hSmeas : MeasurableSet S)
    (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) : iprop%
    (∀ e₂ σ₂ e₂' σ₂' b', ⌜⟨e₂, σ₂⟩ ∈ S⌝ ∗ Z₁ e₂ σ₂ e₂' σ₂' b' -∗ Z₂ e₂ σ₂ e₂' σ₂' b') ∗
    progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ := by
  iintro ⟨Hm, HCpl⟩
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  classical
  obtain ⟨hf, hprog⟩ := Hf
  obtain ⟨hf', hspec⟩ := Hf'
  have hA : MeasurableSet (f ⁻¹' S) := hf hSmeas
  have hμ : μ₀ (f ⁻¹' S)ᶜ = 0 := by
    rw [← preimage_compl, ← map_apply hf hSmeas.compl, ← hprog]
    exact hSconc
  -- head_supp: setting the leftover to ⊤ off f⁻¹ S keeps the head, so continuations are only
  -- needed on S
  iapply progCoupl_intro_map law Hred hf hprog hf' hspec (law.head_supp hA hμ Hhead) Hside.supp
    Heras
  iintro %ρ %ρ' %hR
  by_cases hmem : ρ ∈ f ⁻¹' S
  · simp only [piecewise_eq_of_mem _ _ _ hmem] at hR ⊢
    imod HCont $$ %ρ %ρ' %hR with HZ₁
    imodintro
    iapply Hm
    have hmem' : (⟨(f ρ).expr, (f ρ).state⟩ : Cfg rT) ∈ S := hmem
    iframe %hmem' HZ₁
  · simp [piecewise_eq_of_notMem _ _ _ hmem] at hR

/-- The continuation may assume the program landed in `S` (Rocq `prog_coupl_strengthen`). -/
theorem progCoupl_strengthen {S : Set (Cfg rT)} (hSmeas : MeasurableSet S)
    (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
    progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b fun e₂ σ₂ e₂' σ₂' b' =>
      iprop(⌜⟨e₂, σ₂⟩ ∈ S⌝ ∧ Z e₂ σ₂ e₂' σ₂' b') := by
  iintro HCpl
  iapply progCoupl_strong_mono hSmeas hSconc
  iframe HCpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %b' ⟨%Hmem, HZ⟩
  isplitr; · ipureintro; exact Hmem
  iexact HZ

/-- A program step under an evaluation context, for any bind law: the program-side map is
composed with `K.fill` (Rocq `prog_coupl_ctx_bind`). -/
theorem progCoupl_ctx_bind {K : Ectx rT} (hv : ¬ e₁.isValue) :
    progCoupl L e₁ σ₁ e₁' σ₁' b (fun e₂ => Z (K.fill e₂)) ⊢
    progCoupl L (K.fill e₁) σ₁ e₁' σ₁' b Z := by
  iintro HCpl
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  obtain ⟨hf, hprog⟩ := Hf
  obtain ⟨hf', hspec⟩ := Hf'
  have hK : Measurable fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT) := by fun_prop
  iapply progCoupl_intro_map law (Hred.fill K) (hK.comp hf)
    (by rw [primStep_fill hv, hprog, map_map hK hf]) hf' hspec Hhead Hside
    Heras
  simp only [Function.comp_apply]
  iexact HCont

/-! ## Steps for a given law -/

/-- One spec step from a reducible configuration, written as a `pexecN 1` run from `δ σ₁'`. -/
theorem dirac_bind_pexecN_one (Hred' : Reducible e₁' σ₁') :
    (dirac σ₁').bind (fun σ => pexecN 1 ⟨e₁', σ⟩) = primStep ⟨e₁', σ₁'⟩ := by
  rw [dirac_bind (by fun_prop), pexecN_one,
    stepOrFinal_not_isValue (val_stuck Hred')]

/-- Couple one program step against one spec step by a step of any bind law (Rocq
`prog_coupl_one_step_top`). -/
theorem progCoupl_steps_law (law : L.BindLaw) (Hred : Reducible e₁ σ₁)
    (Hred' : Reducible e₁' σ₁')
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R b)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R id) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_intro_law law Hred (dirac_bind_pexecN_one Hred' ▸ hhead)
    (dirac_bind_pexecN_one Hred' ▸ hside) (dret σ₁')

/-- `progCoupl_steps_law` spending `b₁` of the budget `b` on the step and carrying `b₂` through
it, for a law whose heads shift (Rocq `wp_couple_spend`, `gbl_head_shift`). -/
theorem progCoupl_steps_spend_law [Add B] (law : L.BindLaw) [law.HeadShift] {b₁ b₂ : B}
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
    iprop(|={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  classical
  iintro HZ
  -- unit law at the Dirac pair `(⟨e₂, σ₂⟩, ⟨e₁', σ₁'⟩)` with leftover `b` there and `⊤` elsewhere
  let R : Cfg rT → Cfg rT → B := fun ρ ρ' =>
    if ρ = ⟨e₂, σ₂⟩ ∧ ρ' = ⟨e₁', σ₁'⟩ then b else (⊤ : B)
  have hR : R ⟨e₂, σ₂⟩ ⟨e₁', σ₁'⟩ = b := ite_eq_left ⟨rfl, rfl⟩
  have hhead : (BindLaw.unit L).head (primStep ⟨e₁, σ₁⟩)
      ((dirac σ₁').bind fun σ => pexecN 0 ⟨e₁', σ⟩) R b := by
    rw [dirac_bind (by fun_prop), pexecN_zero, Hdet]
    exact unit_head_dirac (hR ▸ hb) hR.le
  iapply progCoupl_intro_law (.unit L) Hred hhead (.of_forall fun _ _ => trivial)
    (dret σ₁')
  iintro %e₃ %σ₃ %e₃' %σ₃' %hlt
  by_cases hS : e₃ = e₂ ∧ σ₃ = σ₂ ∧ e₃' = e₁' ∧ σ₃' = σ₁'
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hS
    rw [hR]
    iexact HZ
  · simp [R, and_assoc, hS] at hlt

/-- A program step that leaves the spec in place, by a step of any law with diagonal heads: the
program step against itself, mapped to the spec configuration (Rocq `prog_coupl_step_l`). -/
theorem progCoupl_step_l_law [AddZeroClass B] [CanonicallyOrderedAdd B] (law : L.BindLaw)
    [law.HeadDiag] (hb : b < (⊤ : B)) (Hred : Reducible e₁ σ₁) :
    iprop(∀ e₂ σ₂, |={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  have := prim_step_mass Hred
  iintro H
  -- couple the step with itself (`HeadDiag.diag`: leftover `relCost (· = ·) ρ ρ' + b`), with `f'`
  -- sending the right copy to `⟨e₁', σ₁'⟩`; a finite leftover forces `ρ = ρ'`, so `b` is left
  iapply progCoupl_intro_map (n := 0) (μ₁' := dirac σ₁')
    (f' := fun _ => ⟨e₁', σ₁'⟩) law Hred measurable_id map_id.symm
    measurable_const
    (by rw [dirac_bind (by fun_prop), pexecN_zero,
      Measure.map_const, measure_univ, one_smul])
    (diag _ hb) (fun _ _ _ _ => side_diag _ _ _ _)
    (dret σ₁')
  iintro %ρ %ρ' %hR
  obtain ⟨rfl, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of rfl, zero_add]
  simp only [id]
  iapply H $$ %ρ.expr %ρ.state

/-! ## Steps for the canonical law

(`adv`, Rocq's "advanced", marks a per-pair leftover.) -/

section Canonical
variable [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal]

/-- Couple a program step with `n` spec steps from an erasable distribution, by the canonical law
with per-pair leftover `R`. -/
theorem progCoupl_intro (Hred : Reducible e₁ σ₁)
    (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩))
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_intro_law (canonical L) Hred Hcpl (.of_forall fun _ _ => trivial) Heras

/-- `progCoupl_steps_law` for the canonical law: a lifting with per-pair leftover `R` at the whole
budget `b`. -/
theorem progCoupl_steps_adv' (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_steps_law (canonical L) Hred Hred' Hcpl (.of_forall fun _ _ => trivial)

/-- A program step against an erasable spec-state distribution, spec expression fixed, with
per-pair leftover `R`. -/
theorem progCoupl_step_l_erasable_adv {R : Cfg rT → State rT → B} (Hred : Reducible e₁ σ₁)
    (Heras : ErasableExpr μ₁' σ₁') (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) μ₁') : iprop%
    (∀ e₂ σ₂ σ₂', ⌜R ⟨e₂, σ₂⟩ σ₂' < (⊤ : B)⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₂' (R ⟨e₂, σ₂⟩ σ₂')) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  classical
  iintro Hcnt
  -- read `μ₁'` as a 0-step spec run from `e₁'`; leftover `⊤` off that expression
  have Hcpl' : L b (fun ρ₁ ρ₂ => if ρ₂.expr = e₁' then R ρ₁ ρ₂.state else (⊤ : B))
      (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN 0 ⟨e₁', σ⟩) := by
    simp only [pexecN_zero]
    rw [bind_dirac_eq_map _ (by fun_prop),
      ← map_id (μ := primStep ⟨e₁, σ₁⟩)]
    exact map measurable_id (by fun_prop) (by simpa using Hcpl)
  iapply progCoupl_intro Hred Hcpl' Heras
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  by_cases he : e₂' = e₁'
  · subst he
    simp only [↓reduceIte] at hR ⊢
    iapply Hcnt $$ %e₂ %σ₂ %σ₂' %hR
  · simp [he] at hR

end Canonical

/-- Couple one program step against one spec step within `b₁`, adding `b₂` to every
leftover. -/
theorem progCoupl_steps_adv [AddCommMagma B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] {b₁ b₂ : B} (hb : b₁ + b₂ ≤ b)
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : L b₁ R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  -- `IsTopAbsorbing.frame` needs both primitive steps to be probability measures
  have := prim_step_mass Hred
  have := prim_step_mass Hred'
  progCoupl_steps_adv' Hred Hred'
    (mono (frame Hcpl) hb le_rfl)

section SplitBudget
variable [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsTopAbsorbing] [L.HasBind]
  [L.IsSupportLocal]

/-- Couple one program step against one spec step by a relational lifting within `b₁`, leaving
`b₂` to the continuation: the step spends `b₁` out of the budget `b`. -/
theorem progCoupl_steps {b₁ b₂ : B} {S : Cfg rT → Cfg rT → Prop} (hb : b₁ + b₂ ≤ b)
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜S ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ -∗ |={∅}=> Z e₂ σ₂ e₂' σ₂' b₂) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  iintro Hcnt
  iapply progCoupl_steps_adv hb Hred Hred' Hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of hS, zero_add]
  iapply Hcnt $$ %e₂ %σ₂ %e₂' %σ₂' %hS

/-- `progCoupl_step_l_erasable_adv` with a relational lifting within `b₁`, leaving `b₂` to the
continuation. -/
theorem progCoupl_step_l_erasable {b₁ b₂ : B} {S : Cfg rT → State rT → Prop}
    (hb : b₁ + b₂ ≤ b) (Hred : Reducible e₁ σ₁) (Hcpl : L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) μ₁')
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ σ₂', ⌜S ⟨e₂, σ₂⟩ σ₂'⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₂' b₂) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  have := Heras.isProbabilityMeasure
  have := prim_step_mass Hred
  iintro Hcnt
  iapply progCoupl_step_l_erasable_adv Hred Heras
    (mono (frame Hcpl) hb le_rfl)
  iintro %e₂ %σ₂ %σ₂' %hR
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of hS, zero_add]
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
