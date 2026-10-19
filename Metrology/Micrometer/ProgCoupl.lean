module

public import Metrology.Micrometer.SpecCoupl

/-! The `prog_coupl` modality: one program step coupled with spec steps by a bind law. -/

@[expose] public section

open Std Iris Iris.BI Iris.ProofMode OFE COFE ProbLang GradedLifting

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]

/-! ## `prog_coupl` modality

Couples exactly one program step against any number of spec steps and an erasable distribution,
by a lifting with per-pair leftovers and a bind law chosen for this step (clutch-dp `prog_coupl`).
-/

variable (L) in
/-- One program step against an erasable spec distribution by a step of a bind law: both are
images of the law's head measures under `f` and `f'`, and `Z` continues at each pair whose leftover
is finite (Rocq `prog_coupl`). -/
abbrev progCoupl (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (b : B)
    (Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF) : IProp GF := iprop%
  (∃ (law : L.BindLaw) (n : Nat) (μ₁' : MeasureTheory.Measure (State rT))
      (μ₀ ν₀ : MeasureTheory.Measure (Cfg rT)) (f f' : Cfg rT → Cfg rT)
      (R : Cfg rT → Cfg rT → B),
      ⌜Reducible e₁ σ₁⌝ ∗
      ⌜Measurable f ∧ primStep ⟨e₁, σ₁⟩ = μ₀.map f⌝ ∗
      ⌜Measurable f' ∧ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f'⌝ ∗
      ⌜law.head μ₀ ν₀ R b⌝ ∗
      ⌜law.SideForExec μ₀ ν₀ R f'⌝ ∗
      ⌜ErasableExpr μ₁' σ₁'⌝ ∗
      (∀ ρ ρ', ⌜R ρ ρ' < (⊤ : B)⌝ -∗ |={∅}=>
        Z (f ρ).expr (f ρ).state (f' ρ').expr (f' ρ').state (R ρ ρ')))

theorem progCoupl_ne {n : Nat} {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {b : B} {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → B → IProp GF}
    (HZ : ∀ e₂ σ₂ e₂' σ₂' b', Z₁ e₂ σ₂ e₂' σ₂' b' ≡{n}≡ Z₂ e₂ σ₂ e₂' σ₂' b') :
    progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ≡{n}≡ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ := by
  refine exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ =>
    exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => ?_
  refine sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
    sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) ?_
  exact forall_ne fun _ => forall_ne fun _ =>
    wand_ne.ne (.of_eq rfl) (BIFUpdate.ne.ne (HZ _ _ _ _ _))

theorem progCoupl_mono {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {b : B}
    {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → B → IProp GF} :
    iprop% (∀ e₂ σ₂ e₂' σ₂' b', Z₁ e₂ σ₂ e₂' σ₂' b' -∗ Z₂ e₂ σ₂ e₂' σ₂' b') ∗
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

/-! ## `progCoupl` — derived lemmas -/

theorem progCoupl_reducible {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} :
    progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢ ⌜Reducible e₁ σ₁⌝ := by
  iintro ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, -⟩
  ipureintro; exact Hred

/-- Introduce a program coupling by a step of any bind law, whose program and spec distributions
are images of the law's head measures under `f` and `f'` (Rocq `prog_coupl_intro_map`). -/
theorem progCoupl_intro_map (law : L.BindLaw) {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {n : Nat}
    {μ₁' : MeasureTheory.Measure (State rT)} {μ₀ ν₀ : MeasureTheory.Measure (Cfg rT)}
    {f f' : Cfg rT → Cfg rT} {R : Cfg rT → Cfg rT → B}
    (Hred : Reducible e₁ σ₁) (hf : Measurable f) (hprog : primStep ⟨e₁, σ₁⟩ = μ₀.map f)
    (hf' : Measurable f') (hspec : (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₀ ν₀ R b) (hside : law.SideForExec μ₀ ν₀ R f')
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ ρ ρ', ⌜R ρ ρ' < (⊤ : B)⌝ -∗ |={∅}=>
      Z (f ρ).expr (f ρ).state (f' ρ').expr (f' ρ').state (R ρ ρ')) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  have hF := And.intro hf hprog
  have hF' := And.intro hf' hspec
  iintro H
  iexists law, n, μ₁', μ₀, ν₀, f, f', R
  iframe %
  iexact H

/-- Introduce a program coupling by a step of any bind law (Rocq `prog_coupl_intro`). -/
theorem progCoupl_intro_law (law : L.BindLaw) {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {n : Nat}
    {μ₁' : MeasureTheory.Measure (State rT)} {R : Cfg rT → Cfg rT → B}
    (Hred : Reducible e₁ σ₁)
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R b)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R id)
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  iintro H
  iapply progCoupl_intro_map law Hred measurable_id MeasureTheory.Measure.map_id.symm
    measurable_id MeasureTheory.Measure.map_id.symm hhead hside Heras
  iintro %⟨e₂, σ₂⟩ %⟨e₂', σ₂'⟩ %hR
  simp only [id]
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂' %hR

theorem progCoupl_intro [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal] {e₁ : Exp rT}
    {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {n : Nat}
    {μ₁' : MeasureTheory.Measure (State rT)} {R : Cfg rT → Cfg rT → B}
    (Hred : Reducible e₁ σ₁)
    (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩))
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_intro_law (BindLaw.canonical L) Hred Hcpl (.of_forall fun _ _ => trivial) Heras

theorem dirac_bind_pexecN_one {e₁' : Exp rT} {σ₁' : State rT} (Hred' : Reducible e₁' σ₁') :
    (MeasureTheory.Measure.dirac σ₁').bind (fun σ => pexecN 1 ⟨e₁', σ⟩) = primStep ⟨e₁', σ₁'⟩ := by
  rw [MeasureTheory.Measure.dirac_bind (by fun_prop), pexecN_one,
    stepOrFinal_not_isValue (val_stuck Hred')]

/-- Continuations need only cover a set carrying the program step, by the law's `head_supp`
(Rocq `prog_coupl_strengthen`). -/
theorem progCoupl_strong_mono {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {S : Set
    (Cfg rT)} (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
    iprop% (∀ e₂ σ₂ e₂' σ₂' b', ⌜⟨e₂, σ₂⟩ ∈ S⌝ ∗ Z₁ e₂ σ₂ e₂' σ₂' b' -∗ Z₂ e₂ σ₂ e₂' σ₂' b') ∗
    progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ := by
  iintro ⟨Hm, HCpl⟩
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  classical
  obtain ⟨hf, hprog⟩ := Hf
  obtain ⟨hf', hspec⟩ := Hf'
  have hA : MeasurableSet (f ⁻¹' S) := hf hSmeas
  have hμ : μ₀ (f ⁻¹' S)ᶜ = 0 := by
    rw [← Set.preimage_compl, ← MeasureTheory.Measure.map_apply hf hSmeas.compl, ← hprog]
    exact hSconc
  iapply progCoupl_intro_map law Hred hf hprog hf' hspec (law.head_supp hA hμ Hhead) Hside.supp
    Heras
  iintro %ρ %ρ' %hR
  by_cases hmem : ρ ∈ f ⁻¹' S
  · simp only [Set.piecewise_eq_of_mem _ _ _ hmem] at hR ⊢
    imod HCont $$ %ρ %ρ' %hR with HZ₁
    imodintro
    iapply Hm
    have hmem' : (⟨(f ρ).expr, (f ρ).state⟩ : Cfg rT) ∈ S := hmem
    iframe %hmem' HZ₁
  · simp [Set.piecewise_eq_of_notMem _ _ _ hmem] at hR

theorem progCoupl_strengthen {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {S : Set
    (Cfg rT)} (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
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
theorem progCoupl_ctx_bind {K : Ectx rT} {e₁ : Exp rT} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} (hv : ¬ e₁.isValue) :
    progCoupl L e₁ σ₁ e₁' σ₁' b (fun e₂ => Z (K.fill e₂)) ⊢
    progCoupl L (K.fill e₁) σ₁ e₁' σ₁' b Z := by
  iintro HCpl
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  obtain ⟨hf, hprog⟩ := Hf
  obtain ⟨hf', hspec⟩ := Hf'
  have hK : Measurable fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT) := by fun_prop
  iapply progCoupl_intro_map law (Hred.fill K) (hK.comp hf)
    (by rw [primStep_fill hv, hprog, MeasureTheory.Measure.map_map hK hf]) hf' hspec Hhead Hside
    Heras
  simp only [Function.comp_apply]
  iexact HCont

/-! ### `progCoupl` — coupling-intro lemmas -/

/-- Couple one program step against one spec step by a step of any bind law (Rocq
`prog_coupl_one_step_top`). -/
theorem progCoupl_steps_law (law : L.BindLaw) {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF}
    {R : Cfg rT → Cfg rT → B} (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R b)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R id) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_intro_law (n := 1) law Hred (dirac_bind_pexecN_one Hred' ▸ hhead)
    (dirac_bind_pexecN_one Hred' ▸ hside) (ErasableExpr.dret σ₁')

/-- `progCoupl_steps_law` spending `b₁` of the budget `b` on the step and carrying `b₂` through
it, for a law whose heads shift (Rocq `wp_couple_spend`, `gbl_head_shift`). -/
theorem progCoupl_steps_spend_law [Add B] (law : L.BindLaw) [law.HeadShift] {e₁ : Exp rT}
    {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {b₁ b₂ b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {R : Cfg rT → Cfg rT → B}
    (hb : b₁ + b₂ ≤ b) (hb₂ : b₂ < (⊤ : B)) (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R b₁)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)
      (fun ρ ρ' => R ρ ρ' + b₂) id) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  have := prim_step_mass Hred
  have := prim_step_mass Hred'
  progCoupl_steps_law law Hred Hred' (law.mono_out (BindLaw.HeadShift.shift hb₂ hhead) hb) hside

theorem progCoupl_steps_adv' [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal] {e₁ : Exp rT}
    {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF}
    {R : Cfg rT → Cfg rT → B} (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_steps_law (BindLaw.canonical L) Hred Hred' Hcpl (.of_forall fun _ _ => trivial)

/-- Couple one program step against one spec step within `b₁`, adding `b₂` to every
leftover. -/
theorem progCoupl_steps_adv [AddCommMagma B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] {e₁ : Exp rT} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT}
    {b₁ b₂ b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF}
    {R : Cfg rT → Cfg rT → B} (hb : b₁ + b₂ ≤ b) (Hred : Reducible e₁ σ₁)
    (Hred' : Reducible e₁' σ₁')
    (Hcpl : L b₁ R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  have := prim_step_mass Hred
  have := prim_step_mass Hred'
  progCoupl_steps_adv' (R := fun ρ₁ ρ₂ => R ρ₁ ρ₂ + b₂) Hred Hred'
    (IsLawful.mono (IsTopAbsorbing.frame Hcpl) hb le_rfl)

/-- Couple one program step against one spec step by a relational lifting within `b₁`, leaving
`b₂` to the continuation: the step spends `b₁` out of the budget `b`. -/
theorem progCoupl_steps [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] {e₁ : Exp rT} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT} {b₁ b₂ b : B} {S : Cfg rT → Cfg rT → Prop}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF}
    (hb : b₁ + b₂ ≤ b) (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜S ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ -∗ |={∅}=> Z e₂ σ₂ e₂' σ₂' b₂) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  iintro Hcnt
  iapply progCoupl_steps_adv hb Hred Hred' Hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of hS, zero_add]
  iapply Hcnt $$ %e₂ %σ₂ %e₂' %σ₂' %hS

/-- A deterministic program step with the spec in place, by a step of the unit law (Rocq
`prog_coupl_det_step`). -/
theorem progCoupl_det_step [Add B] [L.IsLawful] {e₁ : Exp rT} {σ₁ : State rT} {e₂ : Exp rT}
    {σ₂ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} (hb : b < (⊤ : B))
    (Hred : Reducible e₁ σ₁)
    (Hdet : primStep ⟨e₁, σ₁⟩ = MeasureTheory.Measure.dirac ⟨e₂, σ₂⟩) :
    iprop(|={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  classical
  iintro HZ
  let R : Cfg rT → Cfg rT → B := fun ρ ρ' =>
    if ρ = ⟨e₂, σ₂⟩ ∧ ρ' = ⟨e₁', σ₁'⟩ then b else (⊤ : B)
  have hR : R ⟨e₂, σ₂⟩ ⟨e₁', σ₁'⟩ = b := ite_eq_left ⟨rfl, rfl⟩
  have hhead : (BindLaw.unit L).head (primStep ⟨e₁, σ₁⟩)
      ((MeasureTheory.Measure.dirac σ₁').bind fun σ => pexecN 0 ⟨e₁', σ⟩) R b := by
    rw [MeasureTheory.Measure.dirac_bind (by fun_prop), pexecN_zero, Hdet]
    exact BindLaw.unit_head_dirac (hR ▸ hb) hR.le
  iapply progCoupl_intro_law (BindLaw.unit L) Hred hhead (.of_forall fun _ _ => trivial)
    (ErasableExpr.dret σ₁')
  iintro %e₃ %σ₃ %e₃' %σ₃' %hlt
  by_cases hS : e₃ = e₂ ∧ σ₃ = σ₂ ∧ e₃' = e₁' ∧ σ₃' = σ₁'
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hS
    rw [hR]
    iexact HZ
  · simp [R, and_assoc, hS] at hlt

/-- A program step that leaves the spec in place, by a step of any law with diagonal heads: the
program step against itself, mapped to the spec configuration (Rocq `prog_coupl_step_l`). -/
theorem progCoupl_step_l_law [AddZeroClass B] [CanonicallyOrderedAdd B] (law : L.BindLaw)
    [law.HeadDiag] {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} (hb : b < (⊤ : B))
    (Hred : Reducible e₁ σ₁) :
    iprop(∀ e₂ σ₂, |={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  have := prim_step_mass Hred
  iintro H
  iapply progCoupl_intro_map (n := 0) (μ₁' := MeasureTheory.Measure.dirac σ₁')
    (f' := fun _ => ⟨e₁', σ₁'⟩) law Hred measurable_id MeasureTheory.Measure.map_id.symm
    measurable_const
    (by rw [MeasureTheory.Measure.dirac_bind (by fun_prop), pexecN_zero,
      MeasureTheory.Measure.map_const, MeasureTheory.measure_univ, one_smul])
    (BindLaw.HeadDiag.diag _ hb) (fun _ _ _ _ => BindLaw.HeadDiag.side_diag _ _ _ _)
    (ErasableExpr.dret σ₁')
  iintro %ρ %ρ' %hR
  obtain ⟨rfl, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of rfl, zero_add]
  simp only [id]
  iapply H $$ %ρ.expr %ρ.state

theorem progCoupl_step_l_erasable_adv [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal]
    {e₁ : Exp rT} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT} {μ₁' : MeasureTheory.Measure (State rT)} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {R : Cfg rT → State rT → B}
    (Hred : Reducible e₁ σ₁) (Heras : ErasableExpr μ₁' σ₁')
    (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) μ₁') : iprop%
    (∀ e₂ σ₂ σ₂', ⌜R ⟨e₂, σ₂⟩ σ₂' < (⊤ : B)⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₂' (R ⟨e₂, σ₂⟩ σ₂')) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  classical
  iintro Hcnt
  have Hcpl' : L b (fun ρ₁ ρ₂ => if ρ₂.expr = e₁' then R ρ₁ ρ₂.state else (⊤ : B))
      (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN 0 ⟨e₁', σ⟩) := by
    simp only [pexecN_zero]
    rw [MeasureTheory.Measure.bind_dirac_eq_map _ (by fun_prop),
      ← MeasureTheory.Measure.map_id (μ := primStep ⟨e₁, σ₁⟩)]
    exact IsLawful.map measurable_id (by fun_prop) (by simpa using Hcpl)
  iapply progCoupl_intro Hred Hcpl' Heras
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  by_cases he : e₂' = e₁'
  · subst he
    simp only [↓reduceIte] at hR ⊢
    iapply Hcnt $$ %e₂ %σ₂ %σ₂' %hR
  · simp [he] at hR

theorem progCoupl_step_l_erasable [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
      {σ₁' : State rT}
    {μ₁' : MeasureTheory.Measure (State rT)} {b₁ b₂ b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {S : Cfg rT → State rT → Prop}
    (hb : b₁ + b₂ ≤ b) (Hred : Reducible e₁ σ₁)
    (Hcpl : L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) μ₁')
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ σ₂', ⌜S ⟨e₂, σ₂⟩ σ₂'⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₂' b₂) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  have := Heras.isProbabilityMeasure
  have := prim_step_mass Hred
  iintro Hcnt
  iapply progCoupl_step_l_erasable_adv Hred Heras
    (IsLawful.mono (IsTopAbsorbing.frame Hcpl) hb le_rfl)
  iintro %e₂ %σ₂ %σ₂' %hR
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of hS, zero_add]
  iapply Hcnt $$ %e₂ %σ₂ %σ₂' %hS

theorem progCoupl_step_l_concentrated [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] {e₁ : Exp rT} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {S : Set (Cfg rT)}
    (Hred : Reducible e₁ σ₁)
    (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) : iprop%
    (∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  iintro H
  have := prim_step_mass Hred
  iapply progCoupl_step_l_erasable (zero_add b).le Hred
    (rel_dirac_right _ hSmeas hSconc σ₁') (ErasableExpr.dret σ₁')
  iintro %e₂ %σ₂ %σ₂' %HS
  obtain ⟨Hmem, rfl⟩ := HS
  iapply H $$ %e₂ %σ₂ %Hmem

end MicrometerWpGS

end ProbLang
