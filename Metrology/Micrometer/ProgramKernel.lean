module

public import Metrology.Micrometer.SpecCoupl
import Metrology.Iris.LocalBI

/-! # Program coupling for an explicit transition kernel -/

@[expose] public section

open Std Iris Iris.BI Iris.ProofMode OFE ProbLang GradedLifting
open MeasureTheory (Measure)
open MeasureTheory.Measure ErasableExpr BindLaw Set

namespace ProbLang.MicrometerWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]
  {step : Cfg rT → Measure (Cfg rT)}
local bi IProp GF

/-- Couple one transition of the kernel `step`, from a configuration it can leave, with an
erasable spec execution by a bind law. -/
abbrev progCouplFor (step : Cfg rT → Measure (Cfg rT)) (L : GradedLifting B)
    (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (b : B)
    (Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF) := iprop%
  (∃ (law : L.BindLaw) (n : Nat) (μ₁' : Measure (State rT)) (μ₀ ν₀ : Measure (Cfg rT))
      (f f' : Cfg rT → Cfg rT) (R : Cfg rT → Cfg rT → B),
      ⌜step ⟨e₁, σ₁⟩ ≠ 0⌝ ∗
      ⌜Measurable f ∧ step ⟨e₁, σ₁⟩ = μ₀.map f⌝ ∗
      ⌜Measurable f' ∧ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f'⌝ ∗
      ⌜law.head μ₀ ν₀ R b⌝ ∗
      ⌜law.SideForExec μ₀ ν₀ R f'⌝ ∗
      ⌜ErasableExpr μ₁' σ₁'⌝ ∗
      (∀ ρ ρ', ⌜R ρ ρ' < (⊤ : B)⌝ -∗ |={∅}=>
        Z (f ρ).expr (f ρ).state (f' ρ').expr (f' ρ').state (R ρ ρ')))

variable {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT} {b : B}
  {Z Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {n : Nat}
  {μ₁' : Measure (State rT)} {R : Cfg rT → Cfg rT → B}

/-- `progCouplFor step` is non-expansive in its continuation. -/
theorem progCouplFor_ne (HZ : ∀ e₂ σ₂ e₂' σ₂' b', Z₁ e₂ σ₂ e₂' σ₂' b' ≡{n}≡ Z₂ e₂ σ₂ e₂' σ₂' b') :
    progCouplFor step L e₁ σ₁ e₁' σ₁' b Z₁ ≡{n}≡ progCouplFor step L e₁ σ₁ e₁' σ₁' b Z₂ := by
  repeat' refine exists_ne fun _ => ?_
  repeat' refine sep_ne.ne (.of_eq rfl) ?_
  exact forall_ne fun _ => forall_ne fun _ =>
    wand_ne.ne (.of_eq rfl) (BIFUpdate.ne.ne (HZ _ _ _ _ _))

/-- `progCouplFor step` is monotone in its continuation. -/
theorem progCouplFor_mono : iprop%
    (∀ e₂ σ₂ e₂' σ₂' b', Z₁ e₂ σ₂ e₂' σ₂' b' -∗ Z₂ e₂ σ₂ e₂' σ₂' b') ∗
      progCouplFor step L e₁ σ₁ e₁' σ₁' b Z₁ ⊢ progCouplFor step L e₁ σ₁ e₁' σ₁' b Z₂ := by
  iintro ⟨HZ, HCpl⟩
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  iexists law, n, μ₁', μ₀, ν₀, f, f', R
  iframe %
  iintro %ρ %ρ' %hR
  imod HCont $$ %ρ %ρ' %hR with HZ'
  imodintro
  iapply HZ $$ HZ'

/-- A `progCouplFor step` step is only possible from a configuration the kernel can leave. -/
theorem progCouplFor_step_ne_zero :
    progCouplFor step L e₁ σ₁ e₁' σ₁' b Z ⊢ ⌜step ⟨e₁, σ₁⟩ ≠ 0⌝ := by
  iintro ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, -⟩
  ipureintro
  exact Hred

/-- Introduce a coupling through measurable images of the head distributions. -/
theorem progCouplFor_intro_map (law : L.BindLaw) {μ₀ ν₀ : Measure (Cfg rT)} {f f' : Cfg rT → Cfg rT}
    (Hred : step ⟨e₁, σ₁⟩ ≠ 0) (hf : Measurable f) (hprog : step ⟨e₁, σ₁⟩ = μ₀.map f)
    (hf' : Measurable f') (hspec : (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₀ ν₀ R b) (hside : law.SideForExec μ₀ ν₀ R f')
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ ρ ρ', ⌜R ρ ρ' < (⊤ : B)⌝ -∗ |={∅}=>
        Z (f ρ).expr (f ρ).state (f' ρ').expr (f' ρ').state (R ρ ρ')) ⊢
      progCouplFor step L e₁ σ₁ e₁' σ₁' b Z := by
  have hF := (⟨hf, hprog⟩ : _ ∧ _)
  have hF' := (⟨hf', hspec⟩ : _ ∧ _)
  iintro H
  iexists law, n, μ₁', μ₀, ν₀, f, f', R
  iframe %
  iexact H

/-- Introduce a coupling with identity maps on both head distributions. -/
theorem progCouplFor_intro_law (law : L.BindLaw) (Hred : step ⟨e₁, σ₁⟩ ≠ 0)
    (hhead : law.head (step ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R b)
    (hside : law.SideForExec (step ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R id)
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
        Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
      progCouplFor step L e₁ σ₁ e₁' σ₁' b Z := by
  iintro H
  iapply progCouplFor_intro_map law Hred measurable_id map_id.symm
    measurable_id map_id.symm hhead hside Heras
  iintro %⟨e₂, σ₂⟩ %⟨e₂', σ₂'⟩ %hR
  simp only [id]
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂' %hR

/-- A deterministic program transition coupled to an unchanged spec configuration. -/
theorem progCouplFor_det_step [Add B] [L.IsLawful] {e₂ : Exp rT} {σ₂ : State rT} (hb : b < (⊤ : B))
    (Hred : step ⟨e₁, σ₁⟩ ≠ 0) (Hdet : step ⟨e₁, σ₁⟩ = dirac ⟨e₂, σ₂⟩) :
    iprop(|={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢ progCouplFor step L e₁ σ₁ e₁' σ₁' b Z := by
  classical
  iintro HZ
  -- unit law at the Dirac pair `(⟨e₂, σ₂⟩, ⟨e₁', σ₁'⟩)` with leftover `b` there and `⊤` elsewhere
  let R : Cfg rT → Cfg rT → B := fun ρ ρ' =>
    if ρ = ⟨e₂, σ₂⟩ ∧ ρ' = ⟨e₁', σ₁'⟩ then b else (⊤ : B)
  have hR : R ⟨e₂, σ₂⟩ ⟨e₁', σ₁'⟩ = b := ite_eq_left ⟨rfl, rfl⟩
  have hhead : (BindLaw.unit L).head (step ⟨e₁, σ₁⟩)
      ((dirac σ₁').bind fun σ => pexecN 0 ⟨e₁', σ⟩) R b := by
    rw [dirac_bind (by fun_prop), pexecN_zero, Hdet]
    exact unit_head_dirac (hR ▸ hb) hR.le
  iapply progCouplFor_intro_law (.unit L) Hred hhead (.of_forall fun _ _ => trivial) (dret σ₁')
  iintro %e₃ %σ₃ %e₃' %σ₃' %hlt
  by_cases hS : e₃ = e₂ ∧ σ₃ = σ₂ ∧ e₃' = e₁' ∧ σ₃' = σ₁'
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hS
    rw [hR]
    iexact HZ
  · simp [R, and_assoc, hS] at hlt

/-- Continuations need only cover a set carrying the kernel step (via the law's `head_supp`). -/
theorem progCouplFor_strong_mono {S : Set (Cfg rT)} (hSmeas : MeasurableSet S)
    (hSconc : Concentrated (step ⟨e₁, σ₁⟩) S) : iprop%
    (∀ e₂ σ₂ e₂' σ₂' b', ⌜⟨e₂, σ₂⟩ ∈ S⌝ ∗ Z₁ e₂ σ₂ e₂' σ₂' b' -∗ Z₂ e₂ σ₂ e₂' σ₂' b') ∗
      progCouplFor step L e₁ σ₁ e₁' σ₁' b Z₁ ⊢ progCouplFor step L e₁ σ₁ e₁' σ₁' b Z₂ := by
  classical
  iintro ⟨Hm, HCpl⟩
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  obtain ⟨hf, hprog⟩ := Hf
  obtain ⟨hf', hspec⟩ := Hf'
  have hA : MeasurableSet (f ⁻¹' S) := hf hSmeas
  have hμ : μ₀ (f ⁻¹' S)ᶜ = 0 := by
    rw [← preimage_compl, ← map_apply hf hSmeas.compl, ← hprog]
    exact hSconc
  iapply progCouplFor_intro_map law Hred hf hprog hf' hspec (law.head_supp hA hμ Hhead) Hside.supp
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

/-- A context-compatible kernel transports program couplings through evaluation contexts. -/
theorem progCouplFor_ctx_bind
    (step_fill : ∀ (K : Ectx rT) (e : Exp rT) (σ : State rT), ¬e.isValue →
      step ⟨K.fill e, σ⟩ = (step ⟨e, σ⟩).map K.fillCfg)
    {K : Ectx rT} (hv : ¬e₁.isValue) :
    progCouplFor step L e₁ σ₁ e₁' σ₁' b (fun e₂ => Z (K.fill e₂)) ⊢
      progCouplFor step L (K.fill e₁) σ₁ e₁' σ₁' b Z := by
  iintro HCpl
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  obtain ⟨hf, hprog⟩ := Hf
  obtain ⟨hf', hspec⟩ := Hf'
  have hK : Measurable K.fillCfg := by fun_prop
  have HredK : step ⟨K.fill e₁, σ₁⟩ ≠ 0 := by
    rw [step_fill K e₁ σ₁ hv]
    exact (map_ne_zero_iff hK.aemeasurable).2 Hred
  iapply progCouplFor_intro_map law HredK (hK.comp hf)
    (by rw [step_fill K e₁ σ₁ hv, hprog, map_map hK hf]) hf' hspec Hhead Hside Heras
  simp only [Function.comp_apply, Ectx.fillCfg]
  iexact HCont

end ProbLang.MicrometerWpGS
