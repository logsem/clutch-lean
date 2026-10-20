module

public import Metrology.TotalEris.TotalWeakestpre

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang
namespace TotalEris
namespace ErisWpGS

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-!
# Total-WP lifting lemmas

Rules proving `tglWp` of a non-value from its prim step, down to pure and `PureExec` steps.
-/

/-- Prove `tglWp` of a non-value from `glm'` on its state and error interpretations. -/
theorem twp_lift_step_fupd_glm {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) : iprop(
    ∀ σ₁ ε₁, stateInterp σ₁ ∗ errInterp (rT := rT) ε₁ -∗
        |={E, ∅}=> glm' e₁ σ₁ ε₁ (fun ρ ε₂ =>
          iprop(|={∅, E}=>
            stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ)))
    ⊢ tglWp E e₁ Φ := by
  iintro HG
  iapply tglWp_unfold
  isimp only [tglWpPre_eq_step hv]
  iintro %σ %ε ⟨Hσ, Hε⟩
  iapply HG $$ %σ %ε [$Hσ $Hε]

/-- Lift a prim step whose outcomes are concentrated on a measurable relation `R`. -/
theorem twp_lift_step_fupd_gen {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) (R : State rT → Cfg rT → Prop)
    (hRmeas : ∀ σ₁, MeasurableSet {ρ | R σ₁ ρ})
    (hconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) {ρ | R σ₁ ρ}) : iprop(
    ∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜R σ₁ ⟨e₂, σ₂⟩⌝ -∗
        |={∅}=> |={∅, E}=> stateInterp σ₂ ∗ tglWp E e₂ Φ)
    ⊢ tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε₁ ⟨Hσ, Hε⟩
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imodintro
  iapply glm'_prim_step
  specialize hRmeas σ₁
  -- No failure mass (`R` is concentrated); every outcome keeps the full budget `ε₁`, whose
  -- expectation is `≤ ε₁` since `primStep` has mass `≤ 1`.
  have hbnd : ∀ ρ : Cfg rT, (fun _ => ε₁) ρ ≤ ε₁ := fun _ => le_rfl
  have hpgl : Pgl 0 (R σ₁) (primStep ⟨e₁, σ₁⟩) := Pgl.of_concentrated (hconc σ₁)
  have hexp : 0 + ∫⁻ ρ, (fun _ => ε₁) ρ ∂primStep ⟨e₁, σ₁⟩ ≤ ε₁ := by
    rw [zero_add, MeasureTheory.lintegral_const]
    calc ε₁ * primStep ⟨e₁, σ₁⟩ .univ
        ≤ ε₁ * 1 := by gcongr; exact primStep_univ_le_one _
      _ = ε₁ := mul_one ε₁
  iexists (R σ₁), 0, (fun _ => ε₁), ε₁
  iframe %Hred %hRmeas %hbnd %hexp %hpgl
  iintro %ρ %HR
  imod HCont $$ %ρ.expr %ρ.state %HR with HC
  imodintro
  iright
  imod HC with ⟨Hσ', HW⟩
  iframe

/-- Lift a prim step with atomic support. -/
theorem twp_lift_step_fupd {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none)
    (hatom : ∀ σ₁, IsAtomicSupport (primStep ⟨e₁, σ₁⟩)) : iprop(
    ∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (primStep ⟨e₁, σ₁⟩)⌝ -∗
        |={∅}=> |={∅, E}=> stateInterp σ₂ ∗ tglWp E e₂ Φ)
    ⊢ tglWp E e₁ Φ :=
  twp_lift_step_fupd_gen hv
    (fun σ₁ ρ => Possible ρ (primStep ⟨e₁, σ₁⟩))
    (fun σ₁ => measurableSet_possible_support)
    (fun σ₁ => by
      have hset : {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)}
          = {ρ | 0 < primStep ⟨e₁, σ₁⟩ {ρ}} := Set.ext fun ρ => possible_iff_pos
      rw [hset]; exact (hatom σ₁).concentrated_atoms)

/-- Lift an atomic prim step whose results are values. -/
theorem twp_lift_atomic_step_fupd {E₁ : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none)
    (hatom : ∀ σ₁, IsAtomicSupport (primStep ⟨e₁, σ₁⟩)) : iprop(
    ∀ σ₁, stateInterp σ₁ -∗ |={E₁}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (primStep ⟨e₁, σ₁⟩)⌝ -∗ |={E₁}=>
          stateInterp σ₂ ∗ match e₂.toVal? with | some v => Φ v | none => iprop(False))
      ⊢ tglWp E₁ e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd hv hatom
  iintro %σ₁ Hσ
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %hstep
  imodintro
  imod Hclose with -
  imod HCont $$ %e₂ %σ₂ %hstep with ⟨Hσ', HΦv⟩
  imodintro
  iframe Hσ'
  cases htv : e₂.toVal? with
  | some v => iapply tglWp_value_of_toVal htv $$ [$]
  | none => iexfalso; iexact HΦv

/-- Lift a pure prim step, which leaves the state unchanged. -/
theorem twp_lift_pure_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none)
    (hatom : ∀ σ₁, IsAtomicSupport (primStep ⟨e₁, σ₁⟩))
    (hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (hstep : ∀ σ₁ e₂ σ₂,
      Possible (⟨e₂, σ₂⟩ : Cfg rT) (primStep ⟨e₁, σ₁⟩) → σ₂ = σ₁) :
    iprop(|={E}=> ∀ e₂ σ, ⌜Possible ⟨e₂, σ⟩ (primStep ⟨e₁, σ⟩)⌝ -∗ tglWp E e₂ Φ)
    ⊢ tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd hv hatom
  iintro %σ₁ Hσ
  imod H
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  specialize hsafe σ₁
  iframe %hsafe
  iintro %e₂ %σ₂ %hstep'
  imodintro
  imod Hclose
  imodintro
  obtain rfl := hstep _ _ _ hstep'
  iframe Hσ
  iapply H $$ %_ %_ %hstep'

/-- Lift a deterministic pure prim step to `e₂`. -/
theorem twp_lift_pure_det_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hv : e₁.toVal? = none)
    (hatom : ∀ σ₁, IsAtomicSupport (primStep ⟨e₁, σ₁⟩))
    (hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (hpuredet : ∀ σ₁ e₂' σ₂,
      Possible ⟨e₂', σ₂⟩ (primStep ⟨e₁, σ₁⟩) → σ₂ = σ₁ ∧ e₂' = e₂) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢ tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_pure_step hv hatom hsafe
    (fun σ e₂' σ₂ hstep => (hpuredet σ e₂' σ₂ hstep).1)
  imod H
  imodintro
  iintro %e₂' %σ %hstep
  obtain ⟨_, rfl⟩ := hpuredet σ e₂' σ hstep
  iexact H

/-- Lift an atomic head step. -/
theorem twp_lift_atomic_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) (hlc : e₁.IsLocallyClosed)
    (hd : e₁.decompItem = none := by simp [Exp.decompItem, Exp.toVal?_lit, Exp.toVal?_ofVal])
    (hne : e₁ ≠ .urand := by nofun) : iprop(
    ∀ σ₁, stateInterp σ₁ -∗ |={E}=>
      ⌜HeadReducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (headStep ⟨e₁, σ₁⟩)⌝ -∗ |={E}=>
          stateInterp σ₂ ∗ match e₂.toVal? with | some v => Φ v | none => iprop(False))
      ⊢ tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_atomic_step_fupd hv
    (fun σ => by rw [primStep_eq_headStep hd]; exact headStep_atomic e₁ σ hne)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ Hσ with ⟨%Hhred, HCont⟩
  rw [← primStep_eq_headStep hd]
  replace Hhred := reducible_of_headReducible hlc Hhred
  imodintro
  iframe %Hhred
  iintro %e₂ %σ₂ %Hpstep
  iapply HCont $$ %e₂ %σ₂ %_
  exact Hpstep

/-- Lift a deterministic pure head step to `e₂`. -/
theorem twp_lift_pure_det_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hlc : e₁.IsLocallyClosed) (hv : e₁.toVal? = none)
    (hsafe : ∀ σ₁, ∃ ρ : Cfg rT, Possible ρ (headStep ⟨e₁, σ₁⟩))
    (hdet : ∀ σ₁ e₂' σ₂,
      Possible (⟨e₂', σ₂⟩ : Cfg rT) (headStep ⟨e₁, σ₁⟩) → σ₂ = σ₁ ∧ e₂' = e₂)
    (hne : e₁ ≠ .urand := by nofun) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢ tglWp E e₁ Φ := by
  have hhr : ∀ σ, HeadReducible e₁ σ := fun σ => (hsafe σ).elim fun _ hρ => hρ.ne_zero
  have hd : e₁.decompItem = none := Exp.decompItem_none_of_lc_headReducible hlc (hhr default)
  iapply twp_lift_pure_det_step hv
    (hatom := fun σ => by rw [primStep_eq_headStep hd]; exact headStep_atomic e₁ σ hne)
    (hsafe := fun σ => reducible_of_headReducible hlc (hhr σ))
  refine fun σ e₂' σ₂ hp => hdet σ e₂' σ₂ ?_
  rwa [← primStep_eq_headStep hd]

/-! ## `PureStep` / `PureExec` integration -/

/-- Lift a `PureStep`. -/
theorem twp_lift_pure_det_step_of_pureStep {E : CoPset} {Φ : Val rT → IProp GF}
    {e₁ e₂ : Exp rT}
    (h : PureStep e₁ e₂) : iprop(|={E}=> tglWp E e₂ Φ) ⊢ tglWp E e₁ Φ := by
  have hv : e₁.toVal? = none := Exp.toVal?_eq_none.mpr <| val_stuck <| h.safe default
  iapply twp_lift_pure_det_step hv
    (hatom := fun σ => by rw [h.det σ]; exact isAtomicSupport_dirac _) (hsafe := h.safe)
  intro σ e₂' σ₂ hp
  rw [h.det σ, possible_iff_pos, dirac_singleton_pos] at hp
  cases hp
  exact ⟨rfl, rfl⟩

/-- Lift `n` pure steps given by `PureExec`. -/
theorem twp_pure_step_fupd {E : CoPset} {Φ : Val rT → IProp GF} {n : ℕ} {e₁ e₂ : Exp rT}
    (φ : Prop) [HEx : PureExec φ n e₁ e₂] (Hφ : φ := by is_value) :
    tglWp E e₂ Φ ⊢ tglWp E e₁ Φ := by
  have Hex := HEx.pure_exec Hφ
  clear HEx
  induction n generalizing e₁ with
  | zero =>
    simp only [nsteps] at Hex
    subst Hex
    exact .rfl
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := Hex
    iintro H
    iapply twp_lift_pure_det_step_of_pureStep hstep
    imodintro
    iapply ih hrest $$ [$]

end ErisWpGS
end TotalEris
end ProbLang
