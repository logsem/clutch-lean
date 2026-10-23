module

public import Metrology.LiveEris.Weakestpre

@[expose] public section

/-! # LiveEris lifting lemmas -/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal
open ProbLang.LiveEris.CreditVec

namespace ProbLang
namespace LiveEris
namespace LiveWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [LiveWpGS rT Coord GF]
variable {Q : State rT → State rT → Prop}

theorem lwp_lift_step_glm {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) : iprop(
    ∀ σ₁ c, stateInterp σ₁ ∗ creditInterp c -∗
      |={E, ∅}=> glm e₁ σ₁ c (fun ρ c₂ =>
        stepCont Q E σ₁ ρ.state c₂ (lwp Q E ρ.expr Φ) (lwp Q E ρ.expr Φ)))
    ⊢ lwp Q E e₁ Φ := by
  rw [lwp_unfold_step hv]

/-- Lift a step whose outcomes are concentrated on `R`. The credits pass through unchanged, and each
outcome may continue ordinarily or cross a checkpoint. -/
theorem lwp_lift_step_gen {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) (R : State rT → Cfg rT → Prop)
    (hRmeas : ∀ σ₁, MeasurableSet {ρ | R σ₁ ρ})
    (hconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) {ρ | R σ₁ ρ}) : iprop(
    ∀ σ₁ c, stateInterp σ₁ ∗ creditInterp c -∗ |={E, ∅}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜R σ₁ ⟨e₂, σ₂⟩⌝ -∗ |={∅}=>
        stepCont Q E σ₁ σ₂ c (lwp Q E e₂ Φ) (lwp Q E e₂ Φ))
    ⊢ lwp Q E e₁ Φ := by
  iintro H
  iapply lwp_lift_step_glm hv
  iintro %σ₁ %c Hσc
  imod H $$ %σ₁ %c Hσc with ⟨%Hred, HCont⟩
  imodintro
  iapply glm_prim_step
  specialize hRmeas σ₁
  have hbnd : ∀ ρ : Cfg rT, (fun _ => c) ρ ≤ c := fun _ => le_rfl
  have hpgl : Pgl 0 (R σ₁) (primStep ⟨e₁, σ₁⟩) := (hconc σ₁).le
  have hexp : charge 0 + expect (primStep ⟨e₁, σ₁⟩) (fun _ => c) ≤ c := by
    intro i
    simp only [charge, Pi.add_apply, zero_add, expect, MeasureTheory.lintegral_const]
    calc c i * primStep ⟨e₁, σ₁⟩ .univ
        ≤ c i * 1 := by gcongr; exact primStep_univ_le_one _
      _ = c i := mul_one _
  iexists (R σ₁), 0, (fun _ => c), c
  iframe %Hred %hRmeas %hbnd %hexp %hpgl
  iintro %ρ %HR
  imod HCont $$ %ρ.expr %ρ.state %HR with HC
  imodintro
  iright
  iexact HC

theorem lwp_lift_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) (hatom : ∀ σ₁, IsAtomicSupport (primStep ⟨e₁, σ₁⟩)) : iprop(
    ∀ σ₁ c, stateInterp σ₁ ∗ creditInterp c -∗ |={E, ∅}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (primStep ⟨e₁, σ₁⟩)⌝ -∗ |={∅}=>
        stepCont Q E σ₁ σ₂ c (lwp Q E e₂ Φ) (lwp Q E e₂ Φ))
    ⊢ lwp Q E e₁ Φ :=
  lwp_lift_step_gen hv
    (fun σ₁ ρ => Possible ρ (primStep ⟨e₁, σ₁⟩))
    (fun σ₁ => measurableSet_possible_support)
    (fun σ₁ => by
      have hset : {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)}
          = {ρ | 0 < primStep ⟨e₁, σ₁⟩ {ρ}} := Set.ext fun ρ => possible_iff_pos
      rw [hset]; exact (hatom σ₁).concentrated_atoms)

/-- Lift an atomic head step to a value, which may continue ordinarily or cross a checkpoint. -/
theorem lwp_lift_atomic_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) (hlc : e₁.IsLocallyClosed)
    (hd : e₁.decompItem = none := by simp [Exp.decompItem, Exp.toVal?_lit, Exp.toVal?_ofVal])
    (hne : e₁ ≠ .urand := by nofun) : iprop(
    ∀ σ₁ c, stateInterp σ₁ ∗ creditInterp c -∗ |={E}=>
      ⌜HeadReducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (headStep ⟨e₁, σ₁⟩)⌝ -∗
        match e₂.toVal? with
        | some v => iprop((|={E}=> stateInterp σ₂ ∗ creditInterp c ∗ Φ v) ∨
            (⌜Checkpoint Q σ₁ σ₂ c⌝ ∗ ▷ |={E}=> stateInterp σ₂ ∗ creditInterp c ∗ Φ v))
        | none => iprop(False))
      ⊢ lwp Q E e₁ Φ := by
  iintro H
  have hatom : ∀ σ, IsAtomicSupport (primStep ⟨e₁, σ⟩) :=
    fun σ => by rw [primStep_eq_headStep hd]; exact headStep_atomic e₁ σ hne
  iapply lwp_lift_step hv hatom
  iintro %σ₁ %c Hσc
  imod H $$ %σ₁ %c Hσc with ⟨%Hhred, HCont⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  have Hred := reducible_of_headReducible hlc Hhred
  iframe %Hred
  iintro %e₂ %σ₂ %hstep !>
  rw [primStep_eq_headStep hd] at hstep
  ihave HC := HCont $$ %e₂ %σ₂ %hstep
  cases htv : e₂.toVal? with
  | some v =>
    icases HC with ⟨HC | ⟨%Hck, HC⟩⟩
    · ileft
      imod Hclose with -
      imod HC with ⟨Hσ', Hc', HΦ⟩
      imodintro
      iframe Hσ' Hc'
      iapply lwp_value_of_toVal htv $$ HΦ
    · iright
      isplitr; · ipureintro; exact Hck
      inext
      imod Hclose with -
      imod HC with ⟨Hσ', Hc', HΦ⟩
      imodintro
      iframe Hσ' Hc'
      iapply lwp_value_of_toVal htv $$ HΦ
  | none => iexfalso; iexact HC

/-- Lift a pure deterministic step, which may continue ordinarily or cross a checkpoint. -/
theorem lwp_lift_pure_det_step_of_pureStep {E : CoPset} {Φ : Val rT → IProp GF}
    {e₁ e₂ : Exp rT} (h : PureStep e₁ e₂) :
    iprop(∀ σ c, stateInterp σ ∗ creditInterp c -∗ |={E}=>
      (stateInterp σ ∗ creditInterp c ∗ lwp Q E e₂ Φ) ∨
      (⌜Checkpoint Q σ σ c⌝ ∗ ▷ |={E}=> stateInterp σ ∗ creditInterp c ∗ lwp Q E e₂ Φ))
    ⊢ lwp Q E e₁ Φ := by
  have hv : e₁.toVal? = none := Exp.toVal?_eq_none.mpr <| val_stuck <| h.safe default
  have hatom : ∀ σ, IsAtomicSupport (primStep ⟨e₁, σ⟩) :=
    fun σ => by rw [h.det σ]; exact isAtomicSupport_dirac _
  iintro H
  iapply lwp_lift_step hv hatom
  iintro %σ₁ %c Hσc
  imod H $$ %σ₁ %c Hσc with HC
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  have hred := h.safe σ₁
  iframe %hred
  iintro %e₂' %σ₂ %hp
  have heq : (⟨e₂', σ₂⟩ : Cfg rT) = ⟨e₂, σ₁⟩ := by
    by_contra hne
    rw [h.det σ₁, possible_iff_pos, dirac_singleton_pos] at hp
    exact hne hp.symm
  cases heq
  imodintro
  icases HC with ⟨HC | ⟨%Hck, HC⟩⟩
  · ileft
    imod Hclose with -
    imodintro
    iexact HC
  · iright
    isplitr; · ipureintro; exact Hck
    inext
    imod Hclose with -
    iexact HC

theorem lwp_pure_det_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (h : PureStep e₁ e₂) : lwp Q E e₂ Φ ⊢ lwp Q E e₁ Φ := by
  iintro HW
  iapply lwp_lift_pure_det_step_of_pureStep h
  iintro %σ %c ⟨Hσ, Hc⟩ !>
  ileft
  iframe

theorem lwp_pure_nsteps {E : CoPset} {Φ : Val rT → IProp GF} {n : ℕ} {e₁ e₂ : Exp rT}
    (h : nsteps PureStep n e₁ e₂) : lwp Q E e₂ Φ ⊢ lwp Q E e₁ Φ := by
  induction n generalizing e₁ with
  | zero =>
    simp only [nsteps] at h
    subst h
    exact .rfl
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    exact (ih hrest).trans (lwp_pure_det_step hstep)

theorem lwp_pure_step {E : CoPset} {Φ : Val rT → IProp GF} {n : ℕ} {e₁ e₂ : Exp rT}
    (φ : Prop) [HEx : PureExec φ n e₁ e₂] (Hφ : φ := by is_value) :
    lwp Q E e₂ Φ ⊢ lwp Q E e₁ Φ :=
  lwp_pure_nsteps (HEx.pure_exec Hφ)

end LiveWpGS
end LiveEris
end ProbLang
