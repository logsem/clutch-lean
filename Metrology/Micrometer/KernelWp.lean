module

public import Metrology.Micrometer.ProgramKernel
import Metrology.Iris.LocalBI

/-! # Weakest preconditions for explicit transition kernels -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE GradedLifting
open MeasureTheory.Measure

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {step : Cfg rT → MeasureTheory.Measure (Cfg rT)}

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]
local bi IProp GF

/-! ## `wpPreFor` and its fixpoint `wpFor` -/

section Wp
variable [BudgetGS B GF] {n : Nat} {E E1 E2 : CoPset} {e : Exp rT} {v : Val rT}
  {Φ Ψ : Val rT → IProp GF}
open SpecUpdateGS BIFUpdate
open Exp (ofVal toVal?_ofVal ofVal_of_toVal_some)
open LawfulSet (empty_subset subset_refl)

/-- The type of `wpFor` as a function of its mask, expression and postcondition. -/
abbrev WpType := CoPset → Exp rT → (Val rT → IProp GF) → IProp GF

variable (step L) in
/-- One guarded weakest-precondition unfolding over an explicit program transition kernel. -/
abbrev wpPreFor (W : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : Exp rT) (Φ : Val rT → IProp GF) := iprop%
  ∀ σ₁ e₁' σ₁' (b₁ : B),
    stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗ budgetInterp b₁ -∗
    |={E, ∅}=> specCoupl L ∅ σ₁ e₁' σ₁' b₁ fun σ₂ ρ' b₂ =>
      match e₁.toVal? with
      | some v => iprop(|={∅, E}=> stateInterp σ₂ ∗ specInterp ρ' ∗
          budgetInterp b₂ ∗ Φ v)
      | none => progCouplFor step L e₁ σ₂ ρ'.expr ρ'.state b₂ fun e₃ σ₃ e₃' σ₃' b₃ => iprop%
          ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E}=>
            stateInterp σ₄ ∗ specInterp ρ'' ∗ budgetInterp b₄ ∗ W E e₃ Φ)

/-- The precondition body is non-expansive under one-step-lower agreement of its recursion. -/
theorem wpPreFor_ne_aux {W W' : WpType} (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v)
    (Hwp : ∀ m, m < n → ∀ e₃, W E e₃ Φ ≡{m}≡ W' E e₃ Ψ) :
    wpPreFor step L W E e Φ ≡{n}≡ wpPreFor step L W' E e Ψ := by
  refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
  refine wand_ne.ne (.of_eq rfl) (ne.ne ?_)
  refine least_fixpoint_ne_outer (fun _ _ => ?_) (.of_eq rfl)
  refine or_ne.ne (.of_eq rfl) (or_ne.ne ?_ (.of_eq rfl))
  cases htv : e.toVal? with
  | some v =>
    exact ne.ne <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) (HΦ v)
  | none =>
    refine progCouplFor_ne fun e₃ _ _ _ _ => ?_
    refine Contractive.distLater_dist fun m Hm => ?_
    refine specCoupl_ne fun _ _ _ => ?_
    exact ne.ne <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
      sep_ne.ne (.of_eq rfl) (Hwp m Hm e₃)

/-- The program transition guards recursive weakest preconditions by a later. -/
instance wpPreFor_contractive : Contractive (wpPreFor step L (rT := rT) (GF := GF)) where
  distLater_dist Hwp E _ Φ :=
    wpPreFor_ne_aux (fun _ => .of_eq rfl) fun _ Hm e₃ => DistLater.dist_lt (Hwp · · E e₃ Φ) Hm

variable (step L) in
/-- The Micrometer weakest precondition under the lifting `L`, the fixpoint of `wpPreFor`. -/
noncomputable def wpFor (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF) :=
  fixpoint (wpPreFor step L) E e Φ

/-- `wpFor` is its own one-step unfolding. -/
theorem wpFor_unfold : wpFor step L E e Φ = wpPreFor step L (wpFor step L) E e Φ :=
  congrFun (congrFun (congrFun (fixpoint_unfold ⟨wpPreFor step L, ne_of_contractive _⟩) E) e) Φ

/-- The forward direction of `wpFor_unfold`. -/
theorem wpFor_unfold_mp : wpFor step L E e Φ ⊢ wpPreFor step L (wpFor step L) E e Φ :=
  (equiv_iff.mp wpFor_unfold).1

/-! ## Values -/

theorem wpFor_value_fupd : (|={E}=> Φ v) ⊢ wpFor step L E (.ofVal v) Φ := by
  iintro HΦ
  iapply wpFor_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  rw [toVal?_ofVal]
  imod subset empty_subset with Hclose
  imodintro
  iapply specCoupl_ret
  imod Hclose
  imod HΦ
  imodintro
  iframe

/-- A value satisfies the weakest precondition when it satisfies the postcondition. -/
theorem wpFor_value : Φ v ⊢ wpFor step L E (.ofVal v) Φ :=
  fupd_intro.trans wpFor_value_fupd

theorem wpFor_value_of_toVal (h : e.toVal? = some v) : Φ v ⊢ wpFor step L E e Φ := by
  rw [← ofVal_of_toVal_some h]
  exact wpFor_value

theorem wpFor_value_fupd_of_toVal (h : e.toVal? = some v) : (|={E}=> Φ v) ⊢ wpFor step L E e Φ := by
  rw [← ofVal_of_toVal_some h]
  exact wpFor_value_fupd

/-- A weakest precondition at a value unfolds to a spec coupling. -/
theorem wpFor_value_specCoupl_unfold (E : CoPset) (He : e.toVal? = some v) :
    wpFor step L E e Φ ⊢
      ∀ σ₁ e₁' σ₁' b₁,
        stateInterp (rT := rT) σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗
          budgetInterp b₁ -∗
          |={E, ∅}=> specCoupl L ∅ σ₁ e₁' σ₁' b₁ (fun σ₂ ρ' b₂ =>
            iprop(|={∅, E}=>
              stateInterp σ₂ ∗ specInterp ρ' ∗ budgetInterp b₂ ∗ Φ v)) := by
  rw [wpFor_unfold]
  simp only [wpPreFor, He]
  exact .rfl

/-! ## The continuation after a program step -/

variable (step L) in
/-- The guarded continuation after a program transition. -/
noncomputable abbrev wpProgBodyFor (E : CoPset) (Φ : Val rT → IProp GF)
    (e₃ : Exp rT) (σ₃ : State rT) (e₃' : Exp rT) (σ₃' : State rT) (b₃ : B) :=
  iprop% ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E}=>
    stateInterp σ₄ ∗ specInterp ρ'' ∗ budgetInterp b₄ ∗ wpFor step L E e₃ Φ)

variable {b : B}

/-- At an absorbing budget the continuation holds trivially. -/
theorem wpProgBodyFor_absorbing (hb : L.Absorbing b) :
    ⊢ □ ∀ e₃ σ₃ e₃' σ₃', wpProgBodyFor step L E Φ e₃ σ₃ e₃' σ₃' b := by
  iintro !> %e₃ %σ₃ %e₃' %σ₃' !>
  iapply specCoupl_absorbing hb

/-- Map the recursive weakest precondition under the program continuation. -/
theorem wpProgBodyFor_wand {E' : CoPset} {e₃ e₄ : Exp rT}
    {σ₃ : State rT} {e₃' : Exp rT} {σ₃' : State rT} : iprop%
    wpProgBodyFor step L E Φ e₃ σ₃ e₃' σ₃' b ∗
      ▷ (wpFor step L E e₃ Φ ={E, E'}=∗ wpFor step L E' e₄ Ψ) ⊢
      wpProgBodyFor step L E' Ψ e₄ σ₃ e₃' σ₃' b := by
  iintro ⟨HBody, HWand⟩ !>
  iapply specCoupl_mono
  iframe HBody
  iintro %σ₄ %ρ₄ %b₄ HF
  imod HF with ⟨Hσ, Hs, Hb, Hwp⟩
  imod HWand $$ Hwp with Hwp
  imodintro
  iframe

/-! ## Monotonicity and updates -/

/-- The postcondition update `wpFor_strong_mono` asks for, framing the interpretations. -/
abbrev wpStrongMonoCont (E2 : CoPset) (Φ Ψ : Val rT → IProp GF) := iprop%
  □ ∀ σ ρ v (b : B),
    stateInterp (rT := rT) σ ∗ specInterp (rT := rT) ρ ∗ budgetInterp b ∗
      Φ v ={E2}=∗
    stateInterp σ ∗ specInterp ρ ∗ budgetInterp b ∗ Ψ v

variable (step L) in
/-- The generalized monotonicity statement for the guarded weakest precondition. -/
noncomputable abbrev wpForStrongMonoStmt : IProp GF := iprop%
  ∀ E1 E2 (e : Exp rT) Φ Ψ, ⌜E1 ⊆ E2⌝ -∗ wpFor step L E1 e Φ -∗ wpStrongMonoCont (B := B) E2 Φ Ψ -∗
    wpFor step L E2 e Ψ

/-- The weakest precondition is monotone under framed postcondition updates. -/
theorem wpFor_strong_mono (HE : E1 ⊆ E2) : iprop%
    wpFor step L E1 e Φ ∗ wpStrongMonoCont (B := B) E2 Φ Ψ ⊢ wpFor step L E2 e Ψ := by
  iintro ⟨HW, HΦ⟩
  -- Löb induction on the statement generalized over masks, expression and postconditions: rebind
  -- the spec phase with `specCoupl_bind`, then recurse under the later after the program step.
  have Hloeb : ⊢ wpForStrongMonoStmt step L (rT := rT) := by
    iapply loeb_wand
    iintro !> IH %E1' %E2' %e' %Φ' %Ψ' %HE' HW' #HΦ'
    iapply wpFor_unfold
    iintro %σ₁ %e₁' %σ₁' %b₁ Hres
    imod subset HE' with Hclose
    imod wpFor_unfold_mp $$ HW' %σ₁ %e₁' %σ₁' %b₁ Hres with HW'
    imodintro
    iapply specCoupl_bind subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %b₂ HZ₁
    cases htv : e'.toVal? with
    | some v =>
      iapply specCoupl_ret
      imod HZ₁ with ⟨Hσ', Hs', Hb', HΦv⟩
      imod Hclose
      imod HΦ' $$ [Hσ' Hs' Hb' HΦv] with ⟨Hσ', Hs', Hb', HΨv⟩
      · iframe
      imodintro
      iframe
    | none =>
      iapply specCoupl_ret
      iapply progCouplFor_mono
      iframe HZ₁
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater
      iapply wpProgBodyFor_wand
      iframe HLater
      iintro !> HwpInner
      imod Hclose
      imodintro
      iapply IH $$ %E1' %E2' %e₃ %Φ' %Ψ' %HE' HwpInner HΦ'
  iapply Hloeb $$ %E1 %E2 %e %Φ %Ψ %HE HW HΦ

/-- The weakest precondition is monotone in its postcondition, under a persistent wand. -/
theorem wpFor_wand : iprop% wpFor step L E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v) ⊢ wpFor step L E e Ψ := by
  iintro ⟨HW, #HΦ⟩
  iapply wpFor_strong_mono subset_refl
  iframe HW
  iintro !> %σ %ρ %v %b ⟨Hσ, Hs, Hb, HΦv⟩ !>
  iframe
  iapply HΦ $$ [$]

/-- A fancy update in the postcondition can be absorbed. -/
theorem wpFor_fupd : wpFor step L E e (fun v => iprop(|={E}=> Φ v)) ⊢ wpFor step L E e Φ := by
  iintro HW
  iapply wpFor_strong_mono subset_refl
  iframe HW
  iintro !> %σ %ρ %v %b ⟨Hσ, Hs, Hb, HΦ⟩
  imod HΦ
  iframe

/-- A fancy update before a weakest precondition can be absorbed. -/
theorem fupd_wpFor : (|={E}=> wpFor step L E e Φ) ⊢ wpFor step L E e Φ := by
  iintro HF
  iapply wpFor_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ Hres
  imod HF with HW
  iapply wpFor_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ Hres

/-! ## Derived monotonicity -/

/-- The weakest precondition is monotone in its postcondition. -/
theorem wpFor_mono (HΦ : ∀ v, Φ v ⊢ Ψ v) : wpFor step L E e Φ ⊢ wpFor step L E e Ψ := by
  iintro HW
  iapply wpFor_wand
  iframe HW
  iintro !> %v HΦv
  iapply HΦ $$ HΦv

/-- The weakest precondition is monotone in its mask. -/
theorem wpFor_mask_mono (HE : E1 ⊆ E2) : wpFor step L E1 e Φ ⊢ wpFor step L E2 e Φ := by
  iintro HW
  iapply wpFor_strong_mono HE
  iframe HW
  iintro !> %σ %ρ %v %b ⟨Hσ, Hs, Hb, HΦ⟩ !>
  iframe

theorem wpFor_wand_l : iprop% □ (∀ v, Φ v -∗ Ψ v) ∗ wpFor step L E e Φ ⊢ wpFor step L E e Ψ :=
  sep_comm.1.trans wpFor_wand

theorem wpFor_wand_r : iprop% wpFor step L E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v) ⊢ wpFor step L E e Ψ :=
  wpFor_wand

/-! ## Non-expansiveness -/

theorem wpFor_ne_aux (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v) : wpFor step L E e Φ ≡{n}≡ wpFor step L E e Ψ := by
  induction n using Nat.strong_induction_on generalizing e Φ Ψ with
  | _ n IH =>
    calc wpFor step L E e Φ
      _ ≡{n}≡ wpPreFor step L (wpFor step L) E e Φ := eq_dist_1 wpFor_unfold n
      _ ≡{n}≡ wpPreFor step L (wpFor step L) E e Ψ :=
        wpPreFor_ne_aux HΦ fun m Hm _ => IH m Hm fun v => Dist.lt (HΦ v) Hm
      _ ≡{n}≡ wpFor step L E e Ψ := (eq_dist_1 wpFor_unfold n).symm

/-- `wpFor` is non-expansive in the postcondition. -/
instance wpFor_ne : NonExpansive (wpFor step L (GF := GF) E e) where
  ne _ _ _ H := wpFor_ne_aux H

variable (step L) in
/-- The contextual bind statement for the shared guarded weakest precondition. -/
noncomputable abbrev wpForBindStmt (K : Ectx rT) : IProp GF := iprop%
  ∀ E e Φ, wpFor step L E e (fun v => wpFor step L E (K.fill (ofVal v)) Φ) -∗
    wpFor step L E (K.fill e) Φ

/-- A context-compatible kernel satisfies the weakest-precondition bind rule. -/
theorem wpFor_bind [Add B] [L.IsLawful] [L.IsTopAbsorbing]
    (step_fill : ∀ (K : Ectx rT) (e : Exp rT) (σ : State rT), ¬e.isValue →
      step ⟨K.fill e, σ⟩ = (step ⟨e, σ⟩).map K.fillCfg)
    {K : Ectx rT} {E : CoPset} {e : Exp rT}
    {Φ : Val rT → IProp GF} :
    wpFor step L E e (fun v => wpFor step L E (K.fill (ofVal v)) Φ) ⊢
      wpFor step L E (K.fill e) Φ := by
  have Hloeb : ⊢ wpForBindStmt step L K := by
    iapply loeb_wand
    iintro !> IH %E' %e' %Φ' HW
    iapply wpFor_unfold
    iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
    imod wpFor_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with HW'
    imodintro
    iapply specCoupl_bind subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %b₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      -- e' is a value: run the inner wp's spec phase in place of the outer one
      -- (fupd_specCoupl, hence IsTopAbsorbing)
      iapply fupd_specCoupl
      rw [show e' = ofVal v from (ofVal_of_toVal_some htv).symm]
      imod HBody with ⟨Hσ', Hs', Hb', HInner⟩
      imod wpFor_unfold_mp $$ HInner %σ₂ %ρ₂.expr %ρ₂.state %b₂ [$Hσ' $Hs' $Hb'] with HInner'
      imodintro
      iexact HInner'
    | none =>
      have hv : ¬ e'.isValue := Exp.toVal?_eq_none.mp htv
      have hvKfill : ¬ (K.fill e').isValue := fun hKv => hv (Ectx.fill_isValue hKv)
      have hKfillnone : (K.fill e').toVal? = none := Exp.toVal?_eq_none.mpr hvKfill
      iapply specCoupl_ret
      simp only [hKfillnone]
      -- e' steps: push K through the program step, recurse by Löb
      iapply progCouplFor_ctx_bind step_fill hv
      iapply progCouplFor_mono
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater
      iapply wpProgBodyFor_wand
      iframe HLater
      iintro !> HwpInner
      imodintro
      iapply IH $$ %E' %e₃ %Φ' HwpInner
  iapply Hloeb $$ %E %e %Φ

section Deterministic
variable [Add B] [L.IsLawful] [L.IsTopAbsorbing] {e₁ : Exp rT}
  (Hv : e₁.toVal? = none)
include Hv

/-- Lift a deterministic successor selected while owning the authoritative program state. -/
theorem wpFor_lift_det_step : iprop%
    (∀ σ, stateInterp σ -∗ |={E, ∅}=> ∃ next : Cfg rT,
      ⌜step ⟨e₁, σ⟩ = dirac next⌝ ∗ ▷ |={∅, E}=>
        stateInterp next.state ∗ wpFor step L E next.expr Φ) ⊢ wpFor step L E e₁ Φ := by
  iintro H
  iapply wpFor_unfold
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ Hσ with ⟨%next, %Hstep, Hnext⟩
  imodintro
  rcases lt_or_eq_of_le (le_top (a := b)) with hb | rfl
  · iapply specCoupl_ret
    simp only [Hv]
    have Hred : step ⟨e₁, σ₁⟩ ≠ 0 := by
      rw [Hstep]
      exact dirac_ne_zero
    iapply progCouplFor_det_step hb Hred Hstep
    iintro !> !>
    iapply specCoupl_ret
    imod Hnext with ⟨Hσ, Hwp⟩
    imodintro
    iframe
  · iapply specCoupl_absorbing IsTopAbsorbing.absorbing_top

/-- Lift one deterministic kernel transition with a specified state-dependent successor. -/
theorem wpFor_lift_det (next : State rT → Cfg rT)
    (Hstep : ∀ σ, step ⟨e₁, σ⟩ = dirac (next σ)) : iprop%
    (∀ σ, stateInterp σ -∗ |={E, ∅}=> ▷ |={∅, E}=>
      stateInterp (next σ).state ∗ wpFor step L E (next σ).expr Φ) ⊢
      wpFor step L E e₁ Φ := by
  iintro H
  iapply wpFor_lift_det_step Hv
  iintro %σ Hσ
  imod H $$ %σ Hσ with Hnext
  imodintro
  iexists next σ
  have hdet := Hstep σ
  iframe %hdet Hnext

/-- Lift an atomic successor selected while owning the authoritative program state. -/
theorem wpFor_lift_atomic_step : iprop%
    (∀ σ, stateInterp σ -∗ |={E, ∅}=> ∃ (v : Val rT) (σ' : State rT),
      ⌜step ⟨e₁, σ⟩ = dirac ⟨.ofVal v, σ'⟩⌝ ∗ ▷ |={∅, E}=>
        stateInterp σ' ∗ Φ v) ⊢ wpFor step L E e₁ Φ := by
  iintro H
  iapply wpFor_lift_det_step Hv
  iintro %σ Hσ
  imod H $$ %σ Hσ with ⟨%v, %σ', %Hstep, Hnext⟩
  imodintro
  iexists (⟨.ofVal v, σ'⟩ : Cfg rT)
  iframe %Hstep
  iintro !>
  imod Hnext with ⟨Hσ, HΦ⟩
  imodintro
  iframe Hσ
  iapply wpFor_value $$ HΦ

/-- Lift a deterministic atomic kernel transition returning a value and the updated state. -/
theorem wpFor_lift_atomic_det (result : State rT → Val rT) (update : State rT → State rT)
    (Hstep : ∀ σ, step ⟨e₁, σ⟩ = dirac ⟨.ofVal (result σ), update σ⟩) : iprop%
    (∀ σ, stateInterp σ -∗ |={E, ∅}=> ▷ |={∅, E}=>
      stateInterp (update σ) ∗ Φ (result σ)) ⊢ wpFor step L E e₁ Φ := by
  iintro H
  iapply wpFor_lift_det Hv (fun σ => ⟨.ofVal (result σ), update σ⟩) Hstep
  iintro %σ Hσ
  imod H $$ %σ Hσ with Hnext
  imodintro
  iintro !>
  imod Hnext with ⟨Hσ, HΦ⟩
  imodintro
  iframe Hσ
  iapply wpFor_value $$ HΦ

/-- A state-preserving deterministic kernel transition consumes one later. -/
theorem wpFor_pure_step {e₂ : Exp rT}
    (Hstep : ∀ σ, step ⟨e₁, σ⟩ = dirac ⟨e₂, σ⟩) :
    ▷ wpFor step L E e₂ Φ ⊢ wpFor step L E e₁ Φ := by
  iintro HW
  iapply wpFor_lift_det Hv (fun σ => ⟨e₂, σ⟩) Hstep
  iintro %σ Hσ
  imod subset empty_subset with Hclose
  imodintro
  iintro !>
  imod Hclose
  imodintro
  iframe

end Deterministic

-- TODO: `wp_contractive`, as in Iris

end Wp

end MicrometerWpGS

end ProbLang
