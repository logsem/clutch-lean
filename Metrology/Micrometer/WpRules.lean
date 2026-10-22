module

public import Metrology.Micrometer.Wp
import Metrology.Iris.LocalBI

/-! # Structural rules of `wp`

The usual Iris rules for Micrometer's `wp`: `wp_bind`, absorbing spec updates, framing (also
across a step), the proof-mode instances, and `wp_of_absorbing` for an absorbing credit. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE GradedLifting

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]
local bi IProp GF
open BIFUpdate BIUpdateFUpdate
open Exp (ofVal ofVal_of_toVal_some toVal?_eq_none)
open LawfulSet (subset_refl empty_subset)

section Wp
variable [BudgetGS B GF] {E E1 E2 : CoPset} {e : Exp rT} {P R : IProp GF}
  {Φ Ψ : Val rT → IProp GF} {p : Bool} {io : InOut} {n : Nat}

/-! ## Bind and spec updates -/

variable (L) in
/-- The statement of `wp_bind` at the context `K`, proved by Löb induction. -/
noncomputable abbrev wpBindStmt (K : Ectx rT) : IProp GF := iprop%
  ∀ E e Φ, wp L E e (fun v => wp L E (K.fill (ofVal v)) Φ) -∗ wp L E (K.fill e) Φ

/-- Bind: a `wp` for `e` whose postcondition is a `wp` for `K[v]` proves the `wp` for `K[e]`. -/
theorem wp_bind [Add B] [L.IsLawful] [L.IsTopAbsorbing] {K : Ectx rT} {E : CoPset} {e : Exp rT}
    {Φ : Val rT → IProp GF} :
    wp L E e (fun v => wp L E (K.fill (ofVal v)) Φ) ⊢ wp L E (K.fill e) Φ := by
  have Hloeb : ⊢ wpBindStmt L K := by
    iapply loeb_wand
    iintro !> IH %E' %e' %Φ' HW
    iapply wp_unfold
    iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
    imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with HW'
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
      imod wp_unfold_mp $$ HInner %σ₂ %ρ₂.expr %ρ₂.state %b₂ [$Hσ' $Hs' $Hb'] with HInner'
      imodintro
      iexact HInner'
    | none =>
      have hv : ¬ e'.isValue := toVal?_eq_none.mp htv
      have hvKfill : ¬ (K.fill e').isValue := fun hKv => hv (Ectx.fill_isValue hKv)
      have hKfillnone : (K.fill e').toVal? = none := toVal?_eq_none.mpr hvKfill
      iapply specCoupl_ret
      simp only [hKfillnone]
      -- e' steps: push K through the program step, recurse by Löb
      iapply progCoupl_ctx_bind hv
      iapply progCoupl_mono
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater
      iapply wpProgBody_wand
      iframe HLater
      iintro !> HwpInner
      imodintro
      iapply IH $$ %E' %e₃ %Φ' HwpInner
  iapply Hloeb $$ %E %e %Φ

/-- A spec update before a `wp` can be absorbed into it. -/
theorem specUpdate_wp [Add B] [L.IsLawful] [L.IsTopAbsorbing] :
    specUpdate rT E (wp L E e Φ) ⊢ wp L E e Φ := by
  unfold specUpdate
  iintro HS
  iapply wp_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod HS $$ %⟨e₁', σ₁'⟩ Hs with ⟨%ρ', %n, %Hstep, Hs', HW⟩
  cases ρ' with
  | mk e₂' σ₂' =>
    imod wp_unfold_mp $$ HW %σ₁ %e₂' %σ₂' %b₁ [$Hσ $Hs' $Hb] with HW'
    imodintro
    iapply specCoupl_steps_det Hstep $$ HW'

variable (L) in
/-- The statement of `wp_specUpdate`, proved by Löb induction. -/
noncomputable abbrev wpSpecUpdateStmt : IProp GF := iprop%
  ∀ E (e : Exp rT) Φ, wp L E e (fun v => specUpdate rT E (Φ v)) -∗ wp L E e Φ

/-- A spec update in the postcondition can be absorbed into the `wp`. -/
theorem wp_specUpdate [Add B] [L.IsLawful] [L.IsTopAbsorbing] :
    wp L E e (fun v => specUpdate rT E (Φ v)) ⊢ wp L E e Φ := by
  have Hloeb : ⊢ wpSpecUpdateStmt L (rT := rT) := by
    iapply loeb_wand
    iintro !> IH %E' %e' %Φ' HW
    iapply wp_unfold
    iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
    imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with HW'
    imodintro
    iapply specCoupl_bind subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %b₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      iapply fupd_specCoupl
      imod HBody with ⟨Hσ', Hs', Hb', HUpd⟩
      imod HUpd $$ %ρ₂ Hs' with ⟨%ρ₃, %n, %Hstep, Hs'', HΦv⟩
      cases ρ₃ with
      | mk e₃' σ₃' =>
        imod subset empty_subset with Hclose
        imodintro
        iapply specCoupl_steps_det Hstep
        iapply specCoupl_ret
        imod Hclose
        imodintro
        iframe
    | none =>
      iapply specCoupl_ret
      iapply progCoupl_mono
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater
      iapply wpProgBody_wand
      iframe HLater
      iintro !> HwpInner
      imodintro
      iapply IH $$ %E' %e₃ %Φ' HwpInner
  iapply Hloeb $$ %E %e %Φ

/-! ## Framing -/

variable (L) in
/-- The statement of `wp_frame_l`, proved by Löb induction. -/
noncomputable abbrev wpFrameLStmt : IProp GF := iprop%
  ∀ E (e : Exp rT) R Φ, R -∗ wp L E e Φ -∗ wp L E e fun v => iprop(R ∗ Φ v)

/-- Frame a resource into the postcondition. -/
theorem wp_frame_l : iprop% R ∗ wp L E e Φ ⊢ wp L E e fun v => iprop(R ∗ Φ v) := by
  have Hloeb : ⊢ wpFrameLStmt L (rT := rT) := by
    iapply loeb_wand
    iintro !> IH %E' %e' %R' %Φ' HR HW
    iapply wp_unfold
    iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
    imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with HW'
    imodintro
    iapply specCoupl_mono
    iframe HW'
    iintro %σ₂ %ρ₂ %b₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      imod HBody with ⟨Hσ', Hs', Hb', HΦv⟩
      simp only []
      imodintro
      iframe
    | none =>
      iapply progCoupl_mono
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater
      iapply wpProgBody_wand
      iframe HLater
      iintro !> HwpInner
      imodintro
      iapply IH $$ %E' %e₃ %R' %Φ' HR HwpInner
  iintro ⟨HR, HW⟩
  iapply Hloeb $$ %E %e %R %Φ HR HW

/-- Frame a resource into the postcondition, on the right. -/
theorem wp_frame_r : iprop% wp L E e Φ ∗ R ⊢ wp L E e fun v => iprop(Φ v ∗ R) :=
  (sep_comm.1.trans wp_frame_l).trans (wp_mono fun _ => sep_comm.1)

/-- A framed resource pays for a wand in the postcondition. -/
theorem wp_frame_wand : iprop% R ∗ wp L E e (fun v => iprop(R -∗ Φ v)) ⊢ wp L E e Φ :=
  wp_frame_l.trans (wp_mono fun _ => wand_elim_right)

section
variable (HE : E2 ⊆ E1) (hv : e.toVal? = none)
include HE hv

/-- A non-value `e` takes a step, so an update that crosses a later can run around it and hand
its result to the postcondition. -/
theorem wp_step_fupd : iprop%
    (|={E1, E2}=> ▷ |={E2, E1}=> P) ∗ wp L E2 e (fun v => iprop(P -∗ Φ v)) ⊢ wp L E1 e Φ := by
  iintro ⟨HR, HW⟩
  iapply wp_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod HR
  imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with HW'
  imodintro
  iapply specCoupl_mono
  iframe HW'
  iintro %σ₂ %ρ₂ %b₂ HBody
  simp only [hv]
  iapply progCoupl_mono
  iframe HBody
  iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater
  iapply wpProgBody_wand
  iframe HLater
  iintro !> HwpInner
  imod HR
  imodintro
  iapply wp_mask_mono HE
  ihave HwpInner := wp_frame_l $$ [$HR $HwpInner]
  iapply wp_wand
  iframe HwpInner
  iintro !> %v ⟨HP, HWand⟩
  iapply HWand $$ HP

/-- Frame a resource available only after one step into the postcondition. -/
theorem wp_frame_step_l : iprop%
    (|={E1, E2}=> ▷ |={E2, E1}=> R) ∗ wp L E2 e Φ ⊢ wp L E1 e fun v => iprop(R ∗ Φ v) := by
  iintro ⟨HR, HW⟩
  iapply wp_step_fupd HE hv
  iframe HR
  iapply wp_wand
  iframe HW
  iintro !> %v HΦ HR'
  iframe

/-- Frame a resource available only after one step into the postcondition, on the right. -/
theorem wp_frame_step_r : iprop%
    wp L E2 e Φ ∗ (|={E1, E2}=> ▷ |={E2, E1}=> R) ⊢ wp L E1 e fun v => iprop(Φ v ∗ R) :=
  (sep_comm.1.trans (wp_frame_step_l HE hv)).trans (wp_mono fun _ => sep_comm.1)

end

/-! ## Proof-mode instances -/

/-- `wp` is closed under `◇`. -/
instance isExcept0_wp : IsExcept0 (wp L E e Φ) where
  is_except0 := (except0_mono fupd_intro).trans (except0.trans fupd_wp)

/-- Framing through `wp` frames the postcondition. -/
instance frame_wp [inst : ∀ v, Frame p R (Φ v) (Ψ v)] :
    Frame p R (wp L E e Φ) (wp L E e Ψ) where
  frame := wp_frame_l.trans (wp_mono fun v => (inst v).frame)

/-- A `wp` absorbs a leading `|={E}=>`. -/
instance addModal_fupd_wp : AddModal iprop(|={E}=> P) P (wp L E e Φ) where
  add_modal := fupd_frame_right.trans <| (mono wand_elim_right).trans fupd_wp

/-- A `wp` eliminates a leading `|==>`. -/
instance elimModal_bupd_wp :
    ElimModal True p io false iprop(|==> P) P (wp L E e Φ) (wp L E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    (sep_mono_left fupd_of_bupd).trans <|
    fupd_frame_right.trans <| (mono wand_elim_right).trans fupd_wp

/-- A `wp` eliminates a leading `|={E}=>`. -/
instance elimModal_fupd_wp :
    ElimModal True p io false iprop(|={E}=> P) P (wp L E e Φ) (wp L E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (mono wand_elim_right).trans fupd_wp

/-- A `wp` eliminates a leading `specUpdate`. -/
instance elimModal_specUpdate_wp [Add B] [L.IsLawful] [L.IsTopAbsorbing] :
    ElimModal True false io false (specUpdate rT E P) P (wp L E e Φ) (wp L E e Φ) where
  elim_modal _ := by
    simp only [Bool.false_eq_true, ↓reduceIte, intuitionisticallyIf]
    iintro ⟨HP, Hcnt⟩
    iapply specUpdate_wp
    iintro %ρ Hρ
    imod HP $$ %ρ Hρ with ⟨%ρ', %n, %Hstep, Hρ', HPv⟩
    imodintro
    iexists ρ', n
    iframe %Hstep Hρ'
    iapply Hcnt $$ HPv

/-- A `wp` eliminates a leading `specUpdateN`. -/
instance elimModal_specUpdateN_wp [Add B] [L.IsLawful] [L.IsTopAbsorbing] :
    ElimModal True false io false (specUpdateN rT n E P) P (wp L E e Φ) (wp L E e Φ) where
  elim_modal h :=
    (sep_mono_left specUpdateN_specUpdate).trans ((elimModal_specUpdate_wp (io := io)).elim_modal h)

end Wp

/-! ## Budget credits

A local `[BudgetGS B GF]` would shadow `BudgetGS.ofBudgetCredit`, so credit rules sit here. -/

section BudgetCredits
variable [AddCommMonoid B] [CanonicallyOrderedAdd B] [BudgetCreditGS B GF]
open BudgetCredit

/-- An absorbing credit proves any `wp`: the budget it sits in is absorbing too. -/
theorem wp_of_absorbing [L.IsLawful] {c : B} (hc : L.Absorbing c) {E : CoPset} {e : Exp rT}
    {Φ : Val rT → IProp GF} : ↯b c ⊢ wp L E e Φ := by
  iintro Hc
  iapply wp_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨-, -, Hb⟩
  ihave %hle := supply_bound $$ Hb Hc
  imod subset empty_subset with -
  imodintro
  iapply specCoupl_absorbing (hc.mono hle)

end BudgetCredits
end MicrometerWpGS

end ProbLang
