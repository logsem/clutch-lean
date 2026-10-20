module

public import Metrology.Micrometer.Wp

/-! Structural rules of `wp`: bind, spec updates, framing, credits and proof-mode instances. -/

@[expose] public section

open Std Iris Iris.BI Iris.ProofMode OFE COFE ProbLang GradedLifting

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]

section Wp
variable [BudgetGS B GF]

/-! ## WP — structural lemmas -/

variable (L) in
/-- The statement of `wp_bind` at the context `K`, proved by Löb induction. -/
noncomputable abbrev wpBindStmt (K : Ectx rT) : IProp GF := iprop%
  ∀ E e Φ, wp L E e (fun v => wp L E (K.fill (Exp.ofVal v)) Φ) -∗ wp L E (K.fill e) Φ

theorem wp_bind [Add B] [L.IsLawful] [L.IsTopAbsorbing] {K : Ectx rT} {E : CoPset}
    {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp L E e (fun v => wp L E (K.fill (Exp.ofVal v)) Φ) ⊢ wp L E (K.fill e) Φ := by
  have Hloeb : ⊢@{IProp GF} wpBindStmt L K := by
    iapply loeb_wand
    iintro !> IH %E' %e' %Φ' HW
    iapply wp_unfold
    iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
    imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with HW'
    imodintro
    iapply specCoupl_bind Std.LawfulSet.subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %b₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      iapply fupd_specCoupl
      rw [show e' = Exp.ofVal v from (Exp.ofVal_of_toVal_some htv).symm]
      imod HBody with ⟨Hσ', Hs', Hb', HInner⟩
      imod wp_unfold_mp $$ HInner %σ₂ %ρ₂.expr %ρ₂.state %b₂ [$Hσ' $Hs' $Hb'] with HInner'
      imodintro
      iexact HInner'
    | none =>
      have hv : ¬ e'.isValue := Exp.toVal?_eq_none.mp htv
      have hvKfill : ¬ (K.fill e').isValue := fun hKv => hv (Ectx.fill_isValue hKv)
      have hKfillnone : (K.fill e').toVal? = none := Exp.toVal?_eq_none.mpr hvKfill
      iapply specCoupl_ret
      simp only [hKfillnone]
      iapply progCoupl_ctx_bind hv
      iapply progCoupl_mono (Z₁ := wpProgBody L E' fun v => wp L E' (K.fill (Exp.ofVal v)) Φ')
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater !>
      iapply specCoupl_mono_spatial
      iframe HLater
      iintro %σ₄ %ρ₄ %b₄ HF
      imod HF with ⟨Hσ', Hs', Hb', HwpInner⟩
      imodintro
      iframe Hσ' Hs' Hb'
      iapply IH $$ %E' %e₃ %Φ' HwpInner
  iapply Hloeb $$ %E %e %Φ

-- TODO: `wp_atomic` (for atomic `e`, an inner `|={E2, E1}=>` can be absorbed), stated with the
-- `Atomic'` predicate rather than a typeclass.

/-- A spec update before a `wp` can be absorbed into it. -/
theorem specUpdate_wp [Add B] [L.IsLawful] [L.IsTopAbsorbing] {E : CoPset} {e : Exp rT}
    {Φ : Val rT → IProp GF} :
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

theorem wp_specUpdate [Add B] [L.IsLawful] [L.IsTopAbsorbing] {E : CoPset} {e : Exp rT}
    {Φ : Val rT → IProp GF} :
    wp L E e (fun v => specUpdate rT E (Φ v)) ⊢ wp L E e Φ := by
  have Hloeb : ⊢@{IProp GF} wpSpecUpdateStmt L (rT := rT) := by
    iapply loeb_wand
    iintro !> IH %E' %e' %Φ' HW
    iapply wp_unfold
    iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
    imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with HW'
    imodintro
    iapply specCoupl_bind Std.LawfulSet.subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %b₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      iapply fupd_specCoupl
      imod HBody with ⟨Hσ', Hs', Hb', HUpd⟩
      imod HUpd $$ %ρ₂ Hs' with ⟨%ρ₃, %n, %Hstep, Hs'', HΦv⟩
      cases ρ₃ with
      | mk e₃' σ₃' =>
        imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
        imodintro
        iapply specCoupl_steps_det Hstep
        iapply specCoupl_ret
        imod Hclose
        imodintro
        iframe
    | none =>
      iapply specCoupl_ret
      iapply progCoupl_mono (Z₁ := wpProgBody L E' fun v => specUpdate rT E' (Φ' v))
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater !>
      iapply specCoupl_mono_spatial
      iframe HLater
      iintro %σ₄ %ρ₄ %b₄ HF
      imod HF with ⟨Hσ', Hs', Hb', HwpInner⟩
      imodintro
      iframe Hσ' Hs' Hb'
      iapply IH $$ %E' %e₃ %Φ' HwpInner
  iapply Hloeb $$ %E %e %Φ

/-! ## WP — framing lemmas -/

variable (L) in
/-- The statement of `wp_frame_l`, proved by Löb induction. -/
noncomputable abbrev wpFrameLStmt : IProp GF := iprop%
  ∀ E (e : Exp rT) R Φ, R -∗ wp L E e Φ -∗ wp L E e fun v => iprop(R ∗ Φ v)

theorem wp_frame_l {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop% R ∗ wp L E e Φ ⊢ wp L E e fun v => iprop(R ∗ Φ v) := by
  have Hloeb : ⊢@{IProp GF} wpFrameLStmt L (rT := rT) := by
    iapply loeb_wand
    iintro !> IH %E' %e' %R' %Φ' HR HW
    iapply wp_unfold
    iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
    imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with HW'
    imodintro
    iapply specCoupl_mono_spatial
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
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater !>
      iapply specCoupl_mono_spatial
      iframe HLater
      iintro %σ₄ %ρ₄ %b₄ HFinal
      imod HFinal with ⟨Hσ', Hs', Hb', HwpInner⟩
      imodintro
      iframe
      iapply IH $$ %E' %e₃ %R' %Φ' HR HwpInner
  iintro ⟨HR, HW⟩
  iapply Hloeb $$ %E %e %R %Φ HR HW

theorem wp_frame_r {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop% wp L E e Φ ∗ R ⊢ wp L E e fun v => iprop(Φ v ∗ R) :=
  (sep_comm.1.trans wp_frame_l).trans (wp_mono fun _ => sep_comm.1)

theorem wp_frame_wand {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop% R ∗ wp L E e (fun v => iprop(R -∗ Φ v)) ⊢ wp L E e Φ :=
  wp_frame_l.trans (wp_mono fun _ => wand_elim_right)

theorem wp_step_fupd {E1 E2 : CoPset} {e : Exp rT} {P : IProp GF} {Φ : Val rT → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) : iprop%
    (|={E1, E2}=> ▷ |={E2, E1}=> P) ∗ wp L E2 e (fun v => iprop(P -∗ Φ v)) ⊢ wp L E1 e Φ := by
  iintro ⟨HR, HW⟩
  iapply wp_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod HR
  imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with HW'
  imodintro
  iapply specCoupl_mono_spatial
  iframe HW'
  iintro %σ₂ %ρ₂ %b₂ HBody
  simp only [hv]
  iapply progCoupl_mono
  iframe HBody
  iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater !>
  iapply specCoupl_mono_spatial
  iframe HLater
  iintro %σ₄ %ρ₄ %b₄ HFinal
  imod HFinal with ⟨Hσ', Hs', Hb', HwpInner⟩
  imod HR
  imodintro
  iframe Hσ' Hs' Hb'
  iapply wp_mask_mono HE
  ihave HwpInner := wp_frame_l $$ [$HR $HwpInner]
  iapply wp_wand
  iframe HwpInner
  iintro !> %v ⟨HP, HWand⟩
  iapply HWand $$ HP

theorem wp_frame_step_l {E1 E2 : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) : iprop%
    (|={E1, E2}=> ▷ |={E2, E1}=> R) ∗ wp L E2 e Φ ⊢ wp L E1 e fun v => iprop(R ∗ Φ v) := by
  iintro ⟨HR, HW⟩
  iapply wp_step_fupd HE hv
  iframe HR
  iapply wp_wand
  iframe HW
  iintro !> %v HΦ HR'
  iframe

theorem wp_frame_step_r {E1 E2 : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) : iprop%
    wp L E2 e Φ ∗ (|={E1, E2}=> ▷ |={E2, E1}=> R) ⊢ wp L E1 e fun v => iprop(Φ v ∗ R) := by
  iintro ⟨HW, HR⟩
  iapply wp_step_fupd HE hv
  iframe HR
  iapply wp_wand
  iframe HW
  iintro !> %v HΦ HR'
  iframe

/-- `wp` is closed under `◇`. -/
instance isExcept0_wp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    IsExcept0 (wp L E e Φ) where
  is_except0 := (except0_mono fupd_intro).trans (BIFUpdate.except0.trans fupd_wp)

/-- Framing through `wp` frames the postcondition. -/
instance frame_wp {p : Bool} {E : CoPset} {e : Exp rT} {R : IProp GF}
    {Φ Ψ : Val rT → IProp GF} [inst : ∀ v, Frame p R (Φ v) (Ψ v)] :
    Frame p R (wp L E e Φ) (wp L E e Ψ) where
  frame := wp_frame_l.trans (wp_mono fun v => (inst v).frame)

/-- A `wp` absorbs a leading `|={E}=>`. -/
instance addModal_fupd_wp {E : CoPset} {e : Exp rT} {P : IProp GF} {Φ : Val rT → IProp GF} :
    AddModal iprop(|={E}=> P) P (wp L E e Φ) where
  add_modal := fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

/-- A `wp` eliminates a leading `|==>`. -/
instance elimModal_bupd_wp {p : Bool} {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|==> P) P (wp L E e Φ) (wp L E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    (sep_mono_left BIUpdateFUpdate.fupd_of_bupd).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

/-- A `wp` eliminates a leading `|={E}=>`. -/
instance elimModal_fupd_wp {p : Bool} {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|={E}=> P) P (wp L E e Φ) (wp L E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

/-- A `wp` eliminates a leading `specUpdate`. -/
instance elimModal_specUpdate_wp [Add B] [L.IsLawful] [L.IsTopAbsorbing] {io : InOut}
    {E : CoPset} {e : Exp rT} {P : IProp GF} {Φ : Val rT → IProp GF} :
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
instance elimModal_specUpdateN_wp [Add B] [L.IsLawful] [L.IsTopAbsorbing] {n : Nat}
    {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF} {Φ : Val rT → IProp GF} :
    ElimModal True false io false (specUpdateN rT n E P) P (wp L E e Φ) (wp L E e Φ) where
  elim_modal h :=
    (sep_mono_left specUpdateN_specUpdate).trans ((elimModal_specUpdate_wp (io := io)).elim_modal h)

end Wp

/-! ## Budget credits

A local `[BudgetGS B GF]` would shadow `BudgetGS.ofBudgetCredit`, so credit rules sit here. -/

section BudgetCredits
variable [AddCommMonoid B] [CanonicallyOrderedAdd B] [BudgetCreditGS B GF]

/-- An absorbing credit proves any `wp`: the budget it sits in is absorbing too. -/
theorem wp_of_absorbing [L.IsLawful] {c : B} (hc : L.Absorbing c) {E : CoPset} {e : Exp rT}
    {Φ : Val rT → IProp GF} : ↯b c ⊢ wp L E e Φ := by
  iintro Hc
  iapply wp_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨-, -, Hb⟩
  ihave %hle := BudgetCredit.supply_bound $$ Hb Hc
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with -
  imodintro
  iapply specCoupl_absorbing (hc.mono hle)

end BudgetCredits
end MicrometerWpGS

end ProbLang
