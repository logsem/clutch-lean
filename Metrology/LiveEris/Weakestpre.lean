module

public import Metrology.LiveEris.GS

@[expose] public section

noncomputable section

/-!
# The LiveEris weakest precondition

`lwp Q E e Φ` is a guarded fixpoint around a least fixpoint. Each step either continues inside the
least fixpoint, or crosses a `▷` at a *checkpoint*. A checkpoint is free when the step makes progress
(`Q` holds of the pre- and post-step states), and excused when the branch holds a full divergence
credit. A run that never terminates must cross infinitely many checkpoints, so it either makes
progress infinitely often or was written off for progress.
-/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang
namespace LiveEris
namespace LiveWpGS

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [LiveWpGS rT Coord GF]

abbrev WpState (rT : Type _) [LawfulProbLangℝ rT] : Type _ := CoPset × Exp rT

instance : COFE (WpState rT) := COFE.ofDiscrete _
instance : OFE.Discrete (WpState rT) := ⟨id⟩

abbrev WpType (rT : Type _) [LawfulProbLangℝ rT] (GF : BundledGFunctors) : Type _ :=
  CoPset → Exp rT → (Val rT → IProp GF) → IProp GF

/-- A step from state `σ` to `σ₂`, leaving credits `c`, may cross a `▷`: it makes progress, or the
branch is written off for progress. -/
def Checkpoint (Q : State rT → State rT → Prop) (σ σ₂ : State rT) (c : Coord → ℝ≥0∞) : Prop :=
  Q σ σ₂ ∨ 1 ≤ c .tot

/-- What follows a step from state `σ` to `σ₂` that leaves credits `c₂`: close the mask and continue
with `P`, or cross a checkpoint and continue with `R` one `▷` later. -/
abbrev stepCont (Q : State rT → State rT → Prop) (E : CoPset) (σ σ₂ : State rT)
    (c₂ : Coord → ℝ≥0∞) (P R : IProp GF) : IProp GF :=
  iprop((|={∅, E}=> stateInterp σ₂ ∗ creditInterp c₂ ∗ P) ∨
    (⌜Checkpoint Q σ σ₂ c₂⌝ ∗ ▷ |={∅, E}=> stateInterp σ₂ ∗ creditInterp c₂ ∗ R))

/-- The body of the inner least fixpoint at mask `E` and expression `e`: `X` is the recursion
variable of the least fixpoint, `W` the guarded one. -/
abbrev wpBody (Q : State rT → State rT → Prop) (W : WpType rT GF) (Φ : Val rT → IProp GF)
    (X : WpState rT → IProp GF) (E : CoPset) (e : Exp rT) : IProp GF :=
  iprop(∀ (σ : State rT) (c : Coord → ℝ≥0∞),
    (stateInterp σ ∗ creditInterp c) -∗
      match e.toVal? with
      | some v => iprop(|={E}=> stateInterp σ ∗ creditInterp c ∗ Φ v)
      | none => iprop(|={E, ∅}=> glm e σ c (fun ρ c₂ =>
          stepCont Q E σ ρ.state c₂ (X ⟨E, ρ.expr⟩) (W E ρ.expr Φ))))

theorem stepCont_mono {Q : State rT → State rT → Prop} {E : CoPset} {σ σ₂ : State rT}
    {c₂ : Coord → ℝ≥0∞} {P P' R R' : IProp GF} :
    iprop((P -∗ P') ∧ ▷ (R -∗ R')) ∗ stepCont Q E σ σ₂ c₂ P R ⊢ stepCont Q E σ σ₂ c₂ P' R' := by
  iintro ⟨HPR, HC⟩
  icases HC with ⟨HP | ⟨%Hck, HR⟩⟩
  · ileft
    imod HP with ⟨Hσ, Hc, HP⟩
    imodintro
    iframe Hσ Hc
    iapply HPR $$ HP
  · iright
    iframe %Hck
    inext
    imod HR with ⟨Hσ, Hc, HR⟩
    imodintro
    iframe Hσ Hc
    iapply HPR $$ HR

abbrev wpPre (Q : State rT → State rT → Prop) (W : WpType rT GF) (Φ : Val rT → IProp GF)
    (X : WpState rT → IProp GF) : WpState rT → IProp GF :=
  fun s => wpBody Q W Φ X s.1 s.2

instance wpPre_mono {Q : State rT → State rT → Prop} {W : WpType rT GF}
    {Φ : Val rT → IProp GF} : BIMonoPred (wpPre Q W Φ) where
  mono_pred {X Y _ _} := by
    iintro #Hwand %s Hs
    obtain ⟨E, e⟩ := s
    iintro %σ %c Hσc
    ispecialize Hs $$ %σ %c Hσc
    cases htv : e.toVal? with
    | some v => iexact Hs
    | none =>
      imod Hs with HG
      imodintro
      iapply glm_mono_pred
      iframe HG
      iintro !> %ρ %c' HC
      iapply stepCont_mono
      iframe HC
      isplit
      · iapply Hwand
      · inext; iapply wand_rfl
  mono_pred_ne.ne {_ s s'} hd := by
    obtain rfl := eq_of_dist_discrete_leibniz hd; exact .of_eq rfl

/-- The inner least fixpoint, for a fixed guarded recursion variable `W`. -/
abbrev wpInner (Q : State rT → State rT → Prop) (W : WpType rT GF) : WpType rT GF :=
  fun E e Φ => bi_least_fixpoint (wpPre Q W Φ) ⟨E, e⟩

instance wpInner_contractive {Q : State rT → State rT → Prop} :
    Contractive (wpInner (GF := GF) Q) where
  distLater_dist {_ W W'} HW E e Φ := by
    refine least_fixpoint_ne_outer (fun _ s => ?_) (.of_eq rfl)
    obtain ⟨E', e'⟩ := s
    refine forall_ne fun σ => forall_ne fun _ => wand_ne.ne (.of_eq rfl) ?_
    cases e'.toVal? with
    | some v => exact .of_eq rfl
    | none =>
      refine BIFUpdate.ne.ne <| glm_ne fun ρ _ => or_ne.ne (.of_eq rfl) <|
        sep_ne.ne (.of_eq rfl) ?_
      apply Contractive.distLater_dist
      intro m Hm
      exact BIFUpdate.ne.ne <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
        HW m Hm E' ρ.expr Φ

/-- The LiveEris weakest precondition with progress predicate `Q`. -/
def lwp (Q : State rT → State rT → Prop) (E : CoPset) (e : Exp rT)
    (Φ : Val rT → IProp GF) : IProp GF :=
  fixpoint (wpInner Q) E e Φ

variable {Q : State rT → State rT → Prop}

theorem lwp_unfold_inner {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    lwp Q E e Φ = wpInner Q (lwp Q) E e Φ :=
  congrFun (congrFun (congrFun (fixpoint_unfold ⟨wpInner Q, OFE.ne_of_contractive _⟩) E) e) Φ

theorem lwp_unfold {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    lwp Q E e Φ = wpBody Q (lwp Q) Φ (fun s => lwp Q s.1 s.2 Φ) E e := by
  have h : bi_least_fixpoint (wpPre Q (lwp Q) Φ) = fun s : WpState rT => lwp Q s.1 s.2 Φ := by
    funext ⟨E', e'⟩
    exact lwp_unfold_inner.symm
  rw [lwp_unfold_inner]
  exact (least_fixpoint_unfold (F := wpPre Q (lwp Q) Φ) (x := ⟨E, e⟩)).trans (by rw [h])

theorem lwp_unfold_value {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    lwp Q E (Exp.ofVal v) Φ =
      iprop(∀ (σ : State rT) (c : Coord → ℝ≥0∞),
        (stateInterp σ ∗ creditInterp c) -∗
          |={E}=> stateInterp σ ∗ creditInterp c ∗ Φ v) := by
  rw [lwp_unfold]; unfold wpBody; rw [Exp.toVal?_ofVal]

theorem lwp_unfold_step {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e.toVal? = none) :
    lwp Q E e Φ =
      iprop(∀ (σ : State rT) (c : Coord → ℝ≥0∞),
        (stateInterp σ ∗ creditInterp c) -∗
          |={E, ∅}=> glm e σ c (fun ρ c₂ =>
            stepCont Q E σ ρ.state c₂ (lwp Q E ρ.expr Φ) (lwp Q E ρ.expr Φ))) := by
  rw [lwp_unfold]; unfold wpBody; rw [Hv]

/-! ## Induction principle for the inner least fixpoint -/

theorem lwp_ind {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Ψ : Exp rT → IProp GF) [NonExpansive Ψ] :
    iprop(□ (∀ e', wpPre Q (lwp Q) Φ (fun s => Ψ s.2) ⟨E, e'⟩ -∗ Ψ e')) ⊢
      (lwp Q E e Φ -∗ Ψ e) := by
  rw [lwp_unfold_inner]
  iintro #HInd HW
  let Ψ' : WpState rT → IProp GF := fun s => iprop(⌜s.1 = E⌝ -∗ Ψ s.2)
  let : NonExpansive Ψ' := nonExpansive_of_discrete_leibniz Ψ'
  ihave HΨ' : iprop(Ψ' ⟨E, e⟩) $$ [HW]
  · iapply (least_fixpoint_iter (F := wpPre Q (lwp Q) Φ) (Φ := Ψ'))
    · iintro !> %s HF
      obtain ⟨E', e'⟩ := s
      iintro %rfl
      iapply HInd
      iintro %σ %c Hσc
      ispecialize HF $$ %σ %c Hσc
      cases htv : e'.toVal? with
      | some v => iexact HF
      | none =>
        imod HF with HG
        imodintro
        iapply glm_mono_pred
        iframe HG
        iintro !> %ρ %c' HC
        iapply stepCont_mono
        iframe HC
        isplit
        · iintro HX; iapply HX $$ %rfl
        · inext; iapply wand_rfl
    · iexact HW
  iapply HΨ'
  ipureintro
  rfl

/-! ## Value rules -/

theorem lwp_value_fupd {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> Φ v) ⊢ lwp Q E (Exp.ofVal v) Φ := by
  rw [lwp_unfold_value]
  iintro HΦ %σ %c ⟨Hσ, Hc⟩
  imod HΦ
  imodintro
  iframe

theorem lwp_value {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    Φ v ⊢ lwp Q E (Exp.ofVal v) Φ :=
  fupd_intro.trans lwp_value_fupd

theorem lwp_value_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (h : e.toVal? = some v) : Φ v ⊢ lwp Q E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact lwp_value

theorem lwp_value_fupd_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (h : e.toVal? = some v) : iprop(|={E}=> Φ v) ⊢ lwp Q E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact lwp_value_fupd

theorem lwp_value_inv {E : CoPset} {v : Val rT} {σ : State rT} {c : Coord → ℝ≥0∞}
    {Φ : Val rT → IProp GF} :
    iprop(lwp Q E (Exp.ofVal v) Φ ∗ stateInterp σ ∗ creditInterp c) ⊢
      iprop(|={E}=> stateInterp σ ∗ creditInterp c ∗ Φ v) := by
  rw [lwp_unfold_value]
  iintro ⟨HW, Hσ, Hc⟩
  iapply HW $$ %σ %c [$Hσ $Hc]

/-- `lwp` absorbs an update that returns the state and credit interpretations. -/
theorem lwp_of_frame_fupd {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(∀ (σ : State rT) (c : Coord → ℝ≥0∞),
        stateInterp σ ∗ creditInterp c -∗
          |={E}=> stateInterp σ ∗ creditInterp c ∗ lwp Q E e Φ)
      ⊢ lwp Q E e Φ := by
  iintro HF
  cases htv : e.toVal? with
  | some v =>
    obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
    rw [lwp_unfold_value]
    iintro %σ %c Hσc
    imod HF $$ %σ %c Hσc with ⟨Hσ', Hc', HW⟩
    iapply HW $$ %σ %c [$Hσ' $Hc']
  | none =>
    rw [lwp_unfold_step htv]
    iintro %σ %c Hσc
    imod HF $$ %σ %c Hσc with ⟨Hσ', Hc', HW⟩
    iapply HW $$ %σ %c [$Hσ' $Hc']

/-- Before a step, `lwp` absorbs an update that shrinks the credit vector. -/
theorem lwp_of_credit_decrease {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) :
    iprop(∀ (σ : State rT) (c : Coord → ℝ≥0∞),
        stateInterp σ ∗ creditInterp c -∗
          |={E}=> ∃ c' : Coord → ℝ≥0∞, ⌜c' ≤ c⌝ ∗ stateInterp σ ∗ creditInterp c' ∗ lwp Q E e Φ)
      ⊢ lwp Q E e Φ := by
  rw [lwp_unfold_step Hnv]
  iintro HF %σ %c Hσc
  imod HF $$ %σ %c Hσc with ⟨%c', %Hle, Hσ', Hc', HW⟩
  imod HW $$ %σ %c' [$Hσ' $Hc'] with HG
  imodintro
  iapply glm_mono_grading Hle $$ HG

theorem fupd_lwp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> lwp Q E e Φ) ⊢ lwp Q E e Φ := by
  iintro HW
  iapply lwp_of_frame_fupd
  iintro %σ %c ⟨Hσ, Hc⟩
  imod HW
  imodintro
  iframe

/-! ## Structural rules -/

abbrev wpStrongMonoStmt (Q : State rT → State rT → Prop) (E : CoPset)
    (Φ : Val rT → IProp GF) : IProp GF :=
  iprop(∀ (e : Exp rT) (Ψ : Val rT → IProp GF),
    lwp Q E e Φ -∗ (∀ v, Φ v ={E}=∗ Ψ v) -∗ lwp Q E e Ψ)

theorem lwp_strong_mono {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop(lwp Q E e Φ ∗ (∀ v, Φ v ={E}=∗ Ψ v)) ⊢ lwp Q E e Ψ := by
  have Hloeb : ⊢ wpStrongMonoStmt Q E Φ := by
    iapply loeb_wand_intuitionistically
    iintro !> #IH %e' %Ψ' HW
    let P : Exp rT → IProp GF := fun e => iprop(
      ∀ (Ψ : Val rT → IProp GF), (∀ v, Φ v ={E}=∗ Ψ v) -∗ lwp Q E e Ψ)
    let : NonExpansive P := nonExpansive_of_discrete_leibniz P
    ihave HP : iprop(P e') $$ [HW]
    · iapply lwp_ind P $$ [] HW
      iintro !> %e HF %Ψ Hwand
      rw [lwp_unfold]
      iintro %σ %c Hσc
      ispecialize HF $$ %σ %c Hσc
      cases htv : e.toVal? with
      | some v =>
        imod HF with ⟨Hσ', Hc', HΦv⟩
        imod Hwand $$ %v HΦv with HΨv
        imodintro
        iframe
      | none =>
        imod HF with HG
        imodintro
        iapply glm_strong_mono
        iframe HG
        iintro %ρ %c₂ HC
        iapply stepCont_mono
        iframe HC
        isplit
        · iintro HP; iapply HP $$ %Ψ Hwand
        · inext; iintro HW'; iapply IH $$ %ρ.expr %Ψ HW' Hwand
    iapply HP
  iintro ⟨HW, Hwand⟩
  iapply Hloeb $$ %e %Ψ HW Hwand

theorem lwp_wand {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop(lwp Q E e Φ ∗ (∀ v, Φ v -∗ Ψ v)) ⊢ lwp Q E e Ψ := by
  iintro ⟨HW, HΦΨ⟩
  iapply lwp_strong_mono
  iframe HW
  iintro %v HΦv !>
  iapply HΦΨ $$ HΦv

theorem lwp_mono {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} (HΦ : ∀ v, Φ v ⊢ Ψ v) :
    lwp Q E e Φ ⊢ lwp Q E e Ψ := by
  iintro HW
  iapply lwp_wand
  iframe HW
  iintro %v HΦv
  iapply HΦ $$ HΦv

theorem lwp_fupd {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    lwp Q E e (fun v => iprop(|={E}=> Φ v)) ⊢ lwp Q E e Φ := by
  iintro HW
  iapply lwp_strong_mono
  iframe HW
  iintro %v HΦ
  iexact HΦ

theorem lwp_frame_left {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop(R ∗ lwp Q E e Φ) ⊢ lwp Q E e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨HR, HW⟩
  iapply lwp_wand
  iframe HW
  iintro %v HΦv
  iframe

theorem lwp_frame_right {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop(lwp Q E e Φ ∗ R) ⊢ lwp Q E e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨HW, HR⟩
  iapply lwp_wand
  iframe HW
  iintro %v HΦv
  iframe

/-! ## Bind -/

abbrev wpBindStmt (Q : State rT → State rT → Prop) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : IProp GF :=
  iprop(∀ (e : Exp rT), lwp Q E e (fun v => lwp Q E (K.fill (Exp.ofVal v)) Φ) -∗
    lwp Q E (K.fill e) Φ)

theorem lwp_bind {K : Ectx rT} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    lwp Q E e (fun v => lwp Q E (K.fill (Exp.ofVal v)) Φ) ⊢ lwp Q E (K.fill e) Φ := by
  have Hloeb : ⊢ wpBindStmt Q K E Φ := by
    iapply loeb_wand_intuitionistically
    iintro !> #IH %e' HW
    let : NonExpansive (fun e'' => lwp Q E (K.fill e'') Φ) := nonExpansive_of_discrete_leibniz _
    iapply (lwp_ind (Q := Q) (E := E) (Φ := fun v => lwp Q E (K.fill (Exp.ofVal v)) Φ)
      (fun e'' => lwp Q E (K.fill e'') Φ)) $$ [] HW
    iintro !> %e'' HF
    cases htv : e''.toVal? with
    | some v =>
      obtain rfl : e'' = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
      iapply lwp_of_frame_fupd
      iintro %σ %c Hσc
      ispecialize HF $$ %σ %c Hσc
      simp only [Exp.toVal?_ofVal]
      iexact HF
    | none =>
      have hKtv : (K.fill e'').toVal? = none :=
        Exp.toVal?_eq_none.mpr fun hKv => (Exp.toVal?_eq_none.mp htv) (Ectx.fill_isValue hKv)
      rw [lwp_unfold_step hKtv]
      iintro %σ %c Hσc
      ispecialize HF $$ %σ %c Hσc
      simp only [htv]
      imod HF with HG
      imodintro
      iapply glm_bind
      iapply glm_strong_mono
      iframe HG
      iintro %ρ %c₂ HC
      iapply stepCont_mono
      iframe HC
      isplit
      · iapply wand_rfl
      · inext; iintro HW'; iapply IH $$ %ρ.expr HW'
  iapply Hloeb

end LiveWpGS
end LiveEris
end ProbLang
