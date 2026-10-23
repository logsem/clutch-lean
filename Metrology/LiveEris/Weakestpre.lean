module

public import Metrology.LiveEris.GS

@[expose] public section

noncomputable section

/-!
# The LiveEris weakest precondition

The LiveEris weakest precondition as a guarded fixpoint, with checkpoints that are free on progress
or excused by a divergence credit.
-/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang
namespace LiveEris
namespace LiveWpGS

open Exp

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [LiveWpGS rT Coord GF]

/-- The states of the inner least fixpoint: a mask and an expression. -/
abbrev WpState (rT : Type _) [MeasurableSpace rT] [LawfulProbLangℝ rT] : Type _ := CoPset × Exp rT

instance : COFE (WpState rT) := ofDiscrete _
instance : Discrete (WpState rT) := ⟨id⟩

/-- The type of weakest preconditions, as a function of mask, expression and postcondition. -/
abbrev WpType (rT : Type _) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (GF : BundledGFunctors) : Type _ :=
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

/-- `stepCont` is monotone in its two continuations, the second under a `▷`. -/
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

/-- The one-step functor whose least fixpoint is the inner weakest precondition. -/
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
    obtain rfl := Discrete.discrete hd; exact .of_eq rfl

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

variable {Q : State rT → State rT → Prop} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}

/-- `lwp` is the inner least fixpoint taken at `lwp` itself. -/
theorem lwp_unfold_inner :
    lwp Q E e Φ = wpInner Q (lwp Q) E e Φ :=
  congrFun (congrFun (congrFun (fixpoint_unfold ⟨wpInner Q, ne_of_contractive _⟩) E) e) Φ

/-- `lwp` unfolds once through `wpBody`. -/
theorem lwp_unfold :
    lwp Q E e Φ = wpBody Q (lwp Q) Φ (fun s => lwp Q s.1 s.2 Φ) E e := by
  have h : bi_least_fixpoint (wpPre Q (lwp Q) Φ) = fun s : WpState rT => lwp Q s.1 s.2 Φ := by
    funext ⟨E', e'⟩
    exact lwp_unfold_inner.symm
  rw [lwp_unfold_inner]
  exact (least_fixpoint_unfold (F := wpPre Q (lwp Q) Φ) (x := ⟨E, e⟩)).trans (by rw [h])

/-- The weakest precondition of a value. -/
theorem lwp_unfold_value {v : Val rT} :
    lwp Q E (ofVal v) Φ =
      iprop(∀ (σ : State rT) (c : Coord → ℝ≥0∞),
        (stateInterp σ ∗ creditInterp c) -∗
          |={E}=> stateInterp σ ∗ creditInterp c ∗ Φ v) := by
  rw [lwp_unfold]; unfold wpBody; rw [toVal?_ofVal]

/-- The weakest precondition of a non-value expression. -/
theorem lwp_unfold_step (Hv : e.toVal? = none) :
    lwp Q E e Φ =
      iprop(∀ (σ : State rT) (c : Coord → ℝ≥0∞),
        (stateInterp σ ∗ creditInterp c) -∗
          |={E, ∅}=> glm e σ c (fun ρ c₂ =>
            stepCont Q E σ ρ.state c₂ (lwp Q E ρ.expr Φ) (lwp Q E ρ.expr Φ))) := by
  rw [lwp_unfold]; unfold wpBody; rw [Hv]

/-! ## Induction principle for the inner least fixpoint -/

/-- Induction principle for the inner least fixpoint of `lwp`. -/
theorem lwp_ind (Ψ : Exp rT → IProp GF) [NonExpansive Ψ] :
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

/-- A value satisfies the weakest precondition after an update. -/
theorem lwp_value_fupd {v : Val rT} :
    iprop(|={E}=> Φ v) ⊢ lwp Q E (ofVal v) Φ := by
  rw [lwp_unfold_value]
  iintro HΦ %σ %c ⟨Hσ, Hc⟩
  imod HΦ
  imodintro
  iframe

/-- A value satisfies the weakest precondition. -/
theorem lwp_value {v : Val rT} :
    Φ v ⊢ lwp Q E (ofVal v) Φ :=
  fupd_intro.trans lwp_value_fupd

/-- An expression that reads as a value satisfies the weakest precondition. -/
theorem lwp_value_of_toVal {v : Val rT}
    (h : e.toVal? = some v) : Φ v ⊢ lwp Q E e Φ := by
  rw [← ofVal_of_toVal_some h]
  exact lwp_value

/-- An expression that reads as a value satisfies it after an update. -/
theorem lwp_value_fupd_of_toVal {v : Val rT}
    (h : e.toVal? = some v) : iprop(|={E}=> Φ v) ⊢ lwp Q E e Φ := by
  rw [← ofVal_of_toVal_some h]
  exact lwp_value_fupd

/-- The weakest precondition of a value gives back the postcondition after an update. -/
theorem lwp_value_inv {v : Val rT} {σ : State rT} {c : Coord → ℝ≥0∞} :
    iprop(lwp Q E (ofVal v) Φ ∗ stateInterp σ ∗ creditInterp c) ⊢
      iprop(|={E}=> stateInterp σ ∗ creditInterp c ∗ Φ v) := by
  rw [lwp_unfold_value]
  iintro ⟨HW, Hσ, Hc⟩
  iapply HW $$ %σ %c [$Hσ $Hc]

/-- `lwp` absorbs an update that returns the state and credit interpretations. -/
theorem lwp_of_frame_fupd :
    iprop(∀ (σ : State rT) (c : Coord → ℝ≥0∞),
        stateInterp σ ∗ creditInterp c -∗
          |={E}=> stateInterp σ ∗ creditInterp c ∗ lwp Q E e Φ)
      ⊢ lwp Q E e Φ := by
  iintro HF
  cases htv : e.toVal? with
  | some v =>
    obtain rfl : e = ofVal v := (ofVal_of_toVal_some htv).symm
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
theorem lwp_of_credit_decrease (Hnv : e.toVal? = none) :
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

/-- `lwp` absorbs a leading update. -/
theorem fupd_lwp :
    iprop(|={E}=> lwp Q E e Φ) ⊢ lwp Q E e Φ := by
  iintro HW
  iapply lwp_of_frame_fupd
  iintro %σ %c ⟨Hσ, Hc⟩
  imod HW
  imodintro
  iframe

/-! ## Structural rules -/

/-- The statement of `lwp_strong_mono`, for Löb induction. -/
abbrev wpStrongMonoStmt (Q : State rT → State rT → Prop) (E : CoPset)
    (Φ : Val rT → IProp GF) : IProp GF :=
  iprop(∀ (e : Exp rT) (Ψ : Val rT → IProp GF),
    lwp Q E e Φ -∗ (∀ v, Φ v ={E}=∗ Ψ v) -∗ lwp Q E e Ψ)

/-- `lwp` is monotone in its postcondition, under an update. -/
theorem lwp_strong_mono {Ψ : Val rT → IProp GF} :
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

/-- `lwp` is monotone in its postcondition, under a wand. -/
theorem lwp_wand {Ψ : Val rT → IProp GF} :
    iprop(lwp Q E e Φ ∗ (∀ v, Φ v -∗ Ψ v)) ⊢ lwp Q E e Ψ := by
  iintro ⟨HW, HΦΨ⟩
  iapply lwp_strong_mono
  iframe HW
  iintro %v HΦv !>
  iapply HΦΨ $$ HΦv

/-- `lwp` is monotone in its postcondition. -/
theorem lwp_mono {Ψ : Val rT → IProp GF} (HΦ : ∀ v, Φ v ⊢ Ψ v) :
    lwp Q E e Φ ⊢ lwp Q E e Ψ := by
  iintro HW
  iapply lwp_wand
  iframe HW
  iintro %v HΦv
  iapply HΦ $$ HΦv

/-- `lwp` absorbs an update in its postcondition. -/
theorem lwp_fupd :
    lwp Q E e (fun v => iprop(|={E}=> Φ v)) ⊢ lwp Q E e Φ := by
  iintro HW
  iapply lwp_strong_mono
  iframe HW
  iintro %v HΦ
  iexact HΦ

/-- A resource on the left frames through `lwp`. -/
theorem lwp_frame_left {R : IProp GF} :
    iprop(R ∗ lwp Q E e Φ) ⊢ lwp Q E e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨HR, HW⟩
  iapply lwp_wand
  iframe HW
  iintro %v HΦv
  iframe

/-- A resource on the right frames through `lwp`. -/
theorem lwp_frame_right {R : IProp GF} :
    iprop(lwp Q E e Φ ∗ R) ⊢ lwp Q E e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨HW, HR⟩
  iapply lwp_wand
  iframe HW
  iintro %v HΦv
  iframe

/-! ## Bind -/

/-- The statement of `lwp_bind`, for Löb induction. -/
abbrev wpBindStmt (Q : State rT → State rT → Prop) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : IProp GF :=
  iprop(∀ (e : Exp rT), lwp Q E e (fun v => lwp Q E (K.fill (ofVal v)) Φ) -∗
    lwp Q E (K.fill e) Φ)

/-- Bind rule: the weakest precondition of `e` in the evaluation context `K`. -/
theorem lwp_bind {K : Ectx rT} :
    lwp Q E e (fun v => lwp Q E (K.fill (ofVal v)) Φ) ⊢ lwp Q E (K.fill e) Φ := by
  have Hloeb : ⊢ wpBindStmt Q K E Φ := by
    iapply loeb_wand_intuitionistically
    iintro !> #IH %e' HW
    let : NonExpansive (fun e'' => lwp Q E (K.fill e'') Φ) := nonExpansive_of_discrete_leibniz _
    iapply (lwp_ind (Q := Q) (E := E) (Φ := fun v => lwp Q E (K.fill (ofVal v)) Φ)
      (fun e'' => lwp Q E (K.fill e'') Φ)) $$ [] HW
    iintro !> %e'' HF
    cases htv : e''.toVal? with
    | some v =>
      obtain rfl : e'' = ofVal v := (ofVal_of_toVal_some htv).symm
      iapply lwp_of_frame_fupd
      iintro %σ %c Hσc
      ispecialize HF $$ %σ %c Hσc
      simp only [toVal?_ofVal]
      iexact HF
    | none =>
      have hKtv : (K.fill e'').toVal? = none :=
        toVal?_eq_none.mpr fun hKv => (toVal?_eq_none.mp htv) (Ectx.fill_isValue hKv)
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
