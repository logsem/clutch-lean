module

public import Metrology.TotalEris.Glm
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

/-!
# Total weakest precondition

`tglWp` (Eris `tgl_wp`): total weakest precondition over the error-graded modality `glm'`, with
value, bind, monotonicity and frame rules. Micrometer does not use it.
-/

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

namespace TotalEris
namespace ErisWpGS

variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

instance : COFE (Exp rT) := COFE.ofDiscrete _
instance : OFE.Discrete (Exp rT) := ⟨id⟩

/-- The index of the weakest-precondition fixpoint: a mask and an expression. -/
abbrev TglWpState (rT : Type _) : Type _ := CoPset × Exp rT

instance : COFE (TglWpState rT) := COFE.ofDiscrete _
instance : OFE.Discrete (TglWpState rT) := ⟨id⟩

/-- One unfolding of `tglWp`: a value satisfies `Φ`; a non-value takes a `glm'` step. -/
abbrev tglWpPre (wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  iprop(∀ (σ₁ : State rT) (ε₁ : ENNReal),
    (stateInterp σ₁ ∗ errInterp (rT := rT) ε₁) -∗
      match e₁.toVal? with
      | some v => iprop(|={E}=>
          stateInterp σ₁ ∗ errInterp (rT := rT) ε₁ ∗ Φ v)
      | none => iprop(|={E, ∅}=>
          glm' e₁ σ₁ ε₁ (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ wp E ρ.expr Φ))))

private theorem tglWpPre_mono {wp₁ wp₂ : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF}
    {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    □ (∀ e', wp₁ E e' Φ -∗ wp₂ E e' Φ) ⊢ tglWpPre wp₁ E e Φ -∗ tglWpPre wp₂ E e Φ := by
  iintro #Hwand Hs
  unfold tglWpPre
  iintro %σ %ε ⟨Hσ, Hε⟩
  ispecialize Hs $$ %σ %ε [$Hσ $Hε]
  cases e.toVal? with
  | some v => iexact Hs
  | none =>
    imod Hs with HG
    imodintro
    iapply glm'_mono_pred
    iframe HG
    iintro !> %ρ %ε' HC
    imod HC with ⟨Hσ', Hε', HW⟩
    imodintro
    iframe Hσ' Hε'
    iapply Hwand $$ HW

/-- `tglWpPre` with the postcondition fixed, as a functional on `TglWpState`.
`Φ` never changes across recursive calls of `tglWpPre`, so the fixpoint can be taken over (mask,
expression) alone. -/
abbrev tglWpPreFixed (Φ : Val rT → IProp GF)
    (wp : TglWpState rT → IProp GF) : TglWpState rT → IProp GF :=
  fun ⟨E, e⟩ => tglWpPre (fun E' e' _ => wp ⟨E', e'⟩) E e Φ

/-- `tglWpPreFixed` is monotone, so its least fixpoint exists. -/
instance tglWpPreFixed_mono {Φ : Val rT → IProp GF} :
    BIMonoPred (tglWpPreFixed Φ) where
  mono_pred {wp1 wp2 _ _} := by
    iintro #Hwand %s Hs
    obtain ⟨E, e⟩ := s
    unfold tglWpPreFixed
    iapply (tglWpPre_mono (wp₁ := fun E' e' _ => wp1 ⟨E', e'⟩)
      (wp₂ := fun E' e' _ => wp2 ⟨E', e'⟩)) $$ [] Hs
    iintro !> %e'
    iapply Hwand
  mono_pred_ne.ne {_ s s'} hd := by
    obtain rfl := eq_of_dist_discrete_leibniz hd; exact .of_eq rfl

/-- The total weakest precondition: `e` terminates under mask `E` and satisfies `Φ`. -/
noncomputable abbrev tglWp (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  bi_least_fixpoint (tglWpPreFixed Φ) ⟨E, e⟩

theorem tglWp_unfold {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    tglWp E e Φ = tglWpPre tglWp E e Φ :=
  least_fixpoint_unfold (tglWpPreFixed Φ)

theorem tglWpPre_eq_value {wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF}
    {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    tglWpPre wp E (Exp.ofVal v) Φ =
      iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ Φ v) := by
  unfold tglWpPre; rw [Exp.toVal?_ofVal]

theorem tglWpPre_eq_step {wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF}
    {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} (Hv : e.toVal? = none) :
    tglWpPre wp E e Φ =
      iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E, ∅}=> glm' e σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ wp E ρ.expr Φ))) := by
  unfold tglWpPre; rw [Hv]

theorem tglWp_unfold_value {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    tglWp E (Exp.ofVal v) Φ =
      iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ Φ v) :=
  tglWp_unfold.trans tglWpPre_eq_value

theorem tglWp_unfold_step {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e.toVal? = none) :
    tglWp E e Φ =
      iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E, ∅}=> glm' e σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))) :=
  tglWp_unfold.trans (tglWpPre_eq_step Hv)

/-! ## Value rules -/

theorem tglWp_value_fupd {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> Φ v) ⊢ tglWp E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply tglWp_unfold
  isimp only [tglWpPre_eq_value]
  iintro %σ %ε ⟨Hσ, Hε⟩
  imod HΦ
  imodintro
  iframe

theorem tglWp_value {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    Φ v ⊢ tglWp E (Exp.ofVal v) Φ :=
  fupd_intro.trans tglWp_value_fupd

theorem tglWp_value_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT}
    {Φ : Val rT → IProp GF} (h : e.toVal? = some v) :
    Φ v ⊢ tglWp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact tglWp_value

theorem tglWp_value_fupd_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT}
    {Φ : Val rT → IProp GF} (h : e.toVal? = some v) :
    iprop(|={E}=> Φ v) ⊢ tglWp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact tglWp_value_fupd

theorem tglWp_value_inv_with_state {E : CoPset} {v : Val rT} {σ : State rT}
    {ε : ENNReal} {Φ : Val rT → IProp GF} :
    iprop(tglWp E (Exp.ofVal v) Φ ∗ stateInterp σ ∗ errInterp (rT := rT) ε) ⊢
      iprop(|={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ Φ v) := by
  iintro ⟨HW, Hσ, Hε⟩
  isimp only [tglWp_unfold_value] at HW
  iapply HW $$ %σ %ε [$Hσ $Hε]

theorem tglWp_of_frame_fupd {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(∀ (σ : State rT) (ε : ENNReal),
        stateInterp σ ∗ errInterp (rT := rT) ε -∗
          |={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ tglWp E e Φ)
      ⊢ tglWp E e Φ := by
  iintro HF
  cases htv : e.toVal? with
  | some v =>
    obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
    isimp only [tglWp_unfold_value]
    iintro %σ %ε ⟨Hσ, Hε⟩
    imod HF $$ %σ %ε [$Hσ $Hε] with ⟨Hσ', Hε', HW⟩
    iapply tglWp_value_inv_with_state
    iframe
  | none =>
    isimp only [tglWp_unfold_step htv]
    iintro %σ %ε ⟨Hσ, Hε⟩
    imod HF $$ %σ %ε [$Hσ $Hε] with ⟨Hσ', Hε', HW⟩
    isimp only [tglWp_unfold_step htv] at HW
    iapply HW $$ %σ %ε [$Hσ' $Hε']

/-! ## Induction principle -/

theorem tglWp_ind {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Q : Exp rT → IProp GF) [NonExpansive Q] :
    iprop(□ (∀ e',
      tglWpPre (fun _ e'' _ => Q e'') E e' Φ -∗ Q e')) ⊢
        (tglWp E e Φ -∗ Q e) := by
  iintro #HInd HW
  let Q' : TglWpState rT → IProp GF := fun s => iprop(⌜s.1 = E⌝ -∗ Q s.2)
  let : NonExpansive Q' := nonExpansive_of_discrete_leibniz Q'
  ihave HQ' : iprop(Q' ⟨E, e⟩) $$ [HW]
  · iapply (least_fixpoint_iter (F := tglWpPreFixed Φ) (Φ := Q')) $$ [] HW
    iintro !> %s HF
    obtain ⟨E', e'⟩ := s
    iintro %rfl
    iapply HInd
    iapply (tglWpPre_mono (wp₁ := fun E' e' _ => Q' ⟨E', e'⟩)) $$ [] HF
    iintro !> %e'' HQ
    iapply HQ
    itrivial
  iapply HQ'
  itrivial

/-! ## Derived structural rules -/

theorem tglWp_strong_mono {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop(tglWp E e Φ ∗ (∀ v, Φ v ={E}=∗ Ψ v)) ⊢ tglWp E e Ψ := by
  iintro ⟨HW, Hwand⟩
  let Q : Exp rT → IProp GF := fun e' => iprop(
    ∀ (Ψ' : Val rT → IProp GF), (∀ v, Φ v ={E}=∗ Ψ' v) -∗ tglWp E e' Ψ')
  let : NonExpansive Q := nonExpansive_of_discrete_leibniz Q
  ihave HQe : iprop(Q e) $$ [HW]
  · iapply (tglWp_ind (E := E) (Φ := Φ) (Q := Q))
    · iintro !> %e' HF %Ψ' Hwand'
      iapply tglWp_unfold
      iintro %σ %ε ⟨Hσ, Hε⟩
      ispecialize HF $$ %σ %ε [$Hσ $Hε]
      cases htv : e'.toVal? with
      | some v =>
        imod HF with ⟨Hσ', Hε', HΦv⟩
        imod Hwand' $$ %v HΦv with HΨv
        imodintro
        iframe
      | none =>
        imod HF with HG
        imodintro
        iapply glm'_strong_mono
        iframe HG
        iintro %ρ %ε₂ HC
        imod HC with ⟨Hσ', Hε', HQρ⟩
        imodintro
        iframe Hσ' Hε'
        iapply HQρ $$ %Ψ' Hwand'
    · iexact HW
  iapply HQe $$ %Ψ Hwand

theorem tglWp_wand {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop(tglWp E e Φ ∗ (∀ v, Φ v -∗ Ψ v)) ⊢ tglWp E e Ψ := by
  iintro ⟨HW, HΦΨ⟩
  iapply tglWp_strong_mono
  iframe HW
  iintro %v HΦv !>
  iapply HΦΨ $$ HΦv

theorem tglWp_wand_left {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop((∀ v, Φ v -∗ Ψ v) ∗ tglWp E e Φ) ⊢ tglWp E e Ψ := by
  iintro ⟨HΦΨ, HW⟩
  iapply tglWp_wand
  iframe

theorem fupd_tglWp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> tglWp E e Φ) ⊢ tglWp E e Φ := by
  iintro HW
  iapply tglWp_of_frame_fupd
  iintro %σ %ε ⟨Hσ, Hε⟩
  imod HW
  imodintro
  iframe

theorem tglWp_fupd {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    tglWp E e (fun v => iprop(|={E}=> Φ v)) ⊢ tglWp E e Φ := by
  iintro HW
  iapply tglWp_strong_mono (Φ := fun v => iprop(|={E}=> Φ v)) (Ψ := Φ)
  iframe HW
  iintro %v HΦ
  iexact HΦ

theorem tglWp_frame_left {E : CoPset} {e : Exp rT} {R : IProp GF}
    {Φ : Val rT → IProp GF} :
    iprop(R ∗ tglWp E e Φ) ⊢ tglWp E e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨HR, HW⟩
  iapply tglWp_wand
  iframe HW
  iintro %v HΦv
  iframe

theorem tglWp_frame_right {E : CoPset} {e : Exp rT} {R : IProp GF}
    {Φ : Val rT → IProp GF} :
    iprop(tglWp E e Φ ∗ R) ⊢ tglWp E e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨HW, HR⟩
  iapply tglWp_wand
  iframe HW
  iintro %v HΦv
  iframe

theorem tglWp_frame_wand {E : CoPset} {e : Exp rT} {R : IProp GF}
    {Φ : Val rT → IProp GF} :
    iprop(R ∗ tglWp E e (fun v => iprop(R -∗ Φ v))) ⊢ tglWp E e Φ := by
  iintro ⟨HR, HW⟩
  iapply (tglWp_wand (Φ := fun v => iprop(R ∗ (R -∗ Φ v))) (Ψ := Φ))
  isplitl [HR HW]
  · iapply (tglWp_frame_left (R := R) (Φ := fun v => iprop(R -∗ Φ v)))
    iframe
  · iintro %v ⟨HRv, HW'⟩
    iapply HW' $$ HRv

theorem tglWp_mono {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF}
    (HΦ : ∀ v, Φ v ⊢ Ψ v) :
    tglWp E e Φ ⊢ tglWp E e Ψ := by
  iintro HW
  iapply tglWp_wand
  iframe HW
  iintro %v HΦv
  iapply HΦ $$ HΦv

/-! ## Bind -/

theorem tglWp_bind {K : Ectx rT} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    tglWp E e (fun v => tglWp E (K.fill (Exp.ofVal v)) Φ) ⊢
      tglWp E (K.fill e) Φ := by
  iintro HW
  let : NonExpansive (fun e' => tglWp E (K.fill e') Φ) :=
    nonExpansive_of_discrete_leibniz _
  iapply (tglWp_ind (E := E)
    (Φ := fun v => tglWp E (K.fill (Exp.ofVal v)) Φ)
    (Q := fun e' => tglWp E (K.fill e') Φ))
  · iintro !> %e' HF
    cases htv : e'.toVal? with
    | some v =>
      obtain rfl : e' = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
      isimp only [tglWpPre_eq_value] at HF
      iapply tglWp_of_frame_fupd $$ HF
    | none =>
      have hKtv : (K.fill e').toVal? = none :=
        Exp.toVal?_eq_none.mpr fun hKv =>
          (Exp.toVal?_eq_none.mp htv) (Ectx.fill_isValue hKv)
      isimp only [tglWpPre_eq_step htv] at HF
      isimp only [tglWp_unfold_step hKtv]
      iintro %σ %ε ⟨Hσ, Hε⟩
      ispecialize HF $$ %σ %ε [$Hσ $Hε]
      imod HF
      imodintro
      iapply (glm'_bind (K := K) (e := e') (σ := σ) (ε := ε)
              (Z := fun ρ ε₂ => iprop(|={∅, E}=>
                stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ)))
      iexact HF
  · iexact HW

/-- `tglWp_bind` with a value in the hole. -/
theorem tglWp_bind_value {K : Ectx rT} {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    tglWp E (Exp.ofVal v) (fun v' => tglWp E (K.fill (Exp.ofVal v')) Φ) ⊢
      tglWp E (K.fill (Exp.ofVal v)) Φ := by
  exact tglWp_bind

end ErisWpGS
end TotalEris
end ProbLang
