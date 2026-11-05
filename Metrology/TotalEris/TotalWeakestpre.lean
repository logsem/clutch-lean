module

public import Metrology.TotalEris.Glm
public import IrisFix.ProofMode.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

/-!
# Total weakest precondition

Total weakest precondition: `tglWp` with its unfolding, induction, monotonicity and bind rules.
-/

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang

namespace ProbLang

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangFFI rT]
  [ProbLangObs rT]

namespace TotalEris
namespace ErisWpGS

variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
variable {E : CoPset} {Φ : Val rT → IProp GF} {e : Exp rT} {v : Val rT}
variable {Ψ : Val rT → IProp GF}

/-- The total weakest precondition, least: a value satisfies `Φ`; a non-value takes a `glm'`
step. -/
ifix tglWp (E : CoPset) (e₁ : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  iprop(∀ (σ₁ : State rT) (ε₁ : ENNReal),
    (stateInterp σ₁ ∗ errInterp (rT := rT) ε₁) -∗
      match e₁.toVal? with
      | some v => iprop(|={E}=>
          stateInterp σ₁ ∗ errInterp (rT := rT) ε₁ ∗ Φ v)
      | none => iprop(|={E, ∅}=>
          glm' e₁ σ₁ ε₁ (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))))

/-- Monotonicity of `tglWp.pre` in its inner predicate, at one mask and postcondition. -/
private theorem tglWp_pre_mono {wp₁ wp₂ : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF} :
    □ (∀ e', wp₁ E e' Φ -∗ wp₂ E e' Φ) ⊢ tglWp.pre wp₁ E e Φ -∗ tglWp.pre wp₂ E e Φ := by
  iintro #Hwand Hs
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

/-- `tglWp.pre` of a value is its value clause. -/
theorem tglWp_pre_eq_value {wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF} :
    tglWp.pre wp E (Exp.ofVal v) Φ = iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ Φ v) := by
  unfold tglWp.pre; rw [Exp.toVal?_ofVal]

/-- `tglWp.pre` of a non-value is its step clause. -/
theorem tglWp_pre_eq_step {wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF}
    (Hv : e.toVal? = none) :
    tglWp.pre wp E e Φ = iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E, ∅}=> glm' e σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ wp E ρ.expr Φ))) := by
  unfold tglWp.pre; rw [Hv]

/-- `tglWp` of a value is its value clause. -/
theorem tglWp_unfold_value :
    tglWp E (Exp.ofVal v) Φ = iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ Φ v) :=
  (tglWp.unfold _ _ _).trans tglWp_pre_eq_value

/-- `tglWp` of a non-value is its step clause. -/
theorem tglWp_unfold_step
    (Hv : e.toVal? = none) :
    tglWp E e Φ = iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E, ∅}=> glm' e σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))) :=
  (tglWp.unfold _ _ _).trans (tglWp_pre_eq_step Hv)

/-! ## Value rules -/

/-- `tglWp` of a value is an update of the postcondition. -/
theorem tglWp_value_fupd :
    iprop(|={E}=> Φ v) ⊢ tglWp E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply tglWp.unfold_mpr
  isimp only [tglWp_pre_eq_value]
  iintro %σ %ε ⟨Hσ, Hε⟩
  imod HΦ
  imodintro
  iframe

/-- `tglWp` of a value follows from the postcondition at that value. -/
theorem tglWp_value :
    Φ v ⊢ tglWp E (Exp.ofVal v) Φ :=
  fupd_intro.trans tglWp_value_fupd

/-- `tglWp` of an expression with `toVal? e = some v` follows from `Φ v`. -/
theorem tglWp_value_of_toVal (h : e.toVal? = some v) :
    Φ v ⊢ tglWp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact tglWp_value

/-- `tglWp` of an expression with `toVal? e = some v` follows from an update of `Φ v`. -/
theorem tglWp_value_fupd_of_toVal (h : e.toVal? = some v) :
    iprop(|={E}=> Φ v) ⊢ tglWp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact tglWp_value_fupd

/-- A value's `tglWp` yields its postcondition together with the state interpretation. -/
theorem tglWp_value_inv_with_state {σ : State rT}
    {ε : ENNReal} :
    iprop(tglWp E (Exp.ofVal v) Φ ∗ stateInterp σ ∗ errInterp (rT := rT) ε) ⊢
      iprop(|={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ Φ v) := by
  iintro ⟨HW, Hσ, Hε⟩
  isimp only [tglWp_unfold_value] at HW
  iapply HW $$ %σ %ε [$Hσ $Hε]

/-- To prove `tglWp`, one may first open the state and error interpretations. -/
theorem tglWp_of_frame_fupd :
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

/-- Induction on `tglWp`: the least-fixpoint principle, at one mask and postcondition. -/
theorem tglWp_ind (Q : Exp rT → IProp GF) :
    iprop(□ (∀ e',
      tglWp.pre (fun _ e'' _ => Q e'') E e' Φ -∗ Q e')) ⊢
        (tglWp E e Φ -∗ Q e) := by
  -- Induct on the fixpoint with a claim that remembers the mask `E` and postcondition `Φ`.
  iintro #HInd HW
  iapply tglWp.iter (fun E' e' Φ' => iprop(⌜E' = E ∧ Φ' = Φ⌝ -∗ Q e')) $$ [] %E %e %Φ HW
    %⟨rfl, rfl⟩
  iintro !> %E' %e' %Φ' HF %⟨hE, hΦ⟩
  subst E' Φ'
  iapply HInd
  iapply (tglWp_pre_mono (wp₁ := fun E' e' Φ' => iprop(⌜E' = E ∧ Φ' = Φ⌝ -∗ Q e'))) $$ [] HF
  iintro !> %e'' HQ
  iapply HQ $$ %⟨rfl, rfl⟩

/-! ## Derived structural rules -/

/-- Strong monotonicity: the postcondition may be weakened by a mask-updating wand. -/
theorem tglWp_strong_mono :
    iprop(tglWp E e Φ ∗ (∀ v, Φ v ={E}=∗ Ψ v)) ⊢ tglWp E e Ψ := by
  iintro ⟨HW, Hwand⟩
  let Q : Exp rT → IProp GF := fun e' => iprop(
    ∀ (Ψ' : Val rT → IProp GF), (∀ v, Φ v ={E}=∗ Ψ' v) -∗ tglWp E e' Ψ')
  ihave HQe : iprop(Q e) $$ [HW]
  · iapply (tglWp_ind (Q := Q))
    · iintro !> %e' HF %Ψ' Hwand'
      iapply tglWp.unfold_mpr
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

/-- `tglWp` is monotone in the postcondition, under the wand. -/
theorem tglWp_wand :
    iprop(tglWp E e Φ ∗ (∀ v, Φ v -∗ Ψ v)) ⊢ tglWp E e Ψ := by
  iintro ⟨HW, HΦΨ⟩
  iapply tglWp_strong_mono
  iframe HW
  iintro %v HΦv !>
  iapply HΦΨ $$ HΦv

/-- `tglWp` is monotone in the postcondition, with the wand as a separating conjunct. -/
theorem tglWp_wand_left :
    iprop((∀ v, Φ v -∗ Ψ v) ∗ tglWp E e Φ) ⊢ tglWp E e Ψ := by
  iintro ⟨HΦΨ, HW⟩
  iapply tglWp_wand
  iframe

/-- A mask update in front of `tglWp` can be absorbed. -/
theorem fupd_tglWp :
    iprop(|={E}=> tglWp E e Φ) ⊢ tglWp E e Φ := by
  iintro HW
  iapply tglWp_of_frame_fupd
  iintro %σ %ε ⟨Hσ, Hε⟩
  imod HW
  imodintro
  iframe

/-- A mask update in the postcondition of `tglWp` can be absorbed. -/
theorem tglWp_fupd :
    tglWp E e (fun v => iprop(|={E}=> Φ v)) ⊢ tglWp E e Φ := by
  iintro HW
  iapply tglWp_strong_mono
  iframe HW
  iintro %v HΦ
  iexact HΦ

/-- Frame rule: an extra resource is carried into the postcondition. -/
theorem tglWp_frame_left {R : IProp GF} :
    iprop(R ∗ tglWp E e Φ) ⊢ tglWp E e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨HR, HW⟩
  iapply tglWp_wand
  iframe HW
  iintro %v HΦv
  iframe

/-- Framing a resource on the right of `tglWp`. -/
theorem tglWp_frame_right {R : IProp GF} :
    iprop(tglWp E e Φ ∗ R) ⊢ tglWp E e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨HW, HR⟩
  iapply tglWp_wand
  iframe HW
  iintro %v HΦv
  iframe

/-- Framing a resource through the wand around `tglWp`. -/
theorem tglWp_frame_wand {R : IProp GF} :
    iprop(R ∗ tglWp E e (fun v => iprop(R -∗ Φ v))) ⊢ tglWp E e Φ := by
  iintro ⟨HR, HW⟩
  iapply (tglWp_wand (Φ := fun v => iprop(R ∗ (R -∗ Φ v))) (Ψ := Φ))
  isplitl [HR HW]
  · iapply tglWp_frame_left
    iframe
  · iintro %v ⟨HRv, HW'⟩
    iapply HW' $$ HRv

/-- `tglWp` is monotone in the postcondition. -/
theorem tglWp_mono
    (HΦ : ∀ v, Φ v ⊢ Ψ v) :
    tglWp E e Φ ⊢ tglWp E e Ψ := by
  iintro HW
  iapply tglWp_wand
  iframe HW
  iintro %v HΦv
  iapply HΦ $$ HΦv

/-! ## Bind -/

/-- Bind: run `e` in an evaluation context `K`, then continue with `K` filled by its value. -/
theorem tglWp_bind {K : Ectx rT} :
    tglWp E e (fun v => tglWp E (K.fill (Exp.ofVal v)) Φ) ⊢
      tglWp E (K.fill e) Φ := by
  iintro HW
  iapply (tglWp_ind (Q := fun e' => tglWp E (K.fill e') Φ))
  · iintro !> %e' HF
    cases htv : e'.toVal? with
    | some v =>
      obtain rfl : e' = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
      isimp only [tglWp_pre_eq_value] at HF
      iapply tglWp_of_frame_fupd $$ HF
    | none =>
      have hKtv : (K.fill e').toVal? = none := Exp.toVal?_eq_none.mpr fun hKv =>
          (Exp.toVal?_eq_none.mp htv) (Ectx.fill_isValue hKv)
      isimp only [tglWp_pre_eq_step htv] at HF
      isimp only [tglWp_unfold_step hKtv]
      iintro %σ %ε ⟨Hσ, Hε⟩
      ispecialize HF $$ %σ %ε [$Hσ $Hε]
      imod HF
      imodintro
      iapply (glm'_bind (e := e') (σ := σ) (ε := ε) (Z := fun ρ ε₂ => iprop(|={∅, E}=>
                stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ)))
      iexact HF
  · iexact HW

/-- `tglWp_bind` stated for a value-producing inner expression. -/
theorem tglWp_bind_value {K : Ectx rT} :
    tglWp E (Exp.ofVal v) (fun v' => tglWp E (K.fill (Exp.ofVal v')) Φ) ⊢
      tglWp E (K.fill (Exp.ofVal v)) Φ := by
  exact tglWp_bind

end ErisWpGS
end TotalEris
end ProbLang
