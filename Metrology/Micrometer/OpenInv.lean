module

public import Metrology.Micrometer.AppWeakestpre
public import Metrology.ProbLang.Atomic
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-! # `OpenInv`: opening invariants around `wp`

`OpenInv L e` says `wp` of `e` may open invariants around it; atomic `e` satisfy it, and
`IsOpenInv` instances make `imod`/`iinv` use it on `wp` goals. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang.MicrometerWpGS GradedLifting

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}

/-- `wp` of `e` may open invariants around it (`of_atomic`). -/
def OpenInv (L : GradedLifting.{0} B) (e : Exp rT) : Prop :=
  ∀ {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF] {E1 E2 : CoPset}
    {Φ : Val rT → IProp GF}, iprop%
    (|={E1, E2}=> wp L E2 e (fun v => iprop% |={E2, E1}=> Φ v)) ⊢ wp L E1 e Φ

section Wp
variable {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF] {X : Type}
  {E1 E2 : CoPset} {Φ : Val rT → IProp GF} {e : Exp rT} {P : IProp GF} {σ₁ : State rT}
  {e₁' : Exp rT} {σ₁' : State rT} {b₁ : B}
local bi IProp GF
open SpecUpdateGS BIFUpdate

namespace OpenInv

/-! ## Atomic expressions are `OpenInv` -/

/-- At a value, the closing update `|={E2, E1}=>` moves out to the `specCoupl` postcondition. -/
theorem specCoupl_close_val {hlc : HasLC} [InvGS_gen hlc GF] {v : Val rT} : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b₁ (fun σ₂ ρ' b₂ => iprop(|={∅, E2}=>
        stateInterp σ₂ ∗ specInterp ρ' ∗ budgetInterp b₂ ∗
          (|={E2, E1}=> Φ v))) ⊢
      specCoupl L ∅ σ₁ e₁' σ₁' b₁ fun σ₂ ρ' b₂ => iprop(|={∅, E1}=>
        stateInterp σ₂ ∗ specInterp ρ' ∗ budgetInterp b₂ ∗
          Φ v) := by
  iintro HSC
  iapply specCoupl_mono
  iframe
  iintro %σ₂ %ρ' %b₂ >⟨Hσ, Hs, Hb, >HΦ⟩
  iframe

variable [Add B]
variable [L.IsTopAbsorbing]

/-- After an atomic step, the closing update `|={E2, E1}=>` moves out to the `specCoupl`
postcondition. -/
theorem specCoupl_close_step_of_atomic [L.IsLawful] [L.IsSupportLocal] [L.HasBind]
    (h : Atomic e) : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b₁ (fun σ₂ ρ' b₂ =>
        progCoupl L e σ₂ ρ'.expr ρ'.state b₂ fun e₃ σ₃ e₃' σ₃' b₃ => iprop%
          ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E2}=>
            stateInterp σ₄ ∗ specInterp ρ'' ∗ budgetInterp b₄ ∗
              wp L E2 e₃ (fun v => iprop(|={E2, E1}=> Φ v)))) ⊢
      specCoupl L ∅ σ₁ e₁' σ₁' b₁ fun σ₂ ρ' b₂ =>
        progCoupl L e σ₂ ρ'.expr ρ'.state b₂ fun e₃ σ₃ e₃' σ₃' b₃ => iprop%
          ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E1}=>
            stateInterp σ₄ ∗ specInterp ρ'' ∗ budgetInterp b₄ ∗
              wp L E1 e₃ Φ) := by
  iintro HSC
  iapply specCoupl_mono
  iframe
  iintro %σ₂ %ρ' %b₂ HBody
  iapply progCoupl_mono
  isplitr
  -- Take the `progCoupl` premise first: it pins the intermediate postcondition.
  swap
  · iapply progCoupl_strengthen Cfg.isValue_measurableSet (h σ₂)
    iexact HBody
  -- Atomicity: every e₃ reached in one step is a value (he₃val), so the inner wp is at a value
  -- and its closing update moves out to the postcondition.
  iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ ⟨%he₃val, HInner⟩ !>
  iapply specCoupl_bind LawfulSet.subset_refl
  iframe HInner
  iintro %σ₄ %ρ'' %b₄ HBody4
  iapply fupd_specCoupl
  imod HBody4 with ⟨Hσ4, Hs4, Hb4, HW4⟩
  imod wp_unfold_mp $$ HW4 %σ₄ %ρ''.expr %ρ''.state %b₄ [$] with HSC
  imodintro
  iapply specCoupl_mono
  iframe
  iintro %σ₅ %ρ''' %b₅ HInnerBody
  cases htv : e₃.toVal? with
  | none => exact (Exp.toVal?_eq_none.mp htv he₃val).elim
  | some _ =>
    imod HInnerBody with ⟨Hσ5, Hs5, Hb5, >HΦv⟩
    imodintro
    iframe
    iapply wp_value_of_toVal htv $$ HΦv

/-- Atomic expressions are `OpenInv`. -/
theorem of_atomic [L.IsLawful] [L.IsSupportLocal] [L.HasBind] (h : Atomic e) : OpenInv L e := by
  intro GF _ _ E1 E2 Φ
  iintro HF
  iapply MicrometerWpGS.wp_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ Hres
  imod HF
  imod wp_unfold_mp $$ HF %σ₁ %e₁' %σ₁' %b₁ Hres with HSC
  imodintro
  -- Value case: no step happens. Otherwise atomicity makes the step's result a value.
  cases htv : e.toVal? with
  | some v => iapply specCoupl_close_val $$ HSC
  | none => iapply specCoupl_close_step_of_atomic h $$ HSC

end OpenInv

/-- `OpenInv L e` unfolded: `wp` of `e` absorbs a preceding mask-opening update. -/
theorem wp_atomic (h : OpenInv L e) : iprop%
    (|={E1, E2}=> wp L E2 e (fun v => iprop% |={E2, E1}=> Φ v)) ⊢ wp L E1 e Φ :=
  h

/-! ## `IsOpenInv` instances -/

/-- Registers `OpenInv L e` for instance search. -/
class IsOpenInv (L : GradedLifting.{0} B) (e : Exp rT) : Prop where
  /-- The `OpenInv` property itself. -/
  out : OpenInv L e

section Instances
open OpenInv (of_atomic)
open Atomic (load store alloc rand_unit rand_lbl)
variable [Add B] [L.IsLawful] [L.IsTopAbsorbing] [L.IsSupportLocal]
  [L.HasBind]

instance isOpenInv_urand : IsOpenInv L (rT := rT) .urand where
  out := of_atomic Atomic.urand

variable (l : Loc)

instance isOpenInv_load : IsOpenInv L (rT := rT) pl(!#loc l) where
  out := of_atomic (load l)

instance isOpenInv_store (v : Val rT) : IsOpenInv L (.store pl(#loc l) v.1) where
  out := of_atomic (store l v)

instance isOpenInv_alloc (v : Val rT) : IsOpenInv L (.alloc v.1) where
  out := of_atomic (alloc v)

variable (z : Int)

instance isOpenInv_rand_unit : IsOpenInv L (rT := rT) pl(rand(#z, #())) where
  out := of_atomic (rand_unit z)

instance isOpenInv_rand_lbl : IsOpenInv L (rT := rT) pl(rand(#z, #lbl l)) where
  out := of_atomic (rand_lbl z l)

end Instances

/-! ## `imod` and `iinv` on `wp` -/

/-- Shared postcondition step of the `iinv` instances: the accessor's closing update turns
`β x ∗ (γ x -∗? Φ v)` into `Φ v`. -/
theorem elimAcc_close {β : X → IProp GF} {γ : X → Option (IProp GF)} {x : X} {v : Val rT} : iprop%
    (|={E2}=> β x ∗ (γ x -∗? Φ v)) ⊢ (β x ={E2, E1}=∗ (γ x).getD iprop(emp)) ={E2, E1}=∗ Φ v := by
  iintro Hpost Hcl
  imod Hpost with ⟨Hβ, HΦ⟩
  imod Hcl $$ Hβ
  imodintro
  cases γ x with
  | none =>
    dsimp only [BIBase.wandM]
    iexact HΦ
  | some P => iapply HΦ $$ Hcl

/-- The shared tail of the `iinv` instances: `wp` of the accessor's postcondition with the closing
wand framed in. -/
theorem wp_elimAcc_core {β : X → IProp GF} {γ : X → Option (IProp GF)} {x : X} : iprop%
    (β x ={E2, E1}=∗ (γ x).getD iprop(emp)) ∗
      wp L E2 e (fun v => iprop(|={E2}=> β x ∗ (γ x -∗? Φ v))) ⊢
      wp L E2 e (fun v => iprop(|={E2, E1}=> Φ v)) := by
  iintro ⟨Hclose, Hinner⟩
  iapply MicrometerWpGS.wp_frame_wand
  iframe Hclose
  iapply MicrometerWpGS.wp_mono (fun _ => elimAcc_close) $$ Hinner

variable [h : IsOpenInv L e]

/-- `imod` opens a `|={E1, E2}=>` around `wp` of an `IsOpenInv` expression. -/
instance (priority := low) elimModal_fupd_wp_atomic {p : Bool} {io : InOut} :
    ElimModal True p io false iprop(|={E1, E2}=> P) P
      (wp L E1 e Φ) (wp L E2 e (fun v => iprop(|={E2, E1}=> Φ v))) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (mono wand_elim_right).trans (wp_atomic h.out)

/-- `iinv` opens an invariant around `wp` of an `IsOpenInv` expression. -/
instance (priority := low) elimAcc_wp_atomic (E₁ E₂ : CoPset) (α β : X → _) (γ : X → _) :
    ElimAcc True (fupd E₁ E₂) (fupd E₂ E₁) α β γ (wp L E₁ e Φ)
      (fun x => wp L E₂ e (fun v => iprop(|={E₂}=> β x ∗ (γ x -∗? Φ v)))) where
  elim_acc := by
    dsimp only [accessor]
    iintro %_ Hinner Hacc
    iapply wp_atomic h.out
    imod Hacc with ⟨%x, Hα, Hclose⟩
    imodintro
    ispecialize Hinner $$ %x Hα
    iapply wp_elimAcc_core $$ [$Hclose $Hinner]

/-- `iinv` with an accessor that keeps the mask `E` works around any `wp`. -/
instance elimAcc_wp_nonatomic (E : CoPset) (α β : X → _) (γ : X → _) :
    ElimAcc True (fupd E E) (fupd E E) α β γ (wp L E e Φ)
      (fun x => wp L E e (fun v => iprop(|={E}=> β x ∗ (γ x -∗? Φ v)))) where
  elim_acc := by
    dsimp only [accessor]
    iintro %_ Hinner Hacc
    iapply MicrometerWpGS.fupd_wp
    imod Hacc with ⟨%x, Hα, Hclose⟩
    imodintro
    ispecialize Hinner $$ %x Hα
    iapply MicrometerWpGS.wp_fupd
    iapply wp_elimAcc_core $$ [$Hclose $Hinner]

end Wp

end ProbLang
