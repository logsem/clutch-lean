module

public import Metrology.Micrometer.AppWeakestpre
public import Metrology.ProbLang.Atomic
import Metrology.ProbLang.Syntax.Notation

/-! # `OpenInv e`: the logical-atomicity predicate enabling mask-shift around evaluating `e`. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}

/-- Evaluating `e` is logically atomic: `wp` may open invariants around it. -/
def OpenInv (L : GradedLifting.{0} B) (e : Exp rT) : Prop :=
  ∀ {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF] {E1 E2 : CoPset}
    {Φ : Val rT → IProp GF}, iprop%
    (|={E1, E2}=> wp L E2 e (fun v => iprop% |={E2, E1}=> Φ v)) ⊢ wp L E1 e Φ

namespace OpenInv

theorem specCoupl_atomic_bridge_some {hlc : HasLC} {GF : BundledGFunctors}
    [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF] [InvGS_gen hlc GF] {E1 E2 : CoPset}
    {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {b₁ : B}
    {Φ : Val rT → IProp GF} {v : Val rT} : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b₁ (fun σ₂ ρ' b₂ => iprop(|={∅, E2}=>
      stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ budgetInterp b₂ ∗
        (|={E2, E1}=> Φ v))) ⊢
    specCoupl L ∅ σ₁ e₁' σ₁' b₁ fun σ₂ ρ' b₂ => iprop(|={∅, E1}=>
      stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ budgetInterp b₂ ∗
        Φ v) := by
  iintro HSC
  iapply specCoupl_mono_spatial
  iframe
  iintro %σ₂ %ρ' %b₂ HBody
  imod HBody with ⟨Hσ, Hs, Hb, >HΦ⟩
  iframe

theorem specCoupl_atomic_bridge_none [Add B] [L.IsLawful] [L.IsTopAbsorbing] [L.IsSupportLocal]
    {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF]
    {e : Exp rT} (h : Atomic' e) {E1 E2 : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {b₁ : B} {Φ : Val rT → IProp GF} : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b₁ (fun σ₂ ρ' b₂ =>
      progCoupl L e σ₂ ρ'.expr ρ'.state b₂ fun e₃ σ₃ e₃' σ₃' b₃ => iprop%
        ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E2}=>
          stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ budgetInterp b₄ ∗
            wp L E2 e₃ (fun v => iprop(|={E2, E1}=> Φ v)))) ⊢
    specCoupl L ∅ σ₁ e₁' σ₁' b₁ fun σ₂ ρ' b₂ =>
      progCoupl L e σ₂ ρ'.expr ρ'.state b₂ fun e₃ σ₃ e₃' σ₃' b₃ => iprop%
        ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E1}=>
          stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ budgetInterp b₄ ∗
            wp L E1 e₃ Φ) := by
  iintro HSC
  iapply specCoupl_mono_spatial
  iframe
  iintro %σ₂ %ρ' %b₂ HBody
  iapply progCoupl_mono
  isplitr
  -- Take the `progCoupl` premise first: it pins the intermediate postcondition.
  swap
  · iapply progCoupl_strengthen (S := {ρ : Cfg rT | ρ.1.isValue}) Cfg.isValue_measurableSet (h σ₂)
    iexact HBody
  iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ ⟨%he₃val, HInner⟩ !>
  iapply specCoupl_bind Std.LawfulSet.subset_refl
  iframe HInner
  iintro %σ₄ %ρ'' %b₄ HBody4
  iapply fupd_specCoupl
  imod HBody4 with ⟨Hσ4, Hs4, Hb4, HW4⟩
  imod wp_unfold_mp $$ HW4 %σ₄ %ρ''.expr %ρ''.state %b₄ [$] with HSC
  imodintro
  iapply specCoupl_mono_spatial
  iframe
  iintro %σ₅ %ρ''' %b₅ HInnerBody
  cases htv : e₃.toVal? with
  | none => exact (Exp.toVal?_eq_none.mp htv he₃val).elim
  | some _ =>
    imod HInnerBody with ⟨Hσ5, Hs5, Hb5, >HΦv⟩
    imodintro
    iframe
    iapply wp_value_of_toVal htv $$ HΦv

theorem of_atomic [Add B] [L.IsLawful] [L.IsTopAbsorbing] [L.IsSupportLocal] {e : Exp rT}
    (h : Atomic' e) : OpenInv L e := by
  intro GF _ _ E1 E2 Φ
  iintro HF
  iapply MicrometerWpGS.wp_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ Hres
  imod HF
  imod wp_unfold_mp $$ HF %σ₁ %e₁' %σ₁' %b₁ Hres with HSC
  imodintro
  cases htv : e.toVal? with
  | some v => iapply specCoupl_atomic_bridge_some (v := v) $$ HSC
  | none => iapply specCoupl_atomic_bridge_none h $$ HSC

end OpenInv

theorem wp_atomic {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF]
    {e : Exp rT} (h : OpenInv L e) {E1 E2 : CoPset} {Φ : Val rT → IProp GF} : iprop%
    (|={E1, E2}=> wp L E2 e (fun v => iprop% |={E2, E1}=> Φ v)) ⊢ wp L E1 e Φ :=
  h

/-! ## Proof-mode support

These instances make `imod`/`iinv` find `wp_atomic`. `OpenInv` is a plain `Prop`, so the
concrete redexes register into the class `IsOpenInv` instead. -/

/-- Registers `OpenInv L e` for instance search. -/
class IsOpenInv (L : GradedLifting.{0} B) (e : Exp rT) : Prop where
  out : OpenInv L e

section Instances
variable [MeasurableSingletonClass rT] [Add B] [L.IsLawful] [L.IsTopAbsorbing] [L.IsSupportLocal]

instance : IsOpenInv L (rT := rT) .urand := ⟨OpenInv.of_atomic Atomic.urand'⟩

instance (l : Loc) : IsOpenInv L (rT := rT) pl(!#(.loc l)) := ⟨OpenInv.of_atomic (Atomic.load' l)⟩

instance (l : Loc) (v : Val rT) : IsOpenInv L (Exp.store pl(#(.loc l)) v.1) :=
  ⟨OpenInv.of_atomic (Atomic.store' l v)⟩

instance (v : Val rT) : IsOpenInv L (Exp.alloc v.1) := ⟨OpenInv.of_atomic (Atomic.alloc' v)⟩

instance (z : Int) : IsOpenInv L (rT := rT) pl(rand(#(.int z), #(.unit))) :=
  ⟨OpenInv.of_atomic (Atomic.rand_unit' z)⟩

instance (z : Int) (l : Loc) : IsOpenInv L (rT := rT) pl(rand(#(.int z), #(.lbl l))) :=
  ⟨OpenInv.of_atomic (Atomic.rand_lbl' z l)⟩

end Instances

theorem elimAcc_close {X : Type} {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]
    {E₁ E₂ : CoPset} {Φ : Val rT → IProp GF} {β : X → IProp GF} {γ : X → Option (IProp GF)}
    {x : X} {v : Val rT} : iprop%
    (|={E₂}=> β x ∗ (γ x -∗? Φ v)) ⊢ (β x ={E₂, E₁}=∗ (γ x).getD iprop(emp)) ={E₂, E₁}=∗ Φ v := by
  iintro Hpost Hcl
  imod Hpost with ⟨Hβ, HΦ⟩
  imod Hcl $$ Hβ
  imodintro
  cases γ x with
  | none =>
    dsimp only [BIBase.wandM]
    iexact HΦ
  | some P => iapply HΦ $$ Hcl

instance (priority := low) elimModal_fupd_wp_atomic {p : Bool} {io : InOut} {E1 E2 : CoPset}
    {e : Exp rT} [h : IsOpenInv L e] {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]
    [BudgetGS B GF] {P : IProp GF} {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|={E1, E2}=> P) P
      (wp L E1 e Φ) (wp L E2 e (fun v => iprop(|={E2, E1}=> Φ v))) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans (wp_atomic h.out)

instance (priority := low) elimAcc_wp_atomic {X : Type} {e : Exp rT} [h : IsOpenInv L e]
    {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF] {Φ : Val rT → IProp GF}
    (E₁ E₂ : CoPset) (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
    ElimAcc True (fupd E₁ E₂) (fupd E₂ E₁) α β γ (wp L E₁ e Φ)
      (fun x => wp L E₂ e (fun v => iprop(|={E₂}=> β x ∗ (γ x -∗? Φ v)))) where
  elim_acc := by
    dsimp only [accessor]
    iintro %_ Hinner Hacc
    iapply wp_atomic h.out
    imod Hacc with ⟨%x, Hα, Hclose⟩
    imodintro
    ispecialize Hinner $$ %x Hα
    iapply MicrometerWpGS.wp_frame_wand
    iframe Hclose
    iapply MicrometerWpGS.wp_mono (fun _ => elimAcc_close) $$ Hinner

instance elimAcc_wp_nonatomic {X : Type} {e : Exp rT}
    {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF] {Φ : Val rT → IProp GF}
    (E : CoPset) (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
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
    iapply MicrometerWpGS.wp_frame_wand
    iframe Hclose
    iapply MicrometerWpGS.wp_mono (fun _ => elimAcc_close) $$ Hinner

end ProbLang
