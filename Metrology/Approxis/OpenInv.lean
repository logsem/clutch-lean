module

public import Metrology.Approxis.AppWeakestpre
public import Metrology.ProbLang.Atomic
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # `OpenInv e`: the logical-atomicity predicate enabling mask-shift around evaluating `e`. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]
variable {ι : Type} [Monoid ι] {Δ : GradedDivergence.{0} ι}

def OpenInv (Δ : GradedDivergence.{0} ι) (e : Exp rT) : Prop :=
  ∀ {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) Δ GF] {E1 E2 : CoPset}
    {Φ : Val rT → IProp GF}, iprop%
    (|={E1, E2}=> wp E2 e (fun v => iprop% |={E2, E1}=> Φ v)) ⊢ wp E1 e Φ

namespace OpenInv

theorem specCoupl_atomic_bridge_some {hlc : HasLC} {GF : BundledGFunctors}
    [ApproxisWpGS (rT := rT) Δ GF] [InvGS_gen hlc GF] {E1 E2 : CoPset} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT} {ε₁ : ENNReal} {Φ : Val rT → IProp GF} {v : Val rT} : iprop%
    specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ => iprop(|={∅, E2}=>
      stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ errInterp (rT := rT) ε₂ ∗ (|={E2, E1}=> Φ v))) ⊢
    specCoupl ∅ σ₁ e₁' σ₁' ε₁ fun σ₂ ρ' ε₂ => iprop(|={∅, E1}=>
      stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ errInterp (rT := rT) ε₂ ∗ Φ v) := by
  iintro HSC
  iapply specCoupl_mono_spatial
  iframe
  iintro %σ₂ %ρ' %ε₂ HBody
  imod HBody with ⟨Hσ, Hs, Hε, >HΦ⟩
  iframe

theorem specCoupl_atomic_bridge_none [Δ.IsZeroLeft] {GF : BundledGFunctors}
    [ApproxisWpGS (rT := rT) Δ GF]
    {e : Exp rT} (h : Atomic' e) {E1 E2 : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ : ENNReal} {Φ : Val rT → IProp GF} : iprop%
    specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
      progCoupl e σ₂ ρ'.expr ρ'.state ε₂ fun e₃ σ₃ e₃' σ₃' ε₃ => iprop%
        ▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ fun σ₄ ρ'' ε₄ => iprop(|={∅, E2}=>
          stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ errInterp (rT := rT) ε₄ ∗
            wp E2 e₃ (fun v => iprop(|={E2, E1}=> Φ v)))) ⊢
    specCoupl ∅ σ₁ e₁' σ₁' ε₁ fun σ₂ ρ' ε₂ =>
      progCoupl e σ₂ ρ'.expr ρ'.state ε₂ fun e₃ σ₃ e₃' σ₃' ε₃ => iprop%
        ▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ fun σ₄ ρ'' ε₄ => iprop(|={∅, E1}=>
          stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ errInterp (rT := rT) ε₄ ∗ wp E1 e₃ Φ) := by
  iintro HSC
  iapply specCoupl_mono_spatial
  iframe
  iintro %σ₂ %ρ' %ε₂ HBody
  iapply progCoupl_mono
  isplitr
  swap
  · iapply progCoupl_strengthen (S := {ρ : Cfg rT | ρ.1.isValue}) Cfg.isValue_measurableSet (h σ₂)
    iframe HBody
    iintro !> %_ %_ %_ %_ !>
    iapply specCoupl_err_ge_1 (_root_.le_refl _)
  iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ ⟨%Hreach, HInner⟩
  rcases Hreach with he₃val | Hε1
  · iintro !>
    iapply specCoupl_bind Std.LawfulSet.subset_refl
    iframe HInner
    iintro %σ₄ %ρ'' %ε₄ HBody4
    iapply fupd_specCoupl
    irevert HBody4
    refine BI.entails_wand (fupd_elim ?_)
    iintro ⟨Hσ4, Hs4, Hε4, HW4⟩
    ihave HW4 := wp_unfold_mp $$ HW4 %σ₄ %ρ''.expr %ρ''.state %ε₄ [$]
    irevert HW4
    refine BI.entails_wand (fupd_elim ?_)
    iintro HSC
    iapply fupd_intro
    iapply specCoupl_mono_spatial
    iframe
    iintro %σ₅ %ρ''' %ε₅ HInnerBody
    cases htv : e₃.toVal? with
    | none => exact (Exp.toVal?_eq_none.mp htv he₃val).elim
    | some v' =>
      imod HInnerBody with ⟨Hσ5, Hs5, Hε5, >HΦv⟩
      imodintro
      iframe
      iapply wp_value_of_toVal htv $$ HΦv
  · iintro !>
    iapply specCoupl_err_ge_1 Hε1

theorem of_atomic [Δ.IsZeroLeft] {e : Exp rT} (h : Atomic' e) : OpenInv Δ e := by
  intro GF _ E1 E2 Φ
  iintro HF
  iapply ApproxisWpGS.wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ Hres
  icombine HF Hres as HFR
  irevert HFR
  refine BI.entails_wand (fupd_frame_right.trans (fupd_elim ?_))
  iintro ⟨HW, HresInner⟩
  ihave HW := wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %ε₁ HresInner
  irevert HW
  refine BI.entails_wand (fupd_elim ?_)
  cases htv : e.toVal? with
  | some v => exact (specCoupl_atomic_bridge_some (v := v)).trans fupd_intro
  | none => exact (specCoupl_atomic_bridge_none h).trans fupd_intro

end OpenInv

theorem wp_atomic {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) Δ GF] {e : Exp rT}
    (h : OpenInv Δ e)
    {E1 E2 : CoPset} {Φ : Val rT → IProp GF} :
    iprop(|={E1, E2}=> wp E2 e (fun v => iprop(|={E2, E1}=> Φ v))) ⊢ wp E1 e Φ :=
  h

/-! ## Proof-mode support

`wp_atomic` is the theorem; these make the proof mode *find* it. Without the
`ElimModal` instance below, `imod`/`iinv` will not fire on an atomic `wp` and the
lemma has to be applied by hand. `OpenInv` is a plain `Prop`, so it is wrapped in
a class that the concrete redexes register into. -/

class IsOpenInv (Δ : GradedDivergence.{0} ι) (e : Exp rT) : Prop where
  out : OpenInv Δ e

section Instances
variable [MeasurableSingletonClass rT] [Δ.IsZeroLeft]

instance : IsOpenInv Δ (rT := rT) .urand := ⟨OpenInv.of_atomic Atomic.urand'⟩

instance (l : Loc) : IsOpenInv Δ (rT := rT) pl(!#(.loc l)) := ⟨OpenInv.of_atomic (Atomic.load' l)⟩

instance (l : Loc) (v : Val rT) : IsOpenInv Δ (Exp.store pl(#(.loc l)) v.1) :=
  ⟨OpenInv.of_atomic (Atomic.store' l v)⟩

instance (v : Val rT) : IsOpenInv Δ (Exp.alloc v.1) := ⟨OpenInv.of_atomic (Atomic.alloc' v)⟩

instance (z : Int) : IsOpenInv Δ (rT := rT) pl(rand(#(.int z), #(.unit))) :=
  ⟨OpenInv.of_atomic (Atomic.rand_unit' z)⟩

instance (z : Int) (l : Loc) : IsOpenInv Δ (rT := rT) pl(rand(#(.int z), #(.lbl l))) :=
  ⟨OpenInv.of_atomic (Atomic.rand_lbl' z l)⟩

end Instances

omit [Monoid ι] in
theorem elimAcc_close {X : Type} {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) Δ GF]
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
    {e : Exp rT} [h : IsOpenInv Δ e] {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) Δ GF]
    {P : IProp GF} {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|={E1, E2}=> P) P
      (wp E1 e Φ) (wp E2 e (fun v => iprop(|={E2, E1}=> Φ v))) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans (wp_atomic h.out)

instance (priority := low) elimAcc_wp_atomic {X : Type} {e : Exp rT} [h : IsOpenInv Δ e]
    {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) Δ GF] {Φ : Val rT → IProp GF}
    (E₁ E₂ : CoPset) (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
    ElimAcc True (fupd E₁ E₂) (fupd E₂ E₁) α β γ (wp E₁ e Φ)
      (fun x => wp E₂ e (fun v => iprop(|={E₂}=> β x ∗ (γ x -∗? Φ v)))) where
  elim_acc := by
    dsimp only [accessor]
    iintro %_ Hinner Hacc
    iapply wp_atomic h.out
    imod Hacc with ⟨%x, Hα, Hclose⟩
    imodintro
    ispecialize Hinner $$ %x Hα
    iapply ApproxisWpGS.wp_frame_wand
    iframe Hclose
    iapply ApproxisWpGS.wp_mono
    case HΦ => exact fun _ => elimAcc_close
    iexact Hinner

instance elimAcc_wp_nonatomic {X : Type} {e : Exp rT}
    {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) Δ GF] {Φ : Val rT → IProp GF}
    (E : CoPset) (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
    ElimAcc True (fupd E E) (fupd E E) α β γ (wp E e Φ)
      (fun x => wp E e (fun v => iprop(|={E}=> β x ∗ (γ x -∗? Φ v)))) where
  elim_acc := by
    dsimp only [accessor]
    iintro %_ Hinner Hacc
    iapply ApproxisWpGS.fupd_wp
    imod Hacc with ⟨%x, Hα, Hclose⟩
    imodintro
    ispecialize Hinner $$ %x Hα
    iapply ApproxisWpGS.wp_fupd
    iapply ApproxisWpGS.wp_frame_wand
    iframe Hclose
    iapply ApproxisWpGS.wp_mono
    case HΦ => exact fun _ => elimAcc_close
    iexact Hinner

end ProbLang
