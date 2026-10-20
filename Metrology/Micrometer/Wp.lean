module

public import Metrology.Micrometer.ProgCoupl

/-! # Micrometer weakest precondition

`wpPre` (a spec phase, then a value or one coupled program step, a later and another spec phase),
its guarded fixpoint `wp` with `wp_unfold`, the `WP[L] e @ E {{ Φ }}` notation, `wp_strong_mono`. -/

@[expose] public section

open Std Iris Iris.BI Iris.ProofMode OFE COFE ProbLang GradedLifting

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]

/-! ## `wpPre` and its fixpoint `wp` -/

section Wp
variable [BudgetGS B GF]

/-- The type of `wp` as a function of its mask, expression and postcondition. -/
abbrev WpType := CoPset → Exp rT → (Val rT → IProp GF) → IProp GF

variable (L) in
/-- One unfolding of `wp`: open the invariants, run a spec phase, then either finish at a value or
take one coupled program step followed by a later and another spec phase (Rocq `wp_pre`). -/
abbrev wpPre (wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : Exp rT) (Φ : Val rT → IProp GF) : IProp GF := iprop%
  ∀ σ₁ e₁' σ₁' (b₁ : B),
    stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ budgetInterp b₁ -∗
    |={E, ∅}=> specCoupl L ∅ σ₁ e₁' σ₁' b₁ fun σ₂ ρ' b₂ =>
      match e₁.toVal? with
      | some v => iprop(|={∅, E}=> stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗
          budgetInterp b₂ ∗ Φ v)
      | none => progCoupl L e₁ σ₂ ρ'.expr ρ'.state b₂ fun e₃ σ₃ e₃' σ₃' b₃ => iprop%
          ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E}=>
            stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ budgetInterp b₄ ∗ wp E e₃ Φ)

/-- `wpPre` is non-expansive in the postcondition and needs `wp` to agree only one step lower. -/
theorem wpPre_ne_aux {n : Nat} {wp wp' : WpType (rT := rT) (GF := GF)} {E : CoPset}
    {e : Exp rT} {Φ Ψ : Val rT → IProp GF} (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v)
    (Hwp : ∀ m, m < n → ∀ e₃, wp E e₃ Φ ≡{m}≡ wp' E e₃ Ψ) :
    wpPre L wp E e Φ ≡{n}≡ wpPre L wp' E e Ψ := by
  refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
  refine wand_ne.ne (.of_eq rfl) (BIFUpdate.ne.ne ?_)
  refine least_fixpoint_ne_outer (fun _ _ => ?_) (.of_eq rfl)
  refine or_ne.ne (.of_eq rfl) (or_ne.ne ?_ (.of_eq rfl))
  cases htv : e.toVal? with
  | some v =>
    exact BIFUpdate.ne.ne <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
      sep_ne.ne (.of_eq rfl) (HΦ v)
  | none =>
    refine progCoupl_ne fun e₃ _ _ _ _ => ?_
    refine Contractive.distLater_dist fun m Hm => ?_
    refine specCoupl_ne fun _ _ _ => ?_
    exact BIFUpdate.ne.ne <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
      sep_ne.ne (.of_eq rfl) (Hwp m Hm e₃)

/-- The later after the program step makes `wpPre` contractive, so its fixpoint `wp` exists. -/
instance wpPre_contractive : Contractive (wpPre L (rT := rT) (GF := GF)) where
  distLater_dist Hwp E _ Φ :=
    wpPre_ne_aux (fun _ => .of_eq rfl) fun _ Hm e₃ => DistLater.dist_lt (Hwp · · E e₃ Φ) Hm

variable (L) in
/-- The Micrometer weakest precondition under the lifting `L`, the fixpoint of `wpPre`. -/
noncomputable def wp (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  fixpoint (wpPre L) E e Φ

/-- `wp` is its own one-step unfolding. -/
theorem wp_unfold {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp L E e Φ = wpPre L (wp L) E e Φ :=
  congrFun (congrFun (congrFun (fixpoint_unfold ⟨wpPre L, OFE.ne_of_contractive _⟩) E) e) Φ

/-- The forward direction of `wp_unfold`. -/
theorem wp_unfold_mp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp L E e Φ ⊢ wpPre L (wp L) E e Φ :=
  (BI.equiv_iff.mp wp_unfold).1

/-! ## The continuation after a program step -/

variable (L) in
/-- The `none`-branch continuation of `wpPre` with `wp` itself plugged in; `wp_unfold` produces it
verbatim. -/
noncomputable abbrev wpProgBody (E : CoPset) (Φ : Val rT → IProp GF)
    (e₃ : Exp rT) (σ₃ : State rT) (e₃' : Exp rT) (σ₃' : State rT) (b₃ : B) : IProp GF :=
  iprop% ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E}=>
    stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ budgetInterp b₄ ∗ wp L E e₃ Φ)

/-- At an absorbing budget the continuation holds trivially. -/
theorem wpProgBody_absorbing {E : CoPset} {Φ : Val rT → IProp GF} {b : B} (hb : L.Absorbing b) :
    ⊢ □ ∀ e₃ σ₃ e₃' σ₃', wpProgBody L E Φ e₃ σ₃ e₃' σ₃' b := by
  iintro !> %e₃ %σ₃ %e₃' %σ₃' !>
  iapply specCoupl_absorbing hb

/-- The continuation can be mapped under its later by an update from the old `wp` to a new one,
which may change the mask, the expression and the postcondition. -/
theorem wpProgBody_wand {E E' : CoPset} {Φ Ψ : Val rT → IProp GF} {e₃ e₄ : Exp rT}
    {σ₃ : State rT} {e₃' : Exp rT} {σ₃' : State rT} {b : B} : iprop%
    wpProgBody L E Φ e₃ σ₃ e₃' σ₃' b ∗ ▷ (wp L E e₃ Φ ={E, E'}=∗ wp L E' e₄ Ψ) ⊢
      wpProgBody L E' Ψ e₄ σ₃ e₃' σ₃' b := by
  iintro ⟨HBody, HWand⟩ !>
  iapply specCoupl_mono_spatial
  iframe HBody
  iintro %σ₄ %ρ₄ %b₄ HF
  imod HF with ⟨Hσ, Hs, Hb, Hwp⟩
  imod HWand $$ Hwp with Hwp
  imodintro
  iframe

/-! ## `WP[L] e @ E {{ Φ }}` notation

The postcondition is either a function `{{ Φ }}` or a binder form `{{ v, P }}`; the mask
defaults to `⊤`. -/

declare_syntax_cat micrometerWpPost
syntax ident ", " term : micrometerWpPost
syntax term : micrometerWpPost

/-- `WP[L] e @ E {{ Φ }}` is `wp L E e Φ`. -/
syntax (name := micrometerWp) "WP[" term "] " term:max (" @ " term:max)?
  " {" noWs "{ " micrometerWpPost " }" noWs "}" : term

macro_rules
  | `(WP[$L] $e $[@ $E]? {{ $v:ident, $P:term }}) => do
    let E ← E.getDM `(⊤)
    `(wp $L $E $e (fun $v => iprop($P)))
  | `(WP[$L] $e $[@ $E]? {{ $Φ:term }}) => do
    let E ← E.getDM `(⊤)
    `(wp $L $E $e iprop($Φ))

@[app_unexpander ProbLang.MicrometerWpGS.wp]
meta def unexpandWp : Lean.PrettyPrinter.Unexpander
  | `($_ $L $E $e $Φ) => do
    let post : Lean.TSyntax `micrometerWpPost ← match Φ with
      | `(fun $v:ident => iprop($P)) => `(micrometerWpPost| $v:ident, $P)
      | `(fun $v:ident => $P) => `(micrometerWpPost| $v:ident, $P)
      | `(iprop($P)) => `(micrometerWpPost| $P:term)
      | _ => `(micrometerWpPost| $Φ:term)
    -- `⊤` is a choice node at quotation time (Iris and Mathlib both notate it), so test the token.
    if E.raw.getNumArgs == 1 && E.raw[0].isToken "⊤" then `(WP[$L] $e {{ $post }})
    else `(WP[$L] $e @ $E {{ $post }})
  | _ => throw ()

/-! ## Values -/

theorem wp_value_fupd {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> Φ v) ⊢ wp L E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply wp_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  rw [Exp.toVal?_ofVal]
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iapply specCoupl_ret
  imod Hclose
  imod HΦ
  imodintro
  iframe

theorem wp_value {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    Φ v ⊢ wp L E (Exp.ofVal v) Φ :=
  fupd_intro.trans wp_value_fupd

theorem wp_value_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (h : e.toVal? = some v) : Φ v ⊢ wp L E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact wp_value

theorem wp_value_fupd_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (h : e.toVal? = some v) : iprop(|={E}=> Φ v) ⊢ wp L E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact wp_value_fupd

/-- A weakest precondition at a value unfolds to a spec coupling. -/
theorem wp_value_specCoupl_unfold {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (E : CoPset) (He : e.toVal? = some v) :
    wp L E e Φ ⊢
      ∀ σ₁ e₁' σ₁' b₁,
        stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
          budgetInterp b₁ -∗
          |={E, ∅}=> specCoupl L ∅ σ₁ e₁' σ₁' b₁ (fun σ₂ ρ' b₂ =>
            iprop(|={∅, E}=>
              stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ budgetInterp b₂ ∗ Φ v)) := by
  rw [wp_unfold]
  simp only [wpPre, He]
  exact .rfl

/-! ## Monotonicity and updates -/

/-- The postcondition update `wp_strong_mono` asks for, framing the interpretations. -/
abbrev wpStrongMonoCont (E2 : CoPset) (Φ Ψ : Val rT → IProp GF) : IProp GF := iprop%
  □ ∀ σ ρ v (b : B),
    stateInterp (rT := rT) σ ∗ SpecUpdateGS.specInterp (rT := rT) ρ ∗ budgetInterp b ∗
      Φ v ={E2}=∗
    stateInterp σ ∗ SpecUpdateGS.specInterp ρ ∗ budgetInterp b ∗ Ψ v

variable (L) in
/-- The statement of `wp_strong_mono`, proved by Löb induction. -/
noncomputable abbrev wpStrongMonoStmt : IProp GF := iprop%
  ∀ E1 E2 (e : Exp rT) Φ Ψ, ⌜E1 ⊆ E2⌝ -∗ wp L E1 e Φ -∗ wpStrongMonoCont (B := B) E2 Φ Ψ -∗
    wp L E2 e Ψ

/-- `wp` is monotone in the mask and in the postcondition, where the postcondition update may
use the state, spec and budget interpretations. -/
theorem wp_strong_mono {E1 E2 : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} (HE : E1 ⊆ E2) :
    iprop% wp L E1 e Φ ∗ wpStrongMonoCont (B := B) E2 Φ Ψ ⊢ wp L E2 e Ψ := by
  iintro ⟨HW, HΦ⟩
  -- Löb induction on the statement generalized over masks, expression and postconditions: rebind
  -- the spec phase with `specCoupl_bind`, then recurse under the later after the program step.
  have Hloeb : ⊢@{IProp GF} wpStrongMonoStmt L (rT := rT) := by
    iapply loeb_wand
    iintro !> IH %E1' %E2' %e' %Φ' %Ψ' %HE' HW' #HΦ'
    iapply wp_unfold
    iintro %σ₁ %e₁' %σ₁' %b₁ Hres
    imod BIFUpdate.subset HE' with Hclose
    imod wp_unfold_mp $$ HW' %σ₁ %e₁' %σ₁' %b₁ Hres with HW'
    imodintro
    iapply specCoupl_bind Std.LawfulSet.subset_refl
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
      iapply progCoupl_mono
      iframe HZ₁
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater
      iapply wpProgBody_wand
      iframe HLater
      iintro !> HwpInner
      imod Hclose
      imodintro
      iapply IH $$ %E1' %E2' %e₃ %Φ' %Ψ' %HE' HwpInner HΦ'
  iapply Hloeb $$ %E1 %E2 %e %Φ %Ψ %HE HW HΦ

theorem wp_wand {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop% wp L E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v) ⊢ wp L E e Ψ := by
  iintro ⟨HW, #HΦ⟩
  iapply wp_strong_mono Std.LawfulSet.subset_refl
  iframe HW
  iintro !> %σ %ρ %v %b ⟨Hσ, Hs, Hb, HΦv⟩ !>
  iframe
  iapply HΦ $$ [$]

theorem wp_fupd {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp L E e (fun v => iprop(|={E}=> Φ v)) ⊢ wp L E e Φ := by
  iintro HW
  iapply wp_strong_mono Std.LawfulSet.subset_refl
  iframe HW
  iintro !> %σ %ρ %v %b ⟨Hσ, Hs, Hb, HΦ⟩
  imod HΦ
  iframe

theorem fupd_wp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> wp L E e Φ) ⊢ wp L E e Φ := by
  iintro HF
  iapply wp_unfold
  iintro %σ₁ %e₁' %σ₁' %b₁ Hres
  imod HF with HW
  iapply wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %b₁ Hres

/-! ## Derived monotonicity -/

theorem wp_mono {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF}
    (HΦ : ∀ v, Φ v ⊢ Ψ v) : wp L E e Φ ⊢ wp L E e Ψ := by
  iintro HW
  iapply wp_wand
  iframe HW
  iintro !> %v HΦv
  iapply HΦ $$ HΦv

theorem wp_mask_mono {E1 E2 : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} (HE : E1 ⊆ E2) :
    wp L E1 e Φ ⊢ wp L E2 e Φ := by
  iintro HW
  iapply wp_strong_mono HE
  iframe HW
  iintro !> %σ %ρ %v %b ⟨Hσ, Hs, Hb, HΦ⟩ !>
  iframe

theorem wp_wand_l {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop% □ (∀ v, Φ v -∗ Ψ v) ∗ wp L E e Φ ⊢ wp L E e Ψ :=
  sep_comm.1.trans wp_wand

theorem wp_wand_r {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop% wp L E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v) ⊢ wp L E e Ψ :=
  wp_wand

/-! ## Non-expansiveness -/

/-- `wp` is non-expansive in the postcondition, by strong induction on the step index. -/
theorem wp_ne_aux {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} {n : Nat}
    (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v) : wp L E e Φ ≡{n}≡ wp L E e Ψ := by
  induction n using Nat.strong_induction_on generalizing e Φ Ψ with
  | _ n IH =>
    calc wp L E e Φ
      _ ≡{n}≡ wpPre L (wp L) E e Φ := OFE.eq_dist_1 wp_unfold n
      _ ≡{n}≡ wpPre L (wp L) E e Ψ :=
        wpPre_ne_aux HΦ fun m Hm _ => IH m Hm fun v => OFE.Dist.lt (HΦ v) Hm
      _ ≡{n}≡ wp L E e Ψ := (OFE.eq_dist_1 wp_unfold n).symm

instance wp_ne {E : CoPset} {e : Exp rT} : NonExpansive (wp L (GF := GF) E e) where
  ne _ _ _ H := wp_ne_aux H

-- TODO: `wp_contractive`, as in Iris

end Wp

end MicrometerWpGS

end ProbLang
