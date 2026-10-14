module

public import Metrology.Iris.SpecUpdate
public import Metrology.Iris.ErrorCredits
public import Metrology.Iris.Fixpoint
public import Metrology.Couplings.CodensityCost
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Erasable
public import Metrology.ProbLang.Erasure
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang GradedDivergence

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]

/-! ## Approxis ghost state class

The ghost state does not depend on the graded divergence: `Δ` is an explicit argument of `wp`
and the coupling modalities (`wp Δ E e Φ`, notation `WP[Δ] e @ E {{ Φ }}`), never a class
parameter, so the modality instances (`ElimModal`, `Frame`, ...) unify without a `Δ`
metavariable. `Monoid ι` is a section variable next to `Δ` (`Δ.Codensity` needs it). -/

class ApproxisWpGS {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (GF : BundledGFunctors) extends SpecUpdateGS rT GF where
  hlc : HasLC
  invGS : InvGS_gen hlc GF
  stateInterp : State rT → IProp GF
  errInterp : ENNReal → IProp GF

attribute [reducible, instance] ApproxisWpGS.invGS

namespace ApproxisWpGS
variable {ι : Type} [Monoid ι] {Δ : GradedDivergence.{0} ι} {GF : BundledGFunctors}
  [ApproxisWpGS (rT := rT) GF]

/-! ## `spec_coupl` modality

Optionally prepends spec-side steps and erasable distributions on both sides before `Z`. -/

-- TODO remove when fixpoint is added
abbrev SpecCouplState (rT : Type) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] :
    Type _ := State rT × Cfg rT × ENNReal

instance : COFE (SpecCouplState rT) := COFE.ofDiscrete _
instance : OFE.Discrete (SpecCouplState rT) := ⟨id⟩

variable (Δ) in
/-- The coupling disjunct of `specCouplPre`; `Φ` continues at each `S`-related pair with error
`X₂ ⟨e₂', σ₂'⟩`. -/
abbrev specCouplCouple (E : CoPset) (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε : ENNReal)
    (Φ : SpecCouplState rT → IProp GF) : IProp GF := iprop%
  (∃ (S : State rT → Cfg rT → Prop) (n : Nat) (μ₁ : MeasureTheory.Measure (State rT))
      (μ₁' : MeasureTheory.Measure (State rT)) (ε₁ : ENNReal) (X₂ : Cfg rT → ENNReal) (r : ENNReal),
      ⌜Δ.Codensity 1 ε₁ {p | S p.1 p.2} μ₁ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩)⌝ ∗
      ⌜Measurable X₂⌝ ∗
      ⌜∀ ρ, X₂ ρ ≤ r⌝ ∗
      ⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩)) ≤ ε⌝ ∗
      ⌜ErasableExpr μ₁ σ₁⌝ ∗
      ⌜ErasableExpr μ₁' σ₁'⌝ ∗
      (∀ σ₂ e₂' σ₂', ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ |={E}=> Φ (σ₂, ⟨e₂', σ₂'⟩, X₂ ⟨e₂', σ₂'⟩)))

variable (Δ) in
abbrev specCouplPre (E : CoPset) (Z : State rT → Cfg rT → ENNReal → IProp GF)
    (Φ : SpecCouplState rT → IProp GF) : SpecCouplState rT → IProp GF :=
  fun ⟨σ₁, ⟨e₁', σ₁'⟩, ε⟩ => iprop% ⌜1 ≤ ε⌝ ∨ Z σ₁ ⟨e₁', σ₁'⟩ ε ∨ specCouplCouple Δ E σ₁ e₁' σ₁' ε Φ

variable (Δ) in
abbrev specCoupl (E : CoPset) (σ : State rT) (e' : Exp rT) (σ' : State rT) (ε : ENNReal)
    (Z : State rT → Cfg rT → ENNReal → IProp GF) : IProp GF :=
  bi_least_fixpoint (specCouplPre Δ E Z) (σ, ⟨e', σ'⟩, ε)

omit [ApproxisWpGS (rT := rT) GF] in
theorem specCouplState_ne {Φ : SpecCouplState rT → IProp GF} : NonExpansive Φ where
  ne _ _ _ hd := .of_eq (congrArg Φ (OFE.Discrete.discrete_0 hd))

instance specCouplPre_mono {E : CoPset} {Z : State rT → Cfg rT → ENNReal → IProp GF} :
    BIMonoPred (specCouplPre Δ E Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    icases Hs with ⟨HVac | HZ | HCpl⟩
    · ileft; iexact HVac
    · iright; ileft; iexact HZ
    · iright; iright
      icases HCpl with ⟨%S, %n, %μ₁, %μ₁', %ε₁, %X₂, %r, %Hc, %HX₂meas, %Hb, %Hexp, %Herase₁,
        %Herase₂, Hcont⟩
      iexists S, n, μ₁, μ₁', ε₁, X₂, r
      iframe %
      iintro %σ₂ %e₂' %σ₂' %HS
      imod Hcont $$ %σ₂ %e₂' %σ₂' %HS with HΦ
      imodintro
      iapply Hwand $$ HΦ
  mono_pred_ne := specCouplState_ne

theorem specCoupl_err_ge_1 {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT} {ε : ENNReal}
    {Z : State rT → Cfg rT → ENNReal → IProp GF} (hε : 1 ≤ ε) : ⊢ specCoupl Δ E σ e' σ' ε Z := by
  iapply least_fixpoint_unfold_mpr (specCouplPre Δ E Z)
  ileft; ipureintro; exact hε

theorem specCoupl_ret {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF} :
    Z σ ⟨e', σ'⟩ ε ⊢ specCoupl Δ E σ e' σ' ε Z := by
  iintro HZ
  iapply least_fixpoint_unfold_mpr (specCouplPre Δ E Z)
  iright; ileft; iexact HZ

theorem specCoupl_rec {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF} :
    specCouplCouple Δ E σ e' σ' ε (fun s => specCoupl Δ E s.1 s.2.1.expr s.2.1.state s.2.2 Z) ⊢
    specCoupl Δ E σ e' σ' ε Z := by
  iintro HCpl
  iapply least_fixpoint_unfold_mpr (specCouplPre Δ E Z)
  iright; iright; iexact HCpl

theorem specCoupl_mono {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : State rT → Cfg rT → ENNReal → IProp GF} : iprop%
    □ (∀ σ' ρ' ε', Z₁ σ' ρ' ε' -∗ Z₂ σ' ρ' ε') ∗ specCoupl Δ E σ e' σ' ε Z₁ ⊢
    specCoupl Δ E σ e' σ' ε Z₂ := by
  iintro ⟨#HZ, HC⟩
  unfold specCoupl
  iapply least_fixpoint_strong_mono (specCouplPre Δ E Z₁) (specCouplPre Δ E Z₂) $$ [] HC
  iintro !> %Φ %s HF
  icases HF with ⟨HVac | HZ1 | HCpl⟩
  · ileft; iexact HVac
  · iright; ileft
    iapply HZ $$ HZ1
  · iright; iright
    icases HCpl with ⟨%S, %n, %μ₁, %μ₁', %ε₁, %X₂, %r,
      %HCpl_coupl, %HCpl_meas, %HCpl_bnd, %HCpl_exp, %HCpl_e1, %HCpl_e2, HCpl_cont⟩
    iexists S, n, μ₁, μ₁', ε₁, X₂, r
    iframe %
    iexact HCpl_cont

theorem specCoupl_bind {E1 E2 : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : State rT → Cfg rT → ENNReal → IProp GF} (HE : E1 ⊆ E2) : iprop%
    (∀ σ₂ ρ₂ ε', Z₁ σ₂ ρ₂ ε' -∗ specCoupl Δ E2 σ₂ ρ₂.expr ρ₂.state ε' Z₂) ∗
    specCoupl Δ E1 σ e' σ' ε Z₁ ⊢ specCoupl Δ E2 σ e' σ' ε Z₂ := by
  iintro ⟨HZ, HC⟩
  let HZty : IProp GF := iprop% ∀ σ₂ ρ₂ ε', Z₁ σ₂ ρ₂ ε' -∗ specCoupl Δ E2 σ₂ ρ₂.expr ρ₂.state ε' Z₂
  let Φ : SpecCouplState rT → IProp GF := fun s => iprop%
    HZty -∗ specCoupl Δ E2 s.1 s.2.1.expr s.2.1.state s.2.2 Z₂
  have HΦne : NonExpansive Φ := specCouplState_ne
  ihave Hiter := least_fixpoint_iter (Φ := Φ) $$ [] %(σ, ⟨e', σ'⟩, ε) HC
  swap; iapply Hiter $$ HZ
  iintro !> %s HF HZ
  icases HF with ⟨%HVac | HZ1 | HCpl⟩
  · iapply specCoupl_err_ge_1 HVac
  · iapply HZ $$ HZ1
  · iapply specCoupl_rec
    icases HCpl with ⟨%S, %n, %μ₁, %μ₁', %ε₁, %X₂, %r,
      %HCpl_coupl, %HCpl_meas, %HCpl_bnd, %HCpl_exp, %HCpl_e1, %HCpl_e2, HCpl_cont⟩
    iexists S, n, μ₁, μ₁', ε₁, X₂, r
    iframe %
    iintro %σ₂ %e₂' %σ₂' %HS
    imod BIFUpdate.subset HE with Hclose
    imod HCpl_cont $$ %σ₂ %e₂' %σ₂' %HS with HCpl_cont
    imod Hclose
    imodintro
    iapply HCpl_cont $$ HZ

theorem specCoupl_mono_spatial {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : State rT → Cfg rT → ENNReal → IProp GF} : iprop%
    (∀ σ' ρ' ε', Z₁ σ' ρ' ε' -∗ Z₂ σ' ρ' ε') ∗ specCoupl Δ E σ e' σ' ε Z₁ ⊢
    specCoupl Δ E σ e' σ' ε Z₂ := by
  iintro ⟨HZ, HC⟩
  iapply specCoupl_bind Std.LawfulSet.subset_refl
  iframe HC
  iintro %σ₂ %ρ₂ %ε₂ Hz1
  iapply specCoupl_ret
  iapply HZ $$ Hz1

/-! ## `prog_coupl` modality

Couples exactly one program step against any number of spec steps and an erasable distribution. -/

variable (Δ) in
abbrev progCoupl (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε : ENNReal)
    (Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF) : IProp GF := iprop%
  (∃ (n : Nat) (μ₁' : MeasureTheory.Measure (State rT)) (X₂ : Cfg rT → Cfg rT → ENNReal),
      ⌜Reducible e₁ σ₁⌝ ∗
      ⌜∃ r, ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ r⌝ ∗
      ⌜Δ.CodensityE 1 ε X₂ (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩)⌝ ∗
      ⌜ErasableExpr μ₁' σ₁'⌝ ∗
      (∀ e₂ σ₂ e₂' σ₂', |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)))

theorem specCoupl_ne {n : Nat} {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : State rT → Cfg rT → ENNReal → IProp GF}
    (HZ : ∀ σ ρ ε, Z₁ σ ρ ε ≡{n}≡ Z₂ σ ρ ε) :
    specCoupl Δ E σ e' σ' ε Z₁ ≡{n}≡ specCoupl Δ E σ e' σ' ε Z₂ := by
  unfold specCoupl
  refine least_fixpoint_ne_outer (fun _ s => ?_) (.of_eq rfl)
  exact or_ne.ne (.of_eq rfl) (or_ne.ne (HZ s.1 s.2.1 s.2.2) (.of_eq rfl))

theorem progCoupl_ne {n : Nat} {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    (HZ : ∀ e₂ σ₂ e₂' σ₂' ε', Z₁ e₂ σ₂ e₂' σ₂' ε' ≡{n}≡ Z₂ e₂ σ₂ e₂' σ₂' ε') :
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z₁ ≡{n}≡ progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z₂ := by
  refine exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => ?_
  refine sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
    sep_ne.ne (.of_eq rfl) ?_
  exact forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ =>
    BIFUpdate.ne.ne (HZ _ _ _ _ _)

theorem progCoupl_mono {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF} : iprop%
    (∀ e₂ σ₂ e₂' σ₂' ε', Z₁ e₂ σ₂ e₂' σ₂' ε' -∗ Z₂ e₂ σ₂ e₂' σ₂' ε') ∗
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z₁ ⊢ progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z₂ := by
  iintro ⟨HZ, HCpl⟩
  icases HCpl with ⟨%n, %μ₁', %X₂, %Hred, %Hbnd, %Hexp, %Heras, HCont⟩
  iexists n, μ₁', X₂
  iframe %
  iintro %e₂ %σ₂ %e₂' %σ₂'
  imod HCont $$ %e₂ %σ₂ %e₂' %σ₂' with HZ'
  imodintro
  iapply HZ $$ HZ'

/-! ## Weakest precondition -/

variable (Δ) in
abbrev wpPre (wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : Exp rT) (Φ : Val rT → IProp GF) : IProp GF := iprop%
  ∀ σ₁ e₁' σ₁' ε₁,
    stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε₁ -∗
    |={E, ∅}=> specCoupl Δ ∅ σ₁ e₁' σ₁' ε₁ fun σ₂ ρ' ε₂ =>
      match e₁.toVal? with
      | some v => iprop(|={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ errInterp (rT := rT) ε₂ ∗ Φ v)
      | none => progCoupl Δ e₁ σ₂ ρ'.expr ρ'.state ε₂ fun e₃ σ₃ e₃' σ₃' ε₃ => iprop%
          ▷ specCoupl Δ ∅ σ₃ e₃' σ₃' ε₃ fun σ₄ ρ'' ε₄ => iprop(|={∅, E}=>
            stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ errInterp (rT := rT) ε₄ ∗ wp E e₃ Φ)

abbrev WpType := CoPset → Exp rT → (Val rT → IProp GF) → IProp GF

theorem wpPre_ne_aux {n : Nat} {wp wp' : WpType (rT := rT) (GF := GF)} {E : CoPset}
    {e : Exp rT} {Φ Ψ : Val rT → IProp GF} (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v)
    (Hwp : ∀ m, m < n → ∀ e₃, wp E e₃ Φ ≡{m}≡ wp' E e₃ Ψ) :
    wpPre Δ wp E e Φ ≡{n}≡ wpPre Δ wp' E e Ψ := by
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
    apply Contractive.distLater_dist
    intro m Hm
    refine specCoupl_ne fun _ _ _ => ?_
    exact BIFUpdate.ne.ne <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
      sep_ne.ne (.of_eq rfl) (Hwp m Hm e₃)

instance wpPre_contractive : Contractive (wpPre Δ (rT := rT) (GF := GF)) where
  distLater_dist Hwp E _ Φ :=
    wpPre_ne_aux (fun _ => .of_eq rfl) fun _ Hm e₃ => DistLater.dist_lt (Hwp · · E e₃ Φ) Hm

variable (Δ) in
noncomputable def wp (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  fixpoint (wpPre Δ) E e Φ

theorem wp_unfold {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp Δ E e Φ = wpPre Δ (wp Δ) E e Φ :=
  congrFun (congrFun (congrFun (fixpoint_unfold ⟨wpPre Δ, OFE.ne_of_contractive _⟩) E) e) Φ

theorem wp_unfold_mp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp Δ E e Φ ⊢ wpPre Δ (wp Δ) E e Φ :=
  (BI.equiv_iff.mp wp_unfold).1

/-! ## `WP[Δ] e @ E {{ Φ }}` notation

The postcondition is either a function `{{ Φ }}` or a binder form `{{ v, P }}`; the mask
defaults to `⊤`. -/

declare_syntax_cat approxisWpPost
syntax ident ", " term : approxisWpPost
syntax term : approxisWpPost

/-- `WP[Δ] e @ E {{ Φ }}` is `wp Δ E e Φ`. -/
syntax (name := approxisWp) "WP[" term "] " term:max (" @ " term:max)?
  " {" noWs "{ " approxisWpPost " }" noWs "}" : term

macro_rules
  | `(WP[$Δ] $e $[@ $E]? {{ $v:ident, $P:term }}) => do
    let E ← E.getDM `(⊤)
    `(wp $Δ $E $e (fun $v => iprop($P)))
  | `(WP[$Δ] $e $[@ $E]? {{ $Φ:term }}) => do
    let E ← E.getDM `(⊤)
    `(wp $Δ $E $e iprop($Φ))

@[app_unexpander ProbLang.ApproxisWpGS.wp]
meta def unexpandWp : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $E $e $Φ) => do
    let post : Lean.TSyntax `approxisWpPost ← match Φ with
      | `(fun $v:ident => iprop($P)) => `(approxisWpPost| $v:ident, $P)
      | `(fun $v:ident => $P) => `(approxisWpPost| $v:ident, $P)
      | `(iprop($P)) => `(approxisWpPost| $P:term)
      | _ => `(approxisWpPost| $Φ:term)
    -- `⊤` is a choice node at quotation time (Iris and Mathlib both notate it), so test the token.
    if E.raw.getNumArgs == 1 && E.raw[0].isToken "⊤" then `(WP[$Δ] $e {{ $post }})
    else `(WP[$Δ] $e @ $E {{ $post }})
  | _ => throw ()

variable (Δ) in
noncomputable abbrev wpProgBody (E : CoPset) (Φ : Val rT → IProp GF)
    (e₃ : Exp rT) (σ₃ : State rT) (e₃' : Exp rT) (σ₃' : State rT) (ε₃ : ENNReal) : IProp GF :=
  iprop% ▷ specCoupl Δ ∅ σ₃ e₃' σ₃' ε₃ fun σ₄ ρ'' ε₄ => iprop(|={∅, E}=>
    stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ errInterp (rT := rT) ε₄ ∗ wp Δ E e₃ Φ)

theorem wpProgBody_err_ge_1 {E : CoPset} {Φ : Val rT → IProp GF} :
    ⊢ □ ∀ e₃ σ₃ e₃' σ₃', wpProgBody Δ E Φ e₃ σ₃ e₃' σ₃' 1 := by
  iintro !> %e₃ %σ₃ %e₃' %σ₃' !>
  iapply specCoupl_err_ge_1 (_root_.le_refl _)

/-! ## WP structural lemmas -/

theorem wp_value_fupd {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> Φ v) ⊢ wp Δ E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  rw [Exp.toVal?_ofVal]
  imod BIFUpdate.subset (E1 := E) Std.LawfulSet.empty_subset with Hclose
  imodintro
  iapply specCoupl_ret
  imod Hclose
  imod HΦ
  imodintro
  iframe

theorem wp_value {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    Φ v ⊢ wp Δ E (Exp.ofVal v) Φ :=
  fupd_intro.trans wp_value_fupd

theorem wp_value_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (h : e.toVal? = some v) : Φ v ⊢ wp Δ E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact wp_value

abbrev wpStrongMonoCont (E2 : CoPset) (Φ Ψ : Val rT → IProp GF) : IProp GF := iprop% □ ∀ σ ρ v ε,
    stateInterp (rT := rT) σ ∗ SpecUpdateGS.specInterp (rT := rT) ρ ∗ errInterp (rT := rT) ε ∗
      Φ v ={E2}=∗
    stateInterp (rT := rT) σ ∗ SpecUpdateGS.specInterp (rT := rT) ρ ∗ errInterp (rT := rT) ε ∗
      Ψ v

variable (Δ) in
noncomputable abbrev wpStrongMonoStmt : IProp GF := iprop%
  ∀ E1 E2 (e : Exp rT) Φ Ψ, ⌜E1 ⊆ E2⌝ -∗ wp Δ E1 e Φ -∗ wpStrongMonoCont E2 Φ Ψ -∗ wp Δ E2 e Ψ

theorem wp_strong_mono' {E1 E2 : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} (HE : E1 ⊆ E2) :
    iprop% wp Δ E1 e Φ ∗ wpStrongMonoCont E2 Φ Ψ ⊢ wp Δ E2 e Ψ := by
  iintro ⟨HW, HΦ⟩
  have Hloeb : ⊢@{IProp GF} wpStrongMonoStmt Δ (rT := rT) := by
    iapply loeb_wand
    iintro !> IH %E1' %E2' %e' %Φ' %Ψ' %HE' HW' #HΦ'
    iapply wp_unfold
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    imod BIFUpdate.subset HE' with Hclose
    imod wp_unfold_mp $$ HW' %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε] with HW'
    imodintro
    iapply specCoupl_bind Std.LawfulSet.subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %ε₂ HZ₁
    cases htv : e'.toVal? with
    | some v =>
      iapply specCoupl_ret
      imod HZ₁ with ⟨Hσ', Hs', Hε', HΦv⟩
      imod Hclose
      iapply HΦ' $$ [Hσ' Hs' Hε' HΦv]
      iframe
    | none =>
      iapply specCoupl_ret
      iapply progCoupl_mono
      iframe HZ₁
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HCont !>
      iapply specCoupl_mono_spatial
      iframe HCont
      iintro %σ₄ %ρ₄ %ε₄ HInner
      imod HInner with ⟨Hσ', Hs', Hε', HwpInner⟩
      imod Hclose
      imodintro
      iframe
      iapply IH $$ %E1' %E2' %e₃ %Φ' %Ψ' %HE' HwpInner HΦ'
  iapply Hloeb $$ %E1 %E2 %e %Φ %Ψ %HE HW HΦ

theorem wp_wand {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop% wp Δ E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v) ⊢ wp Δ E e Ψ := by
  iintro ⟨HW, #HΦ⟩
  iapply wp_strong_mono' Std.LawfulSet.subset_refl
  iframe HW
  iintro !> %σ %ρ %v %ε ⟨Hσ, Hs, Hε, HΦv⟩ !>
  iframe
  iapply HΦ $$ [$]

theorem wp_fupd {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp Δ E e (fun v => iprop(|={E}=> Φ v)) ⊢ wp Δ E e Φ := by
  iintro HW
  iapply wp_strong_mono' Std.LawfulSet.subset_refl
  iframe HW
  iintro !> %σ %ρ %v %ε ⟨Hσ, Hs, Hε, HΦ⟩
  imod HΦ
  iframe

theorem fupd_wp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> wp Δ E e Φ) ⊢ wp Δ E e Φ := by
  iintro HF
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ Hres
  imod HF with HW
  iapply wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %ε₁ Hres

/-! ## Derived WP lemmas -/

theorem wp_strong_mono {E1 E2 : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} (HE : E1 ⊆ E2) :
    iprop% wp Δ E1 e Φ ∗ wpStrongMonoCont E2 Φ Ψ ⊢ wp Δ E2 e Ψ :=
  wp_strong_mono' HE

theorem wp_mono {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF}
    (HΦ : ∀ v, Φ v ⊢ Ψ v) : wp Δ E e Φ ⊢ wp Δ E e Ψ := by
  iintro HW
  iapply wp_wand
  iframe HW
  iintro !> %v HΦv
  iapply HΦ $$ HΦv

theorem wp_mask_mono {E1 E2 : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} (HE : E1 ⊆ E2) :
    wp Δ E1 e Φ ⊢ wp Δ E2 e Φ := by
  iintro HW
  iapply wp_strong_mono' HE
  iframe HW
  iintro !> %σ %ρ %v %ε ⟨Hσ, Hs, Hε, HΦ⟩ !>
  iframe

theorem wp_wand_l {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop% □ (∀ v, Φ v -∗ Ψ v) ∗ wp Δ E e Φ ⊢ wp Δ E e Ψ :=
  sep_comm.1.trans wp_wand

theorem wp_wand_r {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop% wp Δ E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v) ⊢ wp Δ E e Ψ :=
  wp_wand

/-! ### Measure-theoretic plumbing for the coupling-intro rules -/

theorem lintegral_const_le {α : Type _} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
    (hν : ν Set.univ ≤ 1) (c : ENNReal) : ∫⁻ _, c ∂ν ≤ c := by
  rw [MeasureTheory.lintegral_const]
  calc c * ν Set.univ ≤ c * 1 := by gcongr
    _ = c := mul_one c

theorem bindPexecN_univ_le_one {n : Nat} {e' : Exp rT}
    {μ : MeasureTheory.Measure (State rT)} (hμ : μ Set.univ ≤ 1) :
    (μ.bind fun σ => pexecN n ⟨e', σ⟩) Set.univ ≤ 1 := by
  have hk : Measurable fun σ => pexecN n ⟨e', σ⟩ := by fun_prop
  rw [MeasureTheory.Measure.bind_apply MeasurableSet.univ hk.aemeasurable]
  calc ∫⁻ σ, pexecN n ⟨e', σ⟩ Set.univ ∂μ
    _ ≤ ∫⁻ _, 1 ∂μ := MeasureTheory.lintegral_mono fun σ => pexecN_univ_le_one n _
    _ ≤ 1 := lintegral_const_le hμ 1

theorem concentrated_primStep_support (e : Exp rT) (σ : State rT) (hne : e.decomp.2 ≠ .urand) :
    Concentrated (primStep ⟨e, σ⟩) {ρ | 0 < primStep ⟨e, σ⟩ {ρ}} := by
  have heq : {ρ | 0 < primStep ⟨e, σ⟩ {ρ}}ᶜ = {ρ | primStep ⟨e, σ⟩ {ρ} = 0} := by
    ext ρ; simp [pos_iff_ne_zero]
  show primStep ⟨e, σ⟩ _ = 0
  rw [heq]
  exact primStep_atomic e σ hne

theorem lintegral_le_of_clamped {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    {h₁ : α → ENNReal} {h₂ : β → ENNReal} {ε₁ ε₂ ε : ENNReal}
    (Hε : ε₁ + ε₂ ≤ ε) (hν : ν Set.univ ≤ 1)
    (H : (∫⁻ a, h₁ a ∂μ) ≤ (∫⁻ b, (h₂ b + ε₂) ⊓ 1 ∂ν) + ε₁) :
    (∫⁻ a, h₁ a ∂μ) ≤ (∫⁻ b, h₂ b ∂ν) + ε := by
  refine H.trans ?_
  calc (∫⁻ b, (h₂ b + ε₂) ⊓ 1 ∂ν) + ε₁ ≤ (∫⁻ b, (h₂ b + ε₂) ∂ν) + ε₁ := by gcongr; exact inf_le_left
    _ = (∫⁻ b, h₂ b ∂ν) + ε₂ * ν Set.univ + ε₁ := by
      rw [MeasureTheory.lintegral_add_right _ measurable_const, MeasureTheory.lintegral_const,
        mul_comm]
    _ ≤ (∫⁻ b, h₂ b ∂ν) + ε₂ + ε₁ := by
      gcongr
      calc ε₂ * ν Set.univ ≤ ε₂ * 1 := by gcongr
        _ = ε₂ := mul_one _
    _ ≤ (∫⁻ b, h₂ b ∂ν) + ε := by rw [add_assoc, add_comm ε₂ ε₁]; gcongr

theorem lintegral_le_of_one_le {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    {h₁ : α → ENNReal} {h₂ : β → ENNReal} {ε₁ ε₂ ε : ENNReal}
    (Hε : ε₁ + ε₂ ≤ ε) (hε₂ : 1 ≤ ε₂) (hμ : μ Set.univ ≤ 1) (Hh₁ : ∀ a, h₁ a ≤ 1) :
    (∫⁻ a, h₁ a ∂μ) ≤ (∫⁻ b, h₂ b ∂ν) + ε :=
  calc (∫⁻ a, h₁ a ∂μ) ≤ ∫⁻ _, 1 ∂μ := MeasureTheory.lintegral_mono Hh₁
    _ ≤ 1 := lintegral_const_le hμ 1
    _ ≤ ε₂ := hε₂
    _ ≤ ε := _root_.le_trans _root_.le_add_self Hε
    _ ≤ _ := _root_.le_add_self

/-- An additive coupling gives a coupling in expectation for any cost bounded on the relation
(the `tv` form of `Codensity.codensityE`). -/
theorem expCoupl_of_addCoupl {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} {R : α → β → Prop}
    {Y : α → β → ENNReal} {ε₁ ε₂ ε : ENNReal}
    (Hε : ε₁ + ε₂ ≤ ε) (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1)
    (HY : ∀ a b, R a b → Y a b ≤ ε₂) (Hcpl : AddCoupl ε₁ {p | R p.1 p.2} μ ν) :
    ExpCoupl ε Y μ ν := by
  intro h₁ h₂ Hh₁meas Hh₂meas Hh₁ Hh₂ Hh₁h₂
  by_cases hε₂ : ε₂ ≤ 1
  · refine lintegral_le_of_clamped Hε hν ?_
    have := Hcpl ⟨h₁, Hh₁meas, Hh₁⟩
      ⟨fun b => (h₂ b + ε₂) ⊓ 1, (Hh₂meas.add_const _).inf measurable_const, fun _ => inf_le_right⟩
      (fun {a b} (hab : R a b) => le_inf ((Hh₁h₂ a b).trans (by gcongr; exact HY a b hab)) (Hh₁ a))
    simpa using this
  · exact lintegral_le_of_one_le Hε (_root_.not_le.mp hε₂).le hμ Hh₁

/-- Adding a constant to the cost of a coupling in expectation adds it to the bound
(the `tv` form of `CodensityE.add_const`). -/
theorem expCoupl_add_const {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} {X₂ : α → β → ENNReal}
    {ε₁ ε₂ ε : ENNReal} (Hε : ε₁ + ε₂ ≤ ε) (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1)
    (H : ExpCoupl ε₁ X₂ μ ν) : ExpCoupl ε (fun a b => X₂ a b + ε₂) μ ν := by
  intro h₁ h₂ Hh₁meas Hh₂meas Hh₁ Hh₂ Hh₁h₂
  by_cases hε₂ : ε₂ ≤ 1
  · refine lintegral_le_of_clamped Hε hν ?_
    refine H h₁ (fun b => (h₂ b + ε₂) ⊓ 1) Hh₁meas
      ((Hh₂meas.add_const _).inf measurable_const) Hh₁ (fun _ => inf_le_right) ?_
    intro a b
    by_cases hlt : h₂ b + ε₂ ≤ 1
    · rw [inf_of_le_left hlt]
      calc h₁ a ≤ h₂ b + (X₂ a b + ε₂) := Hh₁h₂ a b
        _ = (h₂ b + ε₂) + X₂ a b := by ring
    · rw [inf_of_le_right (_root_.not_le.mp hlt).le]
      exact le_add_right (Hh₁ a)
  · exact lintegral_le_of_one_le Hε (_root_.not_le.mp hε₂).le hμ Hh₁

theorem specCoupl_couple {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {S : State rT → Cfg rT → Prop} {n : Nat} {ε₁ r : ENNReal} {X₂ : Cfg rT → ENNReal}
    {μ₁ μ₁' : MeasureTheory.Measure (State rT)}
    (Hcpl : Δ.Codensity 1 ε₁ {p | S p.1 p.2} μ₁ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩))
    (HX₂meas : Measurable X₂) (Hbnd : ∀ ρ, X₂ ρ ≤ r)
    (Hexp : ε₁ + (∫⁻ ρ, X₂ ρ ∂(μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩)) ≤ ε)
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ e₂' σ₂', ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ |={E}=> specCoupl Δ E σ₂ e₂' σ₂' (X₂ ⟨e₂', σ₂'⟩) Z) ⊢
    specCoupl Δ E σ₁ e₁' σ₁' ε Z := by
  iintro H
  iapply specCoupl_rec
  iexists S, n, μ₁, μ₁', ε₁, X₂, r
  iframe %
  iexact H

/-! ### `specCoupl` — derived lemmas -/

theorem fupd_specCoupl_of_le {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε₁ ε₂ : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF} (Hε : ε₁ ≤ ε₂) :
    iprop(|={E}=> specCoupl Δ E σ e' σ' ε₁ Z) ⊢ specCoupl Δ E σ e' σ' ε₂ Z := by
  iintro HF
  iapply specCoupl_couple (S := fun s c => s = σ ∧ c = ⟨e', σ'⟩) (n := 0) (ε₁ := ε₂ - ε₁)
    (X₂ := fun _ => ε₁)
    (by
      rw [MeasureTheory.Measure.dirac_bind (by fun_prop)]
      simp only [pexecN_zero]
      refine (codensity_dirac ?_).mono_bound zero_le
      exact ⟨rfl, rfl⟩)
    measurable_const (fun _ => _root_.le_refl _)
    (by
      refine _root_.le_trans ?_ (tsub_add_cancel_of_le Hε).le
      gcongr
      exact lintegral_const_le (bindPexecN_univ_le_one (by simp)) ε₁)
    (ErasableExpr.dret σ) (ErasableExpr.dret σ')
  iintro %σ₂ %e₂' %σ₂' %HS'
  obtain ⟨rfl, ⟨⟩⟩ := HS'
  iexact HF

theorem specCoupl_mono_err {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε₁ ε₂ : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF} (Hε : ε₁ ≤ ε₂) :
    specCoupl Δ E σ e' σ' ε₁ Z ⊢ specCoupl Δ E σ e' σ' ε₂ Z :=
  fupd_intro.trans (fupd_specCoupl_of_le Hε)

theorem fupd_specCoupl {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF} :
    iprop(|={E}=> specCoupl Δ E σ e' σ' ε Z) ⊢ specCoupl Δ E σ e' σ' ε Z :=
  fupd_specCoupl_of_le (_root_.le_refl _)

theorem specCoupl_ind {E : CoPset} {Ψ Z : State rT → Cfg rT → ENNReal → IProp GF} : iprop%
    □ (∀ σ c ε, specCouplPre Δ E Z (fun s => iprop(Ψ s.1 s.2.1 s.2.2 ∧
      specCoupl Δ E s.1 s.2.1.expr s.2.1.state s.2.2 Z)) (σ, c, ε) -∗ Ψ σ c ε) ⊢
    ∀ σ e' σ' ε, specCoupl Δ E σ e' σ' ε Z -∗ Ψ σ ⟨e', σ'⟩ ε := by
  iintro #IH %σ %e' %σ' %ε HC
  let Ψ' : SpecCouplState rT → IProp GF := fun s => Ψ s.1 s.2.1 s.2.2
  have HΨne : NonExpansive Ψ' := specCouplState_ne
  iapply least_fixpoint_ind (F := specCouplPre Δ E Z) (Φ := Ψ') $$ [] %(σ, ⟨e', σ'⟩, ε) HC
  iintro !> %s HF
  obtain ⟨σ'', c, ε'⟩ := s
  iapply IH $$ %σ'' %c %ε' HF

theorem specCoupl_erasables_exp {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF} {R : State rT → State rT → Prop}
    {μ₁ μ₁' : MeasureTheory.Measure (State rT)} {X₂ : State rT → ENNReal} {r : ENNReal}
    (Hcpl : Δ.Codensity 1 ε₁ {p | R p.1 p.2} μ₁ μ₁') (HX₂meas : Measurable X₂)
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁')
    (Hbnd : ∀ σ', X₂ σ' ≤ r) (Hexp : ε₁ + ∫⁻ σ', X₂ σ' ∂μ₁' ≤ ε) : iprop%
    (∀ σ₂ σ₂', ⌜R σ₂ σ₂'⌝ -∗ |={E}=> specCoupl Δ E σ₂ e₁' σ₂' (X₂ σ₂') Z) ⊢
    specCoupl Δ E σ₁ e₁' σ₁' ε Z := by
  iintro H
  have heq : μ₁'.bind (fun σ => pexecN 0 ⟨e₁', σ⟩) = μ₁'.map (fun σ => (⟨e₁', σ⟩ : Cfg rT)) := by
    simp only [pexecN_zero]
    exact MeasureTheory.Measure.bind_dirac_eq_map _ (by fun_prop)
  iapply specCoupl_couple (S := fun σ₂ c => R σ₂ c.state ∧ c.expr = e₁') (n := 0)
    (ε₁ := ε₁) (X₂ := fun ρ => X₂ ρ.state)
    (by
      rw [heq]
      exact Hcpl.map_right fun _ _ HR => ⟨HR, rfl⟩)
    (HX₂meas.comp Cfg.measurable_state) (fun _ => Hbnd _)
    (by
      refine _root_.le_trans ?_ Hexp
      gcongr
      rw [heq, MeasureTheory.lintegral_map (by fun_prop) (by fun_prop)])
    Heras₁ Heras₁'
  iintro %σ₂ %e₂' %σ₂' %HS
  obtain ⟨HR, rfl⟩ := HS
  iapply H $$ %σ₂ %σ₂' %HR

theorem specCoupl_erasables {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε₂ ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {R : State rT → State rT → Prop} {μ₁ μ₁' : MeasureTheory.Measure (State rT)}
    (Hε : ε₁ + ε₂ ≤ ε) (Hcpl : Δ.Codensity 1 ε₁ {p | R p.1 p.2} μ₁ μ₁')
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ σ₂', ⌜R σ₂ σ₂'⌝ -∗ |={E}=> specCoupl Δ E σ₂ e₁' σ₂' ε₂ Z) ⊢
    specCoupl Δ E σ₁ e₁' σ₁' ε Z := by
  iintro H
  have Hexp_bnd : ε₁ + ∫⁻ _, ε₂ ∂μ₁' ≤ ε := by
    refine _root_.le_trans ?_ Hε
    rw [MeasureTheory.lintegral_const, ErasableExpr.mass Heras₁', mul_one]
  iapply specCoupl_erasables_exp (X₂ := fun _ => ε₂) Hcpl measurable_const Heras₁ Heras₁'
    (fun _ => _root_.le_refl _) Hexp_bnd
  iintro %σ₂ %σ₂' %HR
  iapply H $$ %σ₂ %σ₂' %HR

theorem specCoupl_erasable_steps {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {n : Nat} {ε₁ ε₂ ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {R : State rT → Cfg rT → Prop} {μ₁ : MeasureTheory.Measure (State rT)}
    (Hε : ε₁ + ε₂ ≤ ε) (Hcpl : Δ.Codensity 1 ε₁ {p | R p.1 p.2} μ₁ (pexecN n ⟨e₁', σ₁'⟩))
    (Heras₁ : ErasableExpr μ₁ σ₁) : iprop%
    (∀ σ₂ e₂' σ₂', ⌜R σ₂ ⟨e₂', σ₂'⟩⌝ -∗ |={E}=> specCoupl Δ E σ₂ e₂' σ₂' ε₂ Z) ⊢
    specCoupl Δ E σ₁ e₁' σ₁' ε Z := by
  iintro H
  iapply specCoupl_couple (S := R) (n := n) (ε₁ := ε₁) (X₂ := fun _ => ε₂)
    (by rwa [MeasureTheory.Measure.dirac_bind (by fun_prop)])
    measurable_const (fun _ => _root_.le_refl _)
    (by
      refine _root_.le_trans ?_ Hε
      gcongr
      exact lintegral_const_le (bindPexecN_univ_le_one (by simp)) ε₂)
    Heras₁ (ErasableExpr.dret σ₁')
  iintro %σ₂ %e₂' %σ₂' %HR
  iapply H $$ %σ₂ %e₂' %σ₂' %HR

theorem specCoupl_steps {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {n : Nat} {ε₁ ε₂ ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {R : State rT → Cfg rT → Prop} (Hε : ε₁ + ε₂ ≤ ε)
    (Hcpl : Δ.Codensity 1 ε₁ {p | R p.1 p.2} (MeasureTheory.Measure.dirac σ₁)
      (pexecN n ⟨e₁', σ₁'⟩)) :
    iprop% (∀ σ₂ e₂' σ₂', ⌜R σ₂ ⟨e₂', σ₂'⟩⌝ -∗ |={E}=> specCoupl Δ E σ₂ e₂' σ₂' ε₂ Z) ⊢
    specCoupl Δ E σ₁ e₁' σ₁' ε Z :=
  specCoupl_erasable_steps Hε Hcpl (ErasableExpr.dret σ₁)

theorem specCoupl_steps_det {E : CoPset} {σ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {e₂' : Exp rT} {σ₂' : State rT} {n : Nat} {ε : ENNReal}
    {Z : State rT → Cfg rT → ENNReal → IProp GF}
    (Hstep : pexecN n ⟨e₁', σ₁'⟩ = MeasureTheory.Measure.dirac ⟨e₂', σ₂'⟩) :
    specCoupl Δ E σ e₂' σ₂' ε Z ⊢ specCoupl Δ E σ e₁' σ₁' ε Z := by
  iintro HS
  iapply specCoupl_couple (S := fun s c => s = σ ∧ c = ⟨e₂', σ₂'⟩) (n := n) (ε₁ := 0)
    (X₂ := fun _ => ε)
    (by
      rw [MeasureTheory.Measure.dirac_bind (by fun_prop), Hstep]
      exact codensity_dirac ⟨rfl, rfl⟩)
    measurable_const (fun _ => _root_.le_refl _)
    (by
      rw [zero_add]
      exact lintegral_const_le (bindPexecN_univ_le_one (by simp)) ε)
    (ErasableExpr.dret σ) (ErasableExpr.dret σ₁')
  iintro %σ₂ %e₂'' %σ₂'' %HS' !>
  obtain ⟨rfl, ⟨⟩⟩ := HS'
  iexact HS

theorem specCoupl_step_concentrated [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft]
    {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {S : Set (Cfg rT)} (Hred : Reducible e₁' σ₁')
    (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁', σ₁'⟩) S) : iprop%
    (∀ e₂' σ₂', ⌜⟨e₂', σ₂'⟩ ∈ S⌝ -∗ |={E}=> specCoupl Δ E σ₁ e₂' σ₂' ε Z) ⊢
    specCoupl Δ E σ₁ e₁' σ₁' ε Z := by
  iintro H
  have Hε : 0 + ε ≤ ε := by rw [zero_add]
  have := prim_step_mass Hred
  have hpexec1 : pexecN 1 ⟨e₁', σ₁'⟩ = primStep ⟨e₁', σ₁'⟩ := by
    rw [pexecN_one, stepOrFinal_not_isValue (val_stuck Hred)]
  have HcplR : Δ.Codensity 1 0 {p | (fun σ c => σ = σ₁ ∧ c ∈ S) p.1 p.2}
      (MeasureTheory.Measure.dirac σ₁) (pexecN 1 ⟨e₁', σ₁'⟩) := by
    rw [hpexec1]
    exact codensity_dirac_left hSmeas hSconc σ₁
  iapply specCoupl_steps (n := 1) (R := fun σ c => σ = σ₁ ∧ c ∈ S) Hε HcplR
  iintro %σ₂ %e₂' %σ₂' %HR
  obtain ⟨rfl, Hmem⟩ := HR
  iapply H $$ %e₂' %σ₂' %Hmem

@[discrete]
theorem specCoupl_step [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft]
    {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    (Hred : Discrete.Reducible e₁' σ₁') (hne : e₁'.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ e₂' σ₂', ⌜0 < primStep ⟨e₁', σ₁'⟩ {⟨e₂', σ₂'⟩}⌝ -∗ |={E}=> specCoupl Δ E σ₁ e₂' σ₂' ε Z) ⊢
    specCoupl Δ E σ₁ e₁' σ₁' ε Z :=
  specCoupl_step_concentrated Hred.toReducible (measurableSet_primStep_support e₁' σ₁')
    (concentrated_primStep_support e₁' σ₁' hne)

/-! ## `progCoupl` — derived lemmas -/

theorem progCoupl_reducible {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF} :
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z ⊢ ⌜Reducible e₁ σ₁⌝ := by
  iintro ⟨%n, %μ₁', %X₂, %Hred, -⟩
  ipureintro; exact Hred

theorem progCoupl_intro {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {n : Nat} {μ₁' : MeasureTheory.Measure (State rT)} {r : ENNReal}
    {X₂ : Cfg rT → Cfg rT → ENNReal} (Hred : Reducible e₁ σ₁) (Hbnd : ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ r)
    (Hexp : Δ.CodensityE 1 ε X₂ (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩))
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ e₂' σ₂', |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z := by
  have Hbnd : ∃ r, ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ r := ⟨r, Hbnd⟩
  iintro H
  iexists n, μ₁', X₂
  iframe %
  iexact H

theorem dirac_bind_pexecN_one {e₁' : Exp rT} {σ₁' : State rT} (Hred' : Reducible e₁' σ₁') :
    (MeasureTheory.Measure.dirac σ₁').bind (fun σ => pexecN 1 ⟨e₁', σ⟩) = primStep ⟨e₁', σ₁'⟩ := by
  rw [MeasureTheory.Measure.dirac_bind (by fun_prop), pexecN_one,
    stepOrFinal_not_isValue (val_stuck Hred')]

theorem progCoupl_strong_mono [Δ.IsZeroLeft] {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {S : Set (Cfg rT)} (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
    iprop% (□ ∀ e₂ σ₂ e₂' σ₂', Z₂ e₂ σ₂ e₂' σ₂' 1) ∗
    (∀ e₂ σ₂ e₂' σ₂' ε', ⌜⟨e₂, σ₂⟩ ∈ S⌝ ∗ Z₁ e₂ σ₂ e₂' σ₂' ε' -∗ Z₂ e₂ σ₂ e₂' σ₂' ε') ∗
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z₁ ⊢ progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z₂ := by
  iintro ⟨#H1F, Hm, HCpl⟩
  icases HCpl with ⟨%n, %μ₁', %X₂, %Hred, %Hbnd, %Hexp, %Heras, HCont⟩
  obtain ⟨r, Hr⟩ := Hbnd
  classical
  have Hbnd' : ∀ a b, (if a ∈ S then X₂ a b else 1) ≤ max r 1 := by
    intro a b
    split_ifs with h
    · exact (Hr a b).trans (le_max_left _ _)
    · exact le_max_right _ _
  have Hexp' : Δ.CodensityE 1 ε (fun a b => if a ∈ S then X₂ a b else 1)
      (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) :=
    Hexp.concentrated_L hSmeas hSconc fun a ha b => by simp [ha]
  iapply progCoupl_intro Hred Hbnd' Hexp' Heras
  iintro %e₂ %σ₂ %e₂' %σ₂'
  by_cases hmem : ⟨e₂, σ₂⟩ ∈ S
  · simp only [ite_eq_left hmem]
    imod HCont $$ %e₂ %σ₂ %e₂' %σ₂' with HZ₁
    imodintro
    iapply Hm $$ %e₂ %σ₂ %e₂' %σ₂' %(X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) [HZ₁]
    iframe %hmem HZ₁
  · simp only [ite_eq_right hmem]
    imodintro
    iexact H1F

theorem progCoupl_strengthen [Δ.IsZeroLeft] {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {S : Set (Cfg rT)} (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
    iprop% (□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗ progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z ⊢
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε fun e₂ σ₂ e₂' σ₂' ε' =>
      iprop(⌜⟨e₂, σ₂⟩ ∈ S ∨ 1 ≤ ε'⌝ ∧ Z e₂ σ₂ e₂' σ₂' ε') := by
  iintro ⟨#H1F, HCpl⟩
  iapply progCoupl_strong_mono hSmeas hSconc
  isplitr
  · iintro !> %e₂ %σ₂ %e₂' %σ₂'
    isplitr; · ipureintro; exact .inr (_root_.le_refl _)
    iexact H1F
  iframe HCpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %ε' ⟨%Hmem, HZ⟩
  isplitr; · ipureintro; exact .inl Hmem
  iexact HZ

theorem progCoupl_ctx_bind {K : Ectx rT} {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    (hv : ¬ e₁.isValue) : iprop%
    (□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗ progCoupl Δ e₁ σ₁ e₁' σ₁' ε (fun e₂ => Z (K.fill e₂)) ⊢
    progCoupl Δ (K.fill e₁) σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, HCpl⟩
  icases HCpl with ⟨%n, %μ₁', %X₂, %Hred, %Hbnd, %Hexp, %Heras, HCont⟩
  obtain ⟨r, Hr⟩ := Hbnd
  classical
  let Kinv : Exp rT → Option (Exp rT) := Function.partialInv K.fill
  have Kinv_left : ∀ e, Kinv (K.fill e) = some e := Function.partialInv_left (Ectx.fill_injective K)
  have Hbnd' : ∀ a b : Cfg rT, (match Kinv a.expr with
      | some e' => X₂ ⟨e', a.state⟩ b
      | none => 1) ≤ max r 1 := by
    intro a b
    cases Kinv a.expr with
    | none => exact le_max_right _ _
    | some e' => exact (Hr _ _).trans (le_max_left _ _)
  have Hexp' : Δ.CodensityE 1 ε (fun a b => match Kinv a.expr with
        | some e' => X₂ ⟨e', a.state⟩ b
        | none => 1)
      (primStep ⟨K.fill e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) := by
    rw [primStep_fill hv, ← MeasureTheory.Measure.map_id (μ := μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩)]
    exact (Hexp.mono_cost fun ρ b => by simp [Kinv_left]).map (by fun_prop) measurable_id
  iapply progCoupl_intro (Hred.fill K) Hbnd' Hexp' Heras
  iintro %e₂ %σ₂ %e₂' %σ₂'
  cases hKinv : Kinv e₂ with
  | none =>
    imodintro
    iexact H1F
  | some e₃ =>
    have he₂ : K.fill e₃ = e₂ :=
      (Function.Injective.isPartialInv (Ectx.fill_injective K) e₃ e₂).1 hKinv
    imod HCont $$ %e₃ %σ₂ %e₂' %σ₂' with HZ
    imodintro
    rw [← he₂]
    iexact HZ

/-! ### `progCoupl` — coupling-intro lemmas -/

theorem progCoupl_steps_adv' {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {X₂ : Cfg rT → Cfg rT → ENNReal}
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁') (Hbnd : ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ 1)
    (Hcpl : Δ.CodensityE 1 ε X₂ (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z :=
  progCoupl_intro Hred Hbnd (dirac_bind_pexecN_one Hred' ▸ Hcpl) (ErasableExpr.dret σ₁')

theorem progCoupl_steps_adv {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε₂ ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {X₂ : Cfg rT → Cfg rT → ENNReal} (Hε : ε₁ + ε₂ ≤ ε)
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁') (Hbnd : ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ 1)
    (Hcpl : Δ.CodensityE 1 ε₁ X₂ (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂)) ⊢
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z := by
  iintro Hcnt
  iapply progCoupl_intro (r := 1 + ε₂) (X₂ := fun a b => X₂ a b + ε₂) Hred
    (fun a b => by gcongr; exact Hbnd a b)
    (by rw [dirac_bind_pexecN_one Hred']; exact (Hcpl.add_const ε₂).mono_bound Hε)
    (ErasableExpr.dret σ₁')
  iexact Hcnt

theorem progCoupl_steps {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε₂ ε : ENNReal} {R : Cfg rT → Cfg rT → Prop}
    {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    (Hε : ε₁ + ε₂ ≤ ε) (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : Δ.Codensity 1 ε₁ {p | R p.1 p.2} (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ -∗ |={∅}=> Z e₂ σ₂ e₂' σ₂' ε₂) ⊢
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, Hcnt⟩
  classical
  let Y : Cfg rT → Cfg rT → ENNReal := fun ρ₁ ρ₂ => if R ρ₁ ρ₂ ∧ ε₂ ≤ 1 then ε₂ else 1
  have HY_bnd : ∀ ρ₁ ρ₂, Y ρ₁ ρ₂ ≤ 1 := fun ρ₁ ρ₂ => by grind
  have HY_exp : Δ.CodensityE 1 ε Y (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) :=
    (Hcpl.codensityE fun a b hab => by grind).mono_bound Hε
  iapply progCoupl_steps_adv' Hred Hred' HY_bnd HY_exp
  iintro %e₂ %σ₂ %e₂' %σ₂'
  simp only [Y]
  split_ifs with h
  · iapply Hcnt $$ %e₂ %σ₂ %e₂' %σ₂' %(h.1)
  · imodintro
    iexact H1F

theorem progCoupl_step_l_erasable_adv {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {μ₁' : MeasureTheory.Measure (State rT)} {ε : ENNReal}
    {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {X₂ : Cfg rT → State rT → ENNReal} (Hred : Reducible e₁ σ₁) (Heras : ErasableExpr μ₁' σ₁')
    (Hbnd : ∀ ρ₁ σ₂', X₂ ρ₁ σ₂' ≤ 1)
    (Hcpl : Δ.CodensityE 1 ε X₂ (primStep ⟨e₁, σ₁⟩) μ₁') : iprop%
    (□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
    (∀ e₂ σ₂ σ₂', |={∅}=> Z e₂ σ₂ e₁' σ₂' (X₂ ⟨e₂, σ₂⟩ σ₂')) ⊢ progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, Hcnt⟩
  classical
  have Hbnd' : ∀ ρ₁ ρ₂ : Cfg rT, (if ρ₂.expr = e₁' then X₂ ρ₁ ρ₂.state else 1) ≤ 1 :=
    fun ρ₁ ρ₂ => by grind
  have Hexp' : Δ.CodensityE 1 ε (fun ρ₁ ρ₂ => if ρ₂.expr = e₁' then X₂ ρ₁ ρ₂.state else 1)
      (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN 0 ⟨e₁', σ⟩) := by
    simp only [pexecN_zero]
    rw [MeasureTheory.Measure.bind_dirac_eq_map _ (by fun_prop),
      ← MeasureTheory.Measure.map_id (μ := primStep ⟨e₁, σ₁⟩)]
    exact (Hcpl.mono_cost fun ρ σ => by simp).map measurable_id (by fun_prop)
  iapply progCoupl_intro Hred Hbnd' Hexp' Heras
  iintro %e₂ %σ₂ %e₂' %σ₂'
  by_cases he : e₂' = e₁'
  · subst he
    simp only [↓reduceIte]
    iapply Hcnt $$ %e₂ %σ₂ %σ₂'
  · simp only [ite_eq_right he]
    imodintro
    iexact H1F

theorem progCoupl_step_l_erasable {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {μ₁' : MeasureTheory.Measure (State rT)} {ε₁ ε₂ ε : ENNReal}
    {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {R : Cfg rT → State rT → Prop} (Hε : ε₁ + ε₂ ≤ ε) (Hred : Reducible e₁ σ₁)
    (Hcpl : Δ.Codensity 1 ε₁ {p | R p.1 p.2} (primStep ⟨e₁, σ₁⟩) μ₁')
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
    (∀ e₂ σ₂ σ₂', ⌜R ⟨e₂, σ₂⟩ σ₂'⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₂' ε₂) ⊢
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, Hcnt⟩
  classical
  let Y : Cfg rT → State rT → ENNReal := fun ρ₁ σ₂' => if R ρ₁ σ₂' ∧ ε₂ ≤ 1 then ε₂ else 1
  have HY_bnd : ∀ ρ₁ σ₂', Y ρ₁ σ₂' ≤ 1 := fun ρ₁ σ₂' => by grind
  have HY_exp : Δ.CodensityE 1 ε Y (primStep ⟨e₁, σ₁⟩) μ₁' :=
    (Hcpl.codensityE fun a b hab => by grind).mono_bound Hε
  iapply progCoupl_step_l_erasable_adv Hred Heras HY_bnd HY_exp
  iframe H1F
  iintro %e₂ %σ₂ %σ₂'
  simp only [Y]
  split_ifs with h
  · iapply Hcnt $$ %e₂ %σ₂ %σ₂' %(h.1)
  · imodintro
    iexact H1F

/-- Step the left program against a right state that does not move, for an additive coupling
with the right Dirac measure. -/
theorem progCoupl_step_l_dret {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε₂ ε : ENNReal} {R : Cfg rT → State rT → Prop}
    {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    (Hε : ε₁ + ε₂ ≤ ε) (Hred : Reducible e₁ σ₁)
    (Hcpl : AddCoupl ε₁ {p | R p.1 p.2} (primStep ⟨e₁, σ₁⟩) (MeasureTheory.Measure.dirac σ₁')) :
    iprop% (□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
    (∀ e₂ σ₂, ⌜R ⟨e₂, σ₂⟩ σ₁'⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₁' ε₂) ⊢
      progCoupl TVDiv.tv.{0} e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, H⟩
  classical
  have hconc : MeasureTheory.Measure.dirac σ₁' {σ₁'}ᶜ = 0 := by
    rw [MeasureTheory.Measure.dirac_apply' _ (by measurability)]; simp
  have HcplR : AddCoupl ε₁ {p | R p.1 p.2 ∧ p.2 = σ₁'}
      (primStep ⟨e₁, σ₁⟩) (MeasureTheory.Measure.dirac σ₁') := by
    refine AddCoupl.mono_rel ?_ (AddCoupl.concentrated_R (MeasurableSet.singleton σ₁') hconc Hcpl)
    rintro ⟨ρ, σ⟩ ⟨HR, hmem⟩
    exact ⟨HR, hmem⟩
  iapply progCoupl_step_l_erasable (R := fun ρ σ => R ρ σ ∧ σ = σ₁') Hε Hred HcplR.codensity
    (ErasableExpr.dret σ₁')
  iframe H1F
  iintro %e₂ %σ₂ %σ₂' %HR'
  obtain ⟨HR, rfl⟩ := HR'
  iapply H $$ %e₂ %σ₂ %HR

theorem progCoupl_step_l_concentrated [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft]
    {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {S : Set (Cfg rT)} (Hred : Reducible e₁ σ₁)
    (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) : iprop%
    (□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
    (∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₁' ε) ⊢ progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, H⟩
  have := prim_step_mass Hred
  have Hε : 0 + ε ≤ ε := by rw [zero_add]
  have HcplR : Δ.Codensity 1 0 {p | (fun ρ σ => ρ ∈ S ∧ σ = σ₁') p.1 p.2}
      (primStep ⟨e₁, σ₁⟩) (MeasureTheory.Measure.dirac σ₁') :=
    codensity_dirac_right hSmeas hSconc σ₁'
  iapply progCoupl_step_l_erasable (R := fun ρ σ => ρ ∈ S ∧ σ = σ₁') Hε Hred HcplR
    (ErasableExpr.dret σ₁')
  iframe H1F
  iintro %e₂ %σ₂ %σ₂' %HR
  obtain ⟨Hmem, rfl⟩ := HR
  iapply H $$ %e₂ %σ₂ %Hmem

/-! ## WP — outer OFE instances and `IntoVal`-style value intros -/

theorem wp_value_fupd_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (h : e.toVal? = some v) : iprop(|={E}=> Φ v) ⊢ wp Δ E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact wp_value_fupd

theorem wp_ne_aux {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} {n : Nat}
    (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v) : wp Δ E e Φ ≡{n}≡ wp Δ E e Ψ := by
  induction n using Nat.strong_induction_on generalizing e Φ Ψ with
  | _ n IH =>
    have heq1 : wp Δ E e Φ ≡{n}≡ wpPre Δ (wp Δ) E e Φ := OFE.eq_dist_1 wp_unfold n
    have heq2 : wp Δ E e Ψ ≡{n}≡ wpPre Δ (wp Δ) E e Ψ := OFE.eq_dist_1 wp_unfold n
    refine heq1.trans (OFE.Dist.trans ?_ heq2.symm)
    exact wpPre_ne_aux HΦ fun m Hm _ => IH m Hm fun v => OFE.Dist.lt (HΦ v) Hm

instance wp_ne {E : CoPset} {e : Exp rT} : NonExpansive (wp Δ (GF := GF) E e) where
  ne _ _ _ H := wp_ne_aux H

-- TODO: `wp_contractive` — `wp` is `Contractive` in its post when the head
-- is *not* a value. Needs structural `wp_unfold` walk under the
-- `e.toVal? = none` branch; dual to `wpPre_contractive` restricted to `none`.

/-! ## WP — structural lemmas -/

variable (Δ) in
noncomputable abbrev wpBindStmt (K : Ectx rT) : IProp GF := iprop%
  ∀ E e Φ, wp Δ E e (fun v => wp Δ E (K.fill (Exp.ofVal v)) Φ) -∗ wp Δ E (K.fill e) Φ

theorem wp_bind {K : Ectx rT} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp Δ E e (fun v => wp Δ E (K.fill (Exp.ofVal v)) Φ) ⊢ wp Δ E (K.fill e) Φ := by
  have Hloeb : ⊢@{IProp GF} wpBindStmt Δ K := by
    iapply loeb_wand
    iintro !> IH %E' %e' %Φ' HW
    iapply wp_unfold
    unfold wpPre
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε] with HW'
    imodintro
    iapply specCoupl_bind Std.LawfulSet.subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %ε₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      iapply fupd_specCoupl
      rw [show e' = Exp.ofVal v from (Exp.ofVal_of_toVal_some htv).symm]
      imod HBody with ⟨Hσ', Hs', Hε', HInner⟩
      imod wp_unfold_mp $$ HInner %σ₂ %ρ₂.expr %ρ₂.state %ε₂ [$Hσ' $Hs' $Hε'] with HInner'
      imodintro
      iexact HInner'
    | none =>
      have hv : ¬ e'.isValue := Exp.toVal?_eq_none.mp htv
      have hvKfill : ¬ (K.fill e').isValue := fun hKv => hv (Ectx.fill_isValue hKv)
      have hKfillnone : (K.fill e').toVal? = none := Exp.toVal?_eq_none.mpr hvKfill
      iapply specCoupl_ret
      simp only [hKfillnone]
      iapply progCoupl_ctx_bind hv
      isplitr; · iapply wpProgBody_err_ge_1
      iapply progCoupl_mono (Z₁ := wpProgBody Δ E' fun v => wp Δ E' (K.fill (Exp.ofVal v)) Φ')
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater !>
      iapply specCoupl_mono_spatial
      iframe HLater
      iintro %σ₄ %ρ₄ %ε₄ HF
      imod HF with ⟨Hσ', Hs', Hε', HwpInner⟩
      imodintro
      iframe Hσ' Hs' Hε'
      iapply IH $$ %E' %e₃ %Φ' HwpInner
  iapply Hloeb $$ %E %e %Φ

-- TODO: `wp_atomic` — for atomic `e`, an inner `|={E2, E1}=>` can be absorbed.
-- In ProbLang every head step is atomic (reduces to a value or single `primStep`),
-- so state it with an explicit "atomic" predicate over `e` instead of an `Atomic` typeclass.

theorem specUpdate_wp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    specUpdate rT E (wp Δ E e Φ) ⊢ wp Δ E e Φ := by
  unfold specUpdate
  iintro HS
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  imod HS $$ %⟨e₁', σ₁'⟩ Hs with ⟨%ρ', %n, %Hstep, Hs', HW⟩
  cases ρ' with
  | mk e₂' σ₂' =>
    imod wp_unfold_mp $$ HW %σ₁ %e₂' %σ₂' %ε₁ [$Hσ $Hs' $Hε] with HW'
    imodintro
    iapply specCoupl_steps_det Hstep $$ HW'

variable (Δ) in
noncomputable abbrev wpSpecUpdateStmt : IProp GF := iprop%
  ∀ E (e : Exp rT) Φ, wp Δ E e (fun v => specUpdate rT E (Φ v)) -∗ wp Δ E e Φ

theorem wp_specUpdate {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp Δ E e (fun v => specUpdate rT E (Φ v)) ⊢ wp Δ E e Φ := by
  have Hloeb : ⊢@{IProp GF} wpSpecUpdateStmt Δ (rT := rT) := by
    iapply loeb_wand
    iintro !> IH %E' %e' %Φ' HW
    iapply wp_unfold
    unfold wpPre
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε] with HW'
    imodintro
    iapply specCoupl_bind Std.LawfulSet.subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %ε₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      iapply fupd_specCoupl
      imod HBody with ⟨Hσ', Hs', Hε', HUpd⟩
      imod HUpd $$ %ρ₂ Hs' with ⟨%ρ₃, %n, %Hstep, Hs'', HΦv⟩
      cases ρ₃ with
      | mk e₃' σ₃' =>
        imod BIFUpdate.subset (E1 := E') Std.LawfulSet.empty_subset with Hclose
        imodintro
        iapply specCoupl_steps_det Hstep
        iapply specCoupl_ret
        imod Hclose
        imodintro
        iframe
    | none =>
      iapply specCoupl_ret
      iapply progCoupl_mono (Z₁ := wpProgBody Δ E' fun v => specUpdate rT E' (Φ' v))
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater !>
      iapply specCoupl_mono_spatial
      iframe HLater
      iintro %σ₄ %ρ₄ %ε₄ HF
      imod HF with ⟨Hσ', Hs', Hε', HwpInner⟩
      imodintro
      iframe Hσ' Hs' Hε'
      iapply IH $$ %E' %e₃ %Φ' HwpInner
  iapply Hloeb $$ %E %e %Φ

/-! ## WP — framing lemmas -/

variable (Δ) in
noncomputable abbrev wpFrameLStmt : IProp GF := iprop%
  ∀ E (e : Exp rT) R Φ, R -∗ wp Δ E e Φ -∗ wp Δ E e fun v => iprop(R ∗ Φ v)

theorem wp_frame_l {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop% R ∗ wp Δ E e Φ ⊢ wp Δ E e fun v => iprop(R ∗ Φ v) := by
  have Hloeb : ⊢@{IProp GF} wpFrameLStmt Δ (rT := rT) := by
    iapply loeb_wand
    iintro !> IH %E' %e' %R' %Φ' HR HW
    iapply wp_unfold
    unfold wpPre
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε] with HW'
    imodintro
    iapply specCoupl_mono_spatial
    iframe HW'
    iintro %σ₂ %ρ₂ %ε₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      imod HBody with ⟨Hσ', Hs', Hε', HΦv⟩
      simp only []
      imodintro
      iframe
    | none =>
      iapply progCoupl_mono
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater !>
      iapply specCoupl_mono_spatial
      iframe HLater
      iintro %σ₄ %ρ₄ %ε₄ HFinal
      imod HFinal with ⟨Hσ', Hs', Hε', HwpInner⟩
      imodintro
      iframe
      iapply IH $$ %E' %e₃ %R' %Φ' HR HwpInner
  iintro ⟨HR, HW⟩
  iapply Hloeb $$ %E %e %R %Φ HR HW

theorem wp_frame_r {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop% wp Δ E e Φ ∗ R ⊢ wp Δ E e fun v => iprop(Φ v ∗ R) := by
  iintro ⟨HW, HR⟩
  ihave HW := wp_frame_l $$ [$HR $HW]
  iapply wp_wand
  iframe HW
  iintro !> %v ⟨HRv, HΦv⟩
  iframe

theorem wp_frame_wand {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop% R ∗ wp Δ E e (fun v => iprop(R -∗ Φ v)) ⊢ wp Δ E e Φ := by
  iintro ⟨HR, HW⟩
  ihave HW := wp_frame_l $$ [$HR $HW]
  iapply wp_wand
  iframe HW
  iintro !> %v ⟨HRv, HW'⟩
  iapply HW' $$ HRv

theorem wp_step_fupd {E1 E2 : CoPset} {e : Exp rT} {P : IProp GF} {Φ : Val rT → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) : iprop%
    (|={E1, E2}=> ▷ |={E2, E1}=> P) ∗ wp Δ E2 e (fun v => iprop(P -∗ Φ v)) ⊢ wp Δ E1 e Φ := by
  iintro ⟨HR, HW⟩
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  imod HR with HR
  imod wp_unfold_mp $$ HW %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε] with HW'
  imodintro
  iapply specCoupl_mono_spatial
  iframe HW'
  iintro %σ₂ %ρ₂ %ε₂ HBody
  simp only [hv]
  iapply progCoupl_mono
  iframe HBody
  iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater !>
  iapply specCoupl_mono_spatial
  iframe HLater
  iintro %σ₄ %ρ₄ %ε₄ HFinal
  imod HFinal with ⟨Hσ', Hs', Hε', HwpInner⟩
  imod HR with HR
  imodintro
  iframe Hσ' Hs' Hε'
  iapply wp_mask_mono HE
  ihave HwpInner := wp_frame_l $$ [$HR $HwpInner]
  iapply wp_wand
  iframe HwpInner
  iintro !> %v ⟨HP, HWand⟩
  iapply HWand $$ HP

theorem wp_frame_step_l {E1 E2 : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) : iprop%
    (|={E1, E2}=> ▷ |={E2, E1}=> R) ∗ wp Δ E2 e Φ ⊢ wp Δ E1 e fun v => iprop(R ∗ Φ v) := by
  iintro ⟨HR, HW⟩
  iapply wp_step_fupd HE hv
  iframe HR
  iapply wp_wand
  iframe HW
  iintro !> %v HΦ HR'
  iframe

theorem wp_frame_step_r {E1 E2 : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) : iprop%
    wp Δ E2 e Φ ∗ (|={E1, E2}=> ▷ |={E2, E1}=> R) ⊢ wp Δ E1 e fun v => iprop(Φ v ∗ R) := by
  iintro ⟨HW, HR⟩
  iapply wp_step_fupd HE hv
  iframe HR
  iapply wp_wand
  iframe HW
  iintro !> %v HΦ HR'
  iframe

instance isExcept0_wp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    IsExcept0 (wp Δ E e Φ) where
  is_except0 := (except0_mono fupd_intro).trans (BIFUpdate.except0.trans fupd_wp)

instance frame_wp {p : Bool} {E : CoPset} {e : Exp rT} {R : IProp GF}
    {Φ Ψ : Val rT → IProp GF} [inst : ∀ v, Frame p R (Φ v) (Ψ v)] :
    Frame p R (wp Δ E e Φ) (wp Δ E e Ψ) where
  frame := wp_frame_l.trans (wp_mono fun v => (inst v).frame)

instance addModal_fupd_wp {E : CoPset} {e : Exp rT} {P : IProp GF} {Φ : Val rT → IProp GF} :
    AddModal iprop(|={E}=> P) P (wp Δ E e Φ) where
  add_modal := fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

instance elimModal_bupd_wp {p : Bool} {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|==> P) P (wp Δ E e Φ) (wp Δ E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    (sep_mono_left BIUpdateFUpdate.fupd_of_bupd).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

instance elimModal_fupd_wp {p : Bool} {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|={E}=> P) P (wp Δ E e Φ) (wp Δ E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

instance elimModal_specUpdate_wp {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True false io false (specUpdate rT E P) P (wp Δ E e Φ) (wp Δ E e Φ) where
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

instance elimModal_specUpdateN_wp {n : Nat} {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True false io false (specUpdateN rT n E P) P (wp Δ E e Φ) (wp Δ E e Φ) where
  elim_modal _ := by
    simp only [Bool.false_eq_true, ↓reduceIte, intuitionisticallyIf]
    iintro ⟨HP, Hcnt⟩
    ihave HP' := specUpdateN_specUpdate $$ HP
    iapply specUpdate_wp
    iintro %ρ Hρ
    imod HP' $$ %ρ Hρ with ⟨%ρ', %n', %Hstep, Hρ', HPv⟩
    imodintro
    iexists ρ', n'
    iframe %Hstep Hρ'
    iapply Hcnt $$ HPv

/-! ## Lifting lemmas (ports `clutch/theories/approxis/lifting.v`) -/

theorem wp_lift_step_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    (∀ σ₁ e₁' σ₁' ε₁, stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      errInterp (rT := rT) ε₁ -∗ |={E, ∅}=> specCoupl Δ ∅ σ₁ e₁' σ₁' ε₁ fun σ₂ ρ' ε₂ =>
        match e₁.toVal? with
        | some v => iprop(|={∅, E}=>
            stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ errInterp (rT := rT) ε₂ ∗ Φ v)
        | none => progCoupl Δ e₁ σ₂ ρ'.expr ρ'.state ε₂ fun e₃ σ₃ e₃' σ₃' ε₃ => iprop%
            ▷ specCoupl Δ ∅ σ₃ e₃' σ₃' ε₃ fun σ₄ ρ'' ε₄ => iprop(|={∅, E}=>
              stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ errInterp (rT := rT) ε₄ ∗
                wp Δ E e₃ Φ)) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_unfold
  unfold wpPre
  iexact H

theorem wp_lift_step_spec_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    (∀ (σ₁ : State rT) e₁' σ₁' ε₁, stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      errInterp (rT := rT) ε₁ -∗ |={E, ∅}=>
      specCoupl Δ ∅ σ₁ e₁' σ₁' ε₁ fun σ₂ ρ' ε₂ => iprop(|={∅, E}=>
        stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ errInterp (rT := rT) ε₂ ∗ wp Δ E e₁ Φ)) ⊢
    wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  imod H $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε] with H
  imodintro
  iapply specCoupl_bind Std.LawfulSet.subset_refl
  iframe H
  iintro %σ₂ %ρ₂ %ε₂ HInner
  iapply fupd_specCoupl
  imod HInner with ⟨Hσ', Hs', Hε', HW⟩
  imod wp_unfold_mp $$ HW %σ₂ %ρ₂.expr %ρ₂.state %ε₂ [$Hσ' $Hs' $Hε'] with HW'
  imodintro
  iexact HW'

theorem wp_lift_step_prog_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' ε₁, stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      errInterp (rT := rT) ε₁ -∗ |={E, ∅}=>
      progCoupl Δ e₁ σ₁ e₁' σ₁' ε₁ fun e₂ σ₂ e₂' σ₂' ε₂ => iprop% ▷ |={∅, E}=>
        stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗ errInterp (rT := rT) ε₂ ∗
          wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  imod H $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε] with H
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_mono (Z₁ := fun e₂ σ₂ e₂' σ₂' ε₂ => iprop% ▷ |={∅, E}=>
    stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗ errInterp (rT := rT) ε₂ ∗ wp Δ E e₂ Φ)
  iframe H
  iintro %e₂ %σ₂ %e₂' %σ₂' %ε₂ HL !>
  iapply specCoupl_ret
  iexact HL

/-! ### Rules that pair the program step with a Dirac on the other side

Everything below routes through `specCoupl_step_concentrated` or `progCoupl_step_l_concentrated`,
which build the exact coupling along a diagonal (`codensity_dirac_left`/`_right`). -/

section ConcentratedRules
variable [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft]

theorem wp_lift_step_later_concentrated {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none) (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=> ⌜Reducible e₁ σ₁⌝ ∗ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗
      |={∅}=> ▷ |={∅, E}=> stateInterp σ₂ ∗ wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_step_l_concentrated Hred (hSmeas σ₁) (hSconc σ₁)
  isplitr; · iapply wpProgBody_err_ge_1
  iintro %e₂ %σ₂ %Hmem
  imod H $$ %e₂ %σ₂ %Hmem with H
  iintro !> !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', HwpNew⟩
  imodintro
  iframe

@[discrete]
theorem wp_lift_step_later {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) (hne : e₁.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=> ⌜Discrete.Reducible e₁ σ₁⌝ ∗ ∀ e₂ σ₂,
      ⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝ -∗ |={∅}=> ▷ |={∅, E}=> stateInterp σ₂ ∗ wp Δ E e₂ Φ) ⊢
    wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_step_later_concentrated Hv (fun σ₁ => measurableSet_primStep_support e₁ σ₁)
    (fun σ₁ => concentrated_primStep_support e₁ σ₁ hne)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  isplitr; · ipureintro; exact Hred.toReducible
  iintro %e₂ %σ₂ %Hmem
  iapply H $$ %e₂ %σ₂ %Hmem

theorem wp_lift_step_concentrated {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none) (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=> ⌜Reducible e₁ σ₁⌝ ∗ ▷ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗
      |={∅, E}=> stateInterp σ₂ ∗ wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_step_later_concentrated Hv hSmeas hSconc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem wp_lift_prim_steps_coupl {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' ε,
      stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε -∗
      |={E, ∅}=> ∃ (R : Cfg rT → Cfg rT → Prop) (ε₁ ε₂ : ENNReal),
        ⌜ε₁ + ε₂ ≤ ε⌝ ∗
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜Reducible e₁' σ₁'⌝ ∗
        ⌜Δ.Codensity 1 ε₁ {p | R p.1 p.2} (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
        (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ -∗ |={∅}=> ▷ |={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗ errInterp (rT := rT) ε₂ ∗
            wp Δ E e₂ Φ)) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  imod H $$ %σ₁ %e₁' %σ₁' %ε [$Hσ $Hs $Hε] with ⟨%R, %ε₁, %ε₂, %Hεsum, %Hred, %Hred', %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_steps Hεsum Hred Hred' Hcpl
  isplitr; · iapply wpProgBody_err_ge_1
  iintro %e₂ %σ₂ %e₂' %σ₂' %HR
  imod H $$ %e₂ %σ₂ %e₂' %σ₂' %HR with H
  iintro !> !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', Hs', Hε', Hwp'⟩
  imodintro
  iframe

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem wp_lift_prim_step_l_erasable {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' ε,
      stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε -∗
      |={E, ∅}=> ∃ (R : Cfg rT → State rT → Prop) (μ₁' : MeasureTheory.Measure (State rT))
        (ε₁ ε₂ : ENNReal),
        ⌜ε₁ + ε₂ ≤ ε⌝ ∗
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜ErasableExpr μ₁' σ₁'⌝ ∗
        ⌜Δ.Codensity 1 ε₁ {p | R p.1 p.2} (primStep ⟨e₁, σ₁⟩) μ₁'⌝ ∗
        (∀ e₂ σ₂ σ₂', ⌜R ⟨e₂, σ₂⟩ σ₂'⌝ -∗ |={∅}=> ▷ |={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₂'⟩ ∗ errInterp (rT := rT) ε₂ ∗
            wp Δ E e₂ Φ)) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  imod H $$ %σ₁ %e₁' %σ₁' %ε [$Hσ $Hs $Hε] with
    ⟨%R, %μ₁', %ε₁, %ε₂, %Hεsum, %Hred, %Heras, %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_step_l_erasable Hεsum Hred Hcpl Heras
  isplitr; · iapply wpProgBody_err_ge_1
  iintro %e₂ %σ₂ %σ₂' %HR
  imod H $$ %e₂ %σ₂ %σ₂' %HR with H
  iintro !> !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', Hs', Hε', Hwp'⟩
  imodintro
  iframe

theorem wp_lift_atomic_step_fupd_concentrated {E1 E2 : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E1}=> ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗ |={E1}[E2]▷=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp Δ E1 e₁ Φ := by
  iintro H
  iapply wp_lift_step_later_concentrated Hv hSmeas hSconc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imod BIFUpdate.subset (E1 := E1) Std.LawfulSet.empty_subset with Hclose
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hmem
  imod Hclose
  imod H $$ %e₂ %σ₂ %Hmem with H
  imod BIFUpdate.subset (E1 := E2) Std.LawfulSet.empty_subset with Hclose
  iintro !> !>
  imod Hclose
  cases htv : e₂.toVal? with
  | some v =>
    imod H with ⟨Hσ', HΦ⟩
    imodintro
    iframe Hσ'
    iapply wp_value_of_toVal htv $$ HΦ
  | none =>
    imod H with ⟨Hσ', HΦ⟩
    iexfalso
    iexact HΦ

@[discrete]
theorem wp_lift_atomic_step_fupd {E1 E2 : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) (hne : e₁.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E1}=> ⌜Discrete.Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝ -∗ |={E1}[E2]▷=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp Δ E1 e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd_concentrated (E2 := E2) Hv
    (fun σ₁ => measurableSet_primStep_support e₁ σ₁)
    (fun σ₁ => concentrated_primStep_support e₁ σ₁ hne)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  isplitr; · ipureintro; exact Hred.toReducible
  iintro %e₂ %σ₂ %Hpstep
  iapply H $$ %e₂ %σ₂ %Hpstep

theorem wp_lift_atomic_step_concentrated {E : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=> ⌜Reducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗ |={E}=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd_concentrated (E2 := E) Hv hSmeas hSconc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

@[discrete]
theorem wp_lift_atomic_step {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) (hne : e₁.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=> ⌜Discrete.Reducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂, ⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝ -∗ |={E}=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd (E2 := E) Hv hne
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hpstep !> !>
  iapply H $$ %e₂ %σ₂ %Hpstep

theorem wp_lift_pure_det_step_concentrated {E E' : CoPset} {e₁ e₂ : Exp rT}
    {Φ : Val rT → IProp GF} (Hpure : PureStep e₁ e₂) :
    iprop(|={E}[E']▷=> wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ := by
  iintro H
  have Hv : e₁.toVal? = none := by
    rcases htv : e₁.toVal? with _ | v
    · rfl
    · exact absurd (Exp.toVal?_isValue htv) (val_stuck (Hpure.safe default))
  iapply wp_lift_step_concentrated (S := fun σ₁ => {(⟨e₂, σ₁⟩ : Cfg rT)}) Hv
    (fun σ₁ => by measurability)
    (fun σ₁ => by
      show primStep ⟨e₁, σ₁⟩ _ = 0
      rw [Hpure.det σ₁, MeasureTheory.Measure.dirac_apply' _ (by measurability)]
      simp)
  iintro %σ₁ Hσ
  imod H
  imod BIFUpdate.subset (E1 := E') Std.LawfulSet.empty_subset with Hclose
  imodintro
  isplitr; · ipureintro; exact Hpure.safe σ₁
  iintro !> %e₂' %σ₂ %Hmem
  have heq : (⟨e₂', σ₂⟩ : Cfg rT) = ⟨e₂, σ₁⟩ := Hmem
  cases heq
  imod Hclose
  imod H
  imodintro
  iframe Hσ
  iexact H

/-! ### Countability-free pure-step rules

Stated on the measure-theoretic `PureStep` / `PureExec`, so they hold for a diffuse `rT`. -/

theorem wp_pure_step_one' {E : CoPset} {e₁ e₂ : Exp rT} {Φ : Val rT → IProp GF}
    (Hstep : PureStep e₁ e₂) : iprop(▷ wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_pure_det_step_concentrated (E' := E) Hstep
  iintro !> !> !>
  iexact H

theorem wp_pure_step_fupd' {E E' : CoPset} {e₁ e₂ : Exp rT} {φ : Prop} {n : Nat}
    {Φ : Val rT → IProp GF} [Hex : PureExec φ n e₁ e₂] (Hφ : φ) :
    iprop(|={E}[E']▷=>^[n] wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ := by
  have Hsteps := Hex.pure_exec Hφ
  clear Hex
  induction n generalizing e₁ with
  | zero =>
    simp only [nsteps] at Hsteps
    subst Hsteps
    exact .rfl
  | succ n IH =>
    obtain ⟨c, Hstep, Hrest⟩ := Hsteps
    simp only [Nat.repeat]
    iintro H
    iapply wp_lift_pure_det_step_concentrated Hstep
    imod H; imodintro; iintro !>; imod H; imodintro
    iapply IH Hrest $$ H

theorem wp_pure_step_later' {E : CoPset} {e₁ e₂ : Exp rT} {φ : Prop} {n : Nat}
    {Φ : Val rT → IProp GF} [Hex : PureExec φ n e₁ e₂] (Hφ : φ) :
    iprop(▷^[n] wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ := by
  refine BI.Entails.trans ?_ (wp_pure_step_fupd' (E' := E) (e₂ := e₂) (n := n) Hφ)
  induction n with
  | zero =>
    exact .rfl
  | succ n ih =>
    refine (BI.later_mono ih).trans ?_
    simp only [Nat.repeat]
    iintro H !> !> !>
    iexact H

/-! ## Evaluation-context lifting lemmas (ports `clutch/theories/approxis/ectx_lifting.v`) -/

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem wp_lift_head_step_prog_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' ε₁, stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      errInterp (rT := rT) ε₁ -∗ |={E, ∅}=> ⌜∃ ρ : Cfg rT, 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝ ∗
      progCoupl Δ e₁ σ₁ e₁' σ₁' ε₁ fun e₂ σ₂ e₂' σ₂' ε₂ => iprop% ▷ |={∅, E}=>
        stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗ errInterp (rT := rT) ε₂ ∗
          wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_step_prog_couple Hv
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  imod H $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε] with ⟨-, H⟩
  imodintro
  iexact H

@[discrete]
theorem wp_lift_atomic_head_step {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) (Hlc : e₁.IsLocallyClosed := by is_lc)
    (hne : e₁.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=> ⌜∃ ρ : Cfg rT, 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝ ∗
      ▷ ∀ e₂ σ₂, ⌜0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝ -∗ |={E}=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step Hv hne
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hhred, H⟩
  imodintro
  have Hhr : HeadReducible e₁ σ₁ := let ⟨ρ, hρ⟩ := Hhred; fun hz => by rw [hz] at hρ; simp at hρ
  isplitr; · ipureintro; exact Reducible.toDiscrete hne (reducible_of_headReducible Hlc Hhr)
  iintro !> %e₂ %σ₂ %Hpstep
  have hpos : 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩} :=
    primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible Hlc Hhr) ▸ Hpstep
  iapply H $$ %e₂ %σ₂ %hpos

/-! ### Countability-free head-step rules

The head-step rules gate on `headStep` rather than `primStep`. Head-reducibility
is established *inside* the assertion (from the state interpretation), so the
carrying set cannot simply be required to carry `primStep` at every `σ₁` — at a
state where `e₁` is not head-reducible the redex may sit under a context and
`primStep` moves elsewhere. The trick is to pad the carrying set to `Set.univ`
off the head-reducible states, where concentration is free. -/

open scoped Classical in
theorem measurableSet_headPad {e₁ : Exp rT} {S : State rT → Set (Cfg rT)}
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁)) (σ₁ : State rT) :
    MeasurableSet (if HeadReducible e₁ σ₁ then S σ₁ else Set.univ) := by
  split_ifs; exacts [hSmeas σ₁, MeasurableSet.univ]

open scoped Classical in
theorem concentrated_headPad {e₁ : Exp rT} {S : State rT → Set (Cfg rT)} (Hlc : e₁.IsLocallyClosed)
    (hSconc : ∀ σ₁, HeadReducible e₁ σ₁ → Concentrated (headStep ⟨e₁, σ₁⟩) (S σ₁))
    (σ₁ : State rT) :
    Concentrated (primStep ⟨e₁, σ₁⟩) (if HeadReducible e₁ σ₁ then S σ₁ else Set.univ) := by
  split_ifs with hhr
  · rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible Hlc hhr)]
    exact hSconc σ₁ hhr
  · exact Concentrated.univ

open scoped Classical in
theorem wp_lift_head_step_concentrated {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none) (Hlc : e₁.IsLocallyClosed := by is_lc)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, HeadReducible e₁ σ₁ → Concentrated (headStep ⟨e₁, σ₁⟩) (S σ₁)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=> ⌜HeadReducible e₁ σ₁⌝ ∗ ▷ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗
      |={∅, E}=> stateInterp σ₂ ∗ wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_step_concentrated Hv (measurableSet_headPad hSmeas)
    (concentrated_headPad Hlc hSconc)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hhred, H⟩
  imodintro
  isplitr; · ipureintro; exact reducible_of_headReducible Hlc Hhred
  iintro !> %e₂ %σ₂ %Hmem
  rw [ite_eq_left Hhred] at Hmem
  iapply H $$ %e₂ %σ₂ %Hmem

open scoped Classical in
theorem wp_lift_atomic_head_step_fupd_concentrated {E1 E2 : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (Hlc : e₁.IsLocallyClosed := by is_lc)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, HeadReducible e₁ σ₁ → Concentrated (headStep ⟨e₁, σ₁⟩) (S σ₁)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E1}=> ⌜HeadReducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗ |={E1}[E2]▷=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp Δ E1 e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd_concentrated Hv
    (measurableSet_headPad hSmeas) (concentrated_headPad Hlc hSconc)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hhred, H⟩
  imodintro
  isplitr; · ipureintro; exact reducible_of_headReducible Hlc Hhred
  iintro %e₂ %σ₂ %Hmem
  rw [ite_eq_left Hhred] at Hmem
  iapply H $$ %e₂ %σ₂ %Hmem

open scoped Classical in
theorem wp_lift_atomic_head_step_concentrated {E : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (Hlc : e₁.IsLocallyClosed := by is_lc)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, HeadReducible e₁ σ₁ → Concentrated (headStep ⟨e₁, σ₁⟩) (S σ₁)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=> ⌜HeadReducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗ |={E}=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp Δ E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_head_step_fupd_concentrated (E2 := E) Hv Hlc hSmeas hSconc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hhred, H⟩
  imodintro
  iframe %Hhred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

-- DISCRETE: `wp_lift_pure_det_head_step (_Hv : e₁.toVal? = none) (Hlc : e₁.IsLocallyClosed)`
--   `(Hsafe : ∀ σ₁, ∃ ρ, 0 < headStep ⟨e₁, σ₁⟩ {ρ})`
--   `(Hdet : ∀ σ₁ e₂' σ₂, 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂', σ₂⟩} → σ₂ = σ₁ ∧ e₂' = e₂) :`
--   `(|={E}[E']▷=> wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ`

-- DISCRETE: `wp_lift_pure_det_head_step'` — same hypotheses, `▷`-form:
--   `(▷ wp Δ E e₂ Φ) ⊢ wp Δ E e₁ Φ`

end ConcentratedRules

end ApproxisWpGS

end ProbLang
