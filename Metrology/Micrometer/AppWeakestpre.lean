module

public import Metrology.Iris.SpecUpdate
public import Metrology.Iris.BudgetCredits
public import Metrology.Iris.Fixpoint
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Erasable
public import Metrology.ProbLang.Erasure
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

/-! The Micrometer weakest precondition, its coupling modalities and lifting rules. -/

@[expose] public section

open Std Iris Iris.BI Iris.ProofMode OFE COFE ProbLang GradedLifting

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]

/-! ## Micrometer ghost state class

The ghost state does not depend on the lifting: `L` is an explicit argument of `wp` and the
coupling modalities (`wp L E e Φ`, notation `WP[L] e @ E {{ Φ }}`), never a class parameter, so
the modality instances (`ElimModal`, `Frame`, ...) unify without an `L` metavariable. -/

class MicrometerWpGS {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (GF : BundledGFunctors) extends SpecUpdateGS rT GF where
  hlc : HasLC
  invGS : InvGS_gen hlc GF
  stateInterp : State rT → IProp GF

attribute [reducible, instance] MicrometerWpGS.invGS

/-- The budget owned by the state interpretation of `wp` (clutch-dp's `●↯m`). It depends on the
budget type only, never on `L`. -/
class BudgetGS (B : Type) (GF : BundledGFunctors) where
  interp : B → IProp GF

/-- The budget `wp` owns. -/
abbrev budgetInterp {B : Type} {GF : BundledGFunctors} [BudgetGS B GF] (b : B) : IProp GF :=
  BudgetGS.interp b

/-- With budget credits the budget is the authoritative budget credit. -/
instance BudgetGS.ofBudgetCredit {B : Type} [AddCommMonoid B] {GF : BundledGFunctors}
    [BudgetCreditGS B GF] : BudgetGS B GF :=
  ⟨bcAuth⟩

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]

/-! ## `spec_coupl` modality

Optionally prepends spec-side steps and erasable distributions on both sides before `Z`. Each
state carries the budget. -/

-- TODO remove when fixpoint is added
abbrev SpecCouplState (rT : Type) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] (B : Type) :
    Type _ := State rT × Cfg rT × B

instance : COFE (SpecCouplState rT B) := COFE.ofDiscrete _
instance : OFE.Discrete (SpecCouplState rT B) := ⟨id⟩

variable (L) in
/-- The coupling disjunct of `specCouplPre`: a step of a bind law within `b` between erasable
distributions, the spec's being the image of the law's spec-side head measure under `f'`, with
`Φ` continuing at each pair whose leftover is finite (Rocq `spec_coupl_pre`). -/
abbrev specCouplCouple (E : CoPset) (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (b : B)
    (Φ : SpecCouplState rT B → IProp GF) : IProp GF := iprop%
  (∃ (law : L.BindLaw) (n : Nat) (μ₁ μ₁' : MeasureTheory.Measure (State rT))
      (ν₀ : MeasureTheory.Measure (Cfg rT)) (f' : Cfg rT → Cfg rT) (R : State rT → Cfg rT → B),
      ⌜Measurable f' ∧ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f'⌝ ∗
      ⌜law.head μ₁ ν₀ R b⌝ ∗
      ⌜law.SideForExec μ₁ ν₀ R f'⌝ ∗
      ⌜ErasableExpr μ₁ σ₁⌝ ∗
      ⌜ErasableExpr μ₁' σ₁'⌝ ∗
      (∀ σ₂ ρ, ⌜R σ₂ ρ < (⊤ : B)⌝ -∗ |={E}=> Φ (σ₂, f' ρ, R σ₂ ρ)))

variable (L) in
abbrev specCouplPre (E : CoPset) (Z : State rT → Cfg rT → B → IProp GF)
    (Φ : SpecCouplState rT B → IProp GF) : SpecCouplState rT B → IProp GF :=
  fun ⟨σ₁, ⟨e₁', σ₁'⟩, b⟩ => iprop%
    ⌜L.Absorbing b⌝ ∨ Z σ₁ ⟨e₁', σ₁'⟩ b ∨ specCouplCouple L E σ₁ e₁' σ₁' b Φ

variable (L) in
abbrev specCoupl (E : CoPset) (σ : State rT) (e' : Exp rT) (σ' : State rT) (b : B)
    (Z : State rT → Cfg rT → B → IProp GF) : IProp GF :=
  bi_least_fixpoint (specCouplPre L E Z) (σ, ⟨e', σ'⟩, b)

omit [PartialOrder B] [OrderTop B] [MicrometerWpGS (rT := rT) GF] in
theorem specCouplState_ne {Φ : SpecCouplState rT B → IProp GF} : NonExpansive Φ where
  ne _ _ _ hd := .of_eq (congrArg Φ (OFE.Discrete.discrete_0 hd))

instance specCouplPre_mono {E : CoPset} {Z : State rT → Cfg rT → B → IProp GF} :
    BIMonoPred (specCouplPre L E Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    icases Hs with ⟨HVac | HZ | HCpl⟩
    · ileft; iexact HVac
    · iright; ileft; iexact HZ
    · iright; iright
      icases HCpl with ⟨%law, %n, %μ₁, %μ₁', %ν₀, %f', %R, %Hmap, %Hc, %Hside, %Herase₁,
        %Herase₂, Hcont⟩
      iexists law, n, μ₁, μ₁', ν₀, f', R
      iframe %
      iintro %σ₂ %ρ %hR
      imod Hcont $$ %σ₂ %ρ %hR with HΦ
      imodintro
      iapply Hwand $$ HΦ
  mono_pred_ne := specCouplState_ne

theorem specCoupl_absorbing {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT} {b : B}
    {Z : State rT → Cfg rT → B → IProp GF} (hb : L.Absorbing b) :
    ⊢ specCoupl L E σ e' σ' b Z := by
  iapply least_fixpoint_unfold_mpr (specCouplPre L E Z)
  ileft; ipureintro; exact hb

theorem specCoupl_ret {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT} {b : B}
    {Z : State rT → Cfg rT → B → IProp GF} :
    Z σ ⟨e', σ'⟩ b ⊢ specCoupl L E σ e' σ' b Z := by
  iintro HZ
  iapply least_fixpoint_unfold_mpr (specCouplPre L E Z)
  iright; ileft; iexact HZ

theorem specCoupl_rec {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT} {b : B}
    {Z : State rT → Cfg rT → B → IProp GF} :
    specCouplCouple L E σ e' σ' b
      (fun s => specCoupl L E s.1 s.2.1.expr s.2.1.state s.2.2 Z) ⊢
    specCoupl L E σ e' σ' b Z := by
  iintro HCpl
  iapply least_fixpoint_unfold_mpr (specCouplPre L E Z)
  iright; iright; iexact HCpl

theorem specCoupl_mono {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT} {b : B}
    {Z₁ Z₂ : State rT → Cfg rT → B → IProp GF} : iprop%
    □ (∀ σ' ρ' b', Z₁ σ' ρ' b' -∗ Z₂ σ' ρ' b') ∗ specCoupl L E σ e' σ' b Z₁ ⊢
    specCoupl L E σ e' σ' b Z₂ := by
  iintro ⟨#HZ, HC⟩
  unfold specCoupl
  iapply least_fixpoint_strong_mono (specCouplPre L E Z₁) (specCouplPre L E Z₂) $$ [] HC
  iintro !> %Φ %s HF
  icases HF with ⟨HVac | HZ1 | HCpl⟩
  · ileft; iexact HVac
  · iright; ileft
    iapply HZ $$ HZ1
  · iright; iright
    iexact HCpl

theorem specCoupl_bind {E1 E2 : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT} {b : B}
    {Z₁ Z₂ : State rT → Cfg rT → B → IProp GF} (HE : E1 ⊆ E2) : iprop%
    (∀ σ₂ ρ₂ b', Z₁ σ₂ ρ₂ b' -∗ specCoupl L E2 σ₂ ρ₂.expr ρ₂.state b' Z₂) ∗
    specCoupl L E1 σ e' σ' b Z₁ ⊢ specCoupl L E2 σ e' σ' b Z₂ := by
  iintro ⟨HZ, HC⟩
  let Φ : SpecCouplState rT B → IProp GF := fun s => iprop%
    (∀ σ₂ ρ₂ b', Z₁ σ₂ ρ₂ b' -∗ specCoupl L E2 σ₂ ρ₂.expr ρ₂.state b' Z₂) -∗
      specCoupl L E2 s.1 s.2.1.expr s.2.1.state s.2.2 Z₂
  have : NonExpansive Φ := specCouplState_ne
  iapply least_fixpoint_iter (Φ := Φ) $$ [] %(σ, ⟨e', σ'⟩, b) HC HZ
  iintro !> %s HF HZ
  icases HF with ⟨%HVac | HZ1 | HCpl⟩
  · iapply specCoupl_absorbing HVac
  · iapply HZ $$ HZ1
  · iapply specCoupl_rec
    icases HCpl with ⟨%law, %n, %μ₁, %μ₁', %ν₀, %f', %R, %HCpl_map, %HCpl_coupl, %HCpl_side,
      %HCpl_e1, %HCpl_e2, HCpl_cont⟩
    iexists law, n, μ₁, μ₁', ν₀, f', R
    iframe %
    iintro %σ₂ %ρ %hR
    imod BIFUpdate.subset HE with Hclose
    imod HCpl_cont $$ %σ₂ %ρ %hR
    imod Hclose
    imodintro
    iapply HCpl_cont $$ HZ

theorem specCoupl_mono_spatial {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT} {b : B}
    {Z₁ Z₂ : State rT → Cfg rT → B → IProp GF} : iprop%
    (∀ σ' ρ' b', Z₁ σ' ρ' b' -∗ Z₂ σ' ρ' b') ∗ specCoupl L E σ e' σ' b Z₁ ⊢
    specCoupl L E σ e' σ' b Z₂ := by
  iintro ⟨HZ, HC⟩
  iapply specCoupl_bind Std.LawfulSet.subset_refl
  iframe HC
  iintro %σ₂ %ρ₂ %b₂ Hz1
  iapply specCoupl_ret
  iapply HZ $$ Hz1

/-! ## `prog_coupl` modality

Couples exactly one program step against any number of spec steps and an erasable distribution,
by a lifting with per-pair leftovers and a bind law chosen for this step (clutch-dp `prog_coupl`).
-/

variable (L) in
/-- One program step against an erasable spec distribution by a step of a bind law: both are
images of the law's head measures under `f` and `f'`, and `Z` continues at each pair whose leftover
is finite (Rocq `prog_coupl`). -/
abbrev progCoupl (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (b : B)
    (Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF) : IProp GF := iprop%
  (∃ (law : L.BindLaw) (n : Nat) (μ₁' : MeasureTheory.Measure (State rT))
      (μ₀ ν₀ : MeasureTheory.Measure (Cfg rT)) (f f' : Cfg rT → Cfg rT)
      (R : Cfg rT → Cfg rT → B),
      ⌜Reducible e₁ σ₁⌝ ∗
      ⌜Measurable f ∧ primStep ⟨e₁, σ₁⟩ = μ₀.map f⌝ ∗
      ⌜Measurable f' ∧ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f'⌝ ∗
      ⌜law.head μ₀ ν₀ R b⌝ ∗
      ⌜law.SideForExec μ₀ ν₀ R f'⌝ ∗
      ⌜ErasableExpr μ₁' σ₁'⌝ ∗
      (∀ ρ ρ', ⌜R ρ ρ' < (⊤ : B)⌝ -∗ |={∅}=>
        Z (f ρ).expr (f ρ).state (f' ρ').expr (f' ρ').state (R ρ ρ')))

theorem specCoupl_ne {n : Nat} {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT} {b : B}
    {Z₁ Z₂ : State rT → Cfg rT → B → IProp GF} (HZ : ∀ σ ρ b, Z₁ σ ρ b ≡{n}≡ Z₂ σ ρ b) :
    specCoupl L E σ e' σ' b Z₁ ≡{n}≡ specCoupl L E σ e' σ' b Z₂ := by
  unfold specCoupl
  refine least_fixpoint_ne_outer (fun _ s => ?_) (.of_eq rfl)
  exact or_ne.ne (.of_eq rfl) (or_ne.ne (HZ s.1 s.2.1 s.2.2) (.of_eq rfl))

theorem progCoupl_ne {n : Nat} {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {b : B} {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → B → IProp GF}
    (HZ : ∀ e₂ σ₂ e₂' σ₂' b', Z₁ e₂ σ₂ e₂' σ₂' b' ≡{n}≡ Z₂ e₂ σ₂ e₂' σ₂' b') :
    progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ≡{n}≡ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ := by
  refine exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ =>
    exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => ?_
  refine sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
    sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) ?_
  exact forall_ne fun _ => forall_ne fun _ =>
    wand_ne.ne (.of_eq rfl) (BIFUpdate.ne.ne (HZ _ _ _ _ _))

theorem progCoupl_mono {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {b : B}
    {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → B → IProp GF} :
    iprop% (∀ e₂ σ₂ e₂' σ₂' b', Z₁ e₂ σ₂ e₂' σ₂' b' -∗ Z₂ e₂ σ₂ e₂' σ₂' b') ∗
    progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ := by
  iintro ⟨HZ, HCpl⟩
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  iexists law, n, μ₁', μ₀, ν₀, f, f', R
  iframe %
  iintro %ρ %ρ' %hR
  imod HCont $$ %ρ %ρ' %hR with HZ'
  imodintro
  iapply HZ $$ HZ'

/-! ## Weakest precondition -/

section Wp
variable [BudgetGS B GF]

variable (L) in
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

abbrev WpType := CoPset → Exp rT → (Val rT → IProp GF) → IProp GF

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
    apply Contractive.distLater_dist
    intro m Hm
    refine specCoupl_ne fun _ _ _ => ?_
    exact BIFUpdate.ne.ne <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
      sep_ne.ne (.of_eq rfl) (Hwp m Hm e₃)

instance wpPre_contractive : Contractive (wpPre L (rT := rT) (GF := GF)) where
  distLater_dist Hwp E _ Φ :=
    wpPre_ne_aux (fun _ => .of_eq rfl) fun _ Hm e₃ => DistLater.dist_lt (Hwp · · E e₃ Φ) Hm

variable (L) in
noncomputable def wp (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  fixpoint (wpPre L) E e Φ

theorem wp_unfold {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp L E e Φ = wpPre L (wp L) E e Φ :=
  congrFun (congrFun (congrFun (fixpoint_unfold ⟨wpPre L, OFE.ne_of_contractive _⟩) E) e) Φ

theorem wp_unfold_mp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp L E e Φ ⊢ wpPre L (wp L) E e Φ :=
  (BI.equiv_iff.mp wp_unfold).1

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

variable (L) in
noncomputable abbrev wpProgBody (E : CoPset) (Φ : Val rT → IProp GF)
    (e₃ : Exp rT) (σ₃ : State rT) (e₃' : Exp rT) (σ₃' : State rT) (b₃ : B) : IProp GF :=
  iprop% ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E}=>
    stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ budgetInterp b₄ ∗ wp L E e₃ Φ)

theorem wpProgBody_absorbing {E : CoPset} {Φ : Val rT → IProp GF} {b : B} (hb : L.Absorbing b) :
    ⊢ □ ∀ e₃ σ₃ e₃' σ₃', wpProgBody L E Φ e₃ σ₃ e₃' σ₃' b := by
  iintro !> %e₃ %σ₃ %e₃' %σ₃' !>
  iapply specCoupl_absorbing hb

/-! ## WP structural lemmas -/

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

abbrev wpStrongMonoCont (E2 : CoPset) (Φ Ψ : Val rT → IProp GF) : IProp GF := iprop%
  □ ∀ σ ρ v (b : B),
    stateInterp (rT := rT) σ ∗ SpecUpdateGS.specInterp (rT := rT) ρ ∗ budgetInterp b ∗
      Φ v ={E2}=∗
    stateInterp σ ∗ SpecUpdateGS.specInterp ρ ∗ budgetInterp b ∗ Ψ v

variable (L) in
noncomputable abbrev wpStrongMonoStmt : IProp GF := iprop%
  ∀ E1 E2 (e : Exp rT) Φ Ψ, ⌜E1 ⊆ E2⌝ -∗ wp L E1 e Φ -∗ wpStrongMonoCont (B := B) E2 Φ Ψ -∗
    wp L E2 e Ψ

theorem wp_strong_mono' {E1 E2 : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} (HE : E1 ⊆ E2) :
    iprop% wp L E1 e Φ ∗ wpStrongMonoCont (B := B) E2 Φ Ψ ⊢ wp L E2 e Ψ := by
  iintro ⟨HW, HΦ⟩
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
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HCont !>
      iapply specCoupl_mono_spatial
      iframe HCont
      iintro %σ₄ %ρ₄ %b₄ HInner
      imod HInner with ⟨Hσ', Hs', Hb', HwpInner⟩
      imod Hclose
      imodintro
      iframe
      iapply IH $$ %E1' %E2' %e₃ %Φ' %Ψ' %HE' HwpInner HΦ'
  iapply Hloeb $$ %E1 %E2 %e %Φ %Ψ %HE HW HΦ

theorem wp_wand {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop% wp L E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v) ⊢ wp L E e Ψ := by
  iintro ⟨HW, #HΦ⟩
  iapply wp_strong_mono' Std.LawfulSet.subset_refl
  iframe HW
  iintro !> %σ %ρ %v %b ⟨Hσ, Hs, Hb, HΦv⟩ !>
  iframe
  iapply HΦ $$ [$]

theorem wp_fupd {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp L E e (fun v => iprop(|={E}=> Φ v)) ⊢ wp L E e Φ := by
  iintro HW
  iapply wp_strong_mono' Std.LawfulSet.subset_refl
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

/-! ## Derived WP lemmas -/

theorem wp_strong_mono {E1 E2 : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} (HE : E1 ⊆ E2) :
    iprop% wp L E1 e Φ ∗ wpStrongMonoCont (B := B) E2 Φ Ψ ⊢ wp L E2 e Ψ :=
  wp_strong_mono' HE

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
  iapply wp_strong_mono' HE
  iframe HW
  iintro !> %σ %ρ %v %b ⟨Hσ, Hs, Hb, HΦ⟩ !>
  iframe

theorem wp_wand_l {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop% □ (∀ v, Φ v -∗ Ψ v) ∗ wp L E e Φ ⊢ wp L E e Ψ :=
  sep_comm.1.trans wp_wand

theorem wp_wand_r {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop% wp L E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v) ⊢ wp L E e Ψ :=
  wp_wand

end Wp

theorem concentrated_primStep_support (e : Exp rT) (σ : State rT) (hne : e.decomp.2 ≠ .urand) :
    Concentrated (primStep ⟨e, σ⟩) {ρ | 0 < primStep ⟨e, σ⟩ {ρ}} := by
  have heq : {ρ | 0 < primStep ⟨e, σ⟩ {ρ}}ᶜ = {ρ | primStep ⟨e, σ⟩ {ρ} = 0} := by
    ext ρ; simp [pos_iff_ne_zero]
  show primStep ⟨e, σ⟩ _ = 0
  rw [heq]
  exact primStep_atomic e σ hne

/-- Introduce a spec coupling by a step of any bind law, whose spec distribution is the image of
the law's spec-side head measure under `f'` (Rocq `spec_coupl_rec_map`). -/
theorem specCoupl_couple_map (law : L.BindLaw) {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : State rT → Cfg rT → B → IProp GF} {n : Nat}
    {μ₁ μ₁' : MeasureTheory.Measure (State rT)} {ν₀ : MeasureTheory.Measure (Cfg rT)}
    {f' : Cfg rT → Cfg rT} {R : State rT → Cfg rT → B} (hf' : Measurable f')
    (hspec : (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₁ ν₀ R b) (hside : law.SideForExec μ₁ ν₀ R f')
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ ρ, ⌜R σ₂ ρ < (⊤ : B)⌝ -∗ |={E}=>
      specCoupl L E σ₂ (f' ρ).expr (f' ρ).state (R σ₂ ρ) Z) ⊢
    specCoupl L E σ₁ e₁' σ₁' b Z := by
  have hmap := And.intro hf' hspec
  iintro H
  iapply specCoupl_rec
  iexists law, n, μ₁, μ₁', ν₀, f', R
  iframe %
  iexact H

/-- Introduce a spec coupling by a step of any bind law between erasable distributions (Rocq
`spec_coupl_rec`). -/
theorem specCoupl_couple_law (law : L.BindLaw) {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : State rT → Cfg rT → B → IProp GF} {n : Nat}
    {R : State rT → Cfg rT → B} {μ₁ μ₁' : MeasureTheory.Measure (State rT)}
    (hhead : law.head μ₁ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R b)
    (hside : law.SideForExec μ₁ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R id)
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ e₂' σ₂', ⌜R σ₂ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={E}=>
      specCoupl L E σ₂ e₂' σ₂' (R σ₂ ⟨e₂', σ₂'⟩) Z) ⊢
    specCoupl L E σ₁ e₁' σ₁' b Z := by
  iintro H
  iapply specCoupl_couple_map law measurable_id MeasureTheory.Measure.map_id.symm hhead hside
    Heras₁ Heras₁'
  iintro %σ₂ %⟨e₂', σ₂'⟩ %hR
  simp only [id]
  iapply H $$ %σ₂ %e₂' %σ₂' %hR

/-- Introduce a spec coupling from a lifting of erasable distributions. -/
theorem specCoupl_couple [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal] {E : CoPset}
    {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : State rT → Cfg rT → B → IProp GF} {n : Nat}
    {R : State rT → Cfg rT → B} {μ₁ μ₁' : MeasureTheory.Measure (State rT)}
    (Hcpl : L b R μ₁ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩))
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ e₂' σ₂', ⌜R σ₂ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={E}=>
      specCoupl L E σ₂ e₂' σ₂' (R σ₂ ⟨e₂', σ₂'⟩) Z) ⊢
    specCoupl L E σ₁ e₁' σ₁' b Z :=
  specCoupl_couple_law (BindLaw.canonical L) Hcpl (.of_forall fun _ _ => trivial) Heras₁ Heras₁'

/-- Introduce a spec coupling from a relational lifting within `b₁`, leaving `b₂` to every
related pair. -/
theorem specCoupl_couple_rel [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] {E : CoPset} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT}
    {b₁ b₂ b : B} {Z : State rT → Cfg rT → B → IProp GF} {S : State rT → Cfg rT → Prop} {n : Nat}
    {μ₁ μ₁' : MeasureTheory.Measure (State rT)}
    (hb : b₁ + b₂ ≤ b) (Hcpl : L.Rel b₁ S μ₁ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩))
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ e₂' σ₂', ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ |={E}=> specCoupl L E σ₂ e₂' σ₂' b₂ Z) ⊢
    specCoupl L E σ₁ e₁' σ₁' b Z := by
  have := Heras₁.isProbabilityMeasure
  have := Heras₁'.isProbabilityMeasure
  iintro H
  iapply specCoupl_couple (IsLawful.mono (IsTopAbsorbing.frame Hcpl) hb le_rfl) Heras₁ Heras₁'
  iintro %σ₂ %e₂' %σ₂' %hR
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of hS, zero_add]
  iapply H $$ %σ₂ %e₂' %σ₂' %hS

/-! ### `specCoupl` — derived lemmas -/

/-- A deterministic spec run to `⟨e₂', σ₂'⟩` passes on any smaller budget, by a step of the unit
law (Rocq `spec_coupl_steps_det`, `spec_coupl_mono_grade`). -/
theorem fupd_specCoupl_steps_det_of_le [Add B] [L.IsLawful] [L.IsTopAbsorbing]
    {E : CoPset} {σ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {e₂' : Exp rT} {σ₂' : State rT}
    {n : Nat} {b₁ b : B} {Z : State rT → Cfg rT → B → IProp GF}
    (Hstep : pexecN n ⟨e₁', σ₁'⟩ = MeasureTheory.Measure.dirac ⟨e₂', σ₂'⟩) (hb : b₁ ≤ b) :
    iprop(|={E}=> specCoupl L E σ e₂' σ₂' b₁ Z) ⊢ specCoupl L E σ e₁' σ₁' b Z := by
  classical
  rcases lt_or_eq_of_le (le_top : b₁ ≤ (⊤ : B)) with hb₁ | rfl
  · iintro HF
    let R : State rT → Cfg rT → B := fun s c => if s = σ ∧ c = ⟨e₂', σ₂'⟩ then b₁ else (⊤ : B)
    have hR : R σ ⟨e₂', σ₂'⟩ = b₁ := ite_eq_left ⟨rfl, rfl⟩
    have hhead : (BindLaw.unit L).head (MeasureTheory.Measure.dirac σ)
        ((MeasureTheory.Measure.dirac σ₁').bind fun σ => pexecN n ⟨e₁', σ⟩) R b := by
      rw [MeasureTheory.Measure.dirac_bind (by fun_prop), Hstep]
      exact BindLaw.unit_head_dirac (hR ▸ hb₁) (hR ▸ hb)
    iapply specCoupl_couple_law (BindLaw.unit L) hhead (.of_forall fun _ _ => trivial)
      (ErasableExpr.dret σ) (ErasableExpr.dret σ₁')
    iintro %σ₂ %e₂'' %σ₂'' %hlt
    by_cases hS : σ₂ = σ ∧ e₂'' = e₂' ∧ σ₂'' = σ₂'
    · obtain ⟨rfl, rfl, rfl⟩ := hS
      rw [hR]
      iexact HF
    · simp [R, hS] at hlt
  · iintro -
    iapply specCoupl_absorbing
    exact (top_le_iff.1 hb) ▸ IsTopAbsorbing.absorbing_top

theorem fupd_specCoupl_of_le [Add B] [L.IsLawful] [L.IsTopAbsorbing] {E : CoPset}
    {σ : State rT} {e' : Exp rT} {σ' : State rT} {b₁ b₂ : B} {Z : State rT → Cfg rT → B → IProp GF}
    (hb : b₁ ≤ b₂) :
    iprop(|={E}=> specCoupl L E σ e' σ' b₁ Z) ⊢ specCoupl L E σ e' σ' b₂ Z :=
  fupd_specCoupl_steps_det_of_le (pexecN_zero _) hb

theorem specCoupl_mono_err [Add B] [L.IsLawful] [L.IsTopAbsorbing] {E : CoPset}
    {σ : State rT} {e' : Exp rT} {σ' : State rT} {b₁ b₂ : B} {Z : State rT → Cfg rT → B → IProp GF}
    (hb : b₁ ≤ b₂) : specCoupl L E σ e' σ' b₁ Z ⊢ specCoupl L E σ e' σ' b₂ Z :=
  fupd_intro.trans (fupd_specCoupl_of_le hb)

theorem fupd_specCoupl [Add B] [L.IsLawful] [L.IsTopAbsorbing] {E : CoPset}
    {σ : State rT} {e' : Exp rT} {σ' : State rT} {b : B} {Z : State rT → Cfg rT → B → IProp GF} :
    iprop(|={E}=> specCoupl L E σ e' σ' b Z) ⊢ specCoupl L E σ e' σ' b Z :=
  fupd_specCoupl_of_le le_rfl

theorem specCoupl_ind {E : CoPset} {Ψ Z : State rT → Cfg rT → B → IProp GF} : iprop%
    □ (∀ σ c b, specCouplPre L E Z (fun s => iprop(Ψ s.1 s.2.1 s.2.2 ∧
      specCoupl L E s.1 s.2.1.expr s.2.1.state s.2.2 Z)) (σ, c, b) -∗ Ψ σ c b) ⊢
    ∀ σ e' σ' b, specCoupl L E σ e' σ' b Z -∗ Ψ σ ⟨e', σ'⟩ b := by
  iintro #IH %σ %e' %σ' %b HC
  let Ψ' : SpecCouplState rT B → IProp GF := fun s => Ψ s.1 s.2.1 s.2.2
  have HΨne : NonExpansive Ψ' := specCouplState_ne
  iapply least_fixpoint_ind (F := specCouplPre L E Z) (Φ := Ψ') $$ [] %(σ, ⟨e', σ'⟩, b) HC
  iintro !> %s HF
  obtain ⟨σ'', c, b'⟩ := s
  iapply IH $$ %σ'' %c %b' HF

theorem specCoupl_erasables [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT}
      {σ₁' : State rT}
    {b₁ b₂ b : B} {Z : State rT → Cfg rT → B → IProp GF} {S : State rT → State rT → Prop}
    {μ₁ μ₁' : MeasureTheory.Measure (State rT)}
    (hb : b₁ + b₂ ≤ b) (Hcpl : L.Rel b₁ S μ₁ μ₁')
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ σ₂', ⌜S σ₂ σ₂'⌝ -∗ |={E}=> specCoupl L E σ₂ e₁' σ₂' b₂ Z) ⊢
    specCoupl L E σ₁ e₁' σ₁' b Z := by
  have := Heras₁.isProbabilityMeasure
  have := Heras₁'.isProbabilityMeasure
  iintro H
  have heq : μ₁'.bind (fun σ => pexecN 0 ⟨e₁', σ⟩) = μ₁'.map (fun σ => (⟨e₁', σ⟩ : Cfg rT)) := by
    simp only [pexecN_zero]
    exact MeasureTheory.Measure.bind_dirac_eq_map _ (by fun_prop)
  iapply specCoupl_couple_rel (S := fun σ₂ c => S σ₂ c.state ∧ c.expr = e₁') (n := 0) hb
    (heq ▸ Hcpl.map_right fun _ _ HS => ⟨HS, rfl⟩)
    Heras₁ Heras₁'
  iintro %σ₂ %e₂' %σ₂' %HS
  obtain ⟨HS, rfl⟩ := HS
  iapply H $$ %σ₂ %σ₂' %HS

theorem specCoupl_erasable_steps [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT}
      {σ₁' : State rT}
    {n : Nat} {b₁ b₂ b : B} {Z : State rT → Cfg rT → B → IProp GF} {S : State rT → Cfg rT → Prop}
    {μ₁ : MeasureTheory.Measure (State rT)}
    (hb : b₁ + b₂ ≤ b) (Hcpl : L.Rel b₁ S μ₁ (pexecN n ⟨e₁', σ₁'⟩))
    (Heras₁ : ErasableExpr μ₁ σ₁) : iprop%
    (∀ σ₂ e₂' σ₂', ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ |={E}=> specCoupl L E σ₂ e₂' σ₂' b₂ Z) ⊢
    specCoupl L E σ₁ e₁' σ₁' b Z :=
  specCoupl_couple_rel (n := n) hb (by rwa [MeasureTheory.Measure.dirac_bind (by fun_prop)])
    Heras₁ (ErasableExpr.dret σ₁')

theorem specCoupl_steps [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsTopAbsorbing]
    [L.HasBind] [L.IsSupportLocal] {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
      {n : Nat} {b₁ b₂ b : B}
    {Z : State rT → Cfg rT → B → IProp GF} {S : State rT → Cfg rT → Prop} (hb : b₁ + b₂ ≤ b)
    (Hcpl : L.Rel b₁ S (MeasureTheory.Measure.dirac σ₁) (pexecN n ⟨e₁', σ₁'⟩)) :
    iprop% (∀ σ₂ e₂' σ₂', ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ |={E}=> specCoupl L E σ₂ e₂' σ₂' b₂ Z) ⊢
    specCoupl L E σ₁ e₁' σ₁' b Z :=
  specCoupl_erasable_steps hb Hcpl (ErasableExpr.dret σ₁)

theorem specCoupl_steps_det [Add B] [L.IsLawful] [L.IsTopAbsorbing] {E : CoPset}
    {σ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {e₂' : Exp rT} {σ₂' : State rT} {n : Nat} {b : B}
    {Z : State rT → Cfg rT → B → IProp GF}
    (Hstep : pexecN n ⟨e₁', σ₁'⟩ = MeasureTheory.Measure.dirac ⟨e₂', σ₂'⟩) :
    specCoupl L E σ e₂' σ₂' b Z ⊢ specCoupl L E σ e₁' σ₁' b Z :=
  fupd_intro.trans (fupd_specCoupl_steps_det_of_le Hstep le_rfl)

theorem specCoupl_step_concentrated [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] {E : CoPset} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT} {b : B} {Z : State rT → Cfg rT → B → IProp GF} {S : Set
    (Cfg rT)} (Hred : Reducible e₁' σ₁')
    (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁', σ₁'⟩) S) : iprop%
    (∀ e₂' σ₂', ⌜⟨e₂', σ₂'⟩ ∈ S⌝ -∗ |={E}=> specCoupl L E σ₁ e₂' σ₂' b Z) ⊢
    specCoupl L E σ₁ e₁' σ₁' b Z := by
  iintro H
  have := prim_step_mass Hred
  have hpexec1 : pexecN 1 ⟨e₁', σ₁'⟩ = primStep ⟨e₁', σ₁'⟩ := by
    rw [pexecN_one, stepOrFinal_not_isValue (val_stuck Hred)]
  have HcplR : L.Rel 0 (fun σ c => σ = σ₁ ∧ c ∈ S) (MeasureTheory.Measure.dirac σ₁)
      (pexecN 1 ⟨e₁', σ₁'⟩) := by
    rw [hpexec1]
    exact rel_dirac_left _ hSmeas hSconc σ₁
  iapply specCoupl_steps (zero_add b).le HcplR
  iintro %σ₂ %e₂' %σ₂' %HS
  obtain ⟨rfl, Hmem⟩ := HS
  iapply H $$ %e₂' %σ₂' %Hmem

@[discrete]
theorem specCoupl_step [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive]
    [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : State rT → Cfg rT → B → IProp GF}
    (Hred : Discrete.Reducible e₁' σ₁') (hne : e₁'.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ e₂' σ₂', ⌜0 < primStep ⟨e₁', σ₁'⟩ {⟨e₂', σ₂'⟩}⌝ -∗ |={E}=> specCoupl L E σ₁ e₂' σ₂' b Z) ⊢
    specCoupl L E σ₁ e₁' σ₁' b Z :=
  specCoupl_step_concentrated Hred.toReducible (measurableSet_primStep_support e₁' σ₁')
    (concentrated_primStep_support e₁' σ₁' hne)

/-! ## `progCoupl` — derived lemmas -/

theorem progCoupl_reducible {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} :
    progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢ ⌜Reducible e₁ σ₁⌝ := by
  iintro ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, -⟩
  ipureintro; exact Hred

/-- Introduce a program coupling by a step of any bind law, whose program and spec distributions
are images of the law's head measures under `f` and `f'` (Rocq `prog_coupl_intro_map`). -/
theorem progCoupl_intro_map (law : L.BindLaw) {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {n : Nat}
    {μ₁' : MeasureTheory.Measure (State rT)} {μ₀ ν₀ : MeasureTheory.Measure (Cfg rT)}
    {f f' : Cfg rT → Cfg rT} {R : Cfg rT → Cfg rT → B}
    (Hred : Reducible e₁ σ₁) (hf : Measurable f) (hprog : primStep ⟨e₁, σ₁⟩ = μ₀.map f)
    (hf' : Measurable f') (hspec : (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₀ ν₀ R b) (hside : law.SideForExec μ₀ ν₀ R f')
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ ρ ρ', ⌜R ρ ρ' < (⊤ : B)⌝ -∗ |={∅}=>
      Z (f ρ).expr (f ρ).state (f' ρ').expr (f' ρ').state (R ρ ρ')) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  have hF := And.intro hf hprog
  have hF' := And.intro hf' hspec
  iintro H
  iexists law, n, μ₁', μ₀, ν₀, f, f', R
  iframe %
  iexact H

/-- Introduce a program coupling by a step of any bind law (Rocq `prog_coupl_intro`). -/
theorem progCoupl_intro_law (law : L.BindLaw) {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {n : Nat}
    {μ₁' : MeasureTheory.Measure (State rT)} {R : Cfg rT → Cfg rT → B}
    (Hred : Reducible e₁ σ₁)
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R b)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R id)
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  iintro H
  iapply progCoupl_intro_map law Hred measurable_id MeasureTheory.Measure.map_id.symm
    measurable_id MeasureTheory.Measure.map_id.symm hhead hside Heras
  iintro %⟨e₂, σ₂⟩ %⟨e₂', σ₂'⟩ %hR
  simp only [id]
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂' %hR

theorem progCoupl_intro [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal] {e₁ : Exp rT}
    {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {n : Nat}
    {μ₁' : MeasureTheory.Measure (State rT)} {R : Cfg rT → Cfg rT → B}
    (Hred : Reducible e₁ σ₁)
    (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩))
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_intro_law (BindLaw.canonical L) Hred Hcpl (.of_forall fun _ _ => trivial) Heras

theorem dirac_bind_pexecN_one {e₁' : Exp rT} {σ₁' : State rT} (Hred' : Reducible e₁' σ₁') :
    (MeasureTheory.Measure.dirac σ₁').bind (fun σ => pexecN 1 ⟨e₁', σ⟩) = primStep ⟨e₁', σ₁'⟩ := by
  rw [MeasureTheory.Measure.dirac_bind (by fun_prop), pexecN_one,
    stepOrFinal_not_isValue (val_stuck Hred')]

/-- Continuations need only cover a set carrying the program step, by the law's `head_supp`
(Rocq `prog_coupl_strengthen`). -/
theorem progCoupl_strong_mono {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {S : Set
    (Cfg rT)} (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
    iprop% (∀ e₂ σ₂ e₂' σ₂' b', ⌜⟨e₂, σ₂⟩ ∈ S⌝ ∗ Z₁ e₂ σ₂ e₂' σ₂' b' -∗ Z₂ e₂ σ₂ e₂' σ₂' b') ∗
    progCoupl L e₁ σ₁ e₁' σ₁' b Z₁ ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z₂ := by
  iintro ⟨Hm, HCpl⟩
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  classical
  obtain ⟨hf, hprog⟩ := Hf
  obtain ⟨hf', hspec⟩ := Hf'
  have hA : MeasurableSet (f ⁻¹' S) := hf hSmeas
  have hμ : μ₀ (f ⁻¹' S)ᶜ = 0 := by
    rw [← Set.preimage_compl, ← MeasureTheory.Measure.map_apply hf hSmeas.compl, ← hprog]
    exact hSconc
  iapply progCoupl_intro_map law Hred hf hprog hf' hspec (law.head_supp hA hμ Hhead) Hside.supp
    Heras
  iintro %ρ %ρ' %hR
  by_cases hmem : ρ ∈ f ⁻¹' S
  · simp only [Set.piecewise_eq_of_mem _ _ _ hmem] at hR ⊢
    imod HCont $$ %ρ %ρ' %hR with HZ₁
    imodintro
    iapply Hm
    have hmem' : (⟨(f ρ).expr, (f ρ).state⟩ : Cfg rT) ∈ S := hmem
    iframe %hmem' HZ₁
  · simp [Set.piecewise_eq_of_notMem _ _ _ hmem] at hR

theorem progCoupl_strengthen {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {S : Set
    (Cfg rT)} (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
    progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b fun e₂ σ₂ e₂' σ₂' b' =>
      iprop(⌜⟨e₂, σ₂⟩ ∈ S⌝ ∧ Z e₂ σ₂ e₂' σ₂' b') := by
  iintro HCpl
  iapply progCoupl_strong_mono hSmeas hSconc
  iframe HCpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %b' ⟨%Hmem, HZ⟩
  isplitr; · ipureintro; exact Hmem
  iexact HZ

/-- A program step under an evaluation context, for any bind law: the program-side map is
composed with `K.fill` (Rocq `prog_coupl_ctx_bind`). -/
theorem progCoupl_ctx_bind {K : Ectx rT} {e₁ : Exp rT} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} (hv : ¬ e₁.isValue) :
    progCoupl L e₁ σ₁ e₁' σ₁' b (fun e₂ => Z (K.fill e₂)) ⊢
    progCoupl L (K.fill e₁) σ₁ e₁' σ₁' b Z := by
  iintro HCpl
  icases HCpl with ⟨%law, %n, %μ₁', %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead, %Hside,
    %Heras, HCont⟩
  obtain ⟨hf, hprog⟩ := Hf
  obtain ⟨hf', hspec⟩ := Hf'
  have hK : Measurable fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT) := by fun_prop
  iapply progCoupl_intro_map law (Hred.fill K) (hK.comp hf)
    (by rw [primStep_fill hv, hprog, MeasureTheory.Measure.map_map hK hf]) hf' hspec Hhead Hside
    Heras
  simp only [Function.comp_apply]
  iexact HCont

/-! ### `progCoupl` — coupling-intro lemmas -/

/-- Couple one program step against one spec step by a step of any bind law (Rocq
`prog_coupl_one_step_top`). -/
theorem progCoupl_steps_law (law : L.BindLaw) {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF}
    {R : Cfg rT → Cfg rT → B} (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R b)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R id) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_intro_law (n := 1) law Hred (dirac_bind_pexecN_one Hred' ▸ hhead)
    (dirac_bind_pexecN_one Hred' ▸ hside) (ErasableExpr.dret σ₁')

/-- `progCoupl_steps_law` spending `b₁` of the budget `b` on the step and carrying `b₂` through
it, for a law whose heads shift (Rocq `wp_couple_spend`, `gbl_head_shift`). -/
theorem progCoupl_steps_spend_law [Add B] (law : L.BindLaw) [law.HeadShift] {e₁ : Exp rT}
    {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {b₁ b₂ b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {R : Cfg rT → Cfg rT → B}
    (hb : b₁ + b₂ ≤ b) (hb₂ : b₂ < (⊤ : B)) (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (hhead : law.head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R b₁)
    (hside : law.SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)
      (fun ρ ρ' => R ρ ρ' + b₂) id) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  have := prim_step_mass Hred
  have := prim_step_mass Hred'
  progCoupl_steps_law law Hred Hred' (law.mono_out (BindLaw.HeadShift.shift hb₂ hhead) hb) hside

theorem progCoupl_steps_adv' [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal] {e₁ : Exp rT}
    {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT} {b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF}
    {R : Cfg rT → Cfg rT → B} (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  progCoupl_intro Hred (dirac_bind_pexecN_one Hred' ▸ Hcpl) (ErasableExpr.dret σ₁')

/-- Couple one program step against one spec step within `b₁`, adding `b₂` to every
leftover. -/
theorem progCoupl_steps_adv [AddCommMagma B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] {e₁ : Exp rT} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT}
    {b₁ b₂ b : B} {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF}
    {R : Cfg rT → Cfg rT → B} (hb : b₁ + b₂ ≤ b) (Hred : Reducible e₁ σ₁)
    (Hred' : Reducible e₁' σ₁')
    (Hcpl : L b₁ R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂ < (⊤ : B)⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂)) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z :=
  have := prim_step_mass Hred
  have := prim_step_mass Hred'
  progCoupl_intro (R := fun ρ₁ ρ₂ => R ρ₁ ρ₂ + b₂) Hred
    (dirac_bind_pexecN_one Hred' ▸ IsLawful.mono (IsTopAbsorbing.frame Hcpl) hb le_rfl)
    (ErasableExpr.dret σ₁')

/-- Couple one program step against one spec step by a relational lifting within `b₁`, leaving
`b₂` to the continuation: the step spends `b₁` out of the budget `b`. -/
theorem progCoupl_steps [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] {e₁ : Exp rT} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT} {b₁ b₂ b : B} {S : Cfg rT → Cfg rT → Prop}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF}
    (hb : b₁ + b₂ ≤ b) (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜S ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ -∗ |={∅}=> Z e₂ σ₂ e₂' σ₂' b₂) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  iintro Hcnt
  iapply progCoupl_steps_adv hb Hred Hred' Hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of hS, zero_add]
  iapply Hcnt $$ %e₂ %σ₂ %e₂' %σ₂' %hS

/-- A deterministic program step with the spec in place, by a step of the unit law (Rocq
`prog_coupl_det_step`). -/
theorem progCoupl_det_step [Add B] [L.IsLawful] {e₁ : Exp rT} {σ₁ : State rT} {e₂ : Exp rT}
    {σ₂ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} (hb : b < (⊤ : B))
    (Hred : Reducible e₁ σ₁)
    (Hdet : primStep ⟨e₁, σ₁⟩ = MeasureTheory.Measure.dirac ⟨e₂, σ₂⟩) :
    iprop(|={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  classical
  iintro HZ
  let R : Cfg rT → Cfg rT → B := fun ρ ρ' =>
    if ρ = ⟨e₂, σ₂⟩ ∧ ρ' = ⟨e₁', σ₁'⟩ then b else (⊤ : B)
  have hR : R ⟨e₂, σ₂⟩ ⟨e₁', σ₁'⟩ = b := ite_eq_left ⟨rfl, rfl⟩
  have hhead : (BindLaw.unit L).head (primStep ⟨e₁, σ₁⟩)
      ((MeasureTheory.Measure.dirac σ₁').bind fun σ => pexecN 0 ⟨e₁', σ⟩) R b := by
    rw [MeasureTheory.Measure.dirac_bind (by fun_prop), pexecN_zero, Hdet]
    exact BindLaw.unit_head_dirac (hR ▸ hb) hR.le
  iapply progCoupl_intro_law (BindLaw.unit L) Hred hhead (.of_forall fun _ _ => trivial)
    (ErasableExpr.dret σ₁')
  iintro %e₃ %σ₃ %e₃' %σ₃' %hlt
  by_cases hS : e₃ = e₂ ∧ σ₃ = σ₂ ∧ e₃' = e₁' ∧ σ₃' = σ₁'
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hS
    rw [hR]
    iexact HZ
  · simp [R, and_assoc, hS] at hlt

/-- A program step that leaves the spec in place, by a step of any law with diagonal heads: the
program step against itself, mapped to the spec configuration (Rocq `prog_coupl_step_l`). -/
theorem progCoupl_step_l_law [AddZeroClass B] [CanonicallyOrderedAdd B] (law : L.BindLaw)
    [law.HeadDiag] {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} (hb : b < (⊤ : B))
    (Hred : Reducible e₁ σ₁) :
    iprop(∀ e₂ σ₂, |={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢ progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  have := prim_step_mass Hred
  iintro H
  iapply progCoupl_intro_map (n := 0) (μ₁' := MeasureTheory.Measure.dirac σ₁')
    (f' := fun _ => ⟨e₁', σ₁'⟩) law Hred measurable_id MeasureTheory.Measure.map_id.symm
    measurable_const
    (by rw [MeasureTheory.Measure.dirac_bind (by fun_prop), pexecN_zero,
      MeasureTheory.Measure.map_const, MeasureTheory.measure_univ, one_smul])
    (BindLaw.HeadDiag.diag _ hb) (fun _ _ _ _ => BindLaw.HeadDiag.side_diag _ _ _ _)
    (ErasableExpr.dret σ₁')
  iintro %ρ %ρ' %hR
  obtain ⟨rfl, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of rfl, zero_add]
  simp only [id]
  iapply H $$ %ρ.expr %ρ.state

theorem progCoupl_step_l_erasable_adv [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal]
    {e₁ : Exp rT} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT} {μ₁' : MeasureTheory.Measure (State rT)} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {R : Cfg rT → State rT → B}
    (Hred : Reducible e₁ σ₁) (Heras : ErasableExpr μ₁' σ₁')
    (Hcpl : L b R (primStep ⟨e₁, σ₁⟩) μ₁') : iprop%
    (∀ e₂ σ₂ σ₂', ⌜R ⟨e₂, σ₂⟩ σ₂' < (⊤ : B)⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₂' (R ⟨e₂, σ₂⟩ σ₂')) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  classical
  iintro Hcnt
  have Hcpl' : L b (fun ρ₁ ρ₂ => if ρ₂.expr = e₁' then R ρ₁ ρ₂.state else (⊤ : B))
      (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN 0 ⟨e₁', σ⟩) := by
    simp only [pexecN_zero]
    rw [MeasureTheory.Measure.bind_dirac_eq_map _ (by fun_prop),
      ← MeasureTheory.Measure.map_id (μ := primStep ⟨e₁, σ₁⟩)]
    exact IsLawful.map measurable_id (by fun_prop) (by simpa using Hcpl)
  iapply progCoupl_intro Hred Hcpl' Heras
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  by_cases he : e₂' = e₁'
  · subst he
    simp only [↓reduceIte] at hR ⊢
    iapply Hcnt $$ %e₂ %σ₂ %σ₂' %hR
  · simp [he] at hR

theorem progCoupl_step_l_erasable [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal] {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
      {σ₁' : State rT}
    {μ₁' : MeasureTheory.Measure (State rT)} {b₁ b₂ b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {S : Cfg rT → State rT → Prop}
    (hb : b₁ + b₂ ≤ b) (Hred : Reducible e₁ σ₁)
    (Hcpl : L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) μ₁')
    (Heras : ErasableExpr μ₁' σ₁') : iprop%
    (∀ e₂ σ₂ σ₂', ⌜S ⟨e₂, σ₂⟩ σ₂'⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₂' b₂) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  have := Heras.isProbabilityMeasure
  have := prim_step_mass Hred
  iintro Hcnt
  iapply progCoupl_step_l_erasable_adv Hred Heras
    (IsLawful.mono (IsTopAbsorbing.frame Hcpl) hb le_rfl)
  iintro %e₂ %σ₂ %σ₂' %hR
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of hS, zero_add]
  iapply Hcnt $$ %e₂ %σ₂ %σ₂' %hS

theorem progCoupl_step_l_concentrated [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful]
    [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] {e₁ : Exp rT} {σ₁ : State rT}
    {e₁' : Exp rT} {σ₁' : State rT} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} {S : Set (Cfg rT)}
    (Hred : Reducible e₁ σ₁)
    (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) : iprop%
    (∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₁' b) ⊢
    progCoupl L e₁ σ₁ e₁' σ₁' b Z := by
  iintro H
  have := prim_step_mass Hred
  iapply progCoupl_step_l_erasable (zero_add b).le Hred
    (rel_dirac_right _ hSmeas hSconc σ₁') (ErasableExpr.dret σ₁')
  iintro %e₂ %σ₂ %σ₂' %HS
  obtain ⟨Hmem, rfl⟩ := HS
  iapply H $$ %e₂ %σ₂ %Hmem

/-! ## WP — outer OFE instances and `IntoVal`-style value intros -/

section Wp
variable [BudgetGS B GF]

theorem wp_value_fupd_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (h : e.toVal? = some v) : iprop(|={E}=> Φ v) ⊢ wp L E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact wp_value_fupd

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

-- TODO: `wp_contractive` — `wp` is `Contractive` in its post when the head
-- is *not* a value. Needs structural `wp_unfold` walk under the
-- `e.toVal? = none` branch; dual to `wpPre_contractive` restricted to `none`.

/-! ## WP — structural lemmas -/

variable (L) in
noncomputable abbrev wpBindStmt (K : Ectx rT) : IProp GF := iprop%
  ∀ E e Φ, wp L E e (fun v => wp L E (K.fill (Exp.ofVal v)) Φ) -∗ wp L E (K.fill e) Φ

theorem wp_bind [Add B] [L.IsLawful] [L.IsTopAbsorbing] [L.HasBind] {K : Ectx rT} {E : CoPset}
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

-- TODO: `wp_atomic` — for atomic `e`, an inner `|={E2, E1}=>` can be absorbed.
-- In ProbLang every head step is atomic (reduces to a value or single `primStep`),
-- so state it with an explicit "atomic" predicate over `e` instead of an `Atomic` typeclass.

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

instance isExcept0_wp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    IsExcept0 (wp L E e Φ) where
  is_except0 := (except0_mono fupd_intro).trans (BIFUpdate.except0.trans fupd_wp)

instance frame_wp {p : Bool} {E : CoPset} {e : Exp rT} {R : IProp GF}
    {Φ Ψ : Val rT → IProp GF} [inst : ∀ v, Frame p R (Φ v) (Ψ v)] :
    Frame p R (wp L E e Φ) (wp L E e Ψ) where
  frame := wp_frame_l.trans (wp_mono fun v => (inst v).frame)

instance addModal_fupd_wp {E : CoPset} {e : Exp rT} {P : IProp GF} {Φ : Val rT → IProp GF} :
    AddModal iprop(|={E}=> P) P (wp L E e Φ) where
  add_modal := fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

instance elimModal_bupd_wp {p : Bool} {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|==> P) P (wp L E e Φ) (wp L E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    (sep_mono_left BIUpdateFUpdate.fupd_of_bupd).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

instance elimModal_fupd_wp {p : Bool} {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|={E}=> P) P (wp L E e Φ) (wp L E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

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

instance elimModal_specUpdateN_wp [Add B] [L.IsLawful] [L.IsTopAbsorbing] {n : Nat}
    {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF} {Φ : Val rT → IProp GF} :
    ElimModal True false io false (specUpdateN rT n E P) P (wp L E e Φ) (wp L E e Φ) where
  elim_modal h :=
    (sep_mono_left specUpdateN_specUpdate).trans ((elimModal_specUpdate_wp (io := io)).elim_modal h)

/-! ## Lifting lemmas (ports `clutch/theories/approxis/lifting.v`) -/

theorem wp_lift_step_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    (∀ σ₁ e₁' σ₁' (b₁ : B), stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      budgetInterp b₁ -∗
      |={E, ∅}=> specCoupl L ∅ σ₁ e₁' σ₁' b₁ fun σ₂ ρ' b₂ =>
        match e₁.toVal? with
        | some v => iprop(|={∅, E}=> stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗
            budgetInterp b₂ ∗ Φ v)
        | none => progCoupl L e₁ σ₂ ρ'.expr ρ'.state b₂ fun e₃ σ₃ e₃' σ₃' b₃ => iprop%
            ▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ fun σ₄ ρ'' b₄ => iprop(|={∅, E}=>
              stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ budgetInterp b₄ ∗
                wp L E e₃ Φ)) ⊢ wp L E e₁ Φ := by
  rw [wp_unfold]

theorem wp_lift_step_spec_couple [Add B] [L.IsLawful] [L.IsTopAbsorbing] {E : CoPset}
    {e₁ : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    (∀ (σ₁ : State rT) e₁' σ₁' (b₁ : B), stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      budgetInterp b₁ -∗ |={E, ∅}=>
      specCoupl L ∅ σ₁ e₁' σ₁' b₁ fun σ₂ ρ' b₂ => iprop(|={∅, E}=>
        stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ budgetInterp b₂ ∗ wp L E e₁ Φ)) ⊢
    wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb]
  imodintro
  iapply specCoupl_bind Std.LawfulSet.subset_refl
  iframe H
  iintro %σ₂ %ρ₂ %b₂ HInner
  iapply fupd_specCoupl
  imod HInner with ⟨Hσ', Hs', Hb', HW⟩
  imod wp_unfold_mp $$ HW %σ₂ %ρ₂.expr %ρ₂.state %b₂ [$Hσ' $Hs' $Hb'] with HW'
  imodintro
  iexact HW'

theorem wp_lift_step_prog_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' (b₁ : B), stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      budgetInterp b₁ -∗ |={E, ∅}=>
      progCoupl L e₁ σ₁ e₁' σ₁' b₁ fun e₂ σ₂ e₂' σ₂' b₂ => iprop% ▷ |={∅, E}=>
        stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗ budgetInterp b₂ ∗
          wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb]
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_mono (Z₁ := fun e₂ σ₂ e₂' σ₂' b₂ => iprop% ▷ |={∅, E}=>
    stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗ budgetInterp b₂ ∗ wp L E e₂ Φ)
  iframe H
  iintro %e₂ %σ₂ %e₂' %σ₂' %b₂ HL !>
  iapply specCoupl_ret
  iexact HL

/-! ### Rules that pair the program step with a Dirac on the other side

Everything below routes through `specCoupl_step_concentrated` or `progCoupl_step_l_concentrated`,
which build the exact coupling along a diagonal (`rel_dirac_left`/`_right`). -/

section ConcentratedRules
variable [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive]
  [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind]

theorem wp_lift_step_later_concentrated {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none) (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=> ⌜Reducible e₁ σ₁⌝ ∗ ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗
      |={∅}=> ▷ |={∅, E}=> stateInterp σ₂ ∗ wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_step_l_concentrated Hred (hSmeas σ₁) (hSconc σ₁)
  iintro %e₂ %σ₂ %Hmem
  imod H $$ %e₂ %σ₂ %Hmem
  iintro !> !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', HwpNew⟩
  imodintro
  iframe

@[discrete]
theorem wp_lift_step_later {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) (hne : e₁.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=> ⌜Discrete.Reducible e₁ σ₁⌝ ∗ ∀ e₂ σ₂,
      ⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝ -∗ |={∅}=> ▷ |={∅, E}=> stateInterp σ₂ ∗ wp L E e₂ Φ) ⊢
    wp L E e₁ Φ := by
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
      |={∅, E}=> stateInterp σ₂ ∗ wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_later_concentrated Hv hSmeas hSconc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]
  [L.HasBind] in
/-- `wp_lift_prim_steps_coupl` by a step of any bind law whose heads shift: the step's head is at
`b₁`, and `b₂` rides through it on every leftover (Rocq `wp_couple_spend`). -/
theorem wp_lift_prim_steps_coupl_law (law : L.BindLaw) [law.HeadShift] {E : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' (b : B),
      stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ budgetInterp b -∗
      |={E, ∅}=> ∃ (R : Cfg rT → Cfg rT → B) (b₁ b₂ : B),
        ⌜b₁ + b₂ ≤ b⌝ ∗
        ⌜b₂ < (⊤ : B)⌝ ∗
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜Reducible e₁' σ₁'⌝ ∗
        ⌜law.head (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) R b₁⌝ ∗
        ⌜law.SideForExec (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)
          (fun ρ ρ' => R ρ ρ' + b₂) id⌝ ∗
        (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂ < (⊤ : B)⌝ -∗ |={∅}=> ▷ |={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗
            budgetInterp (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂) ∗ wp L E e₂ Φ)) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b Hres
  imod H $$ %σ₁ %e₁' %σ₁' %b Hres with
    ⟨%R, %b₁, %b₂, %hb, %hb₂, %Hred, %Hred', %Hhead, %hside, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_steps_spend_law law hb hb₂ Hred Hred' Hhead hside
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  imod H $$ %e₂ %σ₂ %e₂' %σ₂' %hR
  iintro !> !>
  iapply specCoupl_ret
  iexact H

omit [L.IsReflexive] in
/-- Couple a program step against a spec step within `b₁`, leaving `b₂` to the continuation out
of the budget `b` (clutch-dp's `wp_couple`). -/
theorem wp_lift_prim_steps_coupl {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' (b : B),
      stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ budgetInterp b -∗
      |={E, ∅}=> ∃ (S : Cfg rT → Cfg rT → Prop) (b₁ b₂ : B),
        ⌜b₁ + b₂ ≤ b⌝ ∗
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜Reducible e₁' σ₁'⌝ ∗
        ⌜L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
        (∀ e₂ σ₂ e₂' σ₂', ⌜S ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ -∗ |={∅}=> ▷ |={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗ budgetInterp b₂ ∗
            wp L E e₂ Φ)) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b Hres
  imod H $$ %σ₁ %e₁' %σ₁' %b Hres with ⟨%S, %b₁, %b₂, %hb, %Hred, %Hred', %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_steps hb Hred Hred' Hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %HS
  imod H $$ %e₂ %σ₂ %e₂' %σ₂' %HS
  iintro !> !>
  iapply specCoupl_ret
  iexact H

omit [L.IsReflexive] in
theorem wp_lift_prim_step_l_erasable {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' (b : B),
      stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ budgetInterp b -∗
      |={E, ∅}=> ∃ (S : Cfg rT → State rT → Prop) (μ₁' : MeasureTheory.Measure (State rT))
        (b₁ b₂ : B),
        ⌜b₁ + b₂ ≤ b⌝ ∗
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜ErasableExpr μ₁' σ₁'⌝ ∗
        ⌜L.Rel b₁ S (primStep ⟨e₁, σ₁⟩) μ₁'⌝ ∗
        (∀ e₂ σ₂ σ₂', ⌜S ⟨e₂, σ₂⟩ σ₂'⌝ -∗ |={∅}=> ▷ |={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₂'⟩ ∗ budgetInterp b₂ ∗
            wp L E e₂ Φ)) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b Hres
  imod H $$ %σ₁ %e₁' %σ₁' %b Hres with ⟨%S, %μ₁', %b₁, %b₂, %hb, %Hred, %Heras, %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_step_l_erasable hb Hred Hcpl Heras
  iintro %e₂ %σ₂ %σ₂' %HS
  imod H $$ %e₂ %σ₂ %σ₂' %HS
  iintro !> !>
  iapply specCoupl_ret
  iexact H

theorem wp_lift_atomic_step_fupd_concentrated {E1 E2 : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E1}=> ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜⟨e₂, σ₂⟩ ∈ S σ₁⌝ -∗ |={E1}[E2]▷=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E1 e₁ Φ := by
  iintro H
  iapply wp_lift_step_later_concentrated Hv hSmeas hSconc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hmem
  imod Hclose
  imod H $$ %e₂ %σ₂ %Hmem
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
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
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E1 e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd_concentrated Hv
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
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd_concentrated Hv hSmeas hSconc
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
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd Hv hne
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hpstep !> !>
  iapply H $$ %e₂ %σ₂ %Hpstep

theorem wp_lift_pure_det_step_concentrated {E E' : CoPset} {e₁ e₂ : Exp rT}
    {Φ : Val rT → IProp GF} (Hpure : PureStep e₁ e₂) :
    iprop(|={E}[E']▷=> wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  have Hv : e₁.toVal? = none := Exp.toVal?_eq_none.mpr (val_stuck (Hpure.safe default))
  iapply wp_lift_step_concentrated (S := fun σ₁ => {⟨e₂, σ₁⟩}) Hv
    (fun σ₁ => by measurability)
    (fun σ₁ => by
      show primStep ⟨e₁, σ₁⟩ _ = 0
      rw [Hpure.det σ₁, MeasureTheory.Measure.dirac_apply' _ (by measurability)]
      simp)
  iintro %σ₁ Hσ
  imod H
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  isplitr; · ipureintro; exact Hpure.safe σ₁
  iintro !> %e₂' %σ₂ %Hmem
  cases Set.mem_singleton_iff.mp Hmem
  imod Hclose
  imod H
  imodintro
  iframe Hσ
  iexact H

/-! ### Countability-free pure-step rules

Stated on the measure-theoretic `PureStep` / `PureExec`, so they hold for a diffuse `rT`. -/

theorem wp_pure_step_one' {E : CoPset} {e₁ e₂ : Exp rT} {Φ : Val rT → IProp GF}
    (Hstep : PureStep e₁ e₂) : iprop(▷ wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_pure_det_step_concentrated Hstep
  iintro !> !> !>
  iexact H

theorem wp_pure_step_fupd' {E E' : CoPset} {e₁ e₂ : Exp rT} {φ : Prop} {n : Nat}
    {Φ : Val rT → IProp GF} [Hex : PureExec φ n e₁ e₂] (Hφ : φ) :
    iprop(|={E}[E']▷=>^[n] wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
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
    iprop(▷^[n] wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  refine .trans ?_ (wp_pure_step_fupd' (E' := E) (e₂ := e₂) Hφ)
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    refine (BI.later_mono ih).trans ?_
    simp only [Nat.repeat]
    iintro H !> !> !>
    iexact H

/-! ## Evaluation-context lifting lemmas (ports `clutch/theories/approxis/ectx_lifting.v`) -/

omit [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
theorem wp_lift_head_step_prog_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' (b₁ : B), stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      budgetInterp b₁ -∗ |={E, ∅}=>
      ⌜∃ ρ : Cfg rT, 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝ ∗
      progCoupl L e₁ σ₁ e₁' σ₁' b₁ fun e₂ σ₂ e₂' σ₂' b₂ => iprop% ▷ |={∅, E}=>
        stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗ budgetInterp b₂ ∗
          wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_prog_couple Hv
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ %e₁' %σ₁' %b₁ [$Hσ $Hs $Hb] with ⟨-, H⟩
  imodintro
  iexact H

@[discrete]
theorem wp_lift_atomic_head_step {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) (Hlc : e₁.IsLocallyClosed := by is_lc)
    (hne : e₁.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=> ⌜∃ ρ : Cfg rT, 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝ ∗
      ▷ ∀ e₂ σ₂, ⌜0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝ -∗ |={E}=> stateInterp σ₂ ∗
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step Hv hne
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hhred, H⟩
  imodintro
  have Hhr : HeadReducible e₁ σ₁ := fun hz => by obtain ⟨ρ, hρ⟩ := Hhred; simp [hz] at hρ
  isplitr; · ipureintro; exact Reducible.toDiscrete hne (reducible_of_headReducible Hlc Hhr)
  iintro !> %e₂ %σ₂ %Hpstep
  have hpos : 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩} :=
    primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible Hlc Hhr) ▸ Hpstep
  iapply H $$ %e₂ %σ₂ %hpos

/-! ### Countability-free head-step rules

The head-step rules gate on `headStep`, and head-reducibility is only known inside the assertion.
Off the head-reducible states the redex may sit under a context and `primStep` moves elsewhere,
so the carrying set is padded to `Set.univ` there, where concentration is free. -/

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
      |={∅, E}=> stateInterp σ₂ ∗ wp L E e₂ Φ) ⊢ wp L E e₁ Φ := by
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
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E1 e₁ Φ := by
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
      (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢ wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_head_step_fupd_concentrated Hv Hlc hSmeas hSconc
  iintro %σ₁ Hσ
  imod H $$ %σ₁ [$Hσ] with ⟨%Hhred, H⟩
  imodintro
  iframe %Hhred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

-- DISCRETE: `wp_lift_pure_det_head_step (_Hv : e₁.toVal? = none) (Hlc : e₁.IsLocallyClosed)`
--   `(Hsafe : ∀ σ₁, ∃ ρ, 0 < headStep ⟨e₁, σ₁⟩ {ρ})`
--   `(Hdet : ∀ σ₁ e₂' σ₂, 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂', σ₂⟩} → σ₂ = σ₁ ∧ e₂' = e₂) :`
--   `(|={E}[E']▷=> wp L E e₂ Φ) ⊢ wp L E e₁ Φ`

-- DISCRETE: `wp_lift_pure_det_head_step'` — same hypotheses, `▷`-form:
--   `(▷ wp L E e₂ Φ) ⊢ wp L E e₁ Φ`

end ConcentratedRules

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
