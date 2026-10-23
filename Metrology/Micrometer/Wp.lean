module

public import Metrology.Micrometer.ProgCoupl
public import Metrology.Micrometer.KernelWp
import Metrology.Iris.LocalBI

/-! # Micrometer weakest precondition

`wp L E e Φ` is the guarded fixpoint of `wpPre` (main result `wp_strong_mono`). -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE GradedLifting

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

namespace MicrometerWpGS
variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]
local bi IProp GF

/-! ## `wpPre` and its fixpoint `wp` -/

section Wp
variable [BudgetGS B GF] {n : Nat} {E E1 E2 : CoPset} {e : Exp rT} {v : Val rT}
  {Φ Ψ : Val rT → IProp GF}
open SpecUpdateGS BIFUpdate
open Exp (ofVal toVal?_ofVal ofVal_of_toVal_some)
open LawfulSet (empty_subset subset_refl)

variable (L) in
/-- One unfolding of `wp`: open the invariants, run a spec phase, then either finish at a value or
take one coupled program step followed by a later and another spec phase (Rocq `wp_pre`). -/
noncomputable abbrev wpPre (wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : Exp rT) (Φ : Val rT → IProp GF) :=
  wpPreFor primStep L wp E e₁ Φ

/-- `wpPre` is non-expansive in the postcondition and needs `wp` to agree only one step lower. -/
theorem wpPre_ne_aux {wp wp' : WpType} (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v)
    (Hwp : ∀ m, m < n → ∀ e₃, wp E e₃ Φ ≡{m}≡ wp' E e₃ Ψ) :
    wpPre L wp E e Φ ≡{n}≡ wpPre L wp' E e Ψ :=
  wpPreFor_ne_aux HΦ Hwp

instance wpPre_contractive : Contractive (wpPre L (rT := rT) (GF := GF)) :=
  wpPreFor_contractive

variable (L) in
/-- The Micrometer weakest precondition under the lifting `L`, the fixpoint of `wpPre`. -/
noncomputable abbrev wp (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF) :=
  wpFor primStep L E e Φ

/-- `wp` is its own one-step unfolding. -/
theorem wp_unfold : wp L E e Φ = wpPre L (wp L) E e Φ :=
  wpFor_unfold

/-- The forward direction of `wp_unfold`. -/
theorem wp_unfold_mp : wp L E e Φ ⊢ wpPre L (wp L) E e Φ :=
  wpFor_unfold_mp

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

/-- Prints `wp L E e Φ` back as `WP[L] e @ E {{ Φ }}`, dropping `@ ⊤`. -/
@[app_unexpander wp]
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

theorem wp_value_fupd : (|={E}=> Φ v) ⊢ wp L E (.ofVal v) Φ :=
  wpFor_value_fupd

/-- A value satisfies the weakest precondition when it satisfies the postcondition. -/
theorem wp_value : Φ v ⊢ wp L E (.ofVal v) Φ :=
  wpFor_value

theorem wp_value_of_toVal (h : e.toVal? = some v) : Φ v ⊢ wp L E e Φ :=
  wpFor_value_of_toVal h

theorem wp_value_fupd_of_toVal (h : e.toVal? = some v) : (|={E}=> Φ v) ⊢ wp L E e Φ :=
  wpFor_value_fupd_of_toVal h

/-- A weakest precondition at a value unfolds to a spec coupling. -/
theorem wp_value_specCoupl_unfold (E : CoPset) (He : e.toVal? = some v) :
    wp L E e Φ ⊢
      ∀ σ₁ e₁' σ₁' b₁,
        stateInterp (rT := rT) σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗
          budgetInterp b₁ -∗
          |={E, ∅}=> specCoupl L ∅ σ₁ e₁' σ₁' b₁ (fun σ₂ ρ' b₂ =>
            iprop(|={∅, E}=>
              stateInterp σ₂ ∗ specInterp ρ' ∗ budgetInterp b₂ ∗ Φ v)) :=
  wpFor_value_specCoupl_unfold E He

/-! ## The continuation after a program step -/

variable (L) in
/-- The `none`-branch continuation of `wpPre` with `wp` itself plugged in; `wp_unfold` produces it
verbatim. -/
noncomputable abbrev wpProgBody (E : CoPset) (Φ : Val rT → IProp GF)
    (e₃ : Exp rT) (σ₃ : State rT) (e₃' : Exp rT) (σ₃' : State rT) (b₃ : B) :=
  wpProgBodyFor primStep L E Φ e₃ σ₃ e₃' σ₃' b₃

variable {b : B}

/-- At an absorbing budget the continuation holds trivially. -/
theorem wpProgBody_absorbing (hb : L.Absorbing b) :
    ⊢ □ ∀ e₃ σ₃ e₃' σ₃', wpProgBody L E Φ e₃ σ₃ e₃' σ₃' b :=
  wpProgBodyFor_absorbing hb

/-- The continuation can be mapped under its later by an update from the old `wp` to a new one,
which may change the mask, the expression and the postcondition. -/
theorem wpProgBody_wand {E' : CoPset} {e₃ e₄ : Exp rT}
    {σ₃ : State rT} {e₃' : Exp rT} {σ₃' : State rT} : iprop%
    wpProgBody L E Φ e₃ σ₃ e₃' σ₃' b ∗ ▷ (wp L E e₃ Φ ={E, E'}=∗ wp L E' e₄ Ψ) ⊢
      wpProgBody L E' Ψ e₄ σ₃ e₃' σ₃' b :=
  wpProgBodyFor_wand

/-! ## Monotonicity and updates -/

variable (L) in
/-- `wp_strong_mono` generalized over masks, expression and postconditions: the Löb statement. -/
noncomputable abbrev wpStrongMonoStmt : IProp GF :=
  wpForStrongMonoStmt primStep L

/-- `wp` is monotone in the mask and in the postcondition, where the postcondition update may
use the state, spec and budget interpretations. -/
theorem wp_strong_mono (HE : E1 ⊆ E2) : iprop%
    wp L E1 e Φ ∗ wpStrongMonoCont (B := B) E2 Φ Ψ ⊢ wp L E2 e Ψ :=
  wpFor_strong_mono HE

/-- The weakest precondition is monotone in its postcondition, under a persistent wand. -/
theorem wp_wand : iprop% wp L E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v) ⊢ wp L E e Ψ :=
  wpFor_wand

/-- A fancy update in the postcondition can be absorbed. -/
theorem wp_fupd : wp L E e (fun v => iprop(|={E}=> Φ v)) ⊢ wp L E e Φ :=
  wpFor_fupd

/-- A fancy update before a weakest precondition can be absorbed. -/
theorem fupd_wp : (|={E}=> wp L E e Φ) ⊢ wp L E e Φ :=
  fupd_wpFor

/-! ## Derived monotonicity -/

/-- The weakest precondition is monotone in its postcondition. -/
theorem wp_mono (HΦ : ∀ v, Φ v ⊢ Ψ v) : wp L E e Φ ⊢ wp L E e Ψ :=
  wpFor_mono HΦ

/-- The weakest precondition is monotone in its mask. -/
theorem wp_mask_mono (HE : E1 ⊆ E2) : wp L E1 e Φ ⊢ wp L E2 e Φ :=
  wpFor_mask_mono HE

theorem wp_wand_l : iprop% □ (∀ v, Φ v -∗ Ψ v) ∗ wp L E e Φ ⊢ wp L E e Ψ :=
  wpFor_wand_l

theorem wp_wand_r : iprop% wp L E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v) ⊢ wp L E e Ψ :=
  wpFor_wand_r

/-! ## Non-expansiveness -/

theorem wp_ne_aux (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v) : wp L E e Φ ≡{n}≡ wp L E e Ψ :=
  wpFor_ne_aux HΦ

instance wp_ne : NonExpansive (wp L (GF := GF) E e) :=
  wpFor_ne

-- TODO: `wp_contractive`, as in Iris

end Wp

end MicrometerWpGS

end ProbLang
