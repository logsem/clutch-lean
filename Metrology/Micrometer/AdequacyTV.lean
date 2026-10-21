module

public import Metrology.Micrometer.AdequacyRel
public import Metrology.Couplings.Bridges.AddCoupl
public import Metrology.Couplings.Divergences.Tv
import Metrology.Iris.LocalBI

/-! # Adequacy at total variation

The generic adequacy theorems at `codensity tv`, restated as additive couplings `AddCoupl ε` (or as
`μ S ≤ ν S + ε`), plus a left-step rule against a frozen right state. -/

@[expose] public section

open scoped ENNReal

namespace ProbLang

open Iris Iris.BI ProbLang.MicrometerWpGS GradedLifting GradedDivergence Set
open Exp (ofVal)
open MeasureTheory.Measure (dirac dirac_apply')

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] {GF : BundledGFunctors}
local bi IProp GF

/-! ## Unary adequacy at `tv` -/

section
variable [AppPreGS rT GF] [SpecPreGS rT GF] [BudgetCreditPreGS ℝ≥0∞ GF] [InvGpreS GF]
  (e e' : Exp rT) (σ σ' : State rT)

section
variable (ε : ENNReal)

/-- A `wp` proof at `codensity tv` with credit `ε` gives an additive coupling of the limit
executions (`wp_adequacy`). -/
theorem wp_adequacy_tv (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF),
      ⊢ ⤇ e' -∗ ↯b ε -∗
        wp (codensity tv) ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝))) :
    AddCoupl ε {p | adequacyRel φ p.1 p.2} (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (wp_adequacy e e' σ σ' ε φ Hwp).addCoupl

/-- As `wp_adequacy_tv`, from proofs at every credit `ε' > ε` (`wp_adequacy_budget_lim`). -/
theorem wp_adequacy_budget_lim_tv (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF) (ε' : ENNReal), ε < ε' →
      ⊢ ⤇ e' -∗ ↯b ε' -∗
        wp (codensity tv) ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝))) :
    AddCoupl ε {p | adequacyRel φ p.1 p.2} (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (wp_adequacy_budget_lim e e' σ σ' ε φ Hwp).addCoupl

/-- `wp_adequacy_div` at `tv`: programs whose results agree up to `ε` differ by at most `ε` on
every event. -/
theorem wp_adequacy_div_tv
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF),
      ⊢ ⤇ e' -∗ ↯b ε -∗
        wp (codensity tv) ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜v = v'⌝)))
    {S : Set (Exp rT)} (hS : MeasurableSet S) :
    limExecV ⟨e, σ⟩ S ≤ limExecV ⟨e', σ'⟩ S + ε :=
  tv_iff.1 (wp_adequacy_div e e' σ σ' ε Hwp) S hS

/-- As `wp_adequacy_div_tv`, from proofs at every credit `ε' > ε` (`wp_adequacy_div_budget_lim`). -/
theorem wp_adequacy_div_budget_lim_tv
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF) (ε' : ENNReal), ε < ε' →
      ⊢ ⤇ e' -∗ ↯b ε' -∗
        wp (codensity tv) ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜v = v'⌝)))
    {S : Set (Exp rT)} (hS : MeasurableSet S) :
    limExecV ⟨e, σ⟩ S ≤ limExecV ⟨e', σ'⟩ S + ε :=
  tv_iff.1 (wp_adequacy_div_budget_lim e e' σ σ' ε Hwp) S hS

end

/-- `wp_adequacy_mass` at `tv`: the mass of the left limit is bounded by the right one plus `ε`. -/
theorem wp_adequacy_mass_tv (φ : Val rT → Val rT → Prop) (ε : ENNReal)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF),
      ⊢ ⤇ e' -∗ ↯b ε -∗
        wp (codensity tv) ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝))) :
    limExecV ⟨e, σ⟩ univ ≤ limExecV ⟨e', σ'⟩ univ + ε :=
  wp_adequacy_mass (s := OrderAddMonoidHom.id ℝ≥0∞) e e' σ σ' φ ε Hwp

end

/-! ## Relational adequacy at `tv` -/

section
variable [RefinesPreGS rT ℝ≥0∞ GF]
  (A : ∀ (_ : MicrometerRGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF), lrel rT GF)
  (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT)

/-- A refinement at `codensity tv` from credit `ε` gives an additive coupling with error `ε`
(`approximates_coupling`). -/
theorem approximates_coupling_tv (ε : ENNReal)
    (HA : ∀ IR IBC v v', ⊢ (A IR IBC).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS ℝ≥0∞ GF),
      ⊢ ↯b ε -∗ refines (codensity tv) ⊤ e e' (A IR IBC)) :
    AddCoupl ε {p | adequacyRel φ p.1 p.2} (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (approximates_coupling A φ e e' σ σ' ε HA Hlog).addCoupl

/-- A refinement at `codensity tv` gives an additive coupling with error `0`
(`refines_coupling`). -/
theorem refines_coupling_tv
    (HA : ∀ IR IBC v v', ⊢ (A IR IBC).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS ℝ≥0∞ GF),
      ⊢ refines (codensity tv) ⊤ e e' (A IR IBC)) :
    AddCoupl 0 {p | adequacyRel φ p.1 p.2} (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (refines_coupling A φ e e' σ σ' HA Hlog).addCoupl

end

/-! ## Stepping against a frozen right state -/

section
variable [MicrometerWpGS (rT := rT) GF]

/-- Step the left program against a right state that does not move, for an additive coupling
with the right Dirac measure. -/
theorem progCoupl_step_l_dret {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε₂ ε : ENNReal} {R : Cfg rT → State rT → Prop}
    {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    (Hε : ε₁ + ε₂ ≤ ε) (Hred : Reducible e₁ σ₁)
    (Hcpl : AddCoupl ε₁ {p | R p.1 p.2} (primStep ⟨e₁, σ₁⟩) (dirac σ₁')) : iprop%
    (∀ e₂ σ₂, ⌜R ⟨e₂, σ₂⟩ σ₁'⌝ -∗ |={∅}=> Z e₂ σ₂ e₁' σ₁' ε₂) ⊢
      progCoupl (codensity tv.{0}) e₁ σ₁ e₁' σ₁' ε Z := by
  iintro H
  -- A Dirac measure is concentrated on `σ₁'`, so the coupling can be restricted to `p.2 = σ₁'`;
  -- the right side is then the erasable `dret σ₁'`.
  have hconc : dirac σ₁' {σ₁'}ᶜ = 0 := by
    rw [dirac_apply' _ (by measurability)]; simp
  have HcplR : AddCoupl ε₁ {p | R p.1 p.2 ∧ p.2 = σ₁'}
      (primStep ⟨e₁, σ₁⟩) (dirac σ₁') :=
    AddCoupl.concentrated_R (MeasurableSet.singleton σ₁') hconc Hcpl
  iapply progCoupl_step_l_erasable Hε Hred HcplR.codensity (ErasableExpr.dret σ₁')
  iintro %e₂ %σ₂ %σ₂' %HR'
  obtain ⟨HR, rfl⟩ := HR'
  iapply H $$ %e₂ %σ₂ %HR

end

end ProbLang
