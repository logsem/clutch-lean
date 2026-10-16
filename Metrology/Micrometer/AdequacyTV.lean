module

public import Metrology.Micrometer.AdequacyRel
public import Metrology.Couplings.Bridges.AddCoupl
public import Metrology.Couplings.Divergences.Tv

/-! Adequacy at total variation: the generic statements at `codensity tv`, as additive couplings. -/

@[expose] public section

open scoped ENNReal

namespace ProbLang

open Iris Iris.BI ProbLang.MicrometerWpGS GradedLifting GradedDivergence

variable {rT : Type} [LawfulProbLangℝ rT] {GF : BundledGFunctors}

section
variable [MeasurableSingletonClass rT] [AppPreGS rT GF] [SpecPreGS rT GF]
  [BudgetCreditPreGS ℝ≥0∞ GF] [InvGpreS GF]

/-- `wp_adequacy` at `tv`: an additive coupling of the limit executions. -/
theorem wp_adequacy_tv (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal) (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯b ε -∗
        wp (codensity tv) ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    AddCoupl ε {p | adequacyRel φ p.1 p.2} (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (wp_adequacy (L := codensity tv) e e' σ σ' ε φ Hwp).addCoupl

/-- `wp_adequacy_error_lim` at `tv`. -/
theorem wp_adequacy_error_lim_tv (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF) (ε' : ENNReal), ε < ε' →
      ⊢@{IProp GF} ⤇ e' -∗ ↯b ε' -∗
        wp (codensity tv) ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    AddCoupl ε {p | adequacyRel φ p.1 p.2} (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (wp_adequacy_error_lim (L := codensity tv) e e' σ σ' ε φ Hwp).addCoupl

/-- `wp_adequacy_div` at `tv`: programs whose results agree up to `ε` differ by at most `ε` on
every event. -/
theorem wp_adequacy_div_tv (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯b ε -∗
        wp (codensity tv) ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝)))
    {S : Set (Exp rT)} (hS : MeasurableSet S) :
    limExecV ⟨e, σ⟩ S ≤ limExecV ⟨e', σ'⟩ S + ε :=
  tv_iff.1 (wp_adequacy_div (D := tv) (L := codensity tv) e e' σ σ' ε Hwp) S hS

/-- `wp_adequacy_div_error_lim` at `tv`. -/
theorem wp_adequacy_div_error_lim_tv (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF) (ε' : ENNReal), ε < ε' →
      ⊢@{IProp GF} ⤇ e' -∗ ↯b ε' -∗
        wp (codensity tv) ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝)))
    {S : Set (Exp rT)} (hS : MeasurableSet S) :
    limExecV ⟨e, σ⟩ S ≤ limExecV ⟨e', σ'⟩ S + ε :=
  tv_iff.1 (wp_adequacy_div_error_lim (D := tv) (L := codensity tv) e e' σ σ' ε Hwp) S hS

/-- `wp_adequacy_mass` at `tv`: the mass of the left limit is bounded by the right one plus `ε`. -/
theorem wp_adequacy_mass_tv (e e' : Exp rT) (σ σ' : State rT) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal) (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯b ε -∗
        wp (codensity tv) ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    limExecV ⟨e, σ⟩ Set.univ ≤ limExecV ⟨e', σ'⟩ Set.univ + ε :=
  wp_adequacy_mass (L := codensity tv) (s := OrderAddMonoidHom.id ℝ≥0∞) e e' σ σ' φ ε Hwp

end

/-- `approximates_coupling` at `tv`. -/
theorem approximates_coupling_tv [MeasurableSingletonClass rT] [RefinesPreGS rT ℝ≥0∞ GF]
    (A : ∀ (_ : MicrometerRGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF), lrel rT GF)
    (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (HA : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS ℝ≥0∞ GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR IBC).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS ℝ≥0∞ GF),
      ⊢@{IProp GF} ↯b ε -∗ refines (codensity tv) ⊤ e e' (A IR IBC)) :
    AddCoupl ε {p | adequacyRel φ p.1 p.2} (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (approximates_coupling A φ e e' σ σ' ε HA Hlog).addCoupl

/-- `refines_coupling` at `tv`. -/
theorem refines_coupling_tv [MeasurableSingletonClass rT] [RefinesPreGS rT ℝ≥0∞ GF]
    (A : ∀ (_ : MicrometerRGS rT .hasNoLC GF) (_ : BudgetCreditGS ℝ≥0∞ GF), lrel rT GF)
    (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT)
    (HA : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS ℝ≥0∞ GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR IBC).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS ℝ≥0∞ GF),
      ⊢@{IProp GF} refines (codensity tv) ⊤ e e' (A IR IBC)) :
    AddCoupl 0 {p | adequacyRel φ p.1 p.2} (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (refines_coupling A φ e e' σ σ' HA Hlog).addCoupl

end ProbLang
