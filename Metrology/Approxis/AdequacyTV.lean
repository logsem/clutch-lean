module

public import Metrology.Approxis.AdequacyRel
public import Metrology.Couplings.CodensityTV

@[expose] public section

/-! # Adequacy at total variation

The generic adequacy statements instantiated at `Δ := TVDiv.tv`, read back as additive couplings.
These are exactly the pre-codensity statements of `Adequacy.lean` and `AdequacyRel.lean`. -/

namespace ProbLang

open Iris Iris.BI ProbLang.ApproxisWpGS

variable {rT : Type} [LawfulProbLangℝ rT] {GF : BundledGFunctors}

section
variable [AppPreGS rT GF] [SpecPreGS rT GF] [ECPreGS GF] [InvGpreS GF]

/-- `wp_adequacy` at `tv`: an additive coupling of the limit executions. -/
theorem wp_adequacy_tv (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal) (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗
        wp TVDiv.tv ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    AddCoupl ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (wp_adequacy e e' σ σ' ε φ Hwp).addCoupl

/-- `wp_adequacy_error_lim` at `tv`. -/
theorem wp_adequacy_error_lim_tv (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF) (ε' : ENNReal), ε < ε' →
      ⊢@{IProp GF} ⤇ e' -∗ ec ε' -∗
        wp TVDiv.tv ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    AddCoupl ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (wp_adequacy_error_lim e e' σ σ' ε φ Hwp).addCoupl

/-- `wp_adequacy_mass` at `tv`: the mass of the left limit is bounded by the right one plus `ε`. -/
theorem wp_adequacy_mass_tv (e e' : Exp rT) (σ σ' : State rT) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal) (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗ WP[TVDiv.tv] e {{ v, ∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝ }}) :
    limExecV ⟨e, σ⟩ Set.univ ≤ limExecV ⟨e', σ'⟩ Set.univ + ε := by
  simpa using AddCoupl.mass_leq (wp_adequacy_tv e e' σ σ' ε φ Hwp)

end

/-- `approximates_coupling` at `tv`. -/
theorem approximates_coupling_tv [RefinesPreGS rT GF]
    (A : ∀ (_ : ApproxisRGS rT .hasNoLC GF), lrel rT GF)
    (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (HA : ∀ (IR : ApproxisRGS rT .hasNoLC GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : ApproxisRGS rT .hasNoLC GF),
      ⊢@{IProp GF} ↯ ε -∗ refines TVDiv.tv ⊤ e e' (A IR)) :
    AddCoupl ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (approximates_coupling A φ e e' σ σ' ε HA Hlog).addCoupl

/-- `refines_coupling` at `tv`. -/
theorem refines_coupling_tv [RefinesPreGS rT GF]
    (A : ∀ (_ : ApproxisRGS rT .hasNoLC GF), lrel rT GF)
    (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT)
    (HA : ∀ (IR : ApproxisRGS rT .hasNoLC GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : ApproxisRGS rT .hasNoLC GF), ⊢@{IProp GF} refines TVDiv.tv ⊤ e e' (A IR)) :
    AddCoupl 0 (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  (refines_coupling A φ e e' σ σ' HA Hlog).addCoupl

end ProbLang
