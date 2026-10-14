module

public import Metrology.Approxis.AppWeakestpre
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.ProbLang.Erasure
public import Metrology.Iris.StepFupd

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS ProbLang.Cfg
open GradedDivergence
open scoped AppGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]
variable {ι : Type} [Monoid ι]

def adequacyRel (φ : Val rT → Val rT → Prop) : Set (Exp rT × Exp rT) :=
  fun p => ∃ v v', p.1.toVal? = some v ∧ p.2.toVal? = some v' ∧ φ v v'

omit [LawfulProbLangℝ rT] in
theorem adequacyRel_eq_subset :
    adequacyRel (rT := rT) (· = ·) ⊆ {p : Exp rT × Exp rT | p.1 = p.2} := by
  rintro ⟨e₁, e₂⟩ ⟨v, v', hv, hv', rfl⟩
  exact (Exp.ofVal_of_toVal_some hv).symm.trans (Exp.ofVal_of_toVal_some hv')

/-- The codensity lifting of the finite executions of `ρ` against the limit execution of `ρ'`. -/
@[reducible] def execCoupl (Δ : GradedDivergence.{0} ι) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal) (n : Nat) (ρ ρ' : Cfg rT) : Prop :=
  Δ.Codensity 1 ε (adequacyRel φ) (asExpr (execN n ρ)) (limExecV ρ')

section Adequacy

variable {Δ : GradedDivergence.{0} ι} [Δ.IsMassBounded] [Δ.IsZeroLeft] [Δ.IsLeftContinuous]
  [Δ.IsExpectationAdditive]
variable {GF : BundledGFunctors} [IA : ApproxisGS rT .hasNoLC GF]

omit [Δ.IsZeroLeft] [Δ.IsLeftContinuous] in
theorem wp_adequacy_spec_coupl (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
    (σ₁' : State rT) (Z : State rT → Cfg rT → ENNReal → IProp GF) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal) : iprop%
    specCoupl Δ ∅ σ₁ e₁' σ₁' ε Z ⊢
    (∀ σ₂ e₂' σ₂' ε', Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ ε' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ ε m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  set Ψ : State rT → Cfg rT → ENNReal → IProp GF := fun σ₀ ρ₀ ε₀ => iprop(
    (∀ σ₂ e₂' σ₂' ε', Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ ε' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ ε₀ m ⟨e₁, σ₀⟩ ρ₀⌝)
  iintro Hspec HZ
  iapply specCoupl_ind (Ψ := Ψ) $$ [] %σ₁ %e₁' %σ₁' %ε Hspec HZ
  iintro !> %σ₀ %⟨e₀', σ₀'⟩ %ε₀ H
  simp only [Ψ]
  iintro HZ
  icases H with ⟨%HVac | HZApp | HCpl⟩
  · imodintro
    iapply (laterN_intro n).trans (step_fupdN_intro Std.LawfulSet.empty_subset)
    ipureintro
    exact codensity_of_one_le HVac
  · iapply HZ $$ HZApp
  · icases HCpl with ⟨%S, %k, %μ₁, %μ₁', %ε₁, %X₂, %r,
      %HAC, %HX₂meas, %HX₂bnd, %HεBnd, %Herase1, %Herase1', HCont⟩
    iapply BIFUpdate.mono
    · refine step_fupdN_mono (P := iprop(∀ σ₂ e₂' σ₂', ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗
        ⌜execCoupl Δ φ (X₂ ⟨e₂', σ₂'⟩) m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝ : IProp GF)) ?_
      iintro %Hpure !%
      exact Codensity_erasure_erasable_exp_rhs HX₂meas HAC (_root_.le_refl _) HεBnd Herase1 Herase1'
        fun σ₂ ⟨e₂', σ₂'⟩ hR => Hpure σ₂ e₂' σ₂' hR
    iapply fupd_step_fupdN_plain_forall_3
    iintro %σ₂ %e₂' %σ₂'
    iapply BIFUpdate.mono (step_fupdN_pure_wand_intro ∅ n)
    iapply fupd_pure_wand_intro
    iintro %HS
    imod HCont $$ %σ₂ %e₂' %σ₂' %HS with ⟨HΨ, -⟩
    iapply HΨ $$ HZ

omit [Δ.IsMassBounded] [Δ.IsZeroLeft] [Δ.IsLeftContinuous] [Δ.IsExpectationAdditive] in
theorem wp_adequacy_prog_coupl (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
    (σ₁' : State rT) (Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF)
    (φ : Val rT → Val rT → Prop) (ε : ENNReal) (Hnone : e₁.toVal? = none) : iprop%
    progCoupl Δ e₁ σ₁ e₁' σ₁' ε Z ⊢
    (∀ e₂ σ₂ e₂' σ₂' ε', Z e₂ σ₂ e₂' σ₂' ε' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ ε' m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ ε (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  simp only [execCoupl, execN_succ_not_isValue (ρ := ⟨e₁, σ₁⟩) (Exp.toVal?_eq_none.mp Hnone) m]
  iintro HCpl Hcoupl
  icases HCpl with ⟨%k, %μ₁', %X₂, %_, %_, %Hexp, %Herase', Hcnt⟩
  iapply BIFUpdate.mono
  · refine step_fupdN_mono (P := iprop(∀ e₂ σ₂ e₂' σ₂',
      ⌜execCoupl Δ φ (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ : IProp GF)) ?_
    iintro %Hpure !%
    exact Codensity_erasure_erasable_exp_lhs_kanto Herase' Hexp
      fun ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ => Hpure e₂ σ₂ e₂' σ₂'
  iapply fupd_step_fupdN_plain_forall_4
  iintro %e₂ %σ₂ %e₂' %σ₂'
  imod Hcnt $$ %e₂ %σ₂ %e₂' %σ₂' with Hcnt
  iapply Hcoupl $$ Hcnt

omit [Δ.IsZeroLeft] [Δ.IsLeftContinuous] in
theorem wp_adequacy_spec_coupl_zero (m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
    (σ₁' : State rT) (Z : State rT → Cfg rT → ENNReal → IProp GF) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal) : iprop%
    specCoupl Δ ∅ σ₁ e₁' σ₁' ε Z ⊢
    (∀ σ₂ e₂' σ₂' ε', Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=> ⌜execCoupl Δ φ ε' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> ⌜execCoupl Δ φ ε m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ :=
  wp_adequacy_spec_coupl 0 m e₁ σ₁ e₁' σ₁' Z φ ε

omit [Δ.IsMassBounded] [Δ.IsZeroLeft] [Δ.IsLeftContinuous] [Δ.IsExpectationAdditive] in
variable (Δ) in
theorem wpPre_value_Z_eq {v : Val rT} {Φ : Val rT → IProp GF} (E : CoPset) :
    (fun (σ₂ : State rT) (ρ' : Cfg rT) (ε₂ : ENNReal) =>
      iprop(|={∅, E}=> stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗
        errInterp (rT := rT) ε₂ ∗ Φ v))
    = (fun (σ₂ : State rT) (ρ' : Cfg rT) (ε₂ : ENNReal) =>
      match (Exp.ofVal v).toVal? with
      | some v => iprop(|={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗
            errInterp (rT := rT) ε₂ ∗ Φ v)
      | none => iprop(progCoupl Δ (Exp.ofVal v) σ₂ ρ'.expr ρ'.state ε₂
          (fun e₃ σ₃ e₃' σ₃' ε₃ =>
            iprop(▷ specCoupl Δ ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
              iprop(|={∅, E}=>
                stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗
                  errInterp (rT := rT) ε₄ ∗ wp Δ E e₃ Φ)))))) := by
  funext σ₂ ρ' ε₂
  rw [Exp.toVal?_ofVal]

set_option linter.auxLemma false in
omit [LawfulProbLangℝ rT] in
theorem wpPre_match_eq (motive : Option (Val rT) → Sort u)
    (x : Option (Val rT)) (some_f : (v : Val rT) → motive (some v))
    (none_f : Unit → motive none) :
    ProbLang.wpPre_value_Z_eq.match_1 motive x some_f none_f =
    ProbLang.ApproxisWpGS.wpPre.match_1 motive x some_f none_f := by
  cases x <;> rfl

omit [Δ.IsMassBounded] [Δ.IsZeroLeft] [Δ.IsLeftContinuous] [Δ.IsExpectationAdditive] in
theorem wp_value_specCoupl_unfold {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (E : CoPset) (He : e.toVal? = some v) :
    wp Δ E e Φ ⊢@{IProp GF}
      ∀ σ₁ e₁' σ₁' ε₁,
        stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
          errInterp (rT := rT) ε₁ -∗
          |={E, ∅}=> specCoupl Δ ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
            iprop(|={∅, E}=>
              stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗
                errInterp (rT := rT) ε₂ ∗ Φ v)) := by
  obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  rw [wpPre_value_Z_eq Δ E]
  simp only [wpPre_match_eq]
  iintro Hwp %σ₁ %e₁' %σ₁' %ε₁ Hinterp
  iapply (BI.equiv_iff.mp ApproxisWpGS.wp_unfold).1 $$ Hwp %σ₁ %e₁' %σ₁' %ε₁ Hinterp

omit [Δ.IsLeftContinuous] in
theorem wp_adequacy_val_fupd (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) (v : Val rT) (ε : ENNReal) (He : e.toVal? = some v) :
    appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ ecAuth ε ∗
      wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)) ⊢@{IProp GF}
    |={⊤, ∅}=> ⌜execCoupl Δ φ ε n ⟨e, σ⟩ ⟨e', σ'⟩⌝ := by
  obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  iintro ⟨Hσ, Hs, Hε, Hwp⟩
  imod wp_value_specCoupl_unfold ⊤ He $$ Hwp %σ %e' %σ' %ε [$] with HspecC
  iapply wp_adequacy_spec_coupl_zero $$ HspecC
  iintro %σ₂ %e₂' %σ₂' %ε' HZ
  imod HZ with ⟨-, Hs', -, %v', Hv', %Hφrel⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs' Hv'
  imod BIFUpdate.subset (E2 := ∅) Std.LawfulSet.empty_subset with -
  iintro !%
  unfold execCoupl limExecV asExpr
  cases n with
  | zero =>
    simp only [execN, MeasureTheory.Measure.map_zero]
    exact codensity_zero_left
  | succ n =>
    rw [execN_succ_isValue (ρ := ⟨Exp.ofVal v, σ₂⟩) v.isValue n,
        limExec_of_isVal (e := Exp.ofVal v') (σ := σ₂') v'.2]
    simp only [MeasureTheory.Measure.map_dirac' Cfg.measurable_expr]
    exact (codensity_dirac (R := adequacyRel φ)
      ⟨v, v', Exp.toVal?_ofVal v, Exp.toVal?_ofVal v', Hφrel⟩).mono_bound zero_le

omit [Δ.IsLeftContinuous] in
theorem wp_adequacy_step_fupdN (ε : ENNReal) (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) :
    appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ ecAuth ε ∗
      wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)) ⊢@{IProp GF}
    |={⊤, ∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ ε n ⟨e, σ⟩ ⟨e', σ'⟩⌝ := by
  induction n generalizing ε e e' σ σ' with
  | zero =>
    iintro -
    imod BIFUpdate.subset (E2 := ∅) Std.LawfulSet.empty_subset with -
    imodintro
    simp only [Nat.repeat]
    ipureintro
    simp only [execCoupl, asExpr, execN_zero, MeasureTheory.Measure.map_zero]
    exact codensity_zero_left
  | succ n ih =>
    iintro ⟨Hσ, Hs, Hε, Hwp⟩
    by_cases He : e.isValue
    · obtain ⟨v, Hv⟩ := Exp.toVal?_eq_some_of_isValue He
      imod wp_adequacy_val_fupd e e' σ σ' (n+1) φ v ε Hv $$ [$] with %Hpure
      imodintro
      iapply (laterN_intro (n+1)).trans (step_fupdN_intro Std.LawfulSet.subset_refl)
      ipureintro
      exact Hpure
    · have hnone : e.toVal? = none := Exp.toVal?_eq_none.mpr He
      imod wp_unfold_mp $$ Hwp %σ %e' %σ' %ε [$] with Hwp
      iapply wp_adequacy_spec_coupl $$ Hwp
      rw [hnone]
      iintro %σ₂ %e₂' %σ₂' %ε' Hprog
      iapply wp_adequacy_prog_coupl (Hnone := hnone) $$ Hprog
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ Hspec
      simp only [Nat.repeat]
      iintro !> !> !>
      iapply wp_adequacy_spec_coupl $$ Hspec
      iintro %σ₄ %e₄' %σ₄' %ε₄ HZ
      imod HZ
      iapply ih ε₄ e₃ e₄' σ₄ σ₄' $$ HZ

end Adequacy

variable {Δ : GradedDivergence.{0} ι} [Δ.IsMassBounded] [Δ.IsZeroLeft] [Δ.IsLeftContinuous]
  [Δ.IsExpectationAdditive]
variable {GF : BundledGFunctors}
variable [AppPreGS rT GF] [SpecPreGS rT GF] [IECPre : ECPreGS GF] [InvGpreS GF]

omit [Δ.IsLeftContinuous] in
theorem wp_adequacy_exec_n (e e' : Exp rT) (σ σ' : State rT) (n : Nat) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal) (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    execCoupl Δ φ ε n ⟨e, σ⟩ ⟨e', σ'⟩ := by
  by_cases hε1 : 1 ≤ ε
  · exact codensity_of_one_le hε1
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) n 0 fun Hinv => ?_
  iintro -
  imod app_ra_init σ with ⟨%IA, HappAuth⟩
  imod spec_ra_init e' σ' with ⟨%ISpec, HspecAuth, HspecFrag⟩
  imod ec_alloc ε (lt_of_not_ge hε1) with ⟨%γec, HecAuth, HecFrag⟩
  let IAS : ApproxisGS rT .hasNoLC GF :=
    { appGS := IA, specGS := ISpec, ecGS := { toECPreGS := IECPre, γec := γec }, invGS := Hinv }
  ihave Hwp := Hwp IAS $$ HspecFrag HecFrag
  iapply wp_adequacy_step_fupdN $$ [$]

theorem wp_adequacy (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal) (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    Δ.Codensity 1 ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  limExecV_codensity fun n => wp_adequacy_exec_n e e' σ σ' n φ ε Hwp

theorem wp_adequacy_error_lim (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF) (ε' : ENNReal), ε < ε' →
      ⊢@{IProp GF} ⤇ e' -∗ ec ε' -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    Δ.Codensity 1 ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  Codensity.of_forall_lt fun ε' hε' => wp_adequacy e e' σ σ' ε' φ fun Hinst => Hwp Hinst ε' hε'

/-- Programs whose results agree up to error credits `ε` have output divergence at most `ε`
(via the fundamental property, Approxis Thm. 8.2). -/
theorem wp_adequacy_div [Δ.IsReflexive] (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝))) :
    Δ 1 (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) ≤ ε :=
  ((wp_adequacy e e' σ σ' ε (· = ·) Hwp).mono_rel adequacyRel_eq_subset).le_of_diag

/-- `wp_adequacy_div` with error credits strictly above `ε`. -/
theorem wp_adequacy_div_error_lim [Δ.IsReflexive] (e e' : Exp rT) (σ σ' : State rT)
    (ε : ENNReal)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF) (ε' : ENNReal), ε < ε' →
      ⊢@{IProp GF} ⤇ e' -∗ ec ε' -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝))) :
    Δ 1 (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) ≤ ε :=
  ((wp_adequacy_error_lim e e' σ σ' ε (· = ·) Hwp).mono_rel adequacyRel_eq_subset).le_of_diag

/-- Adequacy bounds the mass of the left program by that of the right plus the error credits
(the `tv` instance of `wp_adequacy`). -/
theorem wp_adequacy_mass (e e' : Exp rT) (σ σ' : State rT) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal) (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗ wp TVDiv.tv.{0} ⊤ e
        (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    limExecV ⟨e, σ⟩ Set.univ ≤ limExecV ⟨e', σ'⟩ Set.univ + ε := by
  simpa using (wp_adequacy e e' σ σ' ε φ Hwp).addCoupl.mass_leq

end ProbLang
