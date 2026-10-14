module

public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.ProbLang.Erasure
public import Metrology.Iris.StepFupd
public import Metrology.Couplings.CodensityMassDetecting

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS ProbLang.Cfg
open GradedDivergence
open scoped AppGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]
variable {ι : Type}

def adequacyRel (φ : Val rT → Val rT → Prop) : Set (Exp rT × Exp rT) :=
  fun p => ∃ v v', p.1.toVal? = some v ∧ p.2.toVal? = some v' ∧ φ v v'

omit [LawfulProbLangℝ rT] in
theorem adequacyRel_eq_subset :
    adequacyRel (rT := rT) (· = ·) ⊆ {p : Exp rT × Exp rT | p.1 = p.2} := by
  rintro ⟨e₁, e₂⟩ ⟨v, v', hv, hv', rfl⟩
  exact (Exp.ofVal_of_toVal_some hv).symm.trans (Exp.ofVal_of_toVal_some hv')

/-- The codensity lifting at grade `α` of the finite executions of `ρ` against the limit execution
of `ρ'`. -/
@[reducible] def execCoupl [Monoid ι] (Δ : GradedDivergence.{0} ι) (φ : Val rT → Val rT → Prop)
    (α : ι) (ε : ENNReal) (n : Nat) (ρ ρ' : Cfg rT) : Prop :=
  Δ.Codensity α ε (adequacyRel φ) (asExpr (execN n ρ)) (limExecV ρ')

section Adequacy

variable [Monoid ι] {Δ : GradedDivergence.{0} ι} [Δ.IsMassBounded] [Δ.IsZeroLeft]
variable {GF : BundledGFunctors} [IA : MicrometerGS rT .hasNoLC GF] [GradeGS ι GF]

omit [Δ.IsZeroLeft] [GradeGS ι GF] in
theorem wp_adequacy_spec_coupl (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
    (σ₁' : State rT) (Z : State rT → Cfg rT → ι → ENNReal → IProp GF)
    (φ : Val rT → Val rT → Prop) (α : ι) (ε : ENNReal) : iprop%
    specCoupl Δ ∅ σ₁ e₁' σ₁' α ε Z ⊢
    (∀ σ₂ e₂' σ₂' α' ε', Z σ₂ ⟨e₂', σ₂'⟩ α' ε' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ α' ε' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ α ε m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  set Ψ : State rT → Cfg rT → ι → ENNReal → IProp GF := fun σ₀ ρ₀ α₀ ε₀ => iprop(
    (∀ σ₂ e₂' σ₂' α' ε', Z σ₂ ⟨e₂', σ₂'⟩ α' ε' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ α' ε' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ α₀ ε₀ m ⟨e₁, σ₀⟩ ρ₀⌝)
  iintro Hspec HZ
  iapply specCoupl_ind (Ψ := Ψ) $$ [] %σ₁ %e₁' %σ₁' %α %ε Hspec HZ
  iintro !> %σ₀ %⟨e₀', σ₀'⟩ %α₀ %ε₀ H
  simp only [Ψ]
  iintro HZ
  icases H with ⟨%HVac | HZApp | HCpl⟩
  · imodintro
    iapply (laterN_intro n).trans (step_fupdN_intro Std.LawfulSet.empty_subset)
    ipureintro
    exact codensity_of_one_le HVac
  · iapply HZ $$ HZApp
  · icases HCpl with ⟨%k, %μ₁, %μ₁', %G, %X₂, %HAC, %Herase1, %Herase1', HCont⟩
    iapply BIFUpdate.mono
    · refine step_fupdN_mono (P := iprop(∀ σ₂ e₂' σ₂',
        ⌜execCoupl Δ φ (G σ₂ ⟨e₂', σ₂'⟩) (X₂ σ₂ ⟨e₂', σ₂'⟩) m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝ : IProp GF)) ?_
      iintro %Hpure !%
      exact Codensity_erasure_erasable_graded HAC Herase1 Herase1'
        fun σ₂ ⟨e₂', σ₂'⟩ => Hpure σ₂ e₂' σ₂'
    iapply fupd_step_fupdN_plain_forall_3
    iintro %σ₂ %e₂' %σ₂'
    imod HCont $$ %σ₂ %e₂' %σ₂' with ⟨HΨ, -⟩
    iapply HΨ $$ HZ

omit [Δ.IsMassBounded] [Δ.IsZeroLeft] [GradeGS ι GF] in
theorem wp_adequacy_prog_coupl (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
    (σ₁' : State rT) (Z : Exp rT → State rT → Exp rT → State rT → ι → ENNReal → IProp GF)
    (φ : Val rT → Val rT → Prop) (α : ι) (ε : ENNReal) (Hnone : e₁.toVal? = none) : iprop%
    progCoupl Δ e₁ σ₁ e₁' σ₁' α ε Z ⊢
    (∀ e₂ σ₂ e₂' σ₂' α' ε', Z e₂ σ₂ e₂' σ₂' α' ε' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ α' ε' m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ α ε (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  simp only [execCoupl, execN_succ_not_isValue (ρ := ⟨e₁, σ₁⟩) (Exp.toVal?_eq_none.mp Hnone) m]
  iintro HCpl Hcoupl
  icases HCpl with ⟨%k, %μ₁', %G, %X₂, %_, %Hexp, %Herase', Hcnt⟩
  iapply BIFUpdate.mono
  · refine step_fupdN_mono (P := iprop(∀ e₂ σ₂ e₂' σ₂',
      ⌜execCoupl Δ φ (G ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) m ⟨e₂, σ₂⟩
        ⟨e₂', σ₂'⟩⌝ : IProp GF)) ?_
    iintro %Hpure !%
    exact Codensity_erasure_erasable_exp_lhs_kanto Herase' Hexp
      fun ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ => Hpure e₂ σ₂ e₂' σ₂'
  iapply fupd_step_fupdN_plain_forall_4
  iintro %e₂ %σ₂ %e₂' %σ₂'
  imod Hcnt $$ %e₂ %σ₂ %e₂' %σ₂' with Hcnt
  iapply Hcoupl $$ Hcnt

omit [Δ.IsZeroLeft] [GradeGS ι GF] in
theorem wp_adequacy_spec_coupl_zero (m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
    (σ₁' : State rT) (Z : State rT → Cfg rT → ι → ENNReal → IProp GF)
    (φ : Val rT → Val rT → Prop) (α : ι) (ε : ENNReal) : iprop%
    specCoupl Δ ∅ σ₁ e₁' σ₁' α ε Z ⊢
    (∀ σ₂ e₂' σ₂' α' ε', Z σ₂ ⟨e₂', σ₂'⟩ α' ε' -∗
      |={∅}=> ⌜execCoupl Δ φ α' ε' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> ⌜execCoupl Δ φ α ε m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ :=
  wp_adequacy_spec_coupl 0 m e₁ σ₁ e₁' σ₁' Z φ α ε

omit [Δ.IsMassBounded] [Δ.IsZeroLeft] in
variable (Δ) in
theorem wpPre_value_Z_eq {v : Val rT} {Φ : Val rT → IProp GF} (E : CoPset) :
    (fun (σ₂ : State rT) (ρ' : Cfg rT) (α₂ : ι) (ε₂ : ENNReal) =>
      iprop(|={∅, E}=> stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ gradeInterp α₂ ∗
        errInterp (rT := rT) ε₂ ∗ Φ v))
    = (fun (σ₂ : State rT) (ρ' : Cfg rT) (α₂ : ι) (ε₂ : ENNReal) =>
      match (Exp.ofVal v).toVal? with
      | some v => iprop(|={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ gradeInterp α₂ ∗
            errInterp (rT := rT) ε₂ ∗ Φ v)
      | none => iprop(progCoupl Δ (Exp.ofVal v) σ₂ ρ'.expr ρ'.state α₂ ε₂
          (fun e₃ σ₃ e₃' σ₃' α₃ ε₃ =>
            iprop(▷ specCoupl Δ ∅ σ₃ e₃' σ₃' α₃ ε₃ (fun σ₄ ρ'' α₄ ε₄ =>
              iprop(|={∅, E}=>
                stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ gradeInterp α₄ ∗
                  errInterp (rT := rT) ε₄ ∗ wp Δ E e₃ Φ)))))) := by
  funext σ₂ ρ' α₂ ε₂
  rw [Exp.toVal?_ofVal]

set_option linter.auxLemma false in
omit [LawfulProbLangℝ rT] in
theorem wpPre_match_eq (motive : Option (Val rT) → Sort u)
    (x : Option (Val rT)) (some_f : (v : Val rT) → motive (some v))
    (none_f : Unit → motive none) :
    ProbLang.wpPre_value_Z_eq.match_1 motive x some_f none_f =
    ProbLang.MicrometerWpGS.wpPre.match_1 motive x some_f none_f := by
  cases x <;> rfl

omit [Δ.IsMassBounded] [Δ.IsZeroLeft] in
theorem wp_value_specCoupl_unfold {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (E : CoPset) (He : e.toVal? = some v) :
    wp Δ E e Φ ⊢@{IProp GF}
      ∀ σ₁ e₁' σ₁' α₁ ε₁,
        stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
          gradeInterp α₁ ∗ errInterp (rT := rT) ε₁ -∗
          |={E, ∅}=> specCoupl Δ ∅ σ₁ e₁' σ₁' α₁ ε₁ (fun σ₂ ρ' α₂ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ gradeInterp α₂ ∗
                errInterp (rT := rT) ε₂ ∗ Φ v)) := by
  obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  rw [wpPre_value_Z_eq Δ E]
  simp only [wpPre_match_eq]
  iintro Hwp %σ₁ %e₁' %σ₁' %α₁ %ε₁ Hinterp
  iapply wp_unfold_mp $$ Hwp %σ₁ %e₁' %σ₁' %α₁ %ε₁ Hinterp

/-- At a value, the remaining budget `α` must be droppable: `gradeInterp α` forces `α` to absorb
(clutch-dp's leftover privacy budget). -/
theorem wp_adequacy_val_fupd (Habs : ∀ α : ι, gradeInterp (GF := GF) α ⊢ ⌜Δ.Absorbs α⌝)
    (e e' : Exp rT) (σ σ' : State rT) (n : Nat) (φ : Val rT → Val rT → Prop) (v : Val rT)
    (α : ι) (ε : ENNReal) (He : e.toVal? = some v) :
    appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ gradeInterp α ∗ ecAuth ε ∗
      wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)) ⊢@{IProp GF}
    |={⊤, ∅}=> ⌜execCoupl Δ φ α ε n ⟨e, σ⟩ ⟨e', σ'⟩⌝ := by
  obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  iintro ⟨Hσ, Hs, Hα, Hε, Hwp⟩
  imod wp_value_specCoupl_unfold ⊤ He $$ Hwp %σ %e' %σ' %α %ε [$] with HspecC
  iapply wp_adequacy_spec_coupl_zero $$ HspecC
  iintro %σ₂ %e₂' %σ₂' %α₂ %ε' HZ
  imod HZ with ⟨-, Hs', Hα₂, -, %v', Hv', %Hφrel⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs' Hv'
  ihave %Hab := Habs α₂ $$ Hα₂
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
    exact (codensity_dirac_of_absorbs Hab (R := adequacyRel φ)
      ⟨v, v', Exp.toVal?_ofVal v, Exp.toVal?_ofVal v', Hφrel⟩).mono_bound zero_le

theorem wp_adequacy_step_fupdN (Habs : ∀ α : ι, gradeInterp (GF := GF) α ⊢ ⌜Δ.Absorbs α⌝)
    (α : ι) (ε : ENNReal) (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) :
    appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ gradeInterp α ∗ ecAuth ε ∗
      wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)) ⊢@{IProp GF}
    |={⊤, ∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl Δ φ α ε n ⟨e, σ⟩ ⟨e', σ'⟩⌝ := by
  induction n generalizing α ε e e' σ σ' with
  | zero =>
    iintro -
    imod BIFUpdate.subset (E2 := ∅) Std.LawfulSet.empty_subset with -
    imodintro
    simp only [Nat.repeat]
    ipureintro
    simp only [execCoupl, asExpr, execN_zero, MeasureTheory.Measure.map_zero]
    exact codensity_zero_left
  | succ n ih =>
    iintro ⟨Hσ, Hs, Hα, Hε, Hwp⟩
    by_cases He : e.isValue
    · obtain ⟨v, Hv⟩ := Exp.toVal?_eq_some_of_isValue He
      imod wp_adequacy_val_fupd Habs e e' σ σ' (n+1) φ v α ε Hv $$ [$] with %Hpure
      imodintro
      iapply (laterN_intro (n+1)).trans (step_fupdN_intro Std.LawfulSet.subset_refl)
      ipureintro
      exact Hpure
    · have hnone : e.toVal? = none := Exp.toVal?_eq_none.mpr He
      imod wp_unfold_mp $$ Hwp %σ %e' %σ' %α %ε [$] with Hwp
      iapply wp_adequacy_spec_coupl $$ Hwp
      rw [hnone]
      iintro %σ₂ %e₂' %σ₂' %α₂ %ε' Hprog
      iapply wp_adequacy_prog_coupl (Hnone := hnone) $$ Hprog
      iintro %e₃ %σ₃ %e₃' %σ₃' %α₃ %ε₃ Hspec
      simp only [Nat.repeat]
      iintro !> !> !>
      iapply wp_adequacy_spec_coupl $$ Hspec
      iintro %σ₄ %e₄' %σ₄' %α₄ %ε₄ HZ
      imod HZ
      iapply ih α₄ ε₄ e₃ e₄' σ₄ σ₄' $$ HZ

end Adequacy

/-! ### Adequacy without grade credits: the budget stays at the unit grade -/

section GradeOne

variable [Monoid ι] {Δ : GradedDivergence.{0} ι} [Δ.IsMassBounded] [Δ.IsZeroLeft]
  [Δ.IsLeftContinuous]
variable {GF : BundledGFunctors}
variable [AppPreGS rT GF] [SpecPreGS rT GF] [IECPre : ECPreGS GF] [InvGpreS GF]

omit [Δ.IsLeftContinuous] in
theorem wp_adequacy_exec_n (e e' : Exp rT) (σ σ' : State rT) (n : Nat) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal) (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    execCoupl Δ φ 1 ε n ⟨e, σ⟩ ⟨e', σ'⟩ := by
  by_cases hε1 : 1 ≤ ε
  · exact codensity_of_one_le hε1
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) n 0 fun Hinv => ?_
  iintro -
  imod app_ra_init σ with ⟨%IA, HappAuth⟩
  imod spec_ra_init e' σ' with ⟨%ISpec, HspecAuth, HspecFrag⟩
  imod ec_alloc ε (lt_of_not_ge hε1) with ⟨%γec, HecAuth, HecFrag⟩
  let IAS : MicrometerGS rT .hasNoLC GF :=
    { appGS := IA, specGS := ISpec, ecGS := { toECPreGS := IECPre, γec := γec }, invGS := Hinv }
  ihave Hwp := Hwp IAS $$ HspecFrag HecFrag
  have Habs (α : ι) : gradeInterp (GF := GF) α ⊢ ⌜Δ.Absorbs α⌝ :=
    pure_mono fun h => h ▸ absorbs_one
  iapply wp_adequacy_step_fupdN Habs 1 ε e e' σ σ' n φ
  iframe
  iapply (pure_intro rfl : ⊢@{IProp GF} gradeInterp (1 : ι))
  iempintro

theorem wp_adequacy (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal) (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    Δ.Codensity 1 ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  limExecV_codensity fun n => wp_adequacy_exec_n e e' σ σ' n φ ε Hwp

theorem wp_adequacy_error_lim (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (ε' : ENNReal), ε < ε' →
      ⊢@{IProp GF} ⤇ e' -∗ ec ε' -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    Δ.Codensity 1 ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  Codensity.of_forall_lt fun ε' hε' => wp_adequacy e e' σ σ' ε' φ fun Hinst => Hwp Hinst ε' hε'

/-- Programs whose results agree up to error credits `ε` have output divergence at most `ε`
(the fundamental property, Thm. 8.2). -/
theorem wp_adequacy_div [Δ.IsReflexive] (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝))) :
    Δ 1 (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) ≤ ε :=
  ((wp_adequacy e e' σ σ' ε (· = ·) Hwp).mono_rel adequacyRel_eq_subset).le_of_diag

/-- `wp_adequacy_div` with error credits strictly above `ε`. -/
theorem wp_adequacy_div_error_lim [Δ.IsReflexive] (e e' : Exp rT) (σ σ' : State rT)
    (ε : ENNReal)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (ε' : ENNReal), ε < ε' →
      ⊢@{IProp GF} ⤇ e' -∗ ec ε' -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝))) :
    Δ 1 (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) ≤ ε :=
  ((wp_adequacy_error_lim e e' σ σ' ε (· = ·) Hwp).mono_rel adequacyRel_eq_subset).le_of_diag

/-- Adequacy bounds the mass of the left program by that of the right plus the error credits. -/
theorem wp_adequacy_mass [Δ.IsReflexive] [Δ.IsMassDetectingAdd] (e e' : Exp rT) (σ σ' : State rT)
    (φ : Val rT → Val rT → Prop) (ε : ENNReal) (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗ wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    limExecV ⟨e, σ⟩ Set.univ ≤ limExecV ⟨e', σ'⟩ Set.univ + ε :=
  (wp_adequacy e e' σ σ' ε φ Hwp).measure_le_add .univ .univ fun _ _ _ _ ↦ trivial

end GradeOne

/-! ### Adequacy with grade credits (clutch-dp `wp_adequacy`)

Starting from `↯g α₀ ∗ ↯ ε`, the executions are related at grade `α₀` within `ε`. The budget left
at the end is dropped, which needs every grade to absorb: canonically ordered grades (`1 ≤ α`)
and a graded divergence. -/

section Graded

variable [CommMonoid ι] [Preorder ι] [CanonicallyOrderedMul ι]
variable {Δ : GradedDivergence.{0} ι} [Δ.IsGraded] [Δ.IsMassBounded] [Δ.IsZeroLeft]
  [Δ.IsLeftContinuous]
variable {GF : BundledGFunctors}
variable [AppPreGS rT GF] [SpecPreGS rT GF] [IECPre : ECPreGS GF] [IGCPre : GradeCreditPreGS ι GF]
  [InvGpreS GF]

omit [Δ.IsLeftContinuous] in
theorem wp_adequacy_exec_n_graded (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) (α₀ : ι) (ε : ENNReal)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : GradeCreditGS ι GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯g α₀ -∗ ec ε -∗
        wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    execCoupl Δ φ α₀ ε n ⟨e, σ⟩ ⟨e', σ'⟩ := by
  by_cases hε1 : 1 ≤ ε
  · exact codensity_of_one_le hε1
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) n 0 fun Hinv => ?_
  iintro -
  imod app_ra_init σ with ⟨%IA, HappAuth⟩
  imod spec_ra_init e' σ' with ⟨%ISpec, HspecAuth, HspecFrag⟩
  imod ec_alloc ε (lt_of_not_ge hε1) with ⟨%γec, HecAuth, HecFrag⟩
  imod gc_alloc α₀ with ⟨%γgc, HgcAuth, HgcFrag⟩
  let IAS : MicrometerGS rT .hasNoLC GF :=
    { appGS := IA, specGS := ISpec, ecGS := { toECPreGS := IECPre, γec := γec }, invGS := Hinv }
  let IGC : GradeCreditGS ι GF := { toGradeCreditPreGS := IGCPre, γgc := γgc }
  ihave Hwp := Hwp IAS IGC $$ HspecFrag HgcFrag HecFrag
  have Habs (α : ι) : gradeInterp (GF := GF) α ⊢ ⌜Δ.Absorbs α⌝ :=
    pure_intro (absorbs_of_canonical α)
  iapply wp_adequacy_step_fupdN Habs α₀ ε e e' σ σ' n φ
  iframe

theorem wp_adequacy_graded (e e' : Exp rT) (σ σ' : State rT) (α₀ : ι) (ε : ENNReal)
    (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : GradeCreditGS ι GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯g α₀ -∗ ec ε -∗
        wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    Δ.Codensity α₀ ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  limExecV_codensity fun n => wp_adequacy_exec_n_graded e e' σ σ' n φ α₀ ε Hwp

/-- Programs whose results agree from grade credits `α₀` and error credits `ε` have output
divergence at most `ε` at grade `α₀` (clutch-dp's `wp_diffpriv`). -/
theorem wp_adequacy_div_graded [Δ.IsReflexive] (e e' : Exp rT) (σ σ' : State rT) (α₀ : ι)
    (ε : ENNReal)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : GradeCreditGS ι GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯g α₀ -∗ ec ε -∗
        wp Δ ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝))) :
    Δ α₀ (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) ≤ ε :=
  ((wp_adequacy_graded e e' σ σ' α₀ ε (· = ·) Hwp).mono_rel adequacyRel_eq_subset).le_of_diag

end Graded

end ProbLang
