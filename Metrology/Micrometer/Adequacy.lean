module

public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.ProbLang.Erasure
public import Metrology.Iris.StepFupd

/-! Adequacy of the graded weakest precondition against the limit execution. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS ProbLang.Cfg
open GradedLifting
open scoped AppGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
variable {B : Type}

/-- `φ` on expressions that are values. -/
def adequacyRel (φ : Val rT → Val rT → Prop) (e e' : Exp rT) : Prop :=
  ∃ v v', e.toVal? = some v ∧ e'.toVal? = some v' ∧ φ v v'

omit [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] in
theorem adequacyRel_eq_subset (e e' : Exp rT) : adequacyRel (· = ·) e e' → e = e' := by
  rintro ⟨v, v', hv, hv', rfl⟩
  exact (Exp.ofVal_of_toVal_some hv).symm.trans (Exp.ofVal_of_toVal_some hv')

/-- The lifting at budget `b` of the finite executions of `ρ` against the limit execution of
`ρ'`. -/
@[reducible] def execCoupl [Zero B] [_root_.Top B] (L : GradedLifting.{0} B)
    (φ : Val rT → Val rT → Prop) (b : B) (n : Nat) (ρ ρ' : Cfg rT) : Prop :=
  L.Rel b (adequacyRel φ) (asExpr (execN n ρ)) (limExecV ρ')

/-! ### Runs that terminate within the fuel -/

section Termination

variable [Zero B] [Preorder B] [_root_.Top B] {L : GradedLifting.{0} B} [L.HasBind]
  [L.IsSupportLocal]

/-- `lift_erasure_erasable` for a run of mass `1`: continuations are needed only at states from
which the run still has mass `1` (Rocq `spec_coupl_adequacy_term`). -/
theorem execCoupl_erasable_of_term {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁ μ₁' : MeasureTheory.Measure (State rT)} {φ : Val rT → Val rT → Prop} {b : B}
    {R : State rT → Cfg rT → B} {k m : Nat} (hterm : execN m ⟨e₁, σ₁⟩ Set.univ = 1)
    (hCoupl : L b R μ₁ (μ₁'.bind fun σ => pexecN k ⟨e₁', σ⟩)) (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', execN m ⟨e₁, σ₂⟩ Set.univ = 1 → R σ₂ ρ' < (⊤ : B) →
      execCoupl L φ (R σ₂ ρ') m ⟨e₁, σ₂⟩ ρ') :
    execCoupl L φ b m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩ := by
  classical
  have hek : Measurable fun σ : State rT => execN m (⟨e₁, σ⟩ : Cfg rT) :=
    (execN_measurable m).comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  have hA : MeasurableSet {σ : State rT | execN m ⟨e₁, σ⟩ Set.univ = 1} :=
    (MeasureTheory.Measure.measurable_coe .univ).comp hek (measurableSet_singleton 1)
  have := hErase₁.isProbabilityMeasure
  have hmass : μ₁.bind (fun σ => execN m ⟨e₁, σ⟩) Set.univ = 1 := by
    have h := congrArg (· Set.univ) (hErase₁ e₁ m)
    simp only [asExpr, MeasureTheory.Measure.map_apply Cfg.measurable_expr .univ,
      Set.preimage_univ] at h
    rw [h, hterm]
  have hAc := MeasureTheory.ae_iff.1 (MeasureTheory.ae_measure_univ_eq_one_of_bind hek hmass)
  refine lift_erasure_erasable (IsSupportLocal.restrict hA hAc hCoupl) hErase₁ hErase₁'
    fun σ₂ ρ' hR => ?_
  by_cases hσ : σ₂ ∈ {σ : State rT | execN m ⟨e₁, σ⟩ Set.univ = 1}
  · simp only [Set.piecewise_eq_of_mem _ _ _ hσ] at hR ⊢
    exact hCont σ₂ ρ' hσ hR
  · simp [Set.piecewise_eq_of_notMem _ _ _ hσ] at hR

/-- `lift_erasure_erasable_exp_lhs_kanto` for a run of mass `1`: continuations are needed only
at configurations whose run has mass `1` (Rocq `prog_coupl_adequacy_term`). -/
theorem execCoupl_prog_of_term {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁' : MeasureTheory.Measure (State rT)} {φ : Val rT → Val rT → Prop} {b : B}
    {R : Cfg rT → Cfg rT → B} {k m : Nat} (Hnone : e₁.toVal? = none)
    (hterm : execN (m + 1) ⟨e₁, σ₁⟩ Set.univ = 1) (hErase₁' : ErasableExpr μ₁' σ₁')
    (hExp : L b R (primStep ⟨e₁, σ₁⟩) (μ₁'.bind fun σ => pexecN k ⟨e₁', σ⟩))
    (hCont : ∀ ρ ρ', execN m ρ Set.univ = 1 → R ρ ρ' < (⊤ : B) →
      execCoupl L φ (R ρ ρ') m ρ ρ') :
    execCoupl L φ b (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩ := by
  classical
  have hA : MeasurableSet {ρ : Cfg rT | execN m ρ Set.univ = 1} :=
    (MeasureTheory.Measure.measurable_coe .univ).comp (execN_measurable m)
      (measurableSet_singleton 1)
  simp only [execCoupl, execN_succ_not_isValue (ρ := ⟨e₁, σ₁⟩) (Exp.toVal?_eq_none.mp Hnone) m]
    at hterm ⊢
  have hAc := MeasureTheory.ae_iff.1
    (MeasureTheory.ae_measure_univ_eq_one_of_bind (execN_measurable m) hterm)
  refine lift_erasure_erasable_exp_lhs_kanto hErase₁' (IsSupportLocal.restrict hA hAc hExp)
    fun ρ ρ' hR => ?_
  by_cases hρ : ρ ∈ {ρ : Cfg rT | execN m ρ Set.univ = 1}
  · simp only [Set.piecewise_eq_of_mem _ _ _ hρ] at hR ⊢
    exact hCont ρ ρ' hρ hR
  · simp [Set.piecewise_eq_of_notMem _ _ _ hρ] at hR

end Termination

/-- A pure fact holds under an update followed by `n` step-updates at the empty mask. -/
theorem fupd_step_fupdN_pure {PROP : Type _} [BI PROP] [BIFUpdate PROP] {p : Prop} (n : Nat)
    (h : p) : ⊢@{PROP} |={∅}=> |={∅}[∅]▷=>^[n] ⌜p⌝ :=
  calc (emp : PROP) ⊢ ⌜p⌝ := pure_intro h
    _ ⊢ ▷^[n] ⌜p⌝ := laterN_intro n
    _ ⊢ |={∅}[∅]▷=>^[n] ⌜p⌝ := step_fupdN_intro Std.LawfulSet.subset_refl
    _ ⊢ |={∅}=> |={∅}[∅]▷=>^[n] ⌜p⌝ := fupd_intro

section Adequacy

variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B] [Nontrivial B]
  {L : GradedLifting.{0} B} [L.IsLawful] [L.HasBind]
variable {GF : BundledGFunctors} [MicrometerGS rT .hasNoLC GF] [BudgetGS B GF]

omit [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsLawful] [BudgetGS B GF] in
theorem wp_adequacy_spec_coupl (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
    (σ₁' : State rT) (Z : State rT → Cfg rT → B → IProp GF)
    (φ : Val rT → Val rT → Prop) (b : B) : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b Z ⊢
    (∀ σ₂ e₂' σ₂' b', Z σ₂ ⟨e₂', σ₂'⟩ b' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  set Ψ : State rT → Cfg rT → B → IProp GF := fun σ₀ ρ₀ b₀ => iprop(
    (∀ σ₂ e₂' σ₂' b', Z σ₂ ⟨e₂', σ₂'⟩ b' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b₀ m ⟨e₁, σ₀⟩ ρ₀⌝)
  iintro Hspec HZ
  iapply specCoupl_ind (Ψ := Ψ) $$ [] %σ₁ %e₁' %σ₁' %b Hspec HZ
  iintro !> %σ₀ %⟨e₀', σ₀'⟩ %b₀ H
  simp only [Ψ]
  iintro HZ
  icases H with ⟨%hVac | HZApp | HCpl⟩
  · iapply fupd_step_fupdN_pure n ?_
    exact hVac _ _ _
  · iapply HZ $$ HZApp
  · icases HCpl with ⟨%k, %μ₁, %μ₁', %R, %hAC, %hErase, %hErase', HCont⟩
    iapply BIFUpdate.mono
    · refine step_fupdN_mono (P := iprop(∀ σ₂ e₂' σ₂', ⌜R σ₂ ⟨e₂', σ₂'⟩ < (⊤ : B) →
        execCoupl L φ (R σ₂ ⟨e₂', σ₂'⟩) m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝)) ?_
      iintro %hpure !%
      exact lift_erasure_erasable hAC hErase hErase' fun σ₂ ⟨e₂', σ₂'⟩ => hpure σ₂ e₂' σ₂'
    iapply fupd_step_fupdN_plain_forall_3
    iintro %σ₂ %e₂' %σ₂'
    by_cases hR : R σ₂ ⟨e₂', σ₂'⟩ < (⊤ : B)
    · simp only [hR, true_implies]
      imod HCont $$ %σ₂ %e₂' %σ₂' %hR with ⟨HΨ, -⟩
      iapply HΨ $$ HZ
    · iapply fupd_step_fupdN_pure n hR.elim

omit [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsLawful] [BudgetGS B GF] in
theorem wp_adequacy_prog_coupl (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
    (σ₁' : State rT) (Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF)
    (φ : Val rT → Val rT → Prop) (b : B) (Hnone : e₁.toVal? = none) : iprop%
    progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢
    (∀ e₂ σ₂ e₂' σ₂' b', Z e₂ σ₂ e₂' σ₂' b' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  simp only [execCoupl, execN_succ_not_isValue (ρ := ⟨e₁, σ₁⟩) (Exp.toVal?_eq_none.mp Hnone) m]
  iintro HCpl Hcoupl
  icases HCpl with ⟨%k, %μ₁', %R, %_, %hExp, %hErase', Hcnt⟩
  iapply BIFUpdate.mono
  · refine step_fupdN_mono (P := iprop(∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B) →
      execCoupl L φ (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝)) ?_
    iintro %hpure !%
    exact lift_erasure_erasable_exp_lhs_kanto hErase' hExp
      fun ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ => hpure e₂ σ₂ e₂' σ₂'
  iapply fupd_step_fupdN_plain_forall_4
  iintro %e₂ %σ₂ %e₂' %σ₂'
  by_cases hR : R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)
  · simp only [hR, true_implies]
    imod Hcnt $$ %e₂ %σ₂ %e₂' %σ₂' %hR with Hcnt
    iapply Hcoupl $$ Hcnt
  · iapply fupd_step_fupdN_pure n hR.elim

omit [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsLawful] [BudgetGS B GF] in
theorem wp_adequacy_spec_coupl_zero (m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
    (σ₁' : State rT) (Z : State rT → Cfg rT → B → IProp GF)
    (φ : Val rT → Val rT → Prop) (b : B) : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b Z ⊢
    (∀ σ₂ e₂' σ₂' b', Z σ₂ ⟨e₂', σ₂'⟩ b' -∗
      |={∅}=> ⌜execCoupl L φ b' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> ⌜execCoupl L φ b m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ :=
  wp_adequacy_spec_coupl 0 m e₁ σ₁ e₁' σ₁' Z φ b

omit [AddCommMonoid B] [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsLawful] [L.HasBind] in
variable (L) in
theorem wpPre_value_Z_eq {v : Val rT} {Φ : Val rT → IProp GF} (E : CoPset) :
    (fun (σ₂ : State rT) (ρ' : Cfg rT) (b₂ : B) =>
      iprop(|={∅, E}=> stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ budgetInterp b₂ ∗ Φ v))
    = (fun (σ₂ : State rT) (ρ' : Cfg rT) (b₂ : B) =>
      match (Exp.ofVal v).toVal? with
      | some v => iprop(|={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ budgetInterp b₂ ∗ Φ v)
      | none => iprop(progCoupl L (Exp.ofVal v) σ₂ ρ'.expr ρ'.state b₂
          (fun e₃ σ₃ e₃' σ₃' b₃ =>
            iprop(▷ specCoupl L ∅ σ₃ e₃' σ₃' b₃ (fun σ₄ ρ'' b₄ =>
              iprop(|={∅, E}=>
                stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ budgetInterp b₄ ∗
                  wp L E e₃ Φ)))))) := by
  funext σ₂ ρ' b₂
  rw [Exp.toVal?_ofVal]

set_option linter.auxLemma false in
omit [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] in
/-- The `match` auxiliary of `wpPre_value_Z_eq` is the one of `wpPre`, so `wp_unfold_mp` applies
after rewriting with `wpPre_value_Z_eq`. -/
theorem wpPre_match_eq (motive : Option (Val rT) → Sort u)
    (x : Option (Val rT)) (some_f : (v : Val rT) → motive (some v))
    (none_f : Unit → motive none) :
    ProbLang.wpPre_value_Z_eq.match_1 motive x some_f none_f =
    ProbLang.MicrometerWpGS.wpPre.match_1 motive x some_f none_f := by
  cases x <;> rfl

omit [AddCommMonoid B] [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsLawful] [L.HasBind] in
theorem wp_value_specCoupl_unfold {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (E : CoPset) (He : e.toVal? = some v) :
    wp L E e Φ ⊢
      ∀ σ₁ e₁' σ₁' b₁,
        stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
          budgetInterp b₁ -∗
          |={E, ∅}=> specCoupl L ∅ σ₁ e₁' σ₁' b₁ (fun σ₂ ρ' b₂ =>
            iprop(|={∅, E}=>
              stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗ budgetInterp b₂ ∗ Φ v)) := by
  obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  rw [wpPre_value_Z_eq L E]
  simp only [wpPre_match_eq]
  iintro Hwp %σ₁ %e₁' %σ₁' %b₁ Hinterp
  iapply wp_unfold_mp $$ Hwp %σ₁ %e₁' %σ₁' %b₁ Hinterp

/-- At a value, the program and spec values are related at any leftover budget; fuel `0` never
reaches a value, so the run has at least one step. -/
theorem wp_adequacy_val_fupd (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) (v : Val rT) (b : B) (He : e.toVal? = some v) :
    appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ budgetInterp b ∗
      wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)) ⊢@{IProp GF}
    |={⊤, ∅}=> ⌜execCoupl L φ b (n + 1) ⟨e, σ⟩ ⟨e', σ'⟩⌝ := by
  obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  iintro ⟨Hσ, Hs, Hb, Hwp⟩
  imod wp_value_specCoupl_unfold ⊤ He $$ Hwp %σ %e' %σ' %b [$] with HspecC
  iapply wp_adequacy_spec_coupl_zero $$ HspecC
  iintro %σ₂ %e₂' %σ₂' %b₂ HZ
  imod HZ with ⟨-, Hs', -, %v', Hv', %hφ⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs' Hv'
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with -
  iintro !%
  unfold execCoupl limExecV asExpr
  rw [execN_succ_isValue (ρ := ⟨Exp.ofVal v, σ₂⟩) v.isValue n,
      limExec_of_isVal (e := Exp.ofVal v') (σ := σ₂') v'.2]
  simp only [MeasureTheory.Measure.map_dirac' Cfg.measurable_expr]
  exact rel_dirac ⟨v, v', Exp.toVal?_ofVal v, Exp.toVal?_ofVal v', hφ⟩ b₂

/-- The `n`-fuel execution of the left program is coupled with the limit execution of the right
one, across `n` later steps. -/
theorem wp_adequacy_step_fupdN [L.IsZeroLeft] (b : B) (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) :
    appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ budgetInterp b ∗
      wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)) ⊢@{IProp GF}
    |={⊤, ∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩⌝ := by
  induction n generalizing b e e' σ σ' with
  | zero =>
    iintro -
    imod BIFUpdate.subset Std.LawfulSet.empty_subset with -
    iapply fupd_step_fupdN_pure 0 ?_
    simp only [execCoupl, asExpr, execN_zero, MeasureTheory.Measure.map_zero]
    exact IsZeroLeft.zero_left _ _ _
  | succ n ih =>
    iintro ⟨Hσ, Hs, Hb, Hwp⟩
    by_cases He : e.isValue
    · obtain ⟨v, Hv⟩ := Exp.toVal?_eq_some_of_isValue He
      imod wp_adequacy_val_fupd e e' σ σ' n φ v b Hv $$ [$] with %hpure
      iapply fupd_step_fupdN_pure (n + 1) hpure
    · have hnone : e.toVal? = none := Exp.toVal?_eq_none.mpr He
      imod wp_unfold_mp $$ Hwp %σ %e' %σ' %b [$] with Hwp
      iapply wp_adequacy_spec_coupl $$ Hwp
      rw [hnone]
      iintro %σ₂ %e₂' %σ₂' %b₂ Hprog
      iapply wp_adequacy_prog_coupl (Hnone := hnone) $$ Hprog
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ Hspec
      simp only [Nat.repeat]
      iintro !> !> !>
      iapply wp_adequacy_spec_coupl $$ Hspec
      iintro %σ₄ %e₄' %σ₄' %b₄ HZ
      imod HZ
      iapply ih b₄ e₃ e₄' σ₄ σ₄' $$ HZ

/-! #### Runs of mass `1` within the fuel

Continuations are needed only where the run still has mass `1`, so neither `IsZeroLeft` nor a
limit is needed (Rocq `wp_adequacy_step_fupdN_term`). -/

omit [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsLawful] [BudgetGS B GF] in
theorem wp_adequacy_spec_coupl_term [L.IsSupportLocal] (n m : Nat) (e₁ : Exp rT)
    (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (Z : State rT → Cfg rT → B → IProp GF)
    (φ : Val rT → Val rT → Prop) (b : B) (hterm : execN m ⟨e₁, σ₁⟩ Set.univ = 1) : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b Z ⊢
    (∀ σ₂ e₂' σ₂' b', ⌜execN m ⟨e₁, σ₂⟩ Set.univ = 1⌝ -∗ Z σ₂ ⟨e₂', σ₂'⟩ b' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  set Ψ : State rT → Cfg rT → B → IProp GF := fun σ₀ ρ₀ b₀ => iprop(
    ⌜execN m ⟨e₁, σ₀⟩ Set.univ = 1⌝ -∗
    (∀ σ₂ e₂' σ₂' b', ⌜execN m ⟨e₁, σ₂⟩ Set.univ = 1⌝ -∗ Z σ₂ ⟨e₂', σ₂'⟩ b' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b₀ m ⟨e₁, σ₀⟩ ρ₀⌝)
  iintro Hspec HZ
  iapply specCoupl_ind (Ψ := Ψ) $$ [] %σ₁ %e₁' %σ₁' %b Hspec %hterm HZ
  iintro !> %σ₀ %⟨e₀', σ₀'⟩ %b₀ H
  simp only [Ψ]
  iintro %hterm₀ HZ
  icases H with ⟨%hVac | HZApp | HCpl⟩
  · iapply fupd_step_fupdN_pure n ?_
    exact hVac _ _ _
  · iapply HZ $$ %σ₀ %e₀' %σ₀' %b₀ %hterm₀ HZApp
  · icases HCpl with ⟨%k, %μ₁, %μ₁', %R, %hAC, %hErase, %hErase', HCont⟩
    iapply BIFUpdate.mono
    · refine step_fupdN_mono (P := iprop(∀ σ₂ e₂' σ₂', ⌜execN m ⟨e₁, σ₂⟩ Set.univ = 1 →
        R σ₂ ⟨e₂', σ₂'⟩ < (⊤ : B) →
        execCoupl L φ (R σ₂ ⟨e₂', σ₂'⟩) m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝)) ?_
      iintro %hpure !%
      exact execCoupl_erasable_of_term hterm₀ hAC hErase hErase'
        fun σ₂ ⟨e₂', σ₂'⟩ => hpure σ₂ e₂' σ₂'
    iapply fupd_step_fupdN_plain_forall_3
    iintro %σ₂ %e₂' %σ₂'
    by_cases h : execN m ⟨e₁, σ₂⟩ Set.univ = 1 ∧ R σ₂ ⟨e₂', σ₂'⟩ < (⊤ : B)
    · simp only [h.1, h.2, true_implies]
      imod HCont $$ %σ₂ %e₂' %σ₂' %h.2 with ⟨HΨ, -⟩
      iapply HΨ $$ %h.1 HZ
    · iapply fupd_step_fupdN_pure n fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h

omit [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsLawful] [BudgetGS B GF] in
theorem wp_adequacy_prog_coupl_term [L.IsSupportLocal] (n m : Nat) (e₁ : Exp rT)
    (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT)
    (Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF) (φ : Val rT → Val rT → Prop)
    (b : B) (Hnone : e₁.toVal? = none) (hterm : execN (m + 1) ⟨e₁, σ₁⟩ Set.univ = 1) : iprop%
    progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢
    (∀ e₂ σ₂ e₂' σ₂' b', ⌜execN m ⟨e₂, σ₂⟩ Set.univ = 1⌝ -∗ Z e₂ σ₂ e₂' σ₂' b' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  iintro HCpl Hcoupl
  icases HCpl with ⟨%k, %μ₁', %R, %_, %hExp, %hErase', Hcnt⟩
  iapply BIFUpdate.mono
  · refine step_fupdN_mono (P := iprop(∀ e₂ σ₂ e₂' σ₂', ⌜execN m ⟨e₂, σ₂⟩ Set.univ = 1 →
      R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B) →
      execCoupl L φ (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝)) ?_
    iintro %hpure !%
    exact execCoupl_prog_of_term Hnone hterm hErase' hExp
      fun ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ => hpure e₂ σ₂ e₂' σ₂'
  iapply fupd_step_fupdN_plain_forall_4
  iintro %e₂ %σ₂ %e₂' %σ₂'
  by_cases h : execN m ⟨e₂, σ₂⟩ Set.univ = 1 ∧ R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)
  · simp only [h.1, h.2, true_implies]
    imod Hcnt $$ %e₂ %σ₂ %e₂' %σ₂' %h.2 with Hcnt
    iapply Hcoupl $$ %e₂ %σ₂ %e₂' %σ₂' %_ %h.1 Hcnt
  · iapply fupd_step_fupdN_pure n fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h

theorem wp_adequacy_step_fupdN_term [L.IsSupportLocal] (b : B) (e e' : Exp rT)
    (σ σ' : State rT) (n : Nat) (φ : Val rT → Val rT → Prop)
    (hterm : execN n ⟨e, σ⟩ Set.univ = 1) :
    appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ budgetInterp b ∗
      wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)) ⊢@{IProp GF}
    |={⊤, ∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩⌝ := by
  induction n generalizing b e e' σ σ' with
  | zero => simp at hterm
  | succ n ih =>
    iintro ⟨Hσ, Hs, Hb, Hwp⟩
    by_cases He : e.isValue
    · obtain ⟨v, Hv⟩ := Exp.toVal?_eq_some_of_isValue He
      imod wp_adequacy_val_fupd e e' σ σ' n φ v b Hv $$ [$] with %hpure
      iapply fupd_step_fupdN_pure (n + 1) hpure
    · have hnone : e.toVal? = none := Exp.toVal?_eq_none.mpr He
      imod wp_unfold_mp $$ Hwp %σ %e' %σ' %b [$] with Hwp
      iapply wp_adequacy_spec_coupl_term (hterm := hterm) $$ Hwp
      rw [hnone]
      iintro %σ₂ %e₂' %σ₂' %b₂ %hterm₂ Hprog
      iapply wp_adequacy_prog_coupl_term (Hnone := hnone) (hterm := hterm₂) $$ Hprog
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ %hterm₃ Hspec
      simp only [Nat.repeat]
      iintro !> !> !>
      iapply wp_adequacy_spec_coupl_term (hterm := hterm₃) $$ Hspec
      iintro %σ₄ %e₄' %σ₄' %b₄ %hterm₄ HZ
      imod HZ
      iapply ih b₄ e₃ e₄' σ₄ σ₄' hterm₄ $$ HZ

end Adequacy

/-! ### Adequacy from a budget credit

Starting from `↯b b`, the executions are related at budget `b`; the budget left at the end is
dropped. -/

section Budget

variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B] [Nontrivial B]
  {L : GradedLifting.{0} B} [L.IsLawful] [L.HasBind] [L.IsZeroLeft] [L.IsLeftContinuous]
variable {GF : BundledGFunctors}
variable [AppPreGS rT GF] [SpecPreGS rT GF] [IBCPre : BudgetCreditPreGS B GF] [InvGpreS GF]

omit [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsLawful] [L.HasBind] [L.IsZeroLeft]
  [L.IsLeftContinuous] in
/-- Allocates the ghost state and turns an `n`-step adequacy entailment into `execCoupl`. -/
theorem execCoupl_of_step_fupdN (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) (b : B)
    (Hstep : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ budgetInterp b ∗
        wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)) ⊢@{IProp GF}
      |={⊤, ∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩⌝)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩ := by
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) n 0 fun Hinv => ?_
  iintro -
  imod app_ra_init σ with ⟨%IA, HappAuth⟩
  imod spec_ra_init e' σ' with ⟨%ISpec, HspecAuth, HspecFrag⟩
  imod bc_alloc b with ⟨%γbc, HbcAuth, HbcFrag⟩
  let IAS : MicrometerGS rT .hasNoLC GF := { appGS := IA, specGS := ISpec, invGS := Hinv }
  let IBC : BudgetCreditGS B GF := { toBudgetCreditPreGS := IBCPre, γbc := γbc }
  ihave Hwp := Hwp IAS IBC $$ HspecFrag HbcFrag
  iapply Hstep IAS IBC
  iframe

omit [L.IsLeftContinuous] in
/-- `wp_adequacy` for the execution with `n` fuel. -/
theorem wp_adequacy_exec_n (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) (b : B)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩ :=
  execCoupl_of_step_fupdN e e' σ σ' n φ b (fun _ _ => wp_adequacy_step_fupdN b e e' σ σ' n φ) Hwp

/-- A weakest precondition from a budget credit `b` couples the limit executions at budget `b`. -/
theorem wp_adequacy (e e' : Exp rT) (σ σ' : State rT) (b : B) (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    L.Rel b (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  limExecV_lift fun n => wp_adequacy_exec_n e e' σ σ' n φ b Hwp

/-- `wp_adequacy` with a budget credit strictly above `b`. -/
theorem wp_adequacy_error_lim [L.IsBudgetClosed] (e e' : Exp rT) (σ σ' : State rT) (b : B)
    (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF) (b' : B), b < b' →
      ⊢@{IProp GF} ⤇ e' -∗ ↯b b' -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    L.Rel b (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  IsBudgetClosed.of_forall_gt fun b' hb' =>
    wp_adequacy e e' σ σ' b' φ fun IGS IBC => Hwp IGS IBC b' hb'

/-- Programs whose results agree from a budget credit `b` have output divergence within `b`
(the fundamental property, Thm. 8.2; clutch-dp `wp_diffpriv`). -/
theorem wp_adequacy_div {D : GradedDivergence.{0} B} [L.IsSound D] (e e' : Exp rT)
    (σ σ' : State rT) (b : B)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝))) :
    D b (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  IsSound.sound ((wp_adequacy e e' σ σ' b (· = ·) Hwp).mono le_rfl adequacyRel_eq_subset)

/-- `wp_adequacy_div` with a budget credit strictly above `b`. -/
theorem wp_adequacy_div_error_lim {D : GradedDivergence.{0} B} [L.IsSound D] [L.IsBudgetClosed]
    (e e' : Exp rT) (σ σ' : State rT) (b : B)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF) (b' : B), b < b' →
      ⊢@{IProp GF} ⤇ e' -∗ ↯b b' -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝))) :
    D b (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  IsSound.sound
    ((wp_adequacy_error_lim e e' σ σ' b (· = ·) Hwp).mono le_rfl adequacyRel_eq_subset)

/-- Adequacy bounds the mass of the left program by that of the right plus the slack `ε`. -/
theorem wp_adequacy_mass {s : ENNReal →+o B} [L.IsMassDetecting s] (e e' : Exp rT)
    (σ σ' : State rT) (φ : Val rT → Val rT → Prop) (ε : ENNReal)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯b (s ε) -∗
        wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    limExecV ⟨e, σ⟩ Set.univ ≤ limExecV ⟨e', σ'⟩ Set.univ + ε :=
  IsMassDetecting.measure_le_add .univ .univ (wp_adequacy e e' σ σ' (s ε) φ Hwp)
    fun _ _ _ _ ↦ trivial

end Budget

/-! ### Adequacy for runs of mass `1` within the fuel -/

section BudgetTerm

variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B] [Nontrivial B]
  {L : GradedLifting.{0} B} [L.IsLawful] [L.HasBind] [L.IsSupportLocal]
variable {GF : BundledGFunctors}
variable [AppPreGS rT GF] [SpecPreGS rT GF] [IBCPre : BudgetCreditPreGS B GF] [InvGpreS GF]

theorem wp_adequacy_exec_n_term (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) (b : B) (hterm : execN n ⟨e, σ⟩ Set.univ = 1)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩ :=
  execCoupl_of_step_fupdN e e' σ σ' n φ b
    (fun _ _ => wp_adequacy_step_fupdN_term b e e' σ σ' n φ hterm) Hwp

/-- `wp_adequacy` for a program whose run has mass `1` within `n` steps: the limit is that run,
so neither `IsZeroLeft` nor `IsLeftContinuous` is needed (Rocq `wp_adequacy_term`). -/
theorem wp_adequacy_term (e e' : Exp rT) (σ σ' : State rT) (n : Nat) (b : B)
    (φ : Val rT → Val rT → Prop) (hterm : execN n ⟨e, σ⟩ Set.univ = 1)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢@{IProp GF} ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    L.Rel b (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) := by
  rw [limExecV, limExec_term hterm]
  exact wp_adequacy_exec_n_term e e' σ σ' n φ b hterm Hwp

end BudgetTerm

end ProbLang
