module

public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.ProbLang.Erasure
public import Metrology.Iris.StepFupd
import Metrology.Iris.LocalBI

/-! # Adequacy of the Micrometer logic

A `wp` proof from `↯b b` relates the two limit outputs at budget `b` (`wp_adequacy`) and bounds
their divergence (`wp_adequacy_div`), via `execCoupl` at every fuel `n`, one later per step. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS ProbLang.Cfg
open GradedLifting Set
open MeasureTheory (Measure)
open MeasureTheory.Measure (map_apply map_dirac' measurable_coe)
open Exp (ofVal ofVal_of_toVal_some toVal?_eq_none toVal?_eq_some_of_isValue toVal?_ofVal)
open BIFUpdate (subset mono)
open GradedLifting.IsSound (sound)
open LawfulSet (empty_subset)
open scoped AppGS

namespace ProbLang

variable {rT : Type}
variable {B : Type}

/-! ## Execution couplings -/

/-- Both expressions are values, and `φ` relates them. -/
def adequacyRel (φ : Val rT → Val rT → Prop) (e e' : Exp rT) : Prop :=
  ∃ v v', e.toVal? = some v ∧ e'.toVal? = some v' ∧ φ v v'

/-- Values related by equality are equal expressions. -/
theorem adequacyRel_eq_subset (e e' : Exp rT) : adequacyRel (· = ·) e e' → e = e' := by
  rintro ⟨v, v', hv, hv', rfl⟩
  exact (ofVal_of_toVal_some hv).symm.trans (ofVal_of_toVal_some hv')

variable [LawfulProbLangℝ rT]

/-- The lifting at budget `b` of the `n`-fuel run of `ρ` against the limit run of `ρ'`, relating
values by `φ`. -/
@[reducible] def execCoupl [Zero B] [_root_.Top B] (L : GradedLifting.{0} B)
    (φ : Val rT → Val rT → Prop) (b : B) (n : Nat) (ρ ρ' : Cfg rT) : Prop :=
  L.Rel b (adequacyRel φ) (asExpr (execN n ρ)) (limExecV ρ')

/-! ## Runs of mass `1`

Neither `IsZeroLeft` nor a limit is needed for the `_term` results (Rocq
`wp_adequacy_step_fupdN_term`). -/

section Termination

open MeasureTheory

variable [Zero B] [Preorder B] [_root_.Top B] {L : GradedLifting.{0} B}
  {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT} {μ₁' : Measure (State rT)} {ν₀ : Measure (Cfg rT)}
  {f' : Cfg rT → Cfg rT} {φ : Val rT → Val rT → Prop} {b : B} {k m : Nat} {law : L.BindLaw}

/-- `lift_erasure_erasable_law` for a run of mass `1`: continuations are needed only at states
from which the run still has mass `1` (Rocq `spec_coupl_adequacy_term`). -/
theorem execCoupl_erasable_of_term {μ₁ : Measure (State rT)} {R : State rT → Cfg rT → B}
    (hterm : execN m ⟨e₁, σ₁⟩ univ = 1) (hf' : Measurable f')
    (hspec : (μ₁'.bind fun σ => pexecN k ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₁ ν₀ R b) (hside : law.SideForExec μ₁ ν₀ R f')
    (hErase₁ : ErasableExpr μ₁ σ₁) (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ, execN m ⟨e₁, σ₂⟩ univ = 1 → R σ₂ ρ < (⊤ : B) →
      execCoupl L φ (R σ₂ ρ) m ⟨e₁, σ₂⟩ (f' ρ)) :
    execCoupl L φ b m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩ := by
  classical
  have hek : Measurable fun σ : State rT => execN m (⟨e₁, σ⟩ : Cfg rT) :=
    (execN_measurable m).comp (measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  have hA : MeasurableSet {σ : State rT | execN m ⟨e₁, σ⟩ univ = 1} :=
    (measurable_coe .univ).comp hek (measurableSet_singleton 1)
  have := hErase₁.isProbabilityMeasure
  have hmass : μ₁.bind (fun σ => execN m ⟨e₁, σ⟩) univ = 1 := by
    have h := congrArg (· univ) (hErase₁ e₁ m)
    simp only [asExpr, map_apply measurable_expr .univ, preimage_univ] at h
    rw [h, hterm]
  have hAc := ae_iff.1 (ae_measure_univ_eq_one_of_bind hek hmass)
  -- head_supp: setting the leftover to ⊤ off the mass-1 set keeps the head, so continuations are
  -- only needed there
  refine lift_erasure_erasable_law law hf' hspec (law.head_supp hA hAc hhead) hside.supp hErase₁
    hErase₁' fun σ₂ ρ hR => ?_
  by_cases hσ : σ₂ ∈ {σ : State rT | execN m ⟨e₁, σ⟩ univ = 1}
  · simp only [piecewise_eq_of_mem _ _ _ hσ] at hR ⊢
    exact hCont σ₂ ρ hσ hR
  · simp [piecewise_eq_of_notMem _ _ _ hσ] at hR

/-- `lift_erasure_erasable_exp_lhs_kanto_law` for a run of mass `1`: continuations are needed
only at configurations whose run has mass `1` (Rocq `prog_coupl_adequacy_term`). -/
theorem execCoupl_prog_of_term {μ₀ : Measure (Cfg rT)} {f : Cfg rT → Cfg rT}
    {R : Cfg rT → Cfg rT → B} (hnone : e₁.toVal? = none)
    (hterm : execN (m + 1) ⟨e₁, σ₁⟩ univ = 1) (hErase₁' : ErasableExpr μ₁' σ₁')
    (hf : Measurable f) (hprog : primStep ⟨e₁, σ₁⟩ = μ₀.map f) (hf' : Measurable f')
    (hspec : (μ₁'.bind fun σ => pexecN k ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₀ ν₀ R b) (hside : law.SideForExec μ₀ ν₀ R f')
    (hCont : ∀ ρ ρ', execN m (f ρ) univ = 1 → R ρ ρ' < (⊤ : B) →
      execCoupl L φ (R ρ ρ') m (f ρ) (f' ρ')) :
    execCoupl L φ b (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩ := by
  classical
  have hA : MeasurableSet {ρ : Cfg rT | execN m (f ρ) univ = 1} :=
    (measurable_coe .univ).comp ((execN_measurable m).comp hf) (measurableSet_singleton 1)
  have : IsSubProbabilityMeasure μ₀ := ⟨by
    have h := congrArg (· univ) hprog
    simp only [map_apply hf .univ, preimage_univ] at h
    rw [← h]
    exact IsSubProbabilityMeasure.measure_univ_le_one⟩
  simp only [execCoupl, execN_succ_not_isValue (ρ := ⟨e₁, σ₁⟩) (toVal?_eq_none.mp hnone) m]
    at hterm ⊢
  rw [hprog, Measure.bind_map hf (execN_measurable m)] at hterm
  have (ρ : Cfg rT) : IsSubProbabilityMeasure ((execN m ∘ f) ρ) :=
    execN.isSubProbabilityMeasure m (f ρ)
  have hAc := ae_iff.1 (ae_measure_univ_eq_one_of_bind ((execN_measurable m).comp hf) hterm)
  -- head_supp: setting the leftover to ⊤ off the mass-1 set keeps the head, so continuations are
  -- only needed there
  refine lift_erasure_erasable_exp_lhs_kanto_law law hErase₁' hf hprog hf' hspec
    (law.head_supp hA hAc hhead) hside.supp fun ρ ρ' hR => ?_
  by_cases hρ : ρ ∈ {ρ : Cfg rT | execN m (f ρ) univ = 1}
  · simp only [piecewise_eq_of_mem _ _ _ hρ] at hR ⊢
    exact hCont ρ ρ' hρ hR
  · simp [piecewise_eq_of_notMem _ _ _ hρ] at hR

end Termination

/-! ## Consuming one spec phase and one program step

Each `specCoupl` round is closed by `lift_erasure_erasable_law` and each `progCoupl` step by
`lift_erasure_erasable_exp_lhs_kanto_law`. -/

section Adequacy

variable [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerGS rT .hasNoLC GF]
local bi IProp GF

section
variable (P : State rT → Prop) (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
  (σ₁' : State rT) (Z : State rT → Cfg rT → B → _) (φ : Val rT → Val rT → Prop) (b : B)

/-- A spec coupling whose continuations give `m`-fuel execution couplings at `P`-states gives one
itself, given the one-round lemma `herase` at `P`-states; `P := True` gives
`wp_adequacy_spec_coupl`, `P := mass 1` gives `wp_adequacy_spec_coupl_term`. -/
theorem wp_adequacy_spec_coupl_guard (hP : P σ₁)
    (herase : ∀ {σ₀ : State rT} {e₀' : Exp rT} {σ₀' : State rT} {b₀ : B}
      {R : State rT → Cfg rT → B} {μ₁ μ₁' : Measure (State rT)}
      {ν₀ : Measure (Cfg rT)} {f' : Cfg rT → Cfg rT} {k : Nat} {law : L.BindLaw},
      P σ₀ → Measurable f' → (μ₁'.bind fun σ => pexecN k ⟨e₀', σ⟩) = ν₀.map f' →
      law.head μ₁ ν₀ R b₀ → law.SideForExec μ₁ ν₀ R f' → ErasableExpr μ₁ σ₀ →
      ErasableExpr μ₁' σ₀' →
      (∀ σ₂ ρ, P σ₂ → R σ₂ ρ < (⊤ : B) → execCoupl L φ (R σ₂ ρ) m ⟨e₁, σ₂⟩ (f' ρ)) →
      execCoupl L φ b₀ m ⟨e₁, σ₀⟩ ⟨e₀', σ₀'⟩) : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b Z ⊢
      (∀ σ₂ e₂' σ₂' b', ⌜P σ₂⌝ -∗ Z σ₂ ⟨e₂', σ₂'⟩ b' -∗
        |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  set Ψ : State rT → Cfg rT → B → IProp GF := fun σ₀ ρ₀ b₀ => iprop(
    ⌜P σ₀⌝ -∗
    (∀ σ₂ e₂' σ₂' b', ⌜P σ₂⌝ -∗ Z σ₂ ⟨e₂', σ₂'⟩ b' -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b₀ m ⟨e₁, σ₀⟩ ρ₀⌝)
  -- induction on the least fixpoint `specCoupl`, with `Ψ` the claim at each node
  iintro Hspec HZ
  iapply specCoupl_ind (Ψ := Ψ) $$ [] %σ₁ %e₁' %σ₁' %b Hspec %hP HZ
  iintro !> %σ₀ %⟨e₀', σ₀'⟩ %b₀ H
  simp only [Ψ]
  iintro %hP₀ HZ
  icases H with ⟨%hVac | HZApp | HCpl⟩
  -- absorbing budget: every pair is related
  · iapply fupd_step_fupdN_pure n ?_
    exact hVac _ _ _
  -- `Z` holds now: the caller's continuation
  · iapply HZ $$ %σ₀ %e₀' %σ₀' %b₀ %hP₀ HZApp
  -- one coupled round: `herase` reduces it to the continuations, which hold by induction
  · icases HCpl with ⟨%law, %k, %μ₁, %μ₁', %ν₀, %f', %R, %hmap, %hhead, %hside, %hErase,
      %hErase', HCont⟩
    iapply mono
    · refine step_fupdN_mono (P := iprop(⌜∀ σ₂ e₂' σ₂', P σ₂ ∧ R σ₂ ⟨e₂', σ₂'⟩ < (⊤ : B) →
        execCoupl L φ (R σ₂ ⟨e₂', σ₂'⟩) m ⟨e₁, σ₂⟩ (f' ⟨e₂', σ₂'⟩)⌝)) ?_
      iintro %hpure !%
      exact herase hP₀ hmap.1 hmap.2 hhead hside hErase hErase' fun σ₂ ⟨e₂', σ₂'⟩ h₁ h₂ =>
        hpure σ₂ e₂' σ₂' ⟨h₁, h₂⟩
    iapply step_fupdN_pure_imp_forall₃
    iintro %σ₂ %e₂' %σ₂' ⟨%hP₂, %hR⟩
    imod HCont $$ %σ₂ %⟨e₂', σ₂'⟩ %hR with ⟨HΨ, -⟩
    iapply HΨ $$ %hP₂ HZ

/-- A spec coupling whose continuations give `m`-fuel execution couplings gives one itself. -/
theorem wp_adequacy_spec_coupl : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b Z ⊢
      (∀ σ₂ e₂' σ₂' b', Z σ₂ ⟨e₂', σ₂'⟩ b' -∗
        |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  iintro Hspec HZ
  iapply wp_adequacy_spec_coupl_guard (fun _ => True) n m e₁ σ₁ e₁' σ₁' Z φ b trivial
    (fun _ hf' hspec hhead hside hErase hErase' hCont =>
      lift_erasure_erasable_law _ hf' hspec hhead hside hErase hErase'
        fun σ₂ ρ' => hCont σ₂ ρ' trivial)
    $$ Hspec
  iintro %σ₂ %e₂' %σ₂' %b' - HZ'
  iapply HZ $$ HZ'

/-- `wp_adequacy_spec_coupl` with no later steps. -/
theorem wp_adequacy_spec_coupl_zero : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b Z ⊢
      (∀ σ₂ e₂' σ₂' b', Z σ₂ ⟨e₂', σ₂'⟩ b' -∗
        |={∅}=> ⌜execCoupl L φ b' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
      |={∅}=> ⌜execCoupl L φ b m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ :=
  wp_adequacy_spec_coupl 0 m e₁ σ₁ e₁' σ₁' Z φ b

/-- `wp_adequacy_spec_coupl` for a run of mass `1`. -/
theorem wp_adequacy_spec_coupl_term [L.IsSupportLocal] (hterm : execN m ⟨e₁, σ₁⟩ univ = 1) : iprop%
    specCoupl L ∅ σ₁ e₁' σ₁' b Z ⊢
      (∀ σ₂ e₂' σ₂' b', ⌜execN m ⟨e₁, σ₂⟩ univ = 1⌝ -∗ Z σ₂ ⟨e₂', σ₂'⟩ b' -∗
        |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ :=
  wp_adequacy_spec_coupl_guard (fun σ => execN m ⟨e₁, σ⟩ univ = 1) n m e₁ σ₁ e₁' σ₁' Z φ b
    hterm fun hterm₀ hf' hspec hhead hside hErase hErase' hCont =>
      execCoupl_erasable_of_term hterm₀ hf' hspec hhead hside hErase hErase' hCont

end

section
variable (P : Exp rT → State rT → Prop) (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT)
  (σ₁' : State rT) (Z : Exp rT → State rT → Exp rT → State rT → B → _)
  (φ : Val rT → Val rT → Prop) (b : B)

/-- A program coupling whose continuations give `m`-fuel execution couplings at `P`-pairs gives an
`m + 1`-fuel one, given the one-step lemma `herase` at `P`-pairs; `P := True` gives
`wp_adequacy_prog_coupl`. -/
theorem wp_adequacy_prog_coupl_guard
    (herase : ∀ {R : Cfg rT → Cfg rT → B} {μ₁' : Measure (State rT)}
      {μ₀ ν₀ : Measure (Cfg rT)} {f f' : Cfg rT → Cfg rT} {k : Nat}
      {law : L.BindLaw},
      ErasableExpr μ₁' σ₁' → Measurable f → primStep ⟨e₁, σ₁⟩ = μ₀.map f → Measurable f' →
      (μ₁'.bind fun σ => pexecN k ⟨e₁', σ⟩) = ν₀.map f' → law.head μ₀ ν₀ R b →
      law.SideForExec μ₀ ν₀ R f' →
      (∀ ρ ρ', P (f ρ).1 (f ρ).2 → R ρ ρ' < (⊤ : B) → execCoupl L φ (R ρ ρ') m (f ρ) (f' ρ')) →
      execCoupl L φ b (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩) : iprop%
    progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢
      (∀ e₂ σ₂ e₂' σ₂' b', ⌜P e₂ σ₂⌝ -∗ Z e₂ σ₂ e₂' σ₂' b' -∗
        |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  iintro ⟨%law, %k, %μ₁', %μ₀, %ν₀, %f, %f', %R, %_, %hF, %hF', %hhead, %hside, %hErase', Hcnt⟩
    Hcoupl
  iapply mono
  · refine step_fupdN_mono (P := iprop(⌜∀ e₂ σ₂ e₂' σ₂', P (f ⟨e₂, σ₂⟩).1 (f ⟨e₂, σ₂⟩).2 ∧
      R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B) →
      execCoupl L φ (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) m (f ⟨e₂, σ₂⟩) (f' ⟨e₂', σ₂'⟩)⌝)) ?_
    iintro %hpure !%
    exact herase hErase' hF.1 hF.2 hF'.1 hF'.2 hhead hside
      fun ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ h₁ h₂ => hpure e₂ σ₂ e₂' σ₂' ⟨h₁, h₂⟩
  iapply step_fupdN_pure_imp_forall₄
  iintro %e₂ %σ₂ %e₂' %σ₂' ⟨%hP₂, %hR⟩
  imod Hcnt $$ %⟨e₂, σ₂⟩ %⟨e₂', σ₂'⟩ %hR with Hcnt
  iapply Hcoupl $$ %_ %_ %_ %_ %_ %hP₂ Hcnt

/-- A program coupling whose continuations give `m`-fuel execution couplings gives an
`m + 1`-fuel one. -/
theorem wp_adequacy_prog_coupl (hnone : e₁.toVal? = none) : iprop%
    progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢
      (∀ e₂ σ₂ e₂' σ₂' b', Z e₂ σ₂ e₂' σ₂' b' -∗
        |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ := by
  iintro Hprog HZ
  iapply wp_adequacy_prog_coupl_guard (fun _ _ => True) n m e₁ σ₁ e₁' σ₁' Z φ b
    (fun hErase' hf hprog hf' hspec hhead hside hCont => by
      simp only [execCoupl, execN_succ_not_isValue (ρ := ⟨e₁, σ₁⟩) (toVal?_eq_none.mp hnone) m]
      exact lift_erasure_erasable_exp_lhs_kanto_law _ hErase' hf hprog hf' hspec hhead hside
        fun ρ ρ' => hCont ρ ρ' trivial) $$ Hprog
  iintro %e₂ %σ₂ %e₂' %σ₂' %b' - HZ'
  iapply HZ $$ HZ'

/-- `wp_adequacy_prog_coupl` for a run of mass `1`. -/
theorem wp_adequacy_prog_coupl_term [L.IsSupportLocal] (hnone : e₁.toVal? = none)
    (hterm : execN (m + 1) ⟨e₁, σ₁⟩ univ = 1) : iprop%
    progCoupl L e₁ σ₁ e₁' σ₁' b Z ⊢
      (∀ e₂ σ₂ e₂' σ₂' b', ⌜execN m ⟨e₂, σ₂⟩ univ = 1⌝ -∗ Z e₂ σ₂ e₂' σ₂' b' -∗
        |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b' m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝ :=
  wp_adequacy_prog_coupl_guard (fun e σ => execN m ⟨e, σ⟩ univ = 1) n m e₁ σ₁ e₁' σ₁' Z φ b
    fun hErase' hf hprog hf' hspec hhead hside hCont =>
      execCoupl_prog_of_term hnone hterm hErase' hf hprog hf' hspec hhead hside hCont

end

/-! ## Inside the logic: one fuel per later -/

section Wp

variable [BudgetGS B GF]

section Lawful

variable [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsLawful]

/-- At a value the two runs are Dirac masses related by `φ` at any leftover; stated at fuel `n + 1`
because `execN 0` is the zero measure. -/
theorem wp_adequacy_val_fupd (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) (v : Val rT) (b : B) (He : e.toVal? = some v) :
    appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ budgetInterp b ∗
        wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝)) ⊢
      |={⊤, ∅}=> ⌜execCoupl L φ b (n + 1) ⟨e, σ⟩ ⟨e', σ'⟩⌝ := by
  obtain rfl : e = ofVal v := (ofVal_of_toVal_some He).symm
  iintro ⟨Hσ, Hs, Hb, Hwp⟩
  imod wp_value_specCoupl_unfold ⊤ He $$ Hwp %σ %e' %σ' %b [$] with HspecC
  iapply wp_adequacy_spec_coupl_zero $$ HspecC
  iintro %σ₂ %e₂' %σ₂' %b₂ HZ
  imod HZ with ⟨-, Hs', -, %v', Hv', %hφ⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs' Hv'
  imod subset empty_subset with -
  iintro !%
  unfold execCoupl limExecV asExpr
  rw [execN_succ_isValue v.isValue n, limExec_of_isVal (e := ofVal v') v'.2]
  simp only [map_dirac' measurable_expr]
  exact rel_dirac ⟨v, v', toVal?_ofVal v, toVal?_ofVal v', hφ⟩ b₂

variable (b : B) (e e' : Exp rT) (σ σ' : State rT) (n : Nat) (φ : Val rT → Val rT → Prop)

/-- Inside the logic, a `wp` gives the coupling of the `n`-fuel left run with the right limit run
after `n` later steps: each `▷` pays for one program step. -/
theorem wp_adequacy_step_fupdN [L.IsZeroLeft] :
    appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ budgetInterp b ∗
        wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝)) ⊢
      |={⊤, ∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩⌝ := by
  induction n generalizing b e e' σ σ' with
  | zero =>
    iintro -
    imod subset empty_subset with -
    iapply fupd_step_fupdN_pure 0 ?_
    simp only [execCoupl, asExpr, execN_zero, Measure.map_zero]
    exact IsZeroLeft.zero_left _ _ _
  | succ n ih =>
    iintro ⟨Hσ, Hs, Hb, Hwp⟩
    by_cases He : e.isValue
    · obtain ⟨v, Hv⟩ := toVal?_eq_some_of_isValue He
      imod wp_adequacy_val_fupd e e' σ σ' n φ v b Hv $$ [$] with %hpure
      iapply fupd_step_fupdN_pure (n + 1) hpure
    · have hnone : e.toVal? = none := toVal?_eq_none.mpr He
      -- `wpPre` at a non-value: specCoupl, then progCoupl, then ▷, then specCoupl, then `wp`
      imod wp_unfold_mp $$ Hwp %σ %e' %σ' %b [$] with Hwp
      iapply wp_adequacy_spec_coupl $$ Hwp
      rw [hnone]
      iintro %σ₂ %e₂' %σ₂' %b₂ Hprog
      iapply wp_adequacy_prog_coupl (hnone := hnone) $$ Hprog
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ Hspec
      -- the ▷ after the program step is spent as one step of |={∅}[∅]▷=>^[n+1]; fuel m+1 here is
      -- fuel m at the continuation (wp_adequacy_prog_coupl)
      simp only [Nat.repeat]
      iintro !> !> !>
      iapply wp_adequacy_spec_coupl $$ Hspec
      iintro %σ₄ %e₄' %σ₄' %b₄ HZ
      imod HZ
      iapply ih b₄ e₃ e₄' σ₄ σ₄' $$ HZ

/-- `wp_adequacy_step_fupdN` for a run of mass `1`. -/
theorem wp_adequacy_step_fupdN_term [L.IsSupportLocal] (hterm : execN n ⟨e, σ⟩ univ = 1) :
    appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ budgetInterp b ∗
        wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝)) ⊢
      |={⊤, ∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩⌝ := by
  induction n generalizing b e e' σ σ' with
  | zero => simp at hterm
  | succ n ih =>
    iintro ⟨Hσ, Hs, Hb, Hwp⟩
    by_cases He : e.isValue
    · obtain ⟨v, Hv⟩ := toVal?_eq_some_of_isValue He
      imod wp_adequacy_val_fupd e e' σ σ' n φ v b Hv $$ [$] with %hpure
      iapply fupd_step_fupdN_pure (n + 1) hpure
    · have hnone : e.toVal? = none := toVal?_eq_none.mpr He
      imod wp_unfold_mp $$ Hwp %σ %e' %σ' %b [$] with Hwp
      iapply wp_adequacy_spec_coupl_term (hterm := hterm) $$ Hwp
      rw [hnone]
      iintro %σ₂ %e₂' %σ₂' %b₂ %hterm₂ Hprog
      iapply wp_adequacy_prog_coupl_term (hnone := hnone) (hterm := hterm₂) $$ Hprog
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ %hterm₃ Hspec
      simp only [Nat.repeat]
      iintro !> !> !>
      iapply wp_adequacy_spec_coupl_term (hterm := hterm₃) $$ Hspec
      iintro %σ₄ %e₄' %σ₄' %b₄ %hterm₄ HZ
      imod HZ
      iapply ih b₄ e₃ e₄' σ₄ σ₄' hterm₄ $$ HZ

end Lawful

end Wp

end Adequacy

/-! ## Leaving the logic, then taking the limit -/

section Budget

variable [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [AppPreGS rT GF] [SpecPreGS rT GF]
  [IBCPre : BudgetCreditPreGS B GF] [InvGpreS GF] (e e' : Exp rT) (σ σ' : State rT)
local bi IProp GF

/-- Allocates the ghost state and turns an `n`-step adequacy entailment into `execCoupl`. -/
theorem execCoupl_of_step_fupdN (n : Nat) (φ : Val rT → Val rT → Prop) (b : B)
    (Hstep : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ budgetInterp b ∗
        wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝)) ⊢
      |={⊤, ∅}=> |={∅}[∅]▷=>^[n] ⌜execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩⌝)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢ ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝))) :
    execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩ := by
  refine pure_soundness (PROP := bi%) ?_
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

section Lawful

variable [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsLawful]

section
variable (n : Nat)

variable (φ : Val rT → Val rT → Prop) (b : B)

/-- A `wp` proof from `↯b b` couples the `n`-fuel left run with the right limit run at budget
`b`. -/
theorem wp_adequacy_exec_n [L.IsZeroLeft]
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢ ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝))) :
    execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩ :=
  execCoupl_of_step_fupdN e e' σ σ' n φ b (fun _ _ => wp_adequacy_step_fupdN b e e' σ σ' n φ) Hwp

variable [L.IsSupportLocal]

/-- `wp_adequacy_exec_n` for a run of mass `1`. -/
theorem wp_adequacy_exec_n_term (hterm : execN n ⟨e, σ⟩ univ = 1)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢ ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝))) :
    execCoupl L φ b n ⟨e, σ⟩ ⟨e', σ'⟩ :=
  execCoupl_of_step_fupdN e e' σ σ' n φ b
    (fun _ _ => wp_adequacy_step_fupdN_term b e e' σ σ' n φ hterm) Hwp

/-- `wp_adequacy` for a program whose run has mass `1` within `n` steps: the limit is that run,
so neither `IsZeroLeft` nor `IsLeftContinuous` is needed (Rocq `wp_adequacy_term`). -/
theorem wp_adequacy_term (b : B)
    (φ : Val rT → Val rT → Prop) (hterm : execN n ⟨e, σ⟩ univ = 1)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢ ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝))) :
    L.Rel b (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) := by
  rw [limExecV, limExec_term hterm]
  exact wp_adequacy_exec_n_term e e' σ σ' n φ b hterm Hwp

end

/-! ### Taking the limit on the left, and reading off a divergence -/

section Limit

variable [L.IsZeroLeft] [L.IsLeftContinuous] (b : B) (φ : Val rT → Val rT → Prop)

/-- A weakest precondition from a budget credit `b` couples the limit executions at budget `b`. -/
theorem wp_adequacy
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢ ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝))) :
    L.Rel b (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  limExecV_lift fun n => wp_adequacy_exec_n e e' σ σ' n φ b Hwp

/-- `wp_adequacy` at `b` from `wp` proofs at every budget `b' > b`, by `IsBudgetClosed`. -/
theorem wp_adequacy_budget_lim [L.IsBudgetClosed]
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF) (b' : B), b < b' →
      ⊢ ⤇ e' -∗ ↯b b' -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝))) :
    L.Rel b (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  IsBudgetClosed.of_forall_gt fun b' hb' =>
    wp_adequacy e e' σ σ' b' φ fun IGS IBC => Hwp IGS IBC b' hb'

variable {D : GradedDivergence.{0} B}
variable [L.IsSound D]

/-- A `wp` proof from `↯b b` whose results agree bounds the divergence of the limit outputs by `b`
(adequacy, Thm. 8.2; clutch-dp `wp_diffpriv`). -/
theorem wp_adequacy_div
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢ ⤇ e' -∗ ↯b b -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜v = v'⌝))) :
    D b (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  sound ((wp_adequacy e e' σ σ' b (· = ·) Hwp).mono le_rfl adequacyRel_eq_subset)

/-- `wp_adequacy_div` at `b` from `wp` proofs at every budget `b' > b`, by `IsBudgetClosed`. -/
theorem wp_adequacy_div_budget_lim [L.IsBudgetClosed]
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF) (b' : B), b < b' →
      ⊢ ⤇ e' -∗ ↯b b' -∗ wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜v = v'⌝))) :
    D b (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  sound ((wp_adequacy_budget_lim e e' σ σ' b (· = ·) Hwp).mono le_rfl adequacyRel_eq_subset)

/-- A `wp` proof from `↯b (s ε)` bounds the left output mass by the right output mass plus `ε`. -/
theorem wp_adequacy_mass {s : ENNReal →+o B} [L.IsMassDetecting s] (ε : ENNReal)
    (Hwp : ∀ (_ : MicrometerGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF),
      ⊢ ⤇ e' -∗ ↯b (s ε) -∗
        wp L ⊤ e (fun v => iprop(∃ v', ⤇ ofVal v' ∗ ⌜φ v v'⌝))) :
    limExecV ⟨e, σ⟩ univ ≤ limExecV ⟨e', σ'⟩ univ + ε :=
  IsMassDetecting.measure_le_add .univ .univ (wp_adequacy e e' σ σ' (s ε) φ Hwp)
    fun _ _ _ _ ↦ trivial

end Limit

end Lawful

end Budget

end ProbLang
