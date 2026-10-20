module

public import Metrology.Micrometer.AppRelRules
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

-- these rules use the @[discrete] lifting lemmas without being discrete themselves
set_option linter.discrete false

/-! Spec draws that split a credit by outcome (Eris `wp_couple_rand_adv_comp`, spec side). -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open scoped ENNReal AppGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] {B : Type}
  [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {L : GradedLifting.{0} B} [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]
  [L.HasBind] {s : ℝ≥0∞ →+o B} [L.IsExpectationAdditive s]

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS rT hlc GF] [BudgetCreditGS B GF]

/-- A spec draw `K[rand N]` turns `↯b (s ε₁)` into `↯b (s (ε₂ n))` at the outcome `n`, where `ε₁`
bounds the average of `ε₂`. -/
theorem wp_rand_r_adv (N : Int) (HN : 0 < N) (ε₁ : ℝ≥0∞) (ε₂ : Int → ℝ≥0∞)
    (hamort : (∑ n ∈ Finset.Ico 0 N, ε₂ n) / N.toNat ≤ ε₁) (hc : IsAddLeftRegular (s ε₁))
    (K : Ectx rT) {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill pl(rand(#(.int N), #(.unit))) ∗ ↯b (s ε₁) ∗
    (∀ n, ⌜0 ≤ n ∧ n < N⌝ -∗ ↯b (s (ε₂ n)) -∗ ⤇ K.fill pl(#(.int n)) -∗ wp L E e Φ) ⊢
    wp L E e Φ := by
  classical
  iintro ⟨Hj, Hc, Hcnt⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod BudgetCredit.supply_decrease hc $$ Hb Hc with ⟨%r, %hr, Hb⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  let rgt : Int → Cfg rT := fun n ↦ ⟨K.fill pl(#(.int n)), σ₁'⟩
  have hrgt : Function.Injective rgt := fun m m' h ↦ by
    simpa [rgt] using Ectx.fill_injective K ((Cfg.mk.injEq ..).mp h).1
  let R : State rT → Cfg rT → B := fun σ ρ ↦
    if σ = σ₁ ∧ ∃ n, 0 ≤ n ∧ n < N ∧ ρ = rgt n then s (ε₂ (Function.invFun rgt ρ)) + r else ⊤
  have hR {n : Int} (h0 : 0 ≤ n) (hN : n < N) : R σ₁ (rgt n) = s (ε₂ n) + r := by
    dsimp only [R]
    rw [ite_eq_left ⟨rfl, n, h0, hN, rfl⟩, Function.leftInverse_invFun hrgt n]
  have hredR := ((randUnit_uniform_step HN σ₁').1.toReducible).fill K
  have hcpl : L b R (MeasureTheory.Measure.dirac σ₁)
      ((MeasureTheory.Measure.dirac σ₁').bind fun σ ↦
        pexecN 1 ⟨K.fill pl(rand(#(.int N), #(.unit))), σ⟩) := by
    rw [dirac_bind_pexecN_one hredR, primStep_fill Exp.rand_not_isValue, primStep_rand_unit HN,
      Cfg.uniform_eq_map HN, MeasureTheory.Measure.map_map (by fun_prop) Measurable.of_discrete,
      ← MeasureTheory.Measure.map_id (μ := MeasureTheory.Measure.dirac σ₁)]
    -- δσ₁ ~ unifInt N at 0 (rel_dirac_left), add s(ε₂ m) in expectation (≤ s ε₁ by hamort),
    -- frame the remainder r, push to configurations
    have h₀ := IsTopAbsorbing.frame (c := r) <| IsExpectationAdditive.add_right (s := s)
      (c := ε₂) Measurable.of_discrete <|
        rel_dirac_left (L := L) (unifInt N HN) (A := Set.Ico 0 N) MeasurableSet.of_discrete
          (unifInt_compl_Ico HN) σ₁
    refine IsLawful.map measurable_id Measurable.of_discrete (IsLawful.mono h₀ ?_ ?_)
    · refine le_trans ?_ hr.ge
      gcongr
      rw [zero_add, lintegral_unifInt, ← ENNReal.div_eq_inv_mul] at *
      exact OrderHomClass.mono s hamort
    · -- on drawn pairs the leftover is s(ε₂ n) + r, elsewhere ⊤
      intro σ n
      dsimp only [id, Function.comp_apply]
      by_cases h : σ = σ₁ ∧ 0 ≤ n ∧ n < N
      · obtain ⟨h, h0, hN⟩ := h
        subst σ
        rw [show (⟨K.fill (Exp.lit (.int n)), σ₁'⟩ : Cfg rT) = rgt n from rfl, hR h0 hN,
          relCost_of (S := fun x y ↦ x = σ₁ ∧ y ∈ Set.Ico 0 N) ⟨rfl, h0, hN⟩, zero_add]
      · rw [relCost_of_not (S := fun x y ↦ x = σ₁ ∧ y ∈ Set.Ico 0 N)
          (fun h' ↦ h ⟨h'.1, h'.2.1, h'.2.2⟩)]
        exact le_top.trans (le_self_add.trans le_self_add)
  iapply specCoupl_couple hcpl (ErasableExpr.dret σ₁) (ErasableExpr.dret σ₁')
  iintro %σ₂ %e₂' %σ₂' %hlt
  obtain ⟨hσ, n, h0, hN, hρ⟩ : σ₂ = σ₁ ∧ ∃ n, 0 ≤ n ∧ n < N ∧ (⟨e₂', σ₂'⟩ : Cfg rT) = rgt n := by
    by_contra hno
    simp [R, hno] at hlt
  obtain ⟨he, hσ'⟩ := (Cfg.mk.injEq ..).mp hρ
  subst σ₂ e₂' σ₂'
  rw [show (⟨K.fill pl(#(.int n)), σ₁'⟩ : Cfg rT) = rgt n from rfl, hR h0 hN]
  imodintro
  iapply specCoupl_ret
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod BudgetCredit.supply_increase $$ Hb with ⟨Hb, Hfrag⟩
  imod Hclose
  imodintro
  rw [add_comm (s (ε₂ n))]
  iframe Hσ Hs' Hb
  iapply Hcnt $$ %n %⟨h0, hN⟩ Hfrag Hj'

end Wp

section Rel

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS B GF]

/-- `wp_rand_r_adv` for refinements: the spec draws alone, splitting `↯b (s ε₁)` by outcome. -/
theorem refines_randU_r_adv {E : CoPset} {K : Ectx rT} {e : Exp rT} {A : lrel rT GF} (N : Int)
    (HN : 0 < N) (ε₁ : ℝ≥0∞) (ε₂ : Int → ℝ≥0∞)
    (hamort : (∑ n ∈ Finset.Ico 0 N, ε₂ n) / N.toNat ≤ ε₁) (hc : IsAddLeftRegular (s ε₁)) :
    iprop%
    ↯b (s ε₁) ∗ (∀ n, ⌜0 ≤ n ∧ n < N⌝ -∗ ↯b (s (ε₂ n)) -∗ refines L E e (K.fill pl(#(.int n))) A) ⊢
    refines L E e (K.fill pl(rand(#(.int N), #(.unit)))) A := by
  unfold refines
  iintro ⟨Hc, Hlog⟩ %K' %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply wp_rand_r_adv N HN ε₁ ε₂ hamort hc (K'.comp K)
  iframe Hj Hc
  iintro %n %hn Hn HKRes
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ %n %hn Hn %K' %b HKRes Hna Herr Hpos

end Rel

end ProbLang
