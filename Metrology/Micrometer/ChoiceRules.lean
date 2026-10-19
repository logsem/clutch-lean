module

public import Metrology.Micrometer.AppRelRules
public import Metrology.Couplings.BindLaws
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

set_option linter.discrete false

/-! # The DP choice rule for two uniform draws

Two DP couplings of the draws, one keeping a set `P` of left draws inside `T` and one keeping its
complement outside `T`, pay `max (ε₁ + ε₂) (ε₁' + ε₂')` once and leave `ε₂` or `ε₂'` to the
continuation, by which side of `P` the draw fell (Rocq `GBL_DP_choice`). -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped ENNReal AppGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- The continuation budget of a choice draw: `(ε₂, δ₂)` on `P`, `(ε₂', δ₂)` off it. -/
noncomputable def choiceBudget (P : Set Int) (ε₂ ε₂' δ₂ : ℝ≥0∞) (r : Int) : ℝ≥0∞ × ℝ≥0∞ := by
  classical exact if r ∈ P then (ε₂, δ₂) else (ε₂', δ₂)

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS rT hlc GF]
  [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF]

/-- Couple `rand N ~ K[rand N]` by the DP choice rule, spending the choice budget and handing
`choiceBudget P ε₂ ε₂' δ₂ r` to the continuation at the left draw `r`. -/
theorem wp_couple_rand_rand_dpChoice (N : Int) (HN : 0 < N) {ε₁ δ₁ ε₁' δ₁' ε₂ ε₂' δ₂ : ℝ≥0∞}
    {S₁ S₂ : Int → Int → Prop} {P T : Set Int}
    (h₁ : (codensity dp).Rel (ε₁, δ₁) S₁ (unifInt N HN) (unifInt N HN))
    (h₂ : (codensity dp).Rel (ε₁', δ₁') S₂ (unifInt N HN) (unifInt N HN))
    (hPT₁ : ∀ r r', r ∈ P → S₁ r r' → r' ∈ T) (hPT₂ : ∀ r r', r ∉ P → S₂ r r' → r' ∉ T)
    (hc : IsAddLeftRegular ((max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) : ℝ≥0∞ × ℝ≥0∞))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int N), #(.unit))) ∗ ↯b (max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) ∗
    (∀ r r', ⌜S₁ r r' ∨ S₂ r r'⌝ -∗ ↯b (choiceBudget P ε₂ ε₂' δ₂ r) -∗
      ⤇ K.fill pl(#(.int r')) -∗ Φ (.int r)) ⊢
    wp (codensity dp) E pl(rand(#(.int N), #(.unit))) Φ := by
  classical
  iintro ⟨Hj, Hc, Hcnt⟩
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod BudgetCredit.supply_decrease hc $$ Hb Hc with ⟨%r, %hr, Hb⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  by_cases hrtop : r = (⊤ : ℝ≥0∞ × ℝ≥0∞)
  · iapply specCoupl_absorbing
    exact IsTopAbsorbing.absorbing_top.mono (by simp [hr, hrtop])
  iapply specCoupl_ret
  simp only [Exp.rand_toVal?_eq_none]
  -- Push the draws, the sets and the leftovers to configurations.
  let lft : Int → Cfg rT := fun n ↦ ⟨pl(#(.int n)), σ₁⟩
  let rgt : Int → Cfg rT := fun m ↦ ⟨K.fill pl(#(.int m)), σ₁'⟩
  have hlft : Function.Injective lft := fun n n' h ↦ by simpa [lft] using h
  have hrgt : Function.Injective rgt := fun m m' h ↦ by
    simpa [rgt] using Ectx.fill_injective K ((Cfg.mk.injEq ..).mp h).1
  let lift (S : Int → Int → Prop) : Cfg rT → Cfg rT → Prop :=
    fun ρ ρ' ↦ ∃ n m, S n m ∧ ρ = lft n ∧ ρ' = rgt m
  let R : Cfg rT → Cfg rT → ℝ≥0∞ × ℝ≥0∞ := fun ρ ρ' ↦
    if lift S₁ ρ ρ' ∨ lift S₂ ρ ρ' then (if ρ ∈ lft '' P then (ε₂, δ₂) else (ε₂', δ₂))
    else (⊤ : ℝ≥0∞ × ℝ≥0∞)
  have hR {S : Int → Int → Prop} (hS : S = S₁ ∨ S = S₂) {n m : Int} (h : S n m) :
      R (lft n) (rgt m) = choiceBudget P ε₂ ε₂' δ₂ n := by
    have hl : lift S₁ (lft n) (rgt m) ∨ lift S₂ (lft n) (rgt m) := by
      rcases hS with rfl | rfl
      exacts [.inl ⟨n, m, h, rfl, rfl⟩, .inr ⟨n, m, h, rfl, rfl⟩]
    simp only [R, hl, ↓reduceIte, choiceBudget, hlft.mem_set_image]
  have hredL := (randUnit_uniform_step HN σ₁).1.toReducible
  have hredR := ((randUnit_uniform_step HN σ₁').1.toReducible).fill K
  have := prim_step_mass hredL
  have := prim_step_mass hredR
  have hstep (S : Int → Int → Prop) {b : ℝ≥0∞ × ℝ≥0∞}
      (h : (codensity dp).Rel b S (unifInt N HN) (unifInt N HN)) :
      (codensity dp).Rel b (lift S) (primStep ⟨pl(rand(#(.int N), #(.unit))), σ₁⟩)
        (primStep ⟨K.fill pl(rand(#(.int N), #(.unit))), σ₁'⟩) := by
    rw [primStep_rand_unit HN, primStep_fill Exp.rand_not_isValue, primStep_rand_unit HN]
    exact Cfg.uniform_codensity_fill HN HN σ₁ σ₁' K h fun n m h ↦ ⟨n, m, h, rfl, rfl⟩
  have hhead : BindLaw.dpChoice.head (primStep ⟨pl(rand(#(.int N), #(.unit))), σ₁⟩)
      (primStep ⟨K.fill pl(rand(#(.int N), #(.unit))), σ₁'⟩) R
      (max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) := by
    refine ⟨ε₁, δ₁, ε₁', δ₁', ε₂, ε₂', δ₂, lift S₁, lift S₂, lft '' P, rgt '' T,
      (P.to_countable.image _).measurableSet, (T.to_countable.image _).measurableSet,
      inferInstance, inferInstance, hstep S₁ h₁, hstep S₂ h₂, ?_, ?_, ?_, ?_, le_rfl⟩
    · rintro _ _ ⟨n, hn, rfl⟩ ⟨n', m, hS, hn', rfl⟩
      obtain rfl := hlft hn'
      exact ⟨m, hPT₁ _ _ hn hS, rfl⟩
    · rintro _ _ hn ⟨n, m, hS, rfl, rfl⟩ ⟨m', hm', hmm⟩
      obtain rfl := hrgt hmm
      exact hPT₂ _ _ (fun h ↦ hn ⟨n, h, rfl⟩) hS hm'
    · rintro _ _ ⟨n, hn, rfl⟩ ⟨n', m, hS, hn', rfl⟩
      obtain rfl := hlft hn'
      rw [hR (.inl rfl) hS, choiceBudget, ite_eq_left hn]
    · rintro _ _ hn ⟨n, m, hS, rfl, rfl⟩
      rw [hR (.inr rfl) hS, choiceBudget, ite_eq_right fun h ↦ hn ⟨n, h, rfl⟩]
  iapply progCoupl_steps_spend_law BindLaw.dpChoice hr.ge (lt_top_iff_ne_top.2 hrtop) hredL hredR
    hhead (.of_forall fun _ _ ↦ trivial)
  iintro %e₂ %σ₂ %e₂' %σ₂' %hlt
  obtain ⟨n, m, hS, hl, hr'⟩ : ∃ n m, (S₁ n m ∨ S₂ n m) ∧ (⟨e₂, σ₂⟩ : Cfg rT) = lft n ∧
      (⟨e₂', σ₂'⟩ : Cfg rT) = rgt m := by
    by_contra hno
    refine hlt.ne ?_
    have : ¬(lift S₁ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ ∨ lift S₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) := by
      rintro (⟨n, m, h, h1, h2⟩ | ⟨n, m, h, h1, h2⟩)
      exacts [hno ⟨n, m, .inl h, h1, h2⟩, hno ⟨n, m, .inr h, h1, h2⟩]
    simp only [R, this, ↓reduceIte]
    exact Prod.ext (top_add _) (top_add _)
  obtain ⟨he, hσ⟩ := (Cfg.mk.injEq ..).mp hl
  obtain ⟨he', hσ'⟩ := (Cfg.mk.injEq ..).mp hr'
  subst e₂ σ₂ e₂' σ₂'
  rw [show R (lft n) (rgt m) = choiceBudget P ε₂ ε₂' δ₂ n from hS.elim (hR (.inl rfl))
    (hR (.inr rfl))]
  iintro !> !>
  iapply specCoupl_ret
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod BudgetCredit.supply_increase $$ Hb with ⟨Hb, Hfrag⟩
  imod Hclose
  imodintro
  rw [add_comm (choiceBudget P ε₂ ε₂' δ₂ n)]
  iframe Hσ Hs' Hb
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %n %m %hS Hfrag Hj'

end Wp

section Rel

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
  [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF]

/-- Couple `rand N ~ rand N` by the DP choice rule, spending the choice budget and handing
`choiceBudget P ε₂ ε₂' δ₂ r` to the continuation at the left draw `r`. -/
theorem refines_couple_rands_dpChoice {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} (N : Int)
    (HN : 0 < N) {ε₁ δ₁ ε₁' δ₁' ε₂ ε₂' δ₂ : ℝ≥0∞} {S₁ S₂ : Int → Int → Prop} {P T : Set Int}
    (h₁ : (codensity dp).Rel (ε₁, δ₁) S₁ (unifInt N HN) (unifInt N HN))
    (h₂ : (codensity dp).Rel (ε₁', δ₁') S₂ (unifInt N HN) (unifInt N HN))
    (hPT₁ : ∀ r r', r ∈ P → S₁ r r' → r' ∈ T) (hPT₂ : ∀ r r', r ∉ P → S₂ r r' → r' ∉ T)
    (hc : IsAddLeftRegular ((max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) : ℝ≥0∞ × ℝ≥0∞)) :
    iprop%
    ↯b (max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) ∗
    (∀ r r', ⌜S₁ r r' ∨ S₂ r r'⌝ -∗ ↯b (choiceBudget P ε₂ ε₂' δ₂ r) -∗
      refines (codensity dp) E (K.fill pl(#(.int r))) (K'.fill pl(#(.int r'))) A) ⊢
    refines (codensity dp) E (K.fill pl(rand(#(.int N), #(.unit))))
      (K'.fill pl(rand(#(.int N), #(.unit)))) A := by
  unfold refines
  iintro ⟨Hc, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_rand_dpChoice N HN h₁ h₂ hPT₁ hPT₂ hc (K2.comp K') ⊤ _
  iframe Hj Hc
  iintro %r %r' %hS Hr HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int r : Val rT) = pl(#(.int r)) from rfl]
  iapply Hcnt $$ %r %r' %hS Hr %K2 %b HKres Hna Herr Hpos

end Rel

end ProbLang
