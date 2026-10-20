module

public import Metrology.Micrometer.RelTactics
public import Metrology.Couplings.BindLaws
import Metrology.ProbLang.Syntax.Notation

/-! # Law-driven `rand` couplings

`wp_couple_rand_rand_law` couples `rand N ~ K[rand N]` by any bind law with `HeadShift`, leaving
`R n m` at the draws (`refines` form: tactic `rel_couple_UU_law`); DP choice is an instance. -/

@[expose] public section

-- these rules use the @[discrete] lifting lemmas without being discrete themselves
set_option linter.discrete false

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang

variable {rT : Type} {B : Type}

open Classical in
/-- The leftover of the draws `rand N ~ K[rand N]` from `σ` and `σ'`: `R n m` at the
configurations drawn as `n` and `m`, and `⊤` elsewhere (keyed by both draws, unlike
`Cfg.advLeftover`). -/
noncomputable def Cfg.drawCost [_root_.Top B] (σ σ' : State rT) (K : Ectx rT)
    (R : Int → Int → B) (ρ ρ' : Cfg rT) : B :=
  if h : ∃ n m : Int, ρ = ⟨pl(#(.int n)), σ⟩ ∧ ρ' = ⟨K.fill pl(#(.int m)), σ'⟩ then
    R h.choose h.choose_spec.choose
  else ⊤

/-- At the configurations drawn as `n` and `m`, `drawCost` is `R n m`. -/
theorem Cfg.drawCost_apply [_root_.Top B] (σ σ' : State rT) (K : Ectx rT) (R : Int → Int → B)
    (n m : Int) :
    Cfg.drawCost σ σ' K R ⟨pl(#(.int n)), σ⟩ ⟨K.fill pl(#(.int m)), σ'⟩ = R n m := by
  -- `choose` returns `n, m` back: integer literals and `K.fill` are injective
  have key (h : ∃ n' m' : Int, (⟨pl(#(.int n)), σ⟩ : Cfg rT) = ⟨pl(#(.int n')), σ⟩ ∧
      (⟨K.fill pl(#(.int m)), σ'⟩ : Cfg rT) = ⟨K.fill pl(#(.int m')), σ'⟩) :
      R h.choose h.choose_spec.choose = R n m := by
    obtain ⟨h1, h2⟩ := h.choose_spec.choose_spec
    have e1 := congrArg Cfg.expr h1
    have e2 := Ectx.fill_injective K (congrArg Cfg.expr h2)
    injection e1 with e1
    injection e1 with e1
    injection e2 with e2
    injection e2 with e2
    rw [← e2, ← e1]
  rw [Cfg.drawCost, dite_eq_left_of_eq_true (eq_true ⟨n, m, rfl, rfl⟩)]
  exact key _

/-- A finite `drawCost` forces both configurations to be drawn ones. -/
theorem Cfg.exists_of_drawCost_lt_top [Preorder B] [OrderTop B] {σ σ' : State rT} {K : Ectx rT}
    {R : Int → Int → B} {ρ ρ' : Cfg rT} (h : Cfg.drawCost σ σ' K R ρ ρ' < (⊤ : B)) :
    ∃ n m : Int, ρ = ⟨pl(#(.int n)), σ⟩ ∧ ρ' = ⟨K.fill pl(#(.int m)), σ'⟩ := by
  by_contra hne
  simp only [Cfg.drawCost, hne, dite_false, lt_self_iff_false] at h

/-! ## The law-driven rule -/

section Law

variable [LawfulProbLangℝ rT] [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
  [OrderTop B]
  {L : GradedLifting.{0} B} [L.IsLawful] [L.IsTopAbsorbing] {hlc : HasLC} {GF : BundledGFunctors}
  [MeasurableSingletonClass rT] [BudgetCreditGS B GF]

section Wp

variable [MicrometerGS rT hlc GF]

/-- Couple `rand N ~ K[rand N]` by a step of `law`, spending `↯b c` on its head and handing the
leftover `R n m` to the draws `n` and `m`; the law's side condition must hold outright (Rocq
`wp_couple_spend`). -/
theorem wp_couple_rand_rand_law (law : L.BindLaw) [law.HeadShift] (N : Int) (HN : 0 < N)
    (R : Int → Int → B) (c : B) (hc : IsAddLeftRegular c) (K : Ectx rT)
    (hhead : ∀ σ σ', law.head ((unifInt N HN).map fun n ↦ (⟨pl(#(.int n)), σ⟩ : Cfg rT))
      ((unifInt N HN).map fun m ↦ (⟨K.fill pl(#(.int m)), σ'⟩ : Cfg rT))
      (Cfg.drawCost σ σ' K R) c)
    (hside : ∀ {X Y X' Y' : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
      [MeasurableSpace Y'] (μ : MeasureTheory.Measure X) (ν : MeasureTheory.Measure Y)
      (R' : X → Y → B)
      (k₁ : ProbabilityTheory.Kernel X X') (k₂ : ProbabilityTheory.Kernel Y Y'),
      law.side μ ν R' k₁ k₂)
    (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int N), #(.unit))) ∗ ↯b c ∗
    (∀ n m, ⌜R n m < (⊤ : B)⌝ -∗ ↯b (R n m) -∗ ⤇ K.fill pl(#(.int m)) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int N), #(.unit))) Φ := by
  iintro ⟨Hj, Hc, Hcnt⟩
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod BudgetCredit.supply_decrease hc $$ Hb Hc with ⟨%r, %hr, Hb⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  -- not via `wp_lift_prim_steps_coupl_law`: that needs the remainder `r < ⊤`; at `r = ⊤` we exit
  -- by absorption instead
  by_cases hrTop : r < (⊤ : B)
  swap
  · iapply specCoupl_absorbing
    exact IsTopAbsorbing.absorbing_top.mono (hr ▸ not_lt_top_iff.1 hrTop ▸ le_add_self)
  iapply specCoupl_ret
  simp only [Exp.rand_toVal?_eq_none]
  have hheadStep : law.head (primStep ⟨pl(rand(#(.int N), #(.unit))), σ₁⟩)
      (primStep ⟨K.fill pl(rand(#(.int N), #(.unit))), σ₁'⟩) (Cfg.drawCost σ₁ σ₁' K R) c := by
    rw [primStep_rand_unit HN, primStep_fill Exp.rand_not_isValue, primStep_rand_unit HN,
      Cfg.uniform_eq_map HN, Cfg.uniform_eq_map HN,
      MeasureTheory.Measure.map_map (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
        (Ectx.fillCfg.measurable K) Measurable.of_discrete]
    exact hhead σ₁ σ₁'
  iapply progCoupl_steps_spend_law law hr.ge hrTop (randUnit_uniform_step HN σ₁).1.toReducible
    ((randUnit_uniform_step HN σ₁').1.toReducible.fill K) hheadStep
    (.of_forall fun k₁ k₂ ↦ hside _ _ _ k₁ k₂)
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  -- R n m + r < ⊤ gives R n m < ⊤, so the pair is a drawn one
  obtain ⟨n, m, h1, h2⟩ := Cfg.exists_of_drawCost_lt_top (lt_of_le_of_lt le_self_add hR)
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h2
  rw [Cfg.drawCost_apply] at hR ⊢
  iintro !> !>
  iapply specCoupl_ret
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod BudgetCredit.supply_increase (c := R n m) $$ Hb with ⟨Hb, Hfrag⟩
  imod Hclose
  imodintro
  rw [add_comm (R n m)]
  iframe Hσ Hs' Hb
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %n %m %(lt_of_le_of_lt le_self_add hR) Hfrag Hj'

end Wp

/-- Couple `rand N ~ rand N` by a step of `law`, spending `↯b c` on its head and handing the
leftover `R r r'` to the draws (relational `wp_couple_rand_rand_law`). -/
theorem refines_couple_rands_law [MicrometerRGS rT hlc GF] [L.IsReflexive] [L.IsSupportLocal]
    [L.HasBind] (law : L.BindLaw) [law.HeadShift] {E : CoPset} {K K' : Ectx rT}
    {A : lrel rT GF} (N : Int) (HN : 0 < N) (R : Int → Int → B) (c : B)
    (hc : IsAddLeftRegular c)
    (hhead : ∀ (K : Ectx rT) σ σ', law.head
      ((unifInt N HN).map fun n ↦ (⟨pl(#(.int n)), σ⟩ : Cfg rT))
      ((unifInt N HN).map fun m ↦ (⟨K.fill pl(#(.int m)), σ'⟩ : Cfg rT))
      (Cfg.drawCost σ σ' K R) c)
    (hside : ∀ {X Y X' Y' : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
      [MeasurableSpace Y'] (μ : MeasureTheory.Measure X) (ν : MeasureTheory.Measure Y)
      (R' : X → Y → B) (k₁ : ProbabilityTheory.Kernel X X') (k₂ : ProbabilityTheory.Kernel Y Y'),
      law.side μ ν R' k₁ k₂) : iprop%
    ↯b c ∗ (∀ r r', ⌜R r r' < (⊤ : B)⌝ -∗ ↯b (R r r') -∗
      refines L E (K.fill pl(#(.int r))) (K'.fill pl(#(.int r'))) A) ⊢
    refines L E (K.fill pl(rand(#(.int N), #(.unit))))
      (K'.fill pl(rand(#(.int N), #(.unit)))) A := by
  unfold refines
  iintro ⟨Hc, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_rand_law law N HN R c hc (K2.comp K') (hhead _) hside ⊤ _
  iframe Hj Hc
  iintro %r %r' %hR Hr HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int r : Val rT) = pl(#(.int r)) from rfl]
  iapply Hcnt $$ %r %r' %hR Hr %K2 %b HKres Hna Herr Hpos

/-- `rel_couple_UU_law law R c hc hhead hside` couples `rand N ~ rand N` by a step of `law`,
spending `↯b c` and leaving `↯b (R r r')` (relational `wp_couple_rand_rand_law`). -/
macro "rel_couple_UU_law " law:term:max ppSpace R:term:max ppSpace c:term:max ppSpace
    hc:term:max ppSpace hhead:term:max ppSpace hside:term:max : tactic =>
  `(tactic| rel_apply (refines_couple_rands_law $law _ _ $R $c $hc $hhead $hside))

end Law

/-! ## The DP choice rule

Two DP couplings of the draws, one keeping a set `P` of left draws inside `T` and one keeping its
complement outside `T`, pay `max (ε₁ + ε₂) (ε₁' + ε₂')` once and leave `ε₂` or `ε₂'` to the
continuation, by which side of `P` the draw fell (Rocq `GBL_DP_choice`). -/

section Choice

variable [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
  {ε₁ δ₁ ε₁' δ₁' ε₂ ε₂' δ₂ : ℝ≥0∞} {S₁ S₂ : Int → Int → Prop} {P T : Set Int}

/-- The continuation budget of a choice draw: `(ε₂, δ₂)` on `P`, `(ε₂', δ₂)` off it. -/
noncomputable def choiceBudget (P : Set Int) (ε₂ ε₂' δ₂ : ℝ≥0∞) (r : Int) : ℝ≥0∞ × ℝ≥0∞ := by
  classical exact if r ∈ P then (ε₂, δ₂) else (ε₂', δ₂)

open Classical in
/-- The leftover of the choice draws: the choice budget on either coupling, `⊤` elsewhere. -/
noncomputable def choiceCost (S₁ S₂ : Int → Int → Prop) (P : Set Int) (ε₂ ε₂' δ₂ : ℝ≥0∞)
    (n m : Int) : ℝ≥0∞ × ℝ≥0∞ :=
  if S₁ n m ∨ S₂ n m then choiceBudget P ε₂ ε₂' δ₂ n else (⊤ : ℝ≥0∞ × ℝ≥0∞)

/-- A finite `choiceCost` forces `S₁ ∨ S₂` and equals the choice budget. -/
theorem choiceCost_of_lt_top {n m : Int}
    (h : choiceCost S₁ S₂ P ε₂ ε₂' δ₂ n m < (⊤ : ℝ≥0∞ × ℝ≥0∞)) :
    (S₁ n m ∨ S₂ n m) ∧ choiceCost S₁ S₂ P ε₂ ε₂' δ₂ n m = choiceBudget P ε₂ ε₂' δ₂ n := by
  by_cases hS : S₁ n m ∨ S₂ n m
  · exact ⟨hS, ite_eq_left hS⟩
  · simp [choiceCost, hS] at h

/-- The DP choice head for the draws `rand N ~ K[rand N]`, pushed to configurations. -/
theorem dpChoice_head_draws (N : Int) (HN : 0 < N) (K : Ectx rT) (σ σ' : State rT)
    (h₁ : (codensity dp).Rel (ε₁, δ₁) S₁ (unifInt N HN) (unifInt N HN))
    (h₂ : (codensity dp).Rel (ε₁', δ₁') S₂ (unifInt N HN) (unifInt N HN))
    (hPT₁ : ∀ r r', r ∈ P → S₁ r r' → r' ∈ T) (hPT₂ : ∀ r r', r ∉ P → S₂ r r' → r' ∉ T) :
    BindLaw.dpChoice.head ((unifInt N HN).map fun n ↦ (⟨pl(#(.int n)), σ⟩ : Cfg rT))
      ((unifInt N HN).map fun m ↦ (⟨K.fill pl(#(.int m)), σ'⟩ : Cfg rT))
      (Cfg.drawCost σ σ' K (choiceCost S₁ S₂ P ε₂ ε₂' δ₂))
      (max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) := by
  classical
  let lft : Int → Cfg rT := fun n ↦ ⟨pl(#(.int n)), σ⟩
  let rgt : Int → Cfg rT := fun m ↦ ⟨K.fill pl(#(.int m)), σ'⟩
  have hlft : Function.Injective lft := fun n n' h ↦ by simpa [lft] using h
  have hrgt : Function.Injective rgt := fun m m' h ↦ by
    simpa [rgt] using Ectx.fill_injective K ((Cfg.mk.injEq ..).mp h).1
  let lift (S : Int → Int → Prop) : Cfg rT → Cfg rT → Prop :=
    fun ρ ρ' ↦ ∃ n m, S n m ∧ ρ = lft n ∧ ρ' = rgt m
  have hcost {n m : Int} (h : S₁ n m ∨ S₂ n m) :
      Cfg.drawCost σ σ' K (choiceCost S₁ S₂ P ε₂ ε₂' δ₂) (lft n) (rgt m) =
        choiceBudget P ε₂ ε₂' δ₂ n := by
    rw [Cfg.drawCost_apply, choiceCost, ite_eq_left h]
  refine ⟨ε₁, δ₁, ε₁', δ₁', ε₂, ε₂', δ₂, lift S₁, lift S₂, lft '' P, rgt '' T,
    (P.to_countable.image _).measurableSet, (T.to_countable.image _).measurableSet,
    inferInstance, inferInstance,
    h₁.map (fun n m h ↦ ⟨n, m, h, rfl, rfl⟩) .of_discrete .of_discrete,
    h₂.map (fun n m h ↦ ⟨n, m, h, rfl, rfl⟩) .of_discrete .of_discrete, ?_, ?_, ?_, ?_, le_rfl⟩
  -- `S₁` keeps `P` inside `T`
  · rintro _ _ ⟨n, hn, rfl⟩ ⟨n', m, hS, hn', rfl⟩
    obtain rfl := hlft hn'
    exact ⟨m, hPT₁ _ _ hn hS, rfl⟩
  -- `S₂` keeps the complement of `P` outside `T`
  · rintro _ _ hn ⟨n, m, hS, rfl, rfl⟩ ⟨m', hm', hmm⟩
    obtain rfl := hrgt hmm
    exact hPT₂ _ _ (fun h ↦ hn ⟨n, h, rfl⟩) hS hm'
  -- the leftover is `(ε₂, δ₂)` on `P` and `(ε₂', δ₂)` off it
  · rintro _ _ ⟨n, hn, rfl⟩ ⟨n', m, hS, hn', rfl⟩
    obtain rfl := hlft hn'
    rw [hcost (.inl hS), choiceBudget, ite_eq_left hn]
  · rintro _ _ hn ⟨n, m, hS, rfl, rfl⟩
    rw [hcost (.inr hS), choiceBudget, ite_eq_right fun h ↦ hn ⟨n, h, rfl⟩]

/-- Couple `rand N ~ K[rand N]` by the DP choice rule, spending the choice budget and handing
`choiceBudget P ε₂ ε₂' δ₂ r` to the continuation at the left draw `r`. -/
theorem wp_couple_rand_rand_dpChoice {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS rT hlc GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (N : Int) (HN : 0 < N)
    (h₁ : (codensity dp).Rel (ε₁, δ₁) S₁ (unifInt N HN) (unifInt N HN))
    (h₂ : (codensity dp).Rel (ε₁', δ₁') S₂ (unifInt N HN) (unifInt N HN))
    (hPT₁ : ∀ r r', r ∈ P → S₁ r r' → r' ∈ T) (hPT₂ : ∀ r r', r ∉ P → S₂ r r' → r' ∉ T)
    (hc : IsAddLeftRegular ((max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) : ℝ≥0∞ × ℝ≥0∞))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int N), #(.unit))) ∗ ↯b (max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) ∗
    (∀ r r', ⌜S₁ r r' ∨ S₂ r r'⌝ -∗ ↯b (choiceBudget P ε₂ ε₂' δ₂ r) -∗
      ⤇ K.fill pl(#(.int r')) -∗ Φ (.int r)) ⊢
    wp (codensity dp) E pl(rand(#(.int N), #(.unit))) Φ := by
  iintro ⟨Hj, Hc, Hcnt⟩
  iapply wp_couple_rand_rand_law BindLaw.dpChoice N HN _ _ hc K
    (fun σ σ' ↦ dpChoice_head_draws N HN K σ σ' h₁ h₂ hPT₁ hPT₂) (fun _ _ _ _ _ ↦ trivial)
  iframe Hj Hc
  iintro %n %m %hR
  obtain ⟨hS, hcost⟩ := choiceCost_of_lt_top hR
  rw [hcost]
  iapply Hcnt $$ %n %m %hS

/-- Couple `rand N ~ rand N` by the DP choice rule, spending the choice budget and handing
`choiceBudget P ε₂ ε₂' δ₂ r` to the continuation at the left draw `r`. -/
theorem refines_couple_rands_dpChoice {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF}
    (N : Int) (HN : 0 < N)
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
  iintro ⟨Hc, Hcnt⟩
  iapply refines_couple_rands_law BindLaw.dpChoice N HN _ _ hc
    (fun K σ σ' ↦ dpChoice_head_draws N HN K σ σ' h₁ h₂ hPT₁ hPT₂) (fun _ _ _ _ _ ↦ trivial)
  iframe Hc
  iintro %n %m %hR
  obtain ⟨hS, hcost⟩ := choiceCost_of_lt_top hR
  rw [hcost]
  iapply Hcnt $$ %n %m %hS

end Choice

end ProbLang
