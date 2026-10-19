module

public import Metrology.Micrometer.CouplingRules
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

set_option linter.discrete false

/-! Coupling two uniform draws by a step of any bind law whose heads shift, spending a credit. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting

namespace ProbLang

variable {rT : Type} {B : Type}

open Classical in
/-- The leftover of the draws `rand N ~ K[rand N]` from `σ` and `σ'`: `R n m` at the
configurations drawn as `n` and `m`, and `⊤` elsewhere. -/
noncomputable def Cfg.drawCost [_root_.Top B] (σ σ' : State rT) (K : Ectx rT)
    (R : Int → Int → B) (ρ ρ' : Cfg rT) : B :=
  if h : ∃ n m : Int, ρ = ⟨pl(#(.int n)), σ⟩ ∧ ρ' = ⟨K.fill pl(#(.int m)), σ'⟩ then
    R h.choose h.choose_spec.choose
  else ⊤

theorem Cfg.drawCost_apply [_root_.Top B] (σ σ' : State rT) (K : Ectx rT) (R : Int → Int → B)
    (n m : Int) :
    Cfg.drawCost σ σ' K R ⟨pl(#(.int n)), σ⟩ ⟨K.fill pl(#(.int m)), σ'⟩ = R n m := by
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

theorem Cfg.exists_of_drawCost_lt_top [Preorder B] [OrderTop B] {σ σ' : State rT} {K : Ectx rT}
    {R : Int → Int → B} {ρ ρ' : Cfg rT} (h : Cfg.drawCost σ σ' K R ρ ρ' < (⊤ : B)) :
    ∃ n m : Int, ρ = ⟨pl(#(.int n)), σ⟩ ∧ ρ' = ⟨K.fill pl(#(.int m)), σ'⟩ := by
  by_contra hne
  simp only [Cfg.drawCost, hne, dite_false, lt_self_iff_false] at h

variable [LawfulProbLangℝ rT] [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
  [OrderTop B]
  {L : GradedLifting.{0} B} [L.IsLawful] [L.IsTopAbsorbing] {hlc : HasLC} {GF : BundledGFunctors}
  [MeasurableSingletonClass rT] [MicrometerGS rT hlc GF] [BudgetCreditGS B GF]

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
  by_cases hr' : r < (⊤ : B)
  swap
  · iapply specCoupl_absorbing
    exact IsTopAbsorbing.absorbing_top.mono (hr ▸ not_lt_top_iff.1 hr' ▸ le_add_self)
  iapply specCoupl_ret
  simp only [Exp.rand_toVal?_eq_none]
  have hhead' : law.head (primStep ⟨pl(rand(#(.int N), #(.unit))), σ₁⟩)
      (primStep ⟨K.fill pl(rand(#(.int N), #(.unit))), σ₁'⟩) (Cfg.drawCost σ₁ σ₁' K R) c := by
    rw [primStep_rand_unit HN, primStep_fill Exp.rand_not_isValue, primStep_rand_unit HN,
      Cfg.uniform_eq_map HN, Cfg.uniform_eq_map HN,
      MeasureTheory.Measure.map_map (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
        (Ectx.fillCfg.measurable K) Measurable.of_discrete]
    exact hhead σ₁ σ₁'
  iapply progCoupl_steps_spend_law law hr.ge hr' (randUnit_uniform_step HN σ₁).1.toReducible
    ((randUnit_uniform_step HN σ₁').1.toReducible.fill K) hhead'
    (.of_forall fun k₁ k₂ ↦ hside _ _ _ k₁ k₂)
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
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

end ProbLang
