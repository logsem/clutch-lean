module

public import Metrology.Micrometer.CouplingRulesLaw
public import Metrology.ProbLang.Reals
import Metrology.ProbLang.Syntax.Notation

/-! # Credit-paying couplings of continuous draws

The `urand` counterparts of the `rand` coupling rules: a lifting of two uniform reals within a
budget (`wp_couple_urand_urand_spend`), a step of any bind law (`wp_couple_urand_urand_law`),
credits paid in expectation (`wp_couple_urand_urand_adv`, `wp_couple_urand_urand_avoid`), and
couplings of `urand` with `rand N` along a map pushing `unifUnit` to `unifInt N`
(`wp_couple_urand_rand`, `wp_couple_rand_urand`; at `ℝ`, `u ↦ ⌊N u⌋`,
`measurePreserving_floor_mul`). Each has a `refines` form and a `rel_couple_*` tactic. -/

@[expose] public section

-- these rules use the @[discrete] lifting lemmas without being discrete themselves
set_option linter.discrete false

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting
open scoped AppGS ENNReal

namespace ProbLang

open LawfulProbLangℝ

variable {rT : Type} [LawfulProbLangℝ rT]
variable {B : Type} {L : GradedLifting.{0} B}

/-! ## Liftings of `unifUnit` pushed to configurations -/

/-- A lifting of two uniform reals lifts to their configurations, the right one in context `K`. -/
theorem Cfg.uniformReal_rel_fill [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    {b : B} (σ σ' : State rT) (K : Ectx rT)
    {S : rT → rT → Prop} {S' : Cfg rT → Cfg rT → Prop} (h : L.Rel b S unifUnit unifUnit)
    (hS : ∀ x y, S x y → S' ⟨pl(#(.real x)), σ⟩ ⟨K.fill pl(#(.real y)), σ'⟩) :
    L.Rel b S' (Cfg.uniformReal σ) ((Cfg.uniformReal σ').map K.fillCfg) := by
  rw [Cfg.uniformReal, Cfg.uniformReal, MeasureTheory.Measure.map_map
    (Ectx.fillCfg.measurable K) (Cfg.measurable_realLit σ')]
  exact h.map hS (Cfg.measurable_realLit σ)
    ((Ectx.fillCfg.measurable K).comp (Cfg.measurable_realLit σ'))

open Classical in
/-- The leftover of the draws `urand ~ K[urand]` from `σ` and `σ'`: `R x y` at the configurations
drawn as `x` and `y`, and `⊤` elsewhere (the real counterpart of `Cfg.drawCost`). -/
noncomputable def Cfg.drawCostReal [_root_.Top B] (σ σ' : State rT) (K : Ectx rT)
    (R : rT → rT → B) (ρ ρ' : Cfg rT) : B :=
  if h : ∃ x y : rT, ρ = ⟨pl(#(.real x)), σ⟩ ∧ ρ' = ⟨K.fill pl(#(.real y)), σ'⟩ then
    R h.choose h.choose_spec.choose
  else ⊤

omit [LawfulProbLangℝ rT] in
/-- At the configurations drawn as `x` and `y`, `drawCostReal` is `R x y`. -/
theorem Cfg.drawCostReal_apply [_root_.Top B] (σ σ' : State rT) (K : Ectx rT)
    (R : rT → rT → B) (x y : rT) :
    Cfg.drawCostReal σ σ' K R ⟨pl(#(.real x)), σ⟩ ⟨K.fill pl(#(.real y)), σ'⟩ = R x y := by
  -- `choose` returns `x, y` back: real literals and `K.fill` are injective
  have key (h : ∃ x' y' : rT, (⟨pl(#(.real x)), σ⟩ : Cfg rT) = ⟨pl(#(.real x')), σ⟩ ∧
      (⟨K.fill pl(#(.real y)), σ'⟩ : Cfg rT) = ⟨K.fill pl(#(.real y')), σ'⟩) :
      R h.choose h.choose_spec.choose = R x y := by
    obtain ⟨h1, h2⟩ := h.choose_spec.choose_spec
    have e1 := congrArg Cfg.expr h1
    have e2 := Ectx.fill_injective K (congrArg Cfg.expr h2)
    injection e1 with e1
    injection e1 with e1
    injection e2 with e2
    injection e2 with e2
    rw [← e2, ← e1]
  rw [Cfg.drawCostReal, dite_eq_left_of_eq_true (eq_true ⟨x, y, rfl, rfl⟩)]
  exact key _

omit [LawfulProbLangℝ rT] in
/-- A finite `drawCostReal` forces both configurations to be drawn ones. -/
theorem Cfg.exists_of_drawCostReal_lt_top [Preorder B] [OrderTop B] {σ σ' : State rT}
    {K : Ectx rT} {R : rT → rT → B} {ρ ρ' : Cfg rT}
    (h : Cfg.drawCostReal σ σ' K R ρ ρ' < (⊤ : B)) :
    ∃ x y : rT, ρ = ⟨pl(#(.real x)), σ⟩ ∧ ρ' = ⟨K.fill pl(#(.real y)), σ'⟩ := by
  by_contra hne
  simp only [Cfg.drawCostReal, hne, dite_false, lt_self_iff_false] at h

open Classical in
/-- The leftover of an expectation-paid coupling along `f`: `s (ε₂ y)` when `y = f x` for `x` in
the support, `⊤` otherwise. -/
noncomputable def advCostReal [_root_.Top B] (s : ℝ≥0∞ → B) (f : rT → rT) (ε₂ : rT → ℝ≥0∞)
    (x y : rT) : B :=
  if x ∈ unifUnitSupport ∧ f x = y then s (ε₂ y) else ⊤

/-- A finite `advCostReal` forces the coupled pair. -/
theorem advCostReal_spec [Preorder B] [OrderTop B] {s : ℝ≥0∞ → B} {f : rT → rT}
    {ε₂ : rT → ℝ≥0∞} {x y : rT} (h : advCostReal s f ε₂ x y < (⊤ : B)) :
    (x ∈ unifUnitSupport ∧ f x = y) ∧ advCostReal s f ε₂ x y = s (ε₂ y) := by
  by_cases hS : x ∈ unifUnitSupport ∧ f x = y
  · exact ⟨hS, ite_eq_left hS⟩
  · simp [advCostReal, hS] at h

/-- Coupling `urand ~ K[urand]` along a measure-preserving `f`, paying `s (ε₂ y)` at the right
draw `y` out of `s ε₁`, where `ε₁` bounds the mean of `ε₂`. -/
theorem Cfg.uniformReal_lift_adv [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
    [OrderTop B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] {s : ℝ≥0∞ →+o B}
    [L.IsExpectationAdditive s] (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f unifUnit unifUnit) (ε₁ : ℝ≥0∞) (ε₂ : rT → ℝ≥0∞)
    (hε₂ : Measurable ε₂) (hamort : ∫⁻ y, ε₂ y ∂unifUnit ≤ ε₁) (σ σ' : State rT) (K : Ectx rT) :
    L (s ε₁) (Cfg.drawCostReal σ σ' K (advCostReal s f ε₂))
      (unifUnit.map fun x ↦ (⟨pl(#(.real x)), σ⟩ : Cfg rT))
      (unifUnit.map fun y ↦ (⟨K.fill pl(#(.real y)), σ'⟩ : Cfg rT)) := by
  classical
  have h0 := (rel_graph (L := L) unifUnit hmp.measurable).restrict unifUnitSupportMeasurable
    unifUnitIsConcentrated
  rw [hmp.map_eq] at h0
  have h1 := IsExpectationAdditive.add_right (s := s) hε₂ h0
  refine IsLawful.map (Cfg.measurable_realLit σ)
    (g := fun y ↦ (⟨K.fill pl(#(.real y)), σ'⟩ : Cfg rT))
    ((Ectx.fillCfg.measurable K).comp (Cfg.measurable_realLit σ'))
    (IsLawful.mono h1 (by rw [zero_add]; exact OrderHomClass.mono s hamort) fun x y => ?_)
  rw [Cfg.drawCostReal_apply]
  by_cases hS : f x = y ∧ x ∈ unifUnitSupport
  · rw [relCost_of (S := fun x y ↦ f x = y ∧ x ∈ unifUnitSupport) hS, zero_add, advCostReal,
      ite_eq_left ⟨hS.2, hS.1⟩]
  · rw [relCost_of_not (S := fun x y ↦ f x = y ∧ x ∈ unifUnitSupport) hS]
    exact le_top.trans le_self_add

/-! ## `urand` against `rand N` along a map -/

/-- Coupling the uniform real with a uniform integer along `g`, which pushes `unifUnit` to
`unifInt N`. -/
theorem Cfg.uniformReal_rel_uniform [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [L.IsReflexive] [L.IsSupportLocal] {N : Int} (HN : 0 < N) (g : rT → Int)
    (hg : MeasureTheory.MeasurePreserving g unifUnit (unifInt N HN)) (σ σ' : State rT)
    (K : Ectx rT) :
    L.Rel 0 (fun c₁ c₂ : Cfg rT => ∃ r, r ∈ unifUnitSupport ∧
        c₁ = ⟨pl(#(.real r)), σ⟩ ∧ c₂ = ⟨K.fill pl(#(.int (g r))), σ'⟩)
      (Cfg.uniformReal σ) ((Cfg.uniform N σ').map K.fillCfg) := by
  have h := (rel_graph (L := L) unifUnit hg.measurable).restrict unifUnitSupportMeasurable
    unifUnitIsConcentrated
  rw [hg.map_eq] at h
  rw [Cfg.uniformReal, Cfg.uniform_eq_map HN, MeasureTheory.Measure.map_map
    (Ectx.fillCfg.measurable K) Measurable.of_discrete]
  exact h.map (fun r _ ⟨hrr', hr⟩ => ⟨r, hr, rfl, hrr' ▸ rfl⟩) (Cfg.measurable_realLit σ)
    ((Ectx.fillCfg.measurable K).comp Measurable.of_discrete)

/-- Coupling a uniform integer with the uniform real, the integer being `g` of the real. -/
theorem Cfg.uniform_rel_uniformReal [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [L.IsReflexive] [L.IsSupportLocal] {N : Int} (HN : 0 < N) (g : rT → Int)
    (hg : MeasureTheory.MeasurePreserving g unifUnit (unifInt N HN)) (σ σ' : State rT)
    (K : Ectx rT) :
    L.Rel 0 (fun c₁ c₂ : Cfg rT => ∃ r, r ∈ unifUnitSupport ∧
        c₁ = ⟨pl(#(.int (g r))), σ⟩ ∧ c₂ = ⟨K.fill pl(#(.real r)), σ'⟩)
      (Cfg.uniform N σ) ((Cfg.uniformReal σ').map K.fillCfg) := by
  have h := (IsReflexive.refl (L := L) (unifUnit (T := rT))).restrict unifUnitSupportMeasurable
    unifUnitIsConcentrated
  rw [Cfg.uniform_eq_map HN, ← hg.map_eq, MeasureTheory.Measure.map_map Measurable.of_discrete
    hg.measurable, Cfg.uniformReal, MeasureTheory.Measure.map_map (Ectx.fillCfg.measurable K)
    (Cfg.measurable_realLit σ')]
  exact h.map (fun r _ ⟨hrr', hr⟩ => ⟨r, hr, rfl, hrr' ▸ rfl⟩)
    (Measurable.of_discrete.comp hg.measurable)
    ((Ectx.fillCfg.measurable K).comp (Cfg.measurable_realLit σ'))

/-- At `ℝ`, `u ↦ ⌊N u⌋` pushes the uniform measure on `[0, 1]` to the uniform measure on
`{0, …, N-1}`. -/
theorem measurePreserving_floor_mul (N : Int) (HN : 0 < N) :
    MeasureTheory.MeasurePreserving (fun u : ℝ => ⌊(N : ℝ) * u⌋) unifUnit (unifInt N HN) := by
  have hNr : (0 : ℝ) < N := Int.cast_pos.mpr HN
  have hmeas : Measurable (fun u : ℝ => ⌊(N : ℝ) * u⌋) :=
    Int.measurable_floor.comp (measurable_const_mul _)
  refine ⟨hmeas, MeasureTheory.Measure.ext_of_singleton fun k => ?_⟩
  have hpre : (fun u : ℝ => ⌊(N : ℝ) * u⌋) ⁻¹' {k} = Set.Ico ((k : ℝ) / N) ((k + 1) / N) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Int.floor_eq_iff, Set.mem_Ico,
      div_le_iff₀ hNr, lt_div_iff₀ hNr]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [MeasureTheory.Measure.map_apply hmeas (measurableSet_singleton k), hpre, unifInt,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete, PMF.uniformOfFinset_apply]
  show (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) _ = _
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ico]
  split_ifs with hk
  · obtain ⟨hk0, hkN⟩ := Finset.mem_Ico.mp hk
    have hk0' : (0 : ℝ) ≤ k := by exact_mod_cast hk0
    have hkN' : (k : ℝ) + 1 ≤ N := by exact_mod_cast (show k + 1 ≤ N by omega)
    have hsub : Set.Ico ((k : ℝ) / N) ((k + 1) / N) ⊆ Set.Icc 0 1 := fun u ⟨h1, h2⟩ =>
      ⟨(div_nonneg hk0' hNr.le).trans h1, h2.le.trans ((div_le_one hNr).mpr hkN')⟩
    rw [Set.inter_eq_left.mpr hsub, Real.volume_Ico, Int.card_Ico, sub_zero, ← sub_div,
      add_sub_cancel_left, ENNReal.ofReal_div_of_pos hNr, ENNReal.ofReal_one, one_div]
    congr 1
    rw [← ENNReal.ofReal_natCast]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg HN.le).symm
  · refine MeasureTheory.measure_mono_null (t := {(1 : ℝ)}) ?_ (Real.volume_singleton)
    rintro u ⟨⟨h1, h2⟩, h3, h4⟩
    rw [div_le_iff₀ hNr] at h1
    rw [lt_div_iff₀ hNr] at h2
    simp only [Finset.mem_Ico] at hk
    rcases Int.lt_or_le k 0 with hk' | hk'
    · have : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast (show k + 1 ≤ 0 by omega)
      nlinarith
    · have : (N : ℝ) ≤ k := by exact_mod_cast (show N ≤ k by omega)
      exact _root_.le_antisymm h4 (by nlinarith)

/-! ## Program rules -/

section Rules
variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSingletonClass rT]

section Wp
variable [MicrometerGS rT hlc GF] [BudgetCreditGS B GF] [L.IsLawful] [L.IsTopAbsorbing]

/-- Couple `urand ~ K[urand]` along `S`, given a lifting of the two uniform reals within the
cancelable budget `c`; spends `↯b c` (the `urand` form of `wp_couple_rand_rand_spend`). -/
theorem wp_couple_urand_urand_spend [L.HasBind] [L.IsSupportLocal] (S : rT → rT → Prop) (c : B)
    (hc : IsAddLeftRegular c) (Hcpl : L.Rel c S unifUnit unifUnit) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(urand) ∗ ↯b c ∗
    (∀ x y, ⌜S x y⌝ -∗ ⤇ K.fill pl(#(.real y)) -∗ Φ (.real x)) ⊢
    wp L E pl(urand) Φ := by
  iintro ⟨Hj, Hc, Hcnt⟩
  iapply wp_lift_prim_steps_coupl Exp.urand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod BudgetCredit.supply_decrease hc $$ Hb Hc with ⟨%r, %hr, Hdec⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  let S' : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ x y, S x y ∧ c₁ = ⟨pl(#(.real x)), σ₁⟩ ∧ c₂ = ⟨K.fill pl(#(.real y)), σ₁'⟩
  iexists S', c, r
  have hsum : c + r ≤ b := hr.ge
  have hredL := reducible_urand σ₁
  have hredR := Reducible.fill K (reducible_urand σ₁')
  have hcpl : L.Rel c S' (primStep ⟨pl(urand), σ₁⟩) (primStep ⟨K.fill pl(urand), σ₁'⟩) := by
    rw [primStep_urand, primStep_fill Exp.urand_not_isValue, primStep_urand]
    exact Cfg.uniformReal_rel_fill σ₁ σ₁' K Hcpl fun x y h => ⟨x, y, h, rfl, rfl⟩
  iframe %hsum %hredL %hredR %hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨x, y, hS, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hdec
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %x %y %hS Hj'

/-- Couple `urand ~ K[urand]` by a step of `law`, spending `↯b c` on its head and handing the
leftover `R x y` to the draws `x` and `y` (the `urand` form of `wp_couple_rand_rand_law`). -/
theorem wp_couple_urand_urand_law (law : L.BindLaw) [law.HeadShift] [law.SideFree]
    (R : rT → rT → B) (c : B) (hc : IsAddLeftRegular c) (K : Ectx rT)
    (hhead : ∀ σ σ', law.head (unifUnit.map fun x ↦ (⟨pl(#(.real x)), σ⟩ : Cfg rT))
      (unifUnit.map fun y ↦ (⟨K.fill pl(#(.real y)), σ'⟩ : Cfg rT))
      (Cfg.drawCostReal σ σ' K R) c)
    (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(urand) ∗ ↯b c ∗
    (∀ x y, ⌜R x y < (⊤ : B)⌝ -∗ ↯b (R x y) -∗ ⤇ K.fill pl(#(.real y)) -∗ Φ (.real x)) ⊢
    wp L E pl(urand) Φ := by
  iintro ⟨Hj, Hc, Hcnt⟩
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod BudgetCredit.supply_decrease hc $$ Hb Hc with ⟨%r, %hr, Hb⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  -- at the remainder `r = ⊤` we exit by absorption, as in `wp_couple_rand_rand_law`
  by_cases hrTop : r < (⊤ : B)
  swap
  · iapply specCoupl_absorbing
    exact IsTopAbsorbing.absorbing_top.mono (hr ▸ not_lt_top_iff.1 hrTop ▸ le_add_self)
  iapply specCoupl_ret
  simp only [Exp.urand_toVal?_eq_none]
  have hheadStep : law.head (primStep ⟨pl(urand), σ₁⟩) (primStep ⟨K.fill pl(urand), σ₁'⟩)
      (Cfg.drawCostReal σ₁ σ₁' K R) c := by
    rw [primStep_urand, primStep_fill Exp.urand_not_isValue, primStep_urand, Cfg.uniformReal,
      Cfg.uniformReal, MeasureTheory.Measure.map_map
        (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
        (Ectx.fillCfg.measurable K) (Cfg.measurable_realLit σ₁')]
    exact hhead σ₁ σ₁'
  iapply progCoupl_steps_spend_law law hr.ge hrTop (reducible_urand σ₁)
    (Reducible.fill K (reducible_urand σ₁')) hheadStep
    (.of_forall fun k₁ k₂ ↦ BindLaw.SideFree.side _ _ _ k₁ k₂)
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  obtain ⟨x, y, h1, h2⟩ := Cfg.exists_of_drawCostReal_lt_top (_root_.lt_of_le_of_lt le_self_add hR)
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h2
  rw [Cfg.drawCostReal_apply] at hR ⊢
  iintro !> !>
  iapply specCoupl_ret
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod BudgetCredit.supply_increase (c := R x y) $$ Hb with ⟨Hb, Hfrag⟩
  imod Hclose
  imodintro
  rw [add_comm (R x y)]
  iframe Hσ Hs' Hb
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %x %y %(_root_.lt_of_le_of_lt le_self_add hR) Hfrag Hj'

/-- Couple `urand ~ K[urand]` along a measure-preserving `f`, turning `↯b (s ε₁)` into
`↯b (s (ε₂ (f x)))` at the draw `x`, where `ε₁` bounds the mean of `ε₂` (the `urand` form of
`wp_couple_rand_rand_adv`). -/
theorem wp_couple_urand_urand_adv [L.IsReflexive] [L.IsSupportLocal] [L.HasBind]
    {s : ℝ≥0∞ →+o B} [L.IsExpectationAdditive s] (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f unifUnit unifUnit) (ε₁ : ℝ≥0∞) (ε₂ : rT → ℝ≥0∞)
    (hε₂ : Measurable ε₂) (hamort : ∫⁻ y, ε₂ y ∂unifUnit ≤ ε₁) (hc : IsAddLeftRegular (s ε₁))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(urand) ∗ ↯b (s ε₁) ∗
    (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗ ⌜¬ L.Absorbing (s (ε₂ (f x)))⌝ -∗ ↯b (s (ε₂ (f x))) -∗
      ⤇ K.fill pl(#(.real (f x))) -∗ Φ (.real x)) ⊢
    wp L E pl(urand) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_lift_prim_steps_coupl_adv_absorbing Exp.urand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  have hredL := reducible_urand σ₁
  have hredR := Reducible.fill K (reducible_urand σ₁')
  imod BudgetCredit.supply_decrease hc $$ Hb Herr with ⟨%r, %hr, Hb⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  have hb : s ε₁ + r ≤ b := hr.ge
  imodintro
  have hlift : L (s ε₁) (Cfg.drawCostReal σ₁ σ₁' K (advCostReal s f ε₂))
      (primStep ⟨pl(urand), σ₁⟩) (primStep ⟨K.fill pl(urand), σ₁'⟩) := by
    rw [primStep_urand, primStep_fill Exp.urand_not_isValue, primStep_urand, Cfg.uniformReal,
      Cfg.uniformReal, MeasureTheory.Measure.map_map
        (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
        (Ectx.fillCfg.measurable K) (Cfg.measurable_realLit σ₁')]
    exact Cfg.uniformReal_lift_adv f hmp ε₁ ε₂ hε₂ hamort σ₁ σ₁' K
  iexists Cfg.drawCostReal σ₁ σ₁' K (advCostReal s f ε₂), s ε₁, r
  iframe %hb %hredL %hredR %hlift
  iintro %e₂ %σ₂ %e₂' %σ₂' !>
  -- leftover absorbing: exit left; otherwise it is finite, so the pair is a coupled draw
  by_cases habs : L.Absorbing (Cfg.drawCostReal σ₁ σ₁' K (advCostReal s f ε₂)
      ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + r)
  · imod Hclose
    imodintro
    ileft
    ipureintro
    exact habs
  have hlt : Cfg.drawCostReal σ₁ σ₁' K (advCostReal s f ε₂) ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B) := by
    by_contra h
    exact habs (IsTopAbsorbing.absorbing_top.mono (not_lt_top_iff.1 h ▸ le_self_add))
  obtain ⟨x, y, h1, h2⟩ := Cfg.exists_of_drawCostReal_lt_top hlt
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h2
  rw [Cfg.drawCostReal_apply] at habs hlt ⊢
  obtain ⟨⟨hx, rfl⟩, hcost⟩ := advCostReal_spec hlt
  rw [hcost] at habs ⊢
  have hna : ¬ L.Absorbing (s (ε₂ (f x))) := fun h => habs (h.mono le_self_add)
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod BudgetCredit.supply_increase $$ Hb with ⟨Hb, Hfrag⟩
  imod Hclose
  imodintro
  iright
  rw [add_comm (s (ε₂ (f x)))]
  iframe Hσ Hs' Hb
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %x %hx %hna Hfrag Hj'

/-- Couple `urand ~ K[urand]` identically, avoiding the measurable set `Bad` for
`↯b (s (unifUnit Bad))` when `s 1` is absorbing (the `urand` form of
`wp_couple_rand_rand_avoid`). -/
theorem wp_couple_urand_urand_avoid [L.IsReflexive] [L.IsSupportLocal] [L.HasBind]
    {s : ℝ≥0∞ →+o B} [L.IsExpectationAdditive s] (Bad : Set rT) (hBad : MeasurableSet Bad)
    (habs : L.Absorbing (s 1)) (hc : IsAddLeftRegular (s (unifUnit Bad))) (K : Ectx rT)
    (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(urand) ∗ ↯b (s (unifUnit Bad)) ∗
    (∀ x, ⌜x ∈ unifUnitSupport ∧ x ∉ Bad⌝ -∗ ⤇ K.fill pl(#(.real x)) -∗ Φ (.real x)) ⊢
    wp L E pl(urand) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_couple_urand_urand_adv id (MeasureTheory.MeasurePreserving.id _) (unifUnit Bad)
    (Bad.indicator 1) (measurable_one.indicator hBad)
    (by rw [MeasureTheory.lintegral_indicator_one hBad]) hc K E Φ
  iframe Hj Herr
  iintro %x %hx %hna - Hj'
  by_cases hb : x ∈ Bad
  · simp only [id_eq, Set.indicator_of_mem hb, Pi.one_apply] at hna
    exact (hna habs).elim
  · simp only [id_eq]
    iapply Hcnt $$ %x %⟨hx, hb⟩ Hj'

/-- Couple `urand ~ K[rand N]` along `g`, which pushes `unifUnit` to `unifInt N`: the left draw is
`x`, the right draw is `g x` (at `ℝ`, `g u = ⌊N u⌋`, `measurePreserving_floor_mul`). -/
theorem wp_couple_urand_rand [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] (N : Int)
    (HN : 0 < N) (g : rT → Int) (hg : MeasureTheory.MeasurePreserving g unifUnit (unifInt N HN))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int N), #(.unit))) ∗
    (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗ ⤇ K.fill pl(#(.int (g x))) -∗ Φ (.real x)) ⊢
    wp L E pl(urand) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply wp_lift_prim_steps_coupl Exp.urand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ => ∃ r, r ∈ unifUnitSupport ∧
    c₁ = ⟨pl(#(.real r)), σ₁⟩ ∧ c₂ = ⟨K.fill pl(#(.int (g r))), σ₁'⟩
  iexists R, 0, b
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact reducible_urand σ₁
  isplitr; · ipureintro; exact ((randUnit_uniform_step HN σ₁').1.toReducible).fill K
  isplitr
  · ipureintro
    rw [primStep_urand σ₁, primStep_fill Exp.rand_not_isValue, primStep_rand_unit HN]
    exact Cfg.uniformReal_rel_uniform HN g hg σ₁ σ₁' K
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨r, hrsupp, heq1, heq2⟩
  cases heq1
  cases heq2
  iintro !> !>
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hb
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %r %hrsupp Hj'

/-- Couple `rand N ~ K[urand]` along `g`, which pushes `unifUnit` to `unifInt N`: the right draw
is `x`, the left draw is `g x`. -/
theorem wp_couple_rand_urand [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] (N : Int)
    (HN : 0 < N) (g : rT → Int) (hg : MeasureTheory.MeasurePreserving g unifUnit (unifInt N HN))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(urand) ∗
    (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗ ⤇ K.fill pl(#(.real x)) -∗ Φ (.int (g x))) ⊢
    wp L E pl(rand(#(.int N), #(.unit))) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply wp_lift_prim_steps_coupl Exp.rand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ => ∃ r, r ∈ unifUnitSupport ∧
    c₁ = ⟨pl(#(.int (g r))), σ₁⟩ ∧ c₂ = ⟨K.fill pl(#(.real r)), σ₁'⟩
  iexists R, 0, b
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact (randUnit_uniform_step HN σ₁).1.toReducible
  isplitr; · ipureintro; exact Reducible.fill K (reducible_urand σ₁')
  isplitr
  · ipureintro
    rw [primStep_rand_unit HN, primStep_fill Exp.urand_not_isValue, primStep_urand σ₁']
    exact Cfg.uniform_rel_uniformReal HN g hg σ₁ σ₁' K
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨r, hrsupp, heq1, heq2⟩
  cases heq1
  cases heq2
  iintro !> !>
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hb
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %r %hrsupp Hj'

end Wp

/-! ## Relational rules

Each is proved as in `AppRelRules`: unfold `refines`, merge the spec context `K2` with `K'`,
apply the `wp` rule, then split the context again for the continuation. -/

section Relational
variable [MicrometerRGS rT hlc GF] [BudgetCreditGS B GF] [L.IsLawful] [L.IsReflexive]
  [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind]

omit [L.IsReflexive] in
/-- Couple `urand ~ urand` along `S` within the budget `c`; spends `↯b c` (relational
`wp_couple_urand_urand_spend`). -/
theorem refines_couple_urands_spend {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF}
    (S : rT → rT → Prop) (c : B) (hc : IsAddLeftRegular c)
    (Hcpl : L.Rel c S unifUnit unifUnit) : iprop%
    ↯b c ∗ (∀ x y, ⌜S x y⌝ -∗
      refines L E (K.fill pl(#(.real x))) (K'.fill pl(#(.real y))) A) ⊢
    refines L E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  unfold refines
  iintro ⟨Hc, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_urand_urand_spend S c hc Hcpl (K2.comp K') ⊤ _
  iframe Hj Hc
  iintro %x %y %hS HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.real x : Val rT) = pl(#(.real x)) from rfl]
  iapply Hcnt $$ %x %y %hS %K2 %b HKres Hna Herr Hpos

omit [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] in
/-- Couple `urand ~ urand` by a step of `law`, spending `↯b c` and handing the leftover `R x y`
to the draws (relational `wp_couple_urand_urand_law`). -/
theorem refines_couple_urands_law (law : L.BindLaw) [law.HeadShift] [law.SideFree]
    {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} (R : rT → rT → B) (c : B)
    (hc : IsAddLeftRegular c)
    (hhead : ∀ (K : Ectx rT) σ σ', law.head
      (unifUnit.map fun x ↦ (⟨pl(#(.real x)), σ⟩ : Cfg rT))
      (unifUnit.map fun y ↦ (⟨K.fill pl(#(.real y)), σ'⟩ : Cfg rT))
      (Cfg.drawCostReal σ σ' K R) c) : iprop%
    ↯b c ∗ (∀ x y, ⌜R x y < (⊤ : B)⌝ -∗ ↯b (R x y) -∗
      refines L E (K.fill pl(#(.real x))) (K'.fill pl(#(.real y))) A) ⊢
    refines L E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  unfold refines
  iintro ⟨Hc, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_urand_urand_law law R c hc (K2.comp K') (hhead _) ⊤ _
  iframe Hj Hc
  iintro %x %y %hR Hr HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.real x : Val rT) = pl(#(.real x)) from rfl]
  iapply Hcnt $$ %x %y %hR Hr %K2 %b HKres Hna Herr Hpos

/-- Couple `urand ~ urand` along a measure-preserving `f`, redistributing `s ε₁` as
`s (ε₂ (f x))` (relational `wp_couple_urand_urand_adv`). -/
theorem refines_couple_urands_adv {s : ℝ≥0∞ →+o B} [L.IsExpectationAdditive s] {E : CoPset}
    {K K' : Ectx rT} {A : lrel rT GF} (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f unifUnit unifUnit) (ε₁ : ℝ≥0∞) (ε₂ : rT → ℝ≥0∞)
    (hε₂ : Measurable ε₂) (hamort : ∫⁻ y, ε₂ y ∂unifUnit ≤ ε₁)
    (hc : IsAddLeftRegular (s ε₁)) : iprop%
    ↯b (s ε₁) ∗ (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗ ↯b (s (ε₂ (f x))) -∗
      refines L E (K.fill pl(#(.real x))) (K'.fill pl(#(.real (f x)))) A) ⊢
    refines L E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  unfold refines
  iintro ⟨Hε, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_urand_urand_adv f hmp ε₁ ε₂ hε₂ hamort hc (K2.comp K') ⊤ _
  iframe Hj Hε
  iintro %x %hx - Hec HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.real x : Val rT) = pl(#(.real x)) from rfl]
  iapply Hcnt $$ %x %hx Hec %K2 %b HKres Hna Herr Hpos

/-- Couple `urand ~ urand` identically, avoiding the measurable set `Bad` for `s (unifUnit Bad)`
(relational `wp_couple_urand_urand_avoid`). -/
theorem refines_couple_urands_avoid {s : ℝ≥0∞ →+o B} [L.IsExpectationAdditive s]
    {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} (Bad : Set rT) (hBad : MeasurableSet Bad)
    (habs : L.Absorbing (s 1)) (hc : IsAddLeftRegular (s (unifUnit Bad))) : iprop%
    ↯b (s (unifUnit Bad)) ∗ (∀ x, ⌜x ∈ unifUnitSupport ∧ x ∉ Bad⌝ -∗
      refines L E (K.fill pl(#(.real x))) (K'.fill pl(#(.real x))) A) ⊢
    refines L E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  unfold refines
  iintro ⟨Hε, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_urand_urand_avoid Bad hBad habs hc (K2.comp K') ⊤ _
  iframe Hj Hε
  iintro %x %hx HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.real x : Val rT) = pl(#(.real x)) from rfl]
  iapply Hcnt $$ %x %hx %K2 %b HKres Hna Herr Hpos

/-- Couple `urand ~ rand N` along `g`, which pushes `unifUnit` to `unifInt N` (relational
`wp_couple_urand_rand`). -/
theorem refines_couple_urand_rand {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} (N : Int)
    (HN : 0 < N) (g : rT → Int)
    (hg : MeasureTheory.MeasurePreserving g unifUnit (unifInt N HN)) : iprop%
    (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗
      refines L E (K.fill pl(#(.real x))) (K'.fill pl(#(.int (g x)))) A) ⊢
    refines L E (K.fill pl(urand)) (K'.fill pl(rand(#(.int N), #(.unit)))) A := by
  unfold refines
  iintro Hcnt %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_urand_rand N HN g hg (K2.comp K') ⊤ _
  iframe Hj
  iintro %x %hx HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.real x : Val rT) = pl(#(.real x)) from rfl]
  iapply Hcnt $$ %x %hx %K2 %b HKres Hna Herr Hpos

/-- Couple `rand N ~ urand` along `g`, which pushes `unifUnit` to `unifInt N` (relational
`wp_couple_rand_urand`). -/
theorem refines_couple_rand_urand {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} (N : Int)
    (HN : 0 < N) (g : rT → Int)
    (hg : MeasureTheory.MeasurePreserving g unifUnit (unifInt N HN)) : iprop%
    (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗
      refines L E (K.fill pl(#(.int (g x)))) (K'.fill pl(#(.real x))) A) ⊢
    refines L E (K.fill pl(rand(#(.int N), #(.unit)))) (K'.fill pl(urand)) A := by
  unfold refines
  iintro Hcnt %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_urand N HN g hg (K2.comp K') ⊤ _
  iframe Hj
  iintro %x %hx HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int (g x) : Val rT) = pl(#(.int (g x))) from rfl]
  iapply Hcnt $$ %x %hx %K2 %b HKres Hna Herr Hpos

end Relational

end Rules

/-! ## Tactics -/

/-- `rel_couple_urands_spend S c hc Hcpl` couples `urand ~ urand` along `S`, spending `↯b c`
(relational `wp_couple_urand_urand_spend`). -/
macro "rel_couple_urands_spend " S:term:max ppSpace c:term:max ppSpace hc:term:max ppSpace
    H:term:max : tactic =>
  `(tactic| rel_apply (refines_couple_urands_spend $S $c $hc $H))

/-- `rel_couple_urands_law law R c hc hhead` couples `urand ~ urand` by a step of `law`,
spending `↯b c` and leaving `↯b (R x y)` (relational `wp_couple_urand_urand_law`). -/
macro "rel_couple_urands_law " law:term:max ppSpace R:term:max ppSpace c:term:max ppSpace
    hc:term:max ppSpace hhead:term:max : tactic =>
  `(tactic| rel_apply (refines_couple_urands_law $law $R $c $hc $hhead))

/-- `rel_couple_urands_adv f hmp ε₁ ε₂ hε₂ hamort hc` couples `urand ~ urand` along `f`, paying
`s (ε₂ (f x))` out of `s ε₁` (relational `wp_couple_urand_urand_adv`). -/
macro "rel_couple_urands_adv " f:term:max ppSpace hmp:term:max ppSpace e₁:term:max ppSpace
    e₂:term:max ppSpace he₂:term:max ppSpace ham:term:max ppSpace hc:term:max : tactic =>
  `(tactic| rel_apply (refines_couple_urands_adv $f $hmp $e₁ $e₂ $he₂ $ham $hc))

/-- `rel_couple_urands_avoid Bad hBad habs hc` couples `urand ~ urand` identically, avoiding
`Bad` (relational `wp_couple_urand_urand_avoid`). -/
macro "rel_couple_urands_avoid " Bad:term:max ppSpace hBad:term:max ppSpace habs:term:max
    ppSpace hc:term:max : tactic =>
  `(tactic| rel_apply (refines_couple_urands_avoid $Bad $hBad $habs $hc))

/-- `rel_couple_urand_rand g hg` couples `urand ~ rand N` along `g`
(relational `wp_couple_urand_rand`). -/
macro "rel_couple_urand_rand " g:term:max ppSpace hg:term:max : tactic =>
  `(tactic| rel_apply (refines_couple_urand_rand _ _ $g $hg))

/-- `rel_couple_rand_urand g hg` couples `rand N ~ urand` along `g`
(relational `wp_couple_rand_urand`). -/
macro "rel_couple_rand_urand " g:term:max ppSpace hg:term:max : tactic =>
  `(tactic| rel_apply (refines_couple_rand_urand _ _ $g $hg))

end ProbLang
