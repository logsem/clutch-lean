module

public import Metrology.Micrometer.CouplingRulesLaw
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-! # Credit-paying couplings of continuous draws

The `urand` counterparts of the `rand` coupling rules, and couplings of `urand` with `rand N`
along a map pushing `unifUnit` to `unifInt N`. -/

@[expose] public section

open Iris hiding wp_bind
open Iris.Std Iris.BI Iris.ProofMode ProbLang ProbLang.MicrometerWpGS GradedLifting
open MeasureTheory (MeasurePreserving)
open scoped AppGS ENNReal

namespace ProbLang

open LawfulProbLangℝ
open Cfg Ectx Exp BudgetCredit BIFUpdate LawfulSet IsLawful IsTopAbsorbing Set
open MeasureTheory.Measure (map_map)
open _root_.Measurable (of_discrete)

variable {rT : Type} {B : Type} {L : GradedLifting.{0} B}

/-! ## Draw costs -/

/-- The leftover of the draws `urand ~ K[urand]` from `σ` and `σ'`: `R x y` at the configurations
drawn as `x` and `y`, and `⊤` elsewhere (the real counterpart of `Cfg.drawCost`). -/
noncomputable abbrev Cfg.drawCostReal [_root_.Top B] : State rT → State rT → Ectx rT →
    (rT → rT → B) → Cfg rT → Cfg rT → B :=
  drawCostOf BaseLit.real

/-- At the configurations drawn as `x` and `y`, `drawCostReal` is `R x y`. -/
theorem Cfg.drawCostReal_apply [_root_.Top B] (σ σ' : State rT) (K : Ectx rT)
    (R : rT → rT → B) (x y : rT) :
    drawCostReal σ σ' K R ⟨pl(#real x), σ⟩ ⟨K.fill pl(#real y), σ'⟩ = R x y :=
  drawCostOf_apply (fun _ _ ↦ BaseLit.real.inj) σ σ' K R x y

/-- A finite `drawCostReal` forces both configurations to be drawn ones. -/
theorem Cfg.exists_of_drawCostReal_lt_top [Preorder B] [OrderTop B] {σ σ' : State rT}
    {K : Ectx rT} {R : rT → rT → B} {ρ ρ' : Cfg rT}
    (h : drawCostReal σ σ' K R ρ ρ' < (⊤ : B)) :
    ∃ x y : rT, ρ = ⟨pl(#real x), σ⟩ ∧ ρ' = ⟨K.fill pl(#real y), σ'⟩ :=
  exists_of_drawCostOf_lt_top h

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

open Classical in
/-- The leftover of an expectation-paid coupling along `f`: `s (ε₂ y)` when `y = f x` for `x` in
the support, `⊤` otherwise. -/
noncomputable def advCostReal [_root_.Top B] (s : ℝ≥0∞ → B) (f : rT → rT) (ε₂ : rT → ℝ≥0∞)
    (x y : rT) : B :=
  if x ∈ unifUnitSupport ∧ f x = y then s (ε₂ y) else ⊤

/-- A finite `advCostReal` forces the coupled pair. -/
theorem advCostReal_of_lt_top [Preorder B] [OrderTop B] {s : ℝ≥0∞ → B} {f : rT → rT}
    {ε₂ : rT → ℝ≥0∞} {x y : rT} (h : advCostReal s f ε₂ x y < (⊤ : B)) :
    (x ∈ unifUnitSupport ∧ f x = y) ∧ advCostReal s f ε₂ x y = s (ε₂ y) := by
  by_cases hS : x ∈ unifUnitSupport ∧ f x = y
  · exact ⟨hS, ite_eq_left hS⟩
  · simp [advCostReal, hS] at h

/-! ## Liftings of `unifUnit` pushed to configurations -/

section Draws

variable (σ σ' : State rT) (K : Ectx rT)

/-- A lifting of two uniform reals lifts to their configurations, the right one in context `K`. -/
theorem Cfg.uniformReal_rel_fill [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful] {b : B}
    {S : rT → rT → Prop} {S' : Cfg rT → Cfg rT → Prop} (h : L.Rel b S unifUnit unifUnit)
    (hS : ∀ x y, S x y → S' ⟨pl(#real x), σ⟩ ⟨K.fill pl(#real y), σ'⟩) :
    L.Rel b S' (uniformReal σ) ((uniformReal σ').map K.fillCfg) := by
  rw [uniformReal, uniformReal, map_map (fillCfg.measurable K) (measurable_realLit σ')]
  exact h.map hS (measurable_realLit σ) ((fillCfg.measurable K).comp (measurable_realLit σ'))

/-- Coupling `urand ~ K[urand]` along a measure-preserving `f`, paying `s (ε₂ y)` at the right
draw `y` out of `s ε₁`, where `ε₁` bounds the mean of `ε₂`. -/
theorem Cfg.uniformReal_lift_adv [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
    [OrderTop B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] {s : ℝ≥0∞ →+o B}
    [L.IsExpectationAdditive s] (f : rT → rT)
    (hmp : MeasurePreserving f unifUnit unifUnit) (ε₁ : ℝ≥0∞) (ε₂ : rT → ℝ≥0∞)
    (hε₂ : Measurable ε₂) (hamort : ∫⁻ y, ε₂ y ∂unifUnit ≤ ε₁) :
    L (s ε₁) (drawCostReal σ σ' K (advCostReal s f ε₂))
      (uniformReal σ) ((uniformReal σ').map K.fillCfg) := by
  classical
  rw [uniformReal, uniformReal, map_map (fillCfg.measurable K) (measurable_realLit σ')]
  have h1 := IsExpectationAdditive.add_right (s := s) hε₂ (rel_graph_unifUnit (L := L) hmp)
  refine map (measurable_realLit σ) ((fillCfg.measurable K).comp (measurable_realLit σ'))
    (mono h1 (by rw [zero_add]; exact OrderHomClass.mono s hamort) fun x y => ?_)
  dsimp only [Function.comp_apply, fillCfg]
  rw [drawCostReal_apply]
  by_cases hS : f x = y ∧ x ∈ unifUnitSupport
  · rw [relCost_of (S := fun x y ↦ f x = y ∧ x ∈ unifUnitSupport) hS, zero_add, advCostReal,
      ite_eq_left ⟨hS.2, hS.1⟩]
  · rw [relCost_of_not (S := fun x y ↦ f x = y ∧ x ∈ unifUnitSupport) hS]
    exact le_top.trans le_self_add

/-! ## `urand` against `rand N` along a map -/

/-- Coupling the uniform real with a uniform integer along `g`, which pushes `unifUnit` to
`unifInt N`. -/
theorem Cfg.uniformReal_rel_uniform {N : Int} [Zero B] [Add B] [Preorder B] [OrderTop B]
    [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] (HN : 0 < N) (g : rT → Int)
    (hg : MeasurePreserving g unifUnit (unifInt N HN)) :
    L.Rel 0 (fun c₁ c₂ : Cfg rT => ∃ r, r ∈ unifUnitSupport ∧
        c₁ = ⟨pl(#real r), σ⟩ ∧ c₂ = ⟨K.fill pl(#int (g r)), σ'⟩)
      (uniformReal σ) ((uniform N σ').map K.fillCfg) := by
  rw [uniformReal, uniform_eq_map HN, map_map (fillCfg.measurable K) of_discrete]
  exact (rel_graph_unifUnit (L := L) hg).map (fun r _ ⟨hrr', hr⟩ => ⟨r, hr, rfl, hrr' ▸ rfl⟩)
    (measurable_realLit σ) ((fillCfg.measurable K).comp of_discrete)

/-- Coupling a uniform integer with the uniform real, the integer being `g` of the real. -/
theorem Cfg.uniform_rel_uniformReal {N : Int} [Zero B] [Add B] [Preorder B] [OrderTop B]
    [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] (HN : 0 < N) (g : rT → Int)
    (hg : MeasurePreserving g unifUnit (unifInt N HN)) :
    L.Rel 0 (fun c₁ c₂ : Cfg rT => ∃ r, r ∈ unifUnitSupport ∧
        c₁ = ⟨pl(#int (g r)), σ⟩ ∧ c₂ = ⟨K.fill pl(#real r), σ'⟩)
      (uniform N σ) ((uniformReal σ').map K.fillCfg) := by
  have h := (IsReflexive.refl (L := L) (unifUnit (T := rT))).restrict unifUnitSupportMeasurable
    unifUnitIsConcentrated
  rw [uniform_eq_map HN, ← hg.map_eq, map_map of_discrete hg.measurable, uniformReal,
    map_map (fillCfg.measurable K) (measurable_realLit σ')]
  exact h.map (fun r _ ⟨hrr', hr⟩ => ⟨r, hr, rfl, hrr' ▸ rfl⟩) (of_discrete.comp hg.measurable)
    ((fillCfg.measurable K).comp (measurable_realLit σ'))

end Draws

/-! ## Program rules -/

section Rules
variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {hlc : HasLC} {GF : BundledGFunctors} [BudgetCreditGS B GF] [L.IsLawful] [L.IsTopAbsorbing]
local bi IProp GF

section Wp
variable [MicrometerGS rT hlc GF]

/-- Couple `urand ~ K[urand]` by a step of `law`, spending `↯b c` on its head and handing the
leftover `R x y` to the draws `x` and `y` (the `urand` form of `wp_couple_rand_rand_law`). -/
theorem wp_couple_urand_urand_law (law : L.BindLaw) [law.HeadShift] [law.SideFree]
    (R : rT → rT → B) (c : B) (hc : IsAddLeftRegular c) (K : Ectx rT)
    (hhead : ∀ σ σ', law.head (unifUnit.map fun x ↦ (⟨pl(#real x), σ⟩ : Cfg rT))
      (unifUnit.map fun y ↦ (⟨K.fill pl(#real y), σ'⟩ : Cfg rT))
      (drawCostReal σ σ' K R) c)
    (E : CoPset) (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(urand) ∗ ↯b c ∗
      (∀ x y, ⌜R x y < (⊤ : B)⌝ -∗ ↯b (R x y) -∗ ⤇ K.fill pl(#real y) -∗ Φ (.real x)) ⊢
      wp L E pl(urand) Φ := by
  refine wp_couple_prim_law law (fun _ _ ↦ BaseLit.real.inj) urand_toVal?_eq_none
    reducible_urand reducible_urand R c hc K (fun σ σ' ↦ ?_) E Φ
  rw [primStep_urand, primStep_fill urand_not_isValue, primStep_urand, uniformReal, uniformReal,
    map_map (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
      (fillCfg.measurable K) (measurable_realLit σ')]
  exact hhead σ σ'

section Bind
variable [L.IsSupportLocal] [L.HasBind]

/-- Couple `urand ~ K[urand]` along `S`, given a lifting of the two uniform reals within the
cancelable budget `c`; spends `↯b c` (the `urand` form of `wp_couple_rand_rand_spend`). -/
theorem wp_couple_urand_urand_spend (S : rT → rT → Prop) (c : B) (hc : IsAddLeftRegular c)
    (Hcpl : L.Rel c S unifUnit unifUnit) (K : Ectx rT) (E : CoPset) (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(urand) ∗ ↯b c ∗
      (∀ x y, ⌜S x y⌝ -∗ ⤇ K.fill pl(#real y) -∗ Φ (.real x)) ⊢
      wp L E pl(urand) Φ := by
  refine wp_couple_prim_lift (ℓ := BaseLit.real) (ℓ' := BaseLit.real) urand_toVal?_eq_none
    reducible_urand reducible_urand S c hc K (fun σ σ' ↦ ?_) E Φ
  rw [primStep_urand, primStep_fill urand_not_isValue, primStep_urand]
  exact uniformReal_rel_fill σ σ' K Hcpl fun x y h ↦ ⟨x, y, h, rfl, rfl⟩

section Reflexive
variable [L.IsReflexive]

/-- Couple `urand ~ K[urand]` along a measure-preserving `f`, turning `↯b (s ε₁)` into
`↯b (s (ε₂ (f x)))` at the draw `x`, where `ε₁` bounds the mean of `ε₂` (the `urand` form of
`wp_couple_rand_rand_adv`). -/
theorem wp_couple_urand_urand_adv {s : ℝ≥0∞ →+o B} [L.IsExpectationAdditive s] (f : rT → rT)
    (hmp : MeasurePreserving f unifUnit unifUnit) (ε₁ : ℝ≥0∞) (ε₂ : rT → ℝ≥0∞)
    (hε₂ : Measurable ε₂) (hamort : ∫⁻ y, ε₂ y ∂unifUnit ≤ ε₁) (hc : IsAddLeftRegular (s ε₁))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(urand) ∗ ↯b (s ε₁) ∗
      (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗ ⌜¬ L.Absorbing (s (ε₂ (f x)))⌝ -∗ ↯b (s (ε₂ (f x))) -∗
        ⤇ K.fill pl(#real (f x)) -∗ Φ (.real x)) ⊢
      wp L E pl(urand) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_lift_prim_steps_coupl_adv_absorbing urand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  have hredL := reducible_urand σ₁
  have hredR := (reducible_urand σ₁').fill K
  imod supply_decrease hc $$ Hb Herr with ⟨%r, %hr, Hb⟩
  imod subset empty_subset with Hclose
  have hb : s ε₁ + r ≤ b := hr.ge
  imodintro
  have hlift : L (s ε₁) (drawCostReal σ₁ σ₁' K (advCostReal s f ε₂))
      (primStep ⟨pl(urand), σ₁⟩) (primStep ⟨K.fill pl(urand), σ₁'⟩) := by
    rw [primStep_urand, primStep_fill urand_not_isValue, primStep_urand]
    exact uniformReal_lift_adv σ₁ σ₁' K f hmp ε₁ ε₂ hε₂ hamort
  iexists drawCostReal σ₁ σ₁' K (advCostReal s f ε₂), s ε₁, r
  iframe %hb %hredL %hredR %hlift
  iintro %e₂ %σ₂ %e₂' %σ₂' !>
  -- leftover absorbing: exit left; otherwise it is finite, so the pair is a coupled draw
  by_cases habs : L.Absorbing (drawCostReal σ₁ σ₁' K (advCostReal s f ε₂) ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + r)
  · imod Hclose
    imodintro
    ileft
    ipureintro
    exact habs
  have hlt : drawCostReal σ₁ σ₁' K (advCostReal s f ε₂) ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B) := by
    by_contra h
    exact habs (absorbing_top.mono (not_lt_top_iff.1 h ▸ le_self_add))
  obtain ⟨x, y, h1, h2⟩ := exists_of_drawCostReal_lt_top hlt
  obtain ⟨rfl, rfl⟩ := (mk.injEq ..).mp h1
  obtain ⟨rfl, rfl⟩ := (mk.injEq ..).mp h2
  rw [drawCostReal_apply] at habs hlt ⊢
  obtain ⟨⟨hx, rfl⟩, hcost⟩ := advCostReal_of_lt_top hlt
  rw [hcost] at habs ⊢
  have hna : ¬ L.Absorbing (s (ε₂ (f x))) := fun h => habs (h.mono le_self_add)
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod supply_increase $$ Hb with ⟨Hb, Hfrag⟩
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
theorem wp_couple_urand_urand_avoid {s : ℝ≥0∞ →+o B} [L.IsExpectationAdditive s]
    (Bad : Set rT) (hBad : MeasurableSet Bad) (habs : L.Absorbing (s 1))
    (hc : IsAddLeftRegular (s (unifUnit Bad))) (K : Ectx rT) (E : CoPset) (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(urand) ∗ ↯b (s (unifUnit Bad)) ∗
      (∀ x, ⌜x ∈ unifUnitSupport ∧ x ∉ Bad⌝ -∗ ⤇ K.fill pl(#real x) -∗ Φ (.real x)) ⊢
      wp L E pl(urand) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_couple_urand_urand_adv id (MeasurePreserving.id _) (unifUnit Bad)
    (Bad.indicator 1) (measurable_one.indicator hBad)
    (by rw [MeasureTheory.lintegral_indicator_one hBad]) hc K E Φ
  iframe Hj Herr
  iintro %x %hx %hna - Hj'
  by_cases hb : x ∈ Bad
  · simp only [id_eq, indicator_of_mem hb, Pi.one_apply] at hna
    exact (hna habs).elim
  · simp only [id_eq]
    iapply Hcnt $$ %x %⟨hx, hb⟩ Hj'

/-- Couple `urand ~ K[rand N]` along `g`, which pushes `unifUnit` to `unifInt N`: the left draw is
`x`, the right draw is `g x` (at `ℝ`, `g u = ⌊N u⌋`, `measurePreserving_floor_mul`). -/
theorem wp_couple_urand_rand (N : Int) (HN : 0 < N) (g : rT → Int)
    (hg : MeasurePreserving g unifUnit (unifInt N HN)) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(rand(#N, #())) ∗
      (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗ ⤇ K.fill pl(#int (g x)) -∗ Φ (.real x)) ⊢
      wp L E pl(urand) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply wp_couple_prim_lift_zero (ℓ := BaseLit.real) (ℓ' := BaseLit.int)
    (S := fun x n ↦ x ∈ unifUnitSupport ∧ n = g x) urand_toVal?_eq_none reducible_urand
    reducible_rand_unit K (fun σ σ' ↦ ?_) E Φ
  · rw [primStep_urand, primStep_fill rand_not_isValue, primStep_rand_unit N]
    exact (uniformReal_rel_uniform σ σ' K HN g hg).mono le_rfl
      fun _ _ ⟨r, hr, h1, h2⟩ ↦ ⟨r, g r, ⟨hr, rfl⟩, h1, h2⟩
  · iframe Hj
    iintro %x %n %⟨hx, rfl⟩ Hj'
    iapply Hcnt $$ %x %hx Hj'

/-- Couple `rand N ~ K[urand]` along `g`, which pushes `unifUnit` to `unifInt N`: the right draw
is `x`, the left draw is `g x`. -/
theorem wp_couple_rand_urand (N : Int) (HN : 0 < N) (g : rT → Int)
    (hg : MeasurePreserving g unifUnit (unifInt N HN)) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(urand) ∗
      (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗ ⤇ K.fill pl(#real x) -∗ Φ (.int (g x))) ⊢
      wp L E pl(rand(#N, #())) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply wp_couple_prim_lift_zero (ℓ := BaseLit.int) (ℓ' := BaseLit.real)
    (S := fun n x ↦ x ∈ unifUnitSupport ∧ n = g x)
    rand_toVal?_eq_none reducible_rand_unit reducible_urand K (fun σ σ' ↦ ?_) E Φ
  · rw [primStep_rand_unit N, primStep_fill urand_not_isValue, primStep_urand]
    exact (uniform_rel_uniformReal σ σ' K HN g hg).mono le_rfl
      fun _ _ ⟨r, hr, h1, h2⟩ ↦ ⟨g r, r, ⟨hr, rfl⟩, h1, h2⟩
  · iframe Hj
    iintro %n %x %⟨hx, rfl⟩ Hj'
    iapply Hcnt $$ %x %hx Hj'

end Reflexive

end Bind

end Wp

/-! ## Relational rules

Each is proved as in `AppRelRules`: unfold `refines`, merge the spec context `K2` with `K'`,
apply the `wp` rule, then split the context again for the continuation. -/

section Relational
variable [MicrometerRGS rT hlc GF]
  {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF}

/-- Couple `urand ~ urand` by a step of `law`, spending `↯b c` and handing the leftover `R x y`
to the draws (relational `wp_couple_urand_urand_law`). -/
theorem refines_couple_urands_law (law : L.BindLaw) [law.HeadShift] [law.SideFree]
    (R : rT → rT → B) (c : B) (hc : IsAddLeftRegular c)
    (hhead : ∀ (K : Ectx rT) σ σ', law.head (unifUnit.map fun x ↦ (⟨pl(#real x), σ⟩ : Cfg rT))
      (unifUnit.map fun y ↦ (⟨K.fill pl(#real y), σ'⟩ : Cfg rT))
      (drawCostReal σ σ' K R) c) : iprop%
    ↯b c ∗ (∀ x y, ⌜R x y < (⊤ : B)⌝ -∗ ↯b (R x y) -∗
        refines L E (K.fill pl(#real x)) (K'.fill pl(#real y)) A) ⊢
      refines L E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  unfold refines
  iintro ⟨Hc, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply wp_bind
  iapply wp_couple_urand_urand_law law R c hc (K2.comp K') (hhead _) ⊤ _
  iframe Hj Hc
  iintro %x %y %hR Hr HKres
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.real x) = pl(#real x) from rfl]
  iapply Hcnt $$ %x %y %hR Hr %K2 %b HKres Hna Herr Hpos

section Bind
variable [L.IsSupportLocal] [L.HasBind]

/-- Couple `urand ~ urand` along `S` within the budget `c`; spends `↯b c` (relational
`wp_couple_urand_urand_spend`). -/
theorem refines_couple_urands_spend (S : rT → rT → Prop) (c : B) (hc : IsAddLeftRegular c)
    (Hcpl : L.Rel c S unifUnit unifUnit) : iprop%
    ↯b c ∗ (∀ x y, ⌜S x y⌝ -∗
        refines L E (K.fill pl(#real x)) (K'.fill pl(#real y)) A) ⊢
      refines L E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  unfold refines
  iintro ⟨Hc, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply wp_bind
  iapply wp_couple_urand_urand_spend S c hc Hcpl (K2.comp K') ⊤ _
  iframe Hj Hc
  iintro %x %y %hS HKres
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.real x) = pl(#real x) from rfl]
  iapply Hcnt $$ %x %y %hS %K2 %b HKres Hna Herr Hpos

section Reflexive
variable [L.IsReflexive]

/-- Couple `urand ~ urand` along a measure-preserving `f`, redistributing `s ε₁` as
`s (ε₂ (f x))` (relational `wp_couple_urand_urand_adv`). -/
theorem refines_couple_urands_adv {s : ℝ≥0∞ →+o B} [L.IsExpectationAdditive s] (f : rT → rT)
    (hmp : MeasurePreserving f unifUnit unifUnit) (ε₁ : ℝ≥0∞) (ε₂ : rT → ℝ≥0∞)
    (hε₂ : Measurable ε₂) (hamort : ∫⁻ y, ε₂ y ∂unifUnit ≤ ε₁)
    (hc : IsAddLeftRegular (s ε₁)) : iprop%
    ↯b (s ε₁) ∗ (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗ ↯b (s (ε₂ (f x))) -∗
        refines L E (K.fill pl(#real x)) (K'.fill pl(#real (f x))) A) ⊢
      refines L E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  unfold refines
  iintro ⟨Hε, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply wp_bind
  iapply wp_couple_urand_urand_adv f hmp ε₁ ε₂ hε₂ hamort hc (K2.comp K') ⊤ _
  iframe Hj Hε
  iintro %x %hx - Hec HKres
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.real x) = pl(#real x) from rfl]
  iapply Hcnt $$ %x %hx Hec %K2 %b HKres Hna Herr Hpos

/-- Couple `urand ~ urand` identically, avoiding the measurable set `Bad` for `s (unifUnit Bad)`
(relational `wp_couple_urand_urand_avoid`). -/
theorem refines_couple_urands_avoid {s : ℝ≥0∞ →+o B} [L.IsExpectationAdditive s]
    (Bad : Set rT) (hBad : MeasurableSet Bad)
    (habs : L.Absorbing (s 1)) (hc : IsAddLeftRegular (s (unifUnit Bad))) : iprop%
    ↯b (s (unifUnit Bad)) ∗ (∀ x, ⌜x ∈ unifUnitSupport ∧ x ∉ Bad⌝ -∗
        refines L E (K.fill pl(#real x)) (K'.fill pl(#real x)) A) ⊢
      refines L E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  unfold refines
  iintro ⟨Hε, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply wp_bind
  iapply wp_couple_urand_urand_avoid Bad hBad habs hc (K2.comp K') ⊤ _
  iframe Hj Hε
  iintro %x %hx HKres
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.real x) = pl(#real x) from rfl]
  iapply Hcnt $$ %x %hx %K2 %b HKres Hna Herr Hpos

/-- Couple `urand ~ rand N` along `g`, which pushes `unifUnit` to `unifInt N` (relational
`wp_couple_urand_rand`). -/
theorem refines_couple_urand_rand (N : Int) (HN : 0 < N) (g : rT → Int)
    (hg : MeasurePreserving g unifUnit (unifInt N HN)) : iprop%
    (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗
        refines L E (K.fill pl(#real x)) (K'.fill pl(#int (g x))) A) ⊢
      refines L E (K.fill pl(urand)) (K'.fill pl(rand(#N, #()))) A := by
  unfold refines
  iintro Hcnt %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply wp_bind
  iapply wp_couple_urand_rand N HN g hg (K2.comp K') ⊤ _
  iframe Hj
  iintro %x %hx HKres
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.real x) = pl(#real x) from rfl]
  iapply Hcnt $$ %x %hx %K2 %b HKres Hna Herr Hpos

/-- Couple `rand N ~ urand` along `g`, which pushes `unifUnit` to `unifInt N` (relational
`wp_couple_rand_urand`). -/
theorem refines_couple_rand_urand (N : Int) (HN : 0 < N) (g : rT → Int)
    (hg : MeasurePreserving g unifUnit (unifInt N HN)) : iprop%
    (∀ x, ⌜x ∈ unifUnitSupport⌝ -∗
        refines L E (K.fill pl(#int (g x))) (K'.fill pl(#real x)) A) ⊢
      refines L E (K.fill pl(rand(#N, #()))) (K'.fill pl(urand)) A := by
  unfold refines
  iintro Hcnt %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply wp_bind
  iapply wp_couple_rand_urand N HN g hg (K2.comp K') ⊤ _
  iframe Hj
  iintro %x %hx HKres
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.int (g x)) = pl(#int (g x)) from rfl]
  iapply Hcnt $$ %x %hx %K2 %b HKres Hna Herr Hpos

end Reflexive

end Bind

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
