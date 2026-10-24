module

public import Metrology.Micrometer.ContinuousCouplings
public import Metrology.Couplings.Divergences.Tv
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-! # Sanity uses of the coupling rules for continuous draws

One short use of each rule of `ContinuousCouplings` and of the `rand` tactics. -/

@[expose] public section

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace ContinuousRules

open LawfulProbLangℝ
open Set (Icc inter_subset_left)
open Exp (lit_isClosedEmpty)

variable {GF : BundledGFunctors}
local bi IProp GF

/-- At `ℝ`, `urand ~ rand N` along `u ↦ ⌊N u⌋`: the spec draw is the floor of `N` times the
program's. -/
theorem wp_urand_floor_real [MicrometerGS ℝ .hasNoLC GF] [BudgetCreditGS ℝ≥0∞ GF] (N : Int)
    (hN : 0 < N) :
    ⤇ pl(rand(#N, #())) ⊢
      wp (codensity tv) ⊤ (pl(urand) : Exp ℝ) fun v ↦
        iprop(∃ x : ℝ, ⌜v = .real x ∧ 0 < x ∧ x < 1⌝ ∗ ⤇ pl(#int (⌊(N : ℝ) * x⌋))) := by
  iintro Hj
  iapply wp_couple_urand_rand (K := []) N hN _ (measurePreserving_floor_mul N hN)
  simp only [Ectx.fill_nil]
  iframe Hj
  iintro %x %hx Hj'
  iexists x
  iframe Hj'
  ipureintro
  exact ⟨rfl, hx⟩

open MeasureTheory

section Generic

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B] [CanonicallyOrderedAdd B]
  {L : GradedLifting.{0} B} [L.IsLawful] [L.IsTopAbsorbing]
  [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS B GF]

/-! ## `urand ~ urand` -/

/-- A law step whose finite leftovers sit on the diagonal returns the same real. -/
theorem urands_law (law : L.BindLaw) [law.HeadShift] [law.SideFree] (R : rT → rT → B) (c : B)
    (hc : IsAddLeftRegular c)
    (hhead : ∀ (K : Ectx rT) σ σ', law.head (unifUnit.map fun x ↦ (⟨pl(#real x), σ⟩ : Cfg rT))
      (unifUnit.map fun y ↦ (⟨K.fill pl(#real y), σ'⟩ : Cfg rT))
      (Cfg.drawCostReal σ σ' K R) c)
    (hR : ∀ x y, R x y < (⊤ : B) → x = y) :
    ⊢ ↯b c -∗ REL[L] (pl(urand) : Exp rT) << pl(urand) : lrel_real := by
  iintro Hc
  rel_couple_urands_law law R c hc hhead
  iframe Hc
  iintro %x %y %hxy -
  obtain rfl := hR x y hxy
  rel_values

section SupportLocal

variable [L.IsSupportLocal] [L.HasBind]

/-- Two draws coupled at equality within `c` return the same real. -/
theorem urands_spend (c : B) (hc : IsAddLeftRegular c)
    (Hcpl : L.Rel c (· = ·) (unifUnit (T := rT)) unifUnit) :
    ⊢ ↯b c -∗ REL[L] (pl(urand) : Exp rT) << pl(urand) : lrel_real := by
  iintro Hc
  rel_couple_urands_spend (· = ·) c hc Hcpl
  iframe Hc
  iintro %x %y %rfl
  rel_values

section Reflexive

variable [L.IsReflexive] {s : ℝ≥0∞ →+o B} [L.IsExpectationAdditive s]

/-- Two draws coupled along the identity, spending `s ε` in expectation, return the same real. -/
theorem urands_adv (ε : ℝ≥0∞) (hc : IsAddLeftRegular (s ε)) :
    ⊢ ↯b (s ε) -∗
      REL[L] (pl(urand) : Exp rT) << pl(urand) : lrel_real := by
  iintro Hc
  rel_couple_urands_adv id (MeasurePreserving.id _) ε (fun _ ↦ ε) measurable_const (by simp) hc
  iframe Hc
  iintro %x %_ -
  simp only [id_eq]
  rel_values

/-- Avoiding a measurable set `Bad` of left draws costs its mass. -/
theorem urands_avoid (Bad : Set rT) (hBad : MeasurableSet Bad) (habs : L.Absorbing (s 1))
    (hc : IsAddLeftRegular (s (unifUnit Bad))) :
    ⊢ ↯b (s (unifUnit Bad)) -∗
      REL[L] (pl(urand) : Exp rT) << pl(urand) : lrel_real := by
  iintro Hc
  rel_couple_urands_avoid Bad hBad habs hc
  iframe Hc
  iintro %x %_
  rel_values

/-! ## `rand ~ rand`: the tactic forms -/

/-- Coupling along the identity with credits paid in expectation returns the same integer. -/
theorem rands_adv (N : Int) (hN : 0 < N)
    (ε₁ : ℝ≥0∞) (ε₂ : Int → ℝ≥0∞) (hamort : (∑ n ∈ Finset.Ico 0 N, ε₂ n) / N.toNat ≤ ε₁)
    (hc : IsAddLeftRegular (s ε₁)) :
    ⊢ ↯b (s ε₁) -∗
      REL[L] (pl(rand(#N, #())) : Exp rT) << pl(rand(#N, #())) : lrel_int := by
  iintro Hc
  rel_couple_UU_adv id ε₁ ε₂ id_dom_range id_bij_range hamort hc
  iframe Hc
  iintro %n %_ -
  simp only [id_eq]
  rel_values

/-- Avoiding one outcome costs `s (1/N)`. -/
theorem rands_avoid (N bad : Int) (hN : 0 < N)
    (habs : L.Absorbing (s 1)) (hc : IsAddLeftRegular (s (N.toNat : ℝ≥0∞)⁻¹)) :
    ⊢ ↯b (s (N.toNat : ℝ≥0∞)⁻¹) -∗
      REL[L] (pl(rand(#N, #())) : Exp rT) << pl(rand(#N, #())) : lrel_int := by
  iintro Hc
  rel_couple_UU_avoid bad habs hc
  iframe Hc
  iintro %n %_
  rel_values

end Reflexive

end SupportLocal

/-- The DP choice rule along two equality couplings returns the same integer. -/
theorem rands_dpChoice [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (N : Int) (hN : 0 < N)
    {ε₁ δ₁ ε₁' δ₁' ε₂ ε₂' δ₂ : ℝ≥0∞} {P T : Set Int}
    (h₁ : (codensity dp).Rel (ε₁, δ₁) (· = ·) (unifInt N hN) (unifInt N hN))
    (h₂ : (codensity dp).Rel (ε₁', δ₁') (· = ·) (unifInt N hN) (unifInt N hN))
    (hPT₁ : ∀ r r', r ∈ P → r = r' → r' ∈ T) (hPT₂ : ∀ r r', r ∉ P → r = r' → r' ∉ T)
    (hc : IsAddLeftRegular ((max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) : ℝ≥0∞ × ℝ≥0∞)) :
    ⊢ ↯b (max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) -∗
      REL[codensity dp] (pl(rand(#N, #())) : Exp rT) << pl(rand(#N, #())) : lrel_int := by
  iintro Hc
  rel_couple_UU_dpChoice h₁ h₂ hPT₁ hPT₂ hc
  iframe Hc
  iintro %r %_ %(rfl | rfl) -
  all_goals rel_values

end Generic

/-! ## At `ℝ` -/

section Real

private theorem lrel_true_lit [MicrometerRGS ℝ .hasNoLC GF] {l₁ l₂ : BaseLit ℝ} :
    ⊢ |={⊤}=> (lrel_true (rT := ℝ) (GF := GF)).car (l₁ : Val ℝ) l₂ := by
  iunfold lrel_true
  ipureintro
  exact ⟨lit_isClosedEmpty _, lit_isClosedEmpty _⟩

variable [MicrometerRGS ℝ .hasNoLC GF] [BudgetCreditGS ℝ≥0∞ GF]

/-- A uniform real avoids `0` for free: the point has no mass. -/
theorem urand_avoid_zero_real :
    ⊢ ↯b (0 : ℝ≥0∞) -∗
      REL[codensity tv] (pl(urand) : Exp ℝ) << pl(urand) : lrel_real := by
  have h0 : unifUnit ({0} : Set ℝ) = 0 := by
    show volume.restrict (Icc (0 : ℝ) 1) {0} = 0
    rw [Measure.restrict_apply (measurableSet_singleton 0)]
    exact measure_mono_null inter_subset_left Real.volume_singleton
  simpa [h0] using urands_avoid (L := codensity tv) (s := .id ℝ≥0∞) ({0} : Set ℝ)
    (measurableSet_singleton 0) absorbing_codensity_tv_one (by simp [h0])

variable (N : Int) (hN : 0 < N)
include hN

/-- At `ℝ`, `rand N ~ urand` along `u ↦ ⌊N u⌋`, as a refinement. -/
theorem rand_urand_floor_real :
    ⊢ REL[codensity tv] (pl(rand(#N, #())) : Exp ℝ) << pl(urand) : lrel_true := by
  rel_couple_rand_urand _ (measurePreserving_floor_mul N hN)
  iintro %x %_
  rel_values
  exact lrel_true_lit

/-- At `ℝ`, `urand ~ rand N` along `u ↦ ⌊N u⌋`, as a refinement. -/
theorem urand_rand_floor_real :
    ⊢ REL[codensity tv] (pl(urand) : Exp ℝ) << pl(rand(#N, #())) : lrel_true := by
  rel_couple_urand_rand _ (measurePreserving_floor_mul N hN)
  iintro %x %_
  rel_values
  exact lrel_true_lit

end Real

end ContinuousRules
end ProbLang
