module

public import Metrology.Code.NoisyCount
public import Metrology.Micrometer.Adequacy
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.WpTactics
public import Metrology.Couplings.Divergences.Laplace
public import Metrology.Micrometer.Mechanism
public import Metrology.ProbLang.Reals
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Algebra.Regular.Prod

@[expose] public section

/-! # The noisy count is `1/b`-differentially private

Adjacent databases have counts at distance at most `1`, so one credit `↯b (1/b, 0)` pays for the
Laplace noise. Every result is conditional on the sampler spec `LaplaceSpec`. -/

open scoped ENNReal NNReal

open Iris Iris.BI ProbabilityTheory Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp codensity codensity_complete dp_laplace)

namespace ProbLang
namespace NoisyCount

variable {lap : Val ℝ} {b : ℝ≥0} {n : ℕ}

/-- `lap #a` couples with a spec copy of `lap #a'` like a primitive sampler with law
`laplace a b` in the lifting `L`. -/
def LaplaceSpec {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
    [OrderTop B] {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS ℝ hlc GF]
    [BudgetCreditGS B GF] (L : GradedLifting.{0} B) (lap : Val ℝ) (b : ℝ≥0) : Prop :=
  ∀ (a a' : ℝ) (S : ℝ → ℝ → Prop) (c : B) (K : Ectx ℝ) (E : CoPset) (Φ : Val ℝ → IProp GF),
    IsAddLeftRegular c → L.Rel c S (laplace a b) (laplace a' b) →
    (⤇ K.fill pl({Exp.ofVal lap} #(.real a')) ∗ ↯b c ∗
      (∀ x y, ⌜S x y⌝ -∗ ⤇ K.fill pl(#(.real y)) -∗ Φ (.real x)) ⊢
      wp L E pl({Exp.ofVal lap} #(.real a)) Φ)

/-- Databases that differ in at most one entry. -/
def Adjacent (db db' : Fin n → Bool) : Prop :=
  ∃ i, ∀ j, j ≠ i → db j = db' j

theorem abs_count_sub_le {db db' : Fin n → Bool} (h : Adjacent db db') :
    |count db - count db'| ≤ 1 := by
  obtain ⟨i, hi⟩ := h
  rw [count, count, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single i (fun j _ hj ↦ by simp [hi j hj]) (by simp)]
  cases db i <;> cases db' i <;> norm_num

/-- The privacy budget `(1/b, 0)`. -/
noncomputable abbrev budget (b : ℝ≥0) : ℝ≥0∞ × ℝ≥0∞ := (ENNReal.ofReal (1 / b), 0)

/-- The noisy counts of adjacent databases release the same value, spending `↯b (1/b, 0)`.
Conditional on the sampler spec `hlap`. -/
theorem wp_noisyCount [Fact (0 < b)] {GF : BundledGFunctors} [MicrometerGS ℝ .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (hlap : LaplaceSpec (GF := GF) (codensity dp) lap b)
    {db db' : Fin n → Bool} (h : Adjacent db db') :
    ⊢@{IProp GF} ⤇ noisyCount lap db' -∗ ↯b (budget b) -∗
      wp (codensity dp) ⊤ (noisyCount lap db) (fun v ↦ iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝)) := by
  rw [spec_eq_fill_nil]
  iintro Hj Hb
  simp only [noisyCount]
  iapply hlap _ _ (· = ·) _ [] _ _ (by simp)
    (codensity_complete (dp_laplace (abs_count_sub_le h) b))
  iframe Hj Hb
  iintro %x %_ %rfl Hj
  iapply spec_fill_nil_exists (.real x) $$ Hj

/-- The noisy count on databases, started from state `σ`. -/
noncomputable abbrev noisyCountMech (lap : Val ℝ) (n : ℕ) (σ : State ℝ) :
    Mechanism (Fin n → Bool) (Exp ℝ) :=
  progMech (noisyCount lap) σ

/-- The noisy count is `(1/b, 0)`-DP for adjacent databases (Def. 2.1). Conditional on the
sampler spec `hlap`. -/
theorem noisyCount_DP [Fact (0 < b)]
    (hlap : ∀ (_ : MicrometerGS ℝ .hasNoLC (MicrometerFunctor ℝ (ℝ≥0∞ × ℝ≥0∞)))
      (_ : BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) (MicrometerFunctor ℝ (ℝ≥0∞ × ℝ≥0∞))),
      LaplaceSpec (GF := MicrometerFunctor ℝ (ℝ≥0∞ × ℝ≥0∞)) (codensity dp) lap b)
    (σ : State ℝ) : (noisyCountMech lap n σ).DP Adjacent (ENNReal.ofReal (1 / b)) 0 :=
  fun _ _ h ↦ wp_adequacy_div (GF := MicrometerFunctor ℝ (ℝ≥0∞ × ℝ≥0∞)) _ _ σ σ _
    fun _ _ ↦ wp_noisyCount (hlap _ _) h

end NoisyCount
end ProbLang
