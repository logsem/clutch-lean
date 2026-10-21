module

public import Metrology.Code.NoisyCount
public import Metrology.Micrometer.Adequacy
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.WpTactics
public import Metrology.Couplings.Divergences.Laplace
public import Metrology.Micrometer.MechanismZcdp
public import Metrology.ProbLang.Reals
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Algebra.Regular.Prod
import Metrology.Iris.LocalBI

@[expose] public section

/-! # NoisyCount: a Laplace-noised count is `1/b`-DP

Adjacent databases have counts at most `1` apart, so one credit `↯b (1/b, 0)` pays for the Laplace
sampler call. Main result `noisyCount_DP`, conditional on the sampler spec `LaplaceSpec`. As
adjacency is symmetric, a terminating noisy count is also `(0, (1/b)² / 2)`-zCDP
(`noisyCount_zCDP`). -/

open scoped ENNReal NNReal

open Iris Iris.BI ProbabilityTheory Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp codensity codensity_complete dp_laplace)

namespace ProbLang
namespace NoisyCount

open Exp (ofVal)
open Finset (sum_sub_distrib sum_eq_single)
open ENNReal (ofReal)
open Kernel (zCDP_of_DP_of_symm DP_of_zCDP_sq)
open Real (log coe_toNNReal)

variable {lap : Val ℝ} {b : ℝ≥0} {n : ℕ}

/-- Assumed rule for the sampler `lap`: `lap #a` against a spec copy of `lap #a'` is coupled like a
primitive with law `laplace a b` in the lifting `L`, paying a cancellable credit `↯b c`. -/
def LaplaceSpec {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
    [OrderTop B] {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS ℝ hlc GF]
    [BudgetCreditGS B GF] (L : GradedLifting.{0} B) (lap : Val ℝ) (b : ℝ≥0) : Prop :=
  ∀ (a a' : ℝ) (S : ℝ → ℝ → Prop) (c : B) (K : Ectx ℝ) (E : CoPset) (Φ : Val ℝ → IProp GF),
    IsAddLeftRegular c → L.Rel c S (laplace a b) (laplace a' b) →
    (⤇ K.fill pl({ofVal lap} #a') ∗ ↯b c ∗
      (∀ x y, ⌜S x y⌝ -∗ ⤇ K.fill pl(#y) -∗ Φ (.real x)) ⊢
      wp L E pl({ofVal lap} #a) Φ)

/-- Databases that differ in at most one entry. -/
def Adjacent (db db' : Fin n → Bool) : Prop :=
  ∃ i, ∀ j, j ≠ i → db j = db' j

/-- Adjacent databases have counts at distance at most `1` (sensitivity 1). -/
theorem abs_count_sub_le {db db' : Fin n → Bool} (h : Adjacent db db') :
    |count db - count db'| ≤ 1 := by
  obtain ⟨i, hi⟩ := h
  rw [count, count, ← sum_sub_distrib,
    sum_eq_single i (fun j _ hj ↦ by simp [hi j hj]) (by simp)]
  cases db i <;> cases db' i <;> norm_num

/-- Adjacency of databases is symmetric. -/
instance : Std.Symm (Adjacent (n := n)) :=
  ⟨fun _ _ ⟨i, hi⟩ ↦ ⟨i, fun j hj ↦ (hi j hj).symm⟩⟩

/-! ## The program logic proof -/

/-- The privacy budget `(1/b, 0)`. -/
noncomputable abbrev budget (b : ℝ≥0) : ℝ≥0∞ × ℝ≥0∞ := (ofReal (1 / b), 0)

section Privacy

variable [Fact (0 < b)] {GF : BundledGFunctors} [MicrometerGS ℝ .hasNoLC GF]
  [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF]
local bi IProp GF

/-- The noisy counts of adjacent databases release the same value, spending `↯b (1/b, 0)`.
Conditional on the sampler spec `hlap`. -/
theorem wp_noisyCount (hlap : LaplaceSpec (GF := GF) (codensity dp) lap b)
    {db db' : Fin n → Bool} (h : Adjacent db db') :
    ⊢ ⤇ noisyCount lap db' -∗ ↯b (budget b) -∗
      wp (codensity dp) ⊤ (noisyCount lap db) (fun v ↦ iprop(∃ v', ⤇ ofVal v' ∗ ⌜v = v'⌝)) := by
  rw [spec_eq_fill_nil]
  iintro Hj Hb
  simp only [noisyCount]
  -- Spend the credit on the sampler spec: `dp_laplace` (sensitivity `1`) bounds the two laws,
  -- and `codensity_complete` turns that bound into an equality coupling.
  iapply hlap _ _ (· = ·) _ [] _ _ (by simp)
    (codensity_complete (dp_laplace (abs_count_sub_le h) b))
  iframe Hj Hb
  iintro %x %_ %rfl Hj
  iapply spec_fill_nil_exists (.real x) $$ Hj

/-! ## Adequacy: the DP statement -/

/-- The noisy count as a mechanism on databases, started from state `σ`. -/
noncomputable abbrev noisyCountMech (lap : Val ℝ) (n : ℕ) (σ : State ℝ) :
    Mechanism (Fin n → Bool) (Exp ℝ) :=
  progMech (noisyCount lap) σ

section Closed

variable
  (hlap : ∀ (_ : MicrometerGS ℝ .hasNoLC (MicrometerFunctor ℝ (ℝ≥0∞ × ℝ≥0∞)))
    (_ : BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) (MicrometerFunctor ℝ (ℝ≥0∞ × ℝ≥0∞))),
    LaplaceSpec (GF := MicrometerFunctor ℝ (ℝ≥0∞ × ℝ≥0∞)) (codensity dp) lap b) (σ : State ℝ)

include hlap

/-- The noisy count is `(1/b, 0)`-DP for adjacent databases (Def. 2.1). Conditional on the
sampler spec `hlap`, which is assumed for every ghost-state instance because adequacy allocates
its own. -/
theorem noisyCount_DP : (noisyCountMech lap n σ).DP Adjacent (ofReal (1 / b)) 0 :=
  fun _ _ h ↦ wp_adequacy_div _ _ σ σ _
    fun _ _ ↦ wp_noisyCount (hlap _ _) h

variable [IsMarkovKernel (noisyCountMech lap n σ)]

/-- The noisy count is `(0, (1/b)² / 2)`-zCDP for adjacent databases, given that it terminates
almost surely (Bun–Steinke 2016, Prop. 3.3). Conditional on the sampler spec `hlap`. -/
theorem noisyCount_zCDP : (noisyCountMech lap n σ).zCDP Adjacent 0 (ofReal ((1 / b) ^ 2 / 2)) := by
  have := zCDP_of_DP_of_symm (noisyCount_DP (n := n) hlap σ)
  rwa [coe_toNNReal _ (by positivity)] at this

/-- The noisy count is `((1/b)² / 2 + 2 √((1/b)² / 2 · log (1 / δ)), δ)`-DP at every slack
`0 < δ < 1`, given that it terminates almost surely. Conditional on the sampler spec `hlap`. -/
theorem noisyCount_DP_sqrt {δ : ℝ} (hδ : 0 < δ)
    (hδ₁ : δ < 1) :
    (noisyCountMech lap n σ).DP Adjacent
      (ofReal ((1 / b) ^ 2 / 2 + 2 * √((1 / b) ^ 2 / 2 * log (1 / δ))))
      (ofReal δ) := by
  have := DP_of_zCDP_sq hδ hδ₁
    (zCDP_of_DP_of_symm (noisyCount_DP (n := n) hlap σ))
  rwa [coe_toNNReal _ (by positivity)] at this

end Closed

end Privacy

end NoisyCount
end ProbLang
