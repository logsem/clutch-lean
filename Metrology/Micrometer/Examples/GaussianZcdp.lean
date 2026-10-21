module

public import Metrology.Micrometer.Adequacy
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.CouplingRules
public import Metrology.Micrometer.WpTactics
public import Metrology.Code.GaussianRelease
public import Metrology.Couplings.Divergences.GaussianRenyi
public import Metrology.Couplings.Divergences.Conversions
public import Metrology.ProbLang.Reals
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Algebra.Regular.Prod
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Repeated Gaussian release is zCDP (Rocq `gen_zcdp_gaussian.v`)

`release gauss a k` draws `k` Gaussian samples centred at `a`. Each draw spends
`(0, (a - a')² / (2 v))` in `zcdpLifting`, so `release_zcdp` gives zCDP and `release_dp_sqrt` gives
DP with `ε` of order `√k`. Every result is conditional on the sampler spec `GaussSpec`. -/

open scoped ENNReal NNReal

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting ProbabilityTheory
open GradedDivergence

namespace ProbLang
namespace GaussianRelease

open ENNReal (ofReal ofReal_mul ofReal_natCast ofReal_le_ofReal toReal_ofReal ofReal_add)
open Exp (ofVal)
open Nat (cast_succ cast_nonneg)
open Prod (mk_add_mk mk_le_mk)
open Real (log)
open LiftingRelHom (zcdpToDp zcdpToDp_map)

variable {gauss : Val ℝ} {v : ℝ≥0}

/-! ## The per-draw cost -/

/-- The zCDP cost `(a - a')² / (2 v)` of one release. -/
noncomputable abbrev cost (v : ℝ≥0) (a a' : ℝ) : ℝ≥0∞ := ofReal ((a - a') ^ 2 / (2 * v))

/-- The budget of `k + 1` releases is one release's budget plus that of `k`. -/
theorem budget_succ (k : ℕ) (ρ : ℝ≥0∞) :
    ((0 : ℝ≥0∞), ((k + 1 : ℕ) : ℝ≥0∞) * ρ) = (0, ρ) + (0, k * ρ) := by
  rw [mk_add_mk, add_zero, cast_succ, add_one_mul, add_comm]

section Logic

variable {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS ℝ hlc GF]
local bi IProp GF

/-! ## The sampler spec -/

section Spec

variable {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  [BudgetCreditGS B GF]

/-- The assumed spec of `gauss`: `gauss #a` couples with a spec copy of `gauss #a'` like a primitive
sampler with law `N(a, v)` in the lifting `L` (the shape of `wp_couple_rand_rand_spend`). -/
def GaussSpec (L : GradedLifting.{0} B) (gauss : Val ℝ) (v : ℝ≥0) : Prop :=
  ∀ (a a' : ℝ) (S : ℝ → ℝ → Prop) (c : B) (K : Ectx ℝ) (E : CoPset) (Φ : Val ℝ → _),
    IsAddLeftRegular c → L.Rel c S (gaussianReal a v) (gaussianReal a' v) →
    (⤇ K.fill pl({ofVal gauss} #a') ∗ ↯b c ∗
      (∀ x y, ⌜S x y⌝ -∗ ⤇ K.fill pl(#real y) -∗ Φ (.real x)) ⊢
      wp L E pl({ofVal gauss} #a) Φ)

end Spec

/-! ## The program logic proof: `k` releases spend `k` times the cost -/

variable [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF]

section Release

variable (hv : v ≠ 0) (hgauss : GaussSpec (GF := GF) zcdpLifting gauss v) (a a' : ℝ) (k : ℕ)

include hv hgauss

/-- `k` releases against the spec in context `K`, spending `(0, (a - a')² / (2 v))` per release:
both sides release the same tuple. Conditional on the sampler spec `hgauss`. -/
theorem wp_release_fill (K : Ectx ℝ) (Φ : Val ℝ → _) :
    ⤇ K.fill (release gauss a' k) ∗ ↯b ((0 : ℝ≥0∞), (k : ℝ≥0∞) * cost v a a') ∗
      (∀ w, ⤇ K.fill (ofVal w) -∗ Φ w) ⊢
      wp zcdpLifting ⊤ (release gauss a k) Φ := by
  induction k generalizing K Φ with
  | zero =>
    iintro ⟨Hj, -, H⟩
    simp only [release]
    wp_pures
    tp_pures
    wp_value
    imodintro
    iapply H
    iapply specProgFrag_reshape (e₁ := K.fill pl(#())) (e₂ := K.fill (ofVal .unit)) rfl
      $$ Hj
  | succ k ih =>
    rw [budget_succ]
    iintro ⟨Hj, Hb, H⟩
    icases BudgetCredit.split $$ Hb with ⟨Hb₁, Hb₂⟩
    simp only [release]
    wp_pure 6
    tp_pure 6
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = k by omega]
    -- the pair evaluates the recursive releases first (spending `Hb₂`), then this draw
    -- (spending `Hb₁`, coupled via `hgauss`)
    wp_bind (release gauss a k)
    tp_bind (release gauss a' k)
    iapply ih
    iframe Hj Hb₂
    iintro %w Hj
    wp_bind pl({ofVal gauss} #a)
    tp_bind pl({ofVal gauss} #a')
    iapply hgauss a a' (· = ·) (0, cost v a a') _ _ _ (by simp)
      (zcdpLifting_rel_gaussianReal hv)
    iframe Hj Hb₁
    iintro %x %_ %rfl Hj
    wp_value_at (Val.pair (.real x) w)
    iapply H
    iapply specProgFrag_reshape (e₁ := Ectx.fill ([.pairL w] ++ K) pl(#x))
      (e₂ := K.fill (ofVal (.pair (.real x) w))) rfl $$ Hj

/-- `k` releases against the spec, spending `(0, (a - a')² / (2 v))` per release: both sides
release the same tuple. Conditional on the sampler spec `hgauss`. -/
theorem wp_release :
    ⊢ ⤇ release gauss a' k -∗ ↯b ((0 : ℝ≥0∞), (k : ℝ≥0∞) * cost v a a') -∗
      wp zcdpLifting ⊤ (release gauss a k) (fun w => iprop(∃ w', ⤇ ofVal w' ∗ ⌜w = w'⌝)) := by
  rw [spec_eq_fill_nil]
  iintro Hj Hb
  iapply wp_release_fill hv hgauss a a' k []
  iframe Hj Hb
  iintro %w Hj
  rw [ofVal]
  iapply spec_fill_nil_exists w $$ Hj

end Release

end Logic

/-! ## Adequacy: from the logic to a zCDP statement about the output laws -/

/-- `k` releases at inputs `a` and `a'` couple along equal outputs in the zCDP lifting at
`(0, k (a - a')² / (2 v))`. Conditional on the sampler spec `hgauss`. -/
theorem release_coupling_of (GF : BundledGFunctors) [AppPreGS ℝ GF] [SpecPreGS ℝ GF]
    [BudgetCreditPreGS (ℝ≥0∞ × ℝ≥0∞) GF] [InvGpreS GF] (hv : v ≠ 0)
    (hgauss : ∀ (_ : MicrometerGS ℝ .hasNoLC GF) (_ : BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF),
      GaussSpec (GF := GF) zcdpLifting gauss v)
    (a a' : ℝ) (k : ℕ) (σ σ' : State ℝ) :
    zcdpLifting.Rel (0, k * cost v a a') (· = ·) (limExecV ⟨release gauss a k, σ⟩)
      (limExecV ⟨release gauss a' k, σ'⟩) :=
  (wp_adequacy _ _ σ σ' _ (· = ·) fun _ _ ↦
    wp_release hv (hgauss _ _) a a' k).mono le_rfl adequacyRel_eq_subset

/-- The ghost state functors used to close the proofs. -/
noncomputable abbrev GF₀ : BundledGFunctors := MicrometerFunctor ℝ (ℝ≥0∞ × ℝ≥0∞)

section Closed

variable (hv : v ≠ 0)
  (hgauss : ∀ (_ : MicrometerGS ℝ .hasNoLC GF₀) (_ : BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF₀),
    GaussSpec (GF := GF₀) zcdpLifting gauss v)

include hv hgauss

/-- `k` releases are `(0, k (a - a')² / (2 v))`-zCDP for inputs `a` and `a'`. Conditional on the
sampler spec `hgauss`. -/
theorem release_zcdp (a a' : ℝ) (k : ℕ) (σ σ' : State ℝ) :
    zcdpDivergence (0, k * cost v a a') (limExecV ⟨release gauss a k, σ⟩)
      (limExecV ⟨release gauss a' k, σ'⟩) :=
  IsSound.sound (release_coupling_of GF₀ hv hgauss a a' k σ σ')

/-! ## From zCDP to DP -/

/-- `k` releases are `(ε, δ)`-DP for inputs `a` and `a'` and every `δ > 0`, with `ε` the best
Rényi conversion of the composed zCDP budget. Conditional on the sampler spec `hgauss`. -/
theorem release_dp (a a' : ℝ) (k : ℕ) (σ σ' : State ℝ) {δ : ℝ} (hδ : 0 < δ) :
    dp (⨅ α ∈ Set.Ioi (1 : ℝ), ofReal α * (k * cost v a a') +
        ofReal (log (1 / δ) / (α - 1)), ofReal δ)
      (limExecV ⟨release gauss a k, σ⟩) (limExecV ⟨release gauss a' k, σ'⟩) := by
  have h := codensity_sound <| (zcdpToDp hδ).map_rel
    (release_coupling_of GF₀ hv hgauss a a' k σ σ')
  simpa only [zcdpToDp_map, zero_add] using h

/-- `k` releases are `(ρₖ + 2 √(ρₖ log (1 / δ)), δ)`-DP for inputs at distance at most `r`, where
`ρₖ = k r² / (2 v)`: the privacy loss grows as `√k`. Conditional on the sampler spec `hgauss`. -/
theorem release_dp_sqrt {a a' r : ℝ} (h : |a - a'| ≤ r) (k : ℕ) (σ σ' : State ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1) :
    dp (ofReal (k * (r ^ 2 / (2 * v)) + 2 * √(k * (r ^ 2 / (2 * v)) * log (1 / δ))),
        ofReal δ)
      (limExecV ⟨release gauss a k, σ⟩) (limExecV ⟨release gauss a' k, σ'⟩) := by
  have hρ : 0 ≤ k * (r ^ 2 / (2 * (v : ℝ))) := by positivity
  have hk : (k : ℝ≥0∞) * ofReal (r ^ 2 / (2 * v)) =
      ofReal (k * (r ^ 2 / (2 * v))) := by
    rw [ofReal_mul (cast_nonneg k), ofReal_natCast]
  have hcost : cost v a a' ≤ ofReal (r ^ 2 / (2 * v)) := by
    refine ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity))
    exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
  -- bound the cost by r²/2v, read the zCDP coupling as a codensity one, then apply the closed-form
  -- zCDP→DP conversion
  have hz := ((LiftingHom.concentratedToCodensity _).toLiftingRelHom rfl).map_rel
    ((release_coupling_of GF₀ hv hgauss a a' k σ σ').mono
      (b' := (0, k * ofReal (r ^ 2 / (2 * v)))) (mk_le_mk.2 ⟨le_rfl, by gcongr⟩)
      fun _ _ ↦ id)
  have := codensity_sound
    (codensity_dp_rel_of_zcdp hδ hδ₁ hz)
  rwa [zero_add, hk, toReal_ofReal hρ, ← ofReal_add hρ (by positivity)] at this

end Closed

end GaussianRelease
end ProbLang
