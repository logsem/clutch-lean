module

public import Metrology.TotalEris
import Metrology.ProbLang.Syntax.Notation
public import Mathlib.Probability.Distributions.Geometric
public import Metrology.Code.Samplers
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Geometric sampler -/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi IProp GF

/-! ## Abstract Bernoulli trial -/
section abstractBernoulli

structure AbstractBernoulli (v : Val rT) (γ : ↑unitInterval) : Prop where
  spec {E} : ⊢ iprop(
    ∀ (F : Bool → ℝ≥0∞),
      ↯ (.ofReal γ * F true + (1 - .ofReal γ) * F false) -∗
      tglWp E pl(&v.1 #()) (fun w : Val rT => iprop(
        ∃ b : Bool, ⌜w.1 = pl(#b)⌝ ∗ ↯ (F b))))

end abstractBernoulli

/-! ## Distribution -/
section distribution

/-- PMF `γ^n · (1-γ)` of the number of `true` trials before the first `false` in `GeometricTrial`. -/
def GeometricPMF (γ : ↑unitInterval) (n : ℕ) : ℝ≥0∞ :=
  .ofReal ((γ : ℝ) ^ n * (1 - γ))

/-- Geometric distribution, shifted right by `shiftR` (supported on `z ≥ shiftR`). -/
def ShiftGeometricPMF (γ : ↑unitInterval) (shiftR z : ℤ) : ℝ≥0∞ :=
  if shiftR ≤ z then .ofReal ((γ : ℝ) ^ (z - shiftR).toNat * (1 - γ)) else 0

theorem shiftGeometricPMF_geometricPMF_eq (γ : ↑unitInterval) (n : ℕ) :
    GeometricPMF γ n = ShiftGeometricPMF γ 0 n := by
  simp [GeometricPMF, ShiftGeometricPMF]

theorem GeometricPMF_zero (γ : ↑unitInterval) :
    GeometricPMF γ 0 = 1 - ENNReal.ofReal (γ : ℝ) := by
  rw [GeometricPMF, pow_zero, one_mul, ENNReal.ofReal_sub 1 γ.2.1, ENNReal.ofReal_one]

theorem GeometricPMF_succ (γ : ↑unitInterval) (k : ℕ) :
    GeometricPMF γ (k + 1) = ENNReal.ofReal (γ : ℝ) * GeometricPMF γ k := by
  have hpow : (γ : ℝ) ^ (k + 1) * (1 - (γ : ℝ))
      = (γ : ℝ) * ((γ : ℝ) ^ k * (1 - (γ : ℝ))) := by ring
  rw [GeometricPMF, GeometricPMF, hpow, ENNReal.ofReal_mul γ.2.1]

end distribution

/-! ## Credit expectation -/
section creditExpectation

/-- Expectation of `F` under the geometric distribution shifted by `shiftR`. -/
def shiftGeometricPMFCreditV (γ : ↑unitInterval) (shiftR : ℤ) (F : ℤ → ℝ≥0∞) :=
  ∑'(k : ℕ), F (shiftR + k) * GeometricPMF γ k

/-- Error-amplification factor `1/γ`. -/
def terminationFactor (γ : ↑unitInterval) : ℝ≥0 :=
  ⟨1 / (γ : ℝ), div_nonneg zero_le_one (unitInterval.nonneg γ)⟩

theorem one_lt_terminationFactor (γ : ↑unitInterval)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) : 1 < terminationFactor γ := by
  rw [terminationFactor]
  exact_mod_cast (one_lt_div hγ0).mpr hγ1

theorem ofReal_mul_terminationFactor (γ : ↑unitInterval) (hγ0 : 0 < (γ : ℝ)) :
    ENNReal.ofReal (γ : ℝ) * (terminationFactor γ : ℝ≥0∞) = 1 := by
  have hcoe : ((terminationFactor γ : ℝ≥0) : ℝ) = 1 / (γ : ℝ) := rfl
  rw [ENNReal.coe_nnreal_eq (terminationFactor γ), hcoe,
    ← ENNReal.ofReal_mul γ.2.1, mul_one_div, div_self hγ0.ne', ENNReal.ofReal_one]

end creditExpectation

/-! ## Credit kernel -/
section creditKernel

def geometricContAmp (F : Int → ℝ≥0∞) (γ : ↑unitInterval) (shift : Int) (ε_term : ℝ≥0∞) :
    Bool → ℝ≥0∞
  | true => shiftGeometricPMFCreditV γ (shift + 1) F + terminationFactor γ * ε_term
  | false => F shift

end creditKernel

/-! ## Credit conservation -/
section conservation

theorem shiftGeometricPMFCreditV_succ (γ : ↑unitInterval) (shift : ℤ) (F : ℤ → ℝ≥0∞) :
    shiftGeometricPMFCreditV γ shift F
      = ENNReal.ofReal (γ : ℝ) * shiftGeometricPMFCreditV γ (shift + 1) F
        + (1 - ENNReal.ofReal (γ : ℝ)) * F shift := by
  unfold shiftGeometricPMFCreditV
  rw [tsum_eq_zero_add' ENNReal.summable, add_comm]
  congr 1
  · rw [← ENNReal.tsum_mul_left]
    congr 1; funext k
    have hshift : shift + (↑(k + 1) : ℤ) = (shift + 1) + ↑k := by rw [Nat.cast_add_one]; ring
    rw [GeometricPMF_succ, hshift]
    ring
  · rw [Nat.cast_zero, add_zero, GeometricPMF_zero, mul_comm]

end conservation

/-! ## Specification -/
section specification

theorem twp_GeometricTrial (E : CoPset) {γ : ↑unitInterval} (shift : Int) (v : Val rT)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Hspec : AbstractBernoulli (GF := GF) v γ) :
    ⊢
      ∀ (F : Int → ℝ≥0∞),
      ↯ (shiftGeometricPMFCreditV γ shift F) -∗
      tglWp E pl(&GeometricTrial &v.1 #shift) (fun w : Val rT => iprop(
        ∃ z : ℤ, ⌜w.1 = pl(#z)⌝ ∗ ⌜shift ≤ z⌝ ∗ ↯ (F z))) := by
  iintro %F Hε_spec
  iapply twp_err_pos solve_not_value
  iintro %ε_term %Hε_term_pos Hε_term
  irevert! %shift
  iapply ErrorCredit.Induction.simple Hε_term_pos
    (one_lt_terminationFactor γ hγ0 hγ1) $$ [] Hε_term
  iintro !> ⟨IH, Hε_term⟩ %shift Hε_spec
  twp_pures
  twp_bind pl({v.fst} #())
  iapply tglWp_wand
  isplitl [Hε_spec Hε_term]
  · iapply Hspec.spec $$ %(geometricContAmp F γ shift ε_term)
    icombine Hε_term Hε_spec as Hε
    iapply ErrorCredit.ext $$ Hε
    simp only [geometricContAmp]
    rw [shiftGeometricPMFCreditV_succ γ shift F, mul_add, ← mul_assoc,
      ofReal_mul_terminationFactor γ hγ0, one_mul]
    ring
  iintro %⟨w, _, _⟩ ⟨%b, %hret, Hε⟩
  dsimp only at hret
  subst hret
  cases b
  · twp_pures
    twp_value
    imodintro
    rw [geometricContAmp]
    iframe Hε
    itrivial
  · twp_pure
    twp_pure
    twp_bind pl(&GeometricTrial &v.1 #(shift + 1))
    iapply tglWp_wand
    isplitl [Hε IH]
    · rw [geometricContAmp]
      ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split $$ Hε
      iapply IH $$ Hterm
      iexact Hexp
    iintro %w ⟨%z, %hzeq, %hzle, Hf⟩
    iapply tglWp_value
    have hzle' : shift ≤ z := by omega
    iframe %hzeq %hzle' Hf

end specification

end
end Examples
end TotalEris
end ProbLang
