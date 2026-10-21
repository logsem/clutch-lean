module

public import Metrology.ProbLang.Reals
public import Metrology.TotalEris
public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Bounded Bernoulli iteration -/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
local bi IProp GF

section abstractBernoulli

structure AbstractBernoulliI (v : Val ℝ) (γ : ↑unitInterval) (I : IProp GF) : Prop where
  spec {E} : ⊢ iprop(
    ∀ (F : Bool → ℝ≥0∞),
      ↯ (.ofReal γ * F true + (1 - .ofReal γ) * F false) ∗ I -∗
      tglWp E pl(&v.1 #())
        (fun w : Val ℝ => iprop(∃ b : Bool, ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b) ∗ I)))

theorem AbstractBernoulli.toAbstractBernoulliI {v : Val ℝ} {γ : ↑unitInterval}
    (H : AbstractBernoulli (GF := GF) v γ) (I : IProp GF) :
    AbstractBernoulliI v γ I where
  spec := by
    intro E
    iintro %F ⟨Hε, HI⟩
    iapply tglWp_wand
    isplitl [Hε]
    · iapply H.spec $$ %F Hε
    iintro %w ⟨%b, %hb, Hfb⟩
    iexists b
    iframe %hb Hfb HI

end abstractBernoulli

def IterPMF (γ : ↑unitInterval) (N : ℕ) : Bool → ℝ≥0∞
  | true => .ofReal ((γ : ℝ) ^ N)
  | false => 1 - .ofReal ((γ : ℝ) ^ N)

def IterCreditV (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) : ℝ≥0∞ :=
  .ofReal ((γ : ℝ) ^ N) * F true + (1 - .ofReal ((γ : ℝ) ^ N)) * F false

def IterCont (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) : Bool → ℝ≥0∞
  | true => IterCreditV F γ N
  | false => F false

theorem ENNReal.one_sub_ofReal {x : ℝ} (hx : 0 ≤ x) :
    (1 : ℝ≥0∞) - ENNReal.ofReal x = ENNReal.ofReal (1 - x) := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hx]

theorem IterCreditV_succ (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) :
    IterCreditV F γ (N + 1) =
      .ofReal γ * IterCont F γ N true + (1 - .ofReal γ) * IterCont F γ N false := by
  have hγ0 : (0 : ℝ) ≤ (γ : ℝ) := γ.2.1
  have hγN1 : (γ : ℝ) ^ N ≤ 1 := pow_le_one₀ hγ0 γ.2.2
  have hT : ENNReal.ofReal ((γ : ℝ) ^ (N + 1)) =
      ENNReal.ofReal (γ : ℝ) * ENNReal.ofReal ((γ : ℝ) ^ N) := by
    rw [ENNReal.ofReal_pow hγ0, ENNReal.ofReal_pow hγ0, pow_succ]; ring
  have hF : ENNReal.ofReal (γ : ℝ) * ENNReal.ofReal (1 - (γ : ℝ) ^ N)
      + ENNReal.ofReal (1 - (γ : ℝ)) = ENNReal.ofReal (1 - (γ : ℝ) ^ (N + 1)) := by
    rw [← ENNReal.ofReal_mul hγ0,
      ← ENNReal.ofReal_add (mul_nonneg hγ0 (by linarith)) (by linarith [γ.2.2])]
    congr 1; ring
  simp only [IterCreditV, IterCont]
  rw [ENNReal.one_sub_ofReal (by positivity),
    ENNReal.one_sub_ofReal (by positivity),
    ENNReal.one_sub_ofReal hγ0, hT, ← hF]
  ring

section specification

theorem twp_IterTrial (E : CoPset) (v : Val ℝ) (γ : ↑unitInterval) (I : IProp GF)
    (Hspec : AbstractBernoulliI v γ I)
    (F : Bool → ℝ≥0∞) (N : ℕ) :
    ⊢ ↯ (IterCreditV F γ N) ∗ I -∗
      tglWp E pl(&IterTrial &v.1 #int (N : ℤ))
        (fun w : Val ℝ => iprop(∃ b : Bool, ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b) ∗ I)) := by
  induction N generalizing F with
  | zero =>
    iintro ⟨Hcr, HI⟩
    twp_pures
    twp_value
    imodintro
    rw [show IterCreditV F γ 0 = F true by simp [IterCreditV]]
    iframe Hcr HI
    itrivial
  | succ N IH =>
    iintro ⟨Hcr, HI⟩
    twp_pures
    twp_bind pl({v.fst} #())
    iapply tglWp_wand
    isplitl [Hcr HI]
    · iapply Hspec.spec $$ %(IterCont F γ N)
      rw [← IterCreditV_succ]
      iframe
    iintro %⟨w', _⟩ ⟨%b, %hret, Hcrb, HIb⟩
    dsimp only at hret
    subst hret
    cases b
    · twp_pures
      twp_value
      imodintro
      rw [IterCont]
      iframe Hcrb HIb
      itrivial
    · twp_pure
      twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&IterTrial {v.fst} #int (N : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH
      rw [IterCont]
      iframe

end specification

end
end Examples
end TotalEris
end ProbLang
