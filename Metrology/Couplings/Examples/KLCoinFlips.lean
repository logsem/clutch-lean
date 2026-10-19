module

public import Metrology.Couplings.KLLaws
public import Mathlib.Probability.Distributions.Bernoulli

/-! KL budgets add along two coin flips, through the KL bind law. -/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory GradedLifting GradedDivergence InformationTheory
open scoped ENNReal unitInterval

namespace KLCoinFlips

variable (p q : I)

/-- A coin landing `true` with probability `p`. -/
noncomputable abbrev coin : Measure Bool := bernoulliMeasure true false p

/-- After the first flip `a`, flip again and keep both. -/
noncomputable def flipAgain : Kernel Bool (Bool × Bool) :=
  ⟨fun a ↦ (coin p).map (a, ·), .of_discrete⟩

instance isMarkovKernel_flipAgain : IsMarkovKernel (flipAgain p) :=
  ⟨fun _ ↦ (isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance⟩

/-- One flip lifts equality at the KL divergence of the two coins. -/
theorem coin_rel : (markovCodensity klDivergence).Rel (klDiv (coin p) (coin q)) (· = ·)
    (coin p) (coin q) :=
  markovCodensity_kl_rel_eq_iff.2 (klDivergence_iff.2 le_rfl)

/-- The second flip after equal first flips lifts equality at the same budget. -/
theorem flipAgain_rel (a : Bool) : (markovCodensity klDivergence).Rel (klDiv (coin p) (coin q))
    (· = ·) (flipAgain p a) (flipAgain q a) :=
  markovCodensity_map (by fun_prop) (by fun_prop) <|
    markovCodensity_mono (coin_rel p q) le_rfl fun x y ↦ by
      obtain rfl | h := eq_or_ne x y
      · simp
      · simp [relCost_of_not h]

/-- Two flips of a `p`-coin are within twice the KL divergence of one flip from two flips of a
`q`-coin: the first flip lifts equality by completeness, and the second binds by `BindLaw.kl`,
whose side condition holds since coin flips lose no mass. -/
theorem klDiv_two_flips_le :
    klDiv (flipAgain p ∘ₘ coin p) (flipAgain q ∘ₘ coin q) ≤ 2 * klDiv (coin p) (coin q) := by
  rw [two_mul]
  refine klDiv_le_of_markovCodensity <| BindLaw.kl.sound
    ⟨inferInstance, inferInstance, markovCodensity_frame (coin_rel p q)⟩
    (fun _ _ _ ↦ by simp) fun a a' h ↦ ?_
  obtain ⟨rfl, -⟩ := relCost_add_lt_top_iff.1 h
  rw [relCost_of rfl, zero_add]
  exact flipAgain_rel p q a

end KLCoinFlips
