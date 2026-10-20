module

public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Regular.Pi
public import Mathlib.Algebra.Regular.Prod
public import Mathlib.Basic.ENNReal.Basic

/-! # Budget order facts

Two facts about canonically ordered budgets: room strictly above `b + c` gives room strictly above
`b`, and `⊤` never cancels. -/

@[expose] public section

variable {B : Type*}

/-- Strictly above `b + c` means strictly above `b` after removing `c`. -/
theorem exists_lt_and_add_eq_of_add_lt [AddCommSemigroup B] [Preorder B]
    [CanonicallyOrderedAdd B] {b c d : B} (h : b + c < d) : ∃ b', b < b' ∧ b' + c = d := by
  obtain ⟨e, rfl⟩ := exists_add_of_le h.le
  refine ⟨b + e, le_self_add.lt_of_not_ge fun hb ↦ h.not_ge ?_, add_right_comm b e c⟩
  rw [add_right_comm]
  exact add_le_add_left hb c

/-- The top budget is not left-cancellable, since `⊤ + b = ⊤` for every `b`
(Rocq `budget_spend_top_fails`). -/
theorem not_isAddLeftRegular_top [AddZeroClass B] [PartialOrder B] [OrderTop B]
    [CanonicallyOrderedAdd B] [Nontrivial B] : ¬IsAddLeftRegular (⊤ : B) := fun h ↦ by
  obtain ⟨b, hb⟩ := exists_ne (0 : B)
  exact hb (h (show ⊤ + b = ⊤ + 0 by rw [add_zero]; exact top_le_iff.1 le_self_add))
