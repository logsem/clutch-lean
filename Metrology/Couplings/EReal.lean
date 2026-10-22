module

public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Finite sums in `EReal`

Finite sums of `EReal` terms: the coercion, avoiding `⊥`, limits, and `EReal.toENNReal`. -/

@[expose] public section

open Filter Topology

namespace EReal

/-- The coercion `ℝ → EReal` commutes with finite sums. -/
theorem coe_finset_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ((∑ i ∈ s, x i : ℝ) : EReal) = ∑ i ∈ s, (x i : EReal) :=
  map_sum (⟨⟨(↑), coe_zero⟩, coe_add⟩ : ℝ →+ EReal) x s

/-- A finite sum of terms that are not `⊥` is not `⊥`. -/
theorem sum_ne_bot {ι : Type*} (s : Finset ι) {a : ι → EReal} (ha : ∀ i ∈ s, a i ≠ ⊥) :
    ∑ i ∈ s, a i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.forall_mem_insert] at ha
    rw [Finset.sum_insert hj]
    exact add_ne_bot_iff.2 ⟨ha.1, ih ha.2⟩

/-- Finite sums of convergent `EReal` functions converge, when no limit is `⊥`. -/
theorem tendsto_finset_sum {ι α : Type*} {l : Filter α} (s : Finset ι) {g : ι → α → EReal}
    {a : ι → EReal} (hg : ∀ i ∈ s, Tendsto (g i) l (𝓝 (a i))) (ha : ∀ i ∈ s, a i ≠ ⊥) :
    Tendsto (fun n ↦ ∑ i ∈ s, g i n) l (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert j s hj ih =>
    rw [Finset.forall_mem_insert] at hg ha
    simp only [Finset.sum_insert hj]
    exact (continuousAt_add (Or.inr (sum_ne_bot s ha.2)) (Or.inl ha.1)).tendsto.comp
      (hg.1.prodMk_nhds (ih hg.2 ha.2))

/-- `EReal.toENNReal` commutes with finite sums of nonnegative terms. -/
theorem toENNReal_sum {ι : Type*} (s : Finset ι) {x : ι → EReal} (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, x i).toENNReal = ∑ i ∈ s, (x i).toENNReal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.forall_mem_insert] at hx
    rw [Finset.sum_insert hj, Finset.sum_insert hj, toENNReal_add hx.1 (Finset.sum_nonneg hx.2),
      ih hx.2]

end EReal
