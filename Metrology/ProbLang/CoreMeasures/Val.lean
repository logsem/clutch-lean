module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Exp

meta import Metrology.Meta

@[expose] public section

/-! # Measurable space on values

The σ-algebra on `Val α` (the pullback along `Val.fst`), with measurability of `Val.fst`, `Val.mk`
and `Exp.ofVal`, and measurable singletons.
-/

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

/-- Proofs that `e` is a value carry the discrete σ-algebra. -/
instance instMeasurableSpaceIsVal {α : Type _} {e : Exp α} : MeasurableSpace (IsVal e) := ⊤

/-- The σ-algebra on values: the pullback along `Val.fst`. A `Sigma` instance would be `⊤`
here (since `IsVal e` is `⊤`), breaking measurability of `Exp.toVal?`; the high priority keeps
this one. -/
instance (priority := 10000) instMeasurableSpaceVal {α : Type _} [MeasurableSpace α] :
    MeasurableSpace (Val α) :=
  MeasurableSpace.comap Val.fst inferInstance

namespace Val

/-- `Val.fst` is measurable, by definition of the σ-algebra. -/
@[fun_prop]
theorem fst.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (Val.fst : Val α → Exp α) :=
  fun _ hS => MeasurableSpace.measurableSet_comap.mpr ⟨_, hS, rfl⟩

/-- `Exp.ofVal` is measurable (it is `Val.fst`). -/
@[fun_prop]
theorem _root_.ProbLang.Exp.ofVal.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (Exp.ofVal : Val α → Exp α) :=
  Val.fst.measurable

/-- `Val.mk` is measurable on `Σ e, IsVal e`, whose σ-algebra is `⊤`. -/
@[fun_prop]
theorem mk.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (fun (p : Σ e : Exp α, IsVal e) => (Val.mk p.1 p.2 p.2.lc : Val α)) := by
  intro T hT
  obtain ⟨U, -, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hT
  exact MeasurableSpace.measurableSet_iInf.mpr fun _ => MeasurableSpace.measurableSet_top

/-- `Val α` has measurable singletons if `α` does. -/
instance instMeasurableSingletonClass
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Val α) where
  measurableSet_singleton v := by
    have heq : ({v} : Set (Val α)) = Val.fst ⁻¹' {v.fst} := by
      ext v'
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => by rw [h], Val.ext⟩
    rw [heq]
    exact Val.fst.measurable (MeasurableSet.singleton v.fst)

end Val
end ProbLang
end ProbLangMeasures
