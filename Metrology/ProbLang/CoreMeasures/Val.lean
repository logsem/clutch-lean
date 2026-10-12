module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Exp

meta import Metrology.Meta

@[expose] public section

/-! # Measurable space on values -/

-- TODO move this to the semantics file once we have that (leave here until then though,
-- during drop-in step, so we can prove discreteness assuming discrete R type)

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

instance instMeasurableSpaceIsVal {α : Type _} {e : Exp α} : MeasurableSpace (IsVal e) := ⊤

/-- The comap of `Val.fst`. `Sigma.instMeasurableSpace` would be `⊤` here (since `IsVal e`
is `⊤`), breaking measurability of `Exp.toVal?`. `Val` is a `structure`, not a `Sigma`, so that
this instance is the one found. -/
instance (priority := 10000) instMeasurableSpaceVal {α : Type _} [MeasurableSpace α] :
    MeasurableSpace (Val α) :=
  MeasurableSpace.comap Val.fst inferInstance

namespace Val

@[fun_prop]
theorem fst.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (Val.fst : Val α → Exp α) :=
  fun _ hS => MeasurableSpace.measurableSet_comap.mpr ⟨_, hS, rfl⟩

@[fun_prop]
theorem _root_.ProbLang.Exp.ofVal.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (Exp.ofVal : Val α → Exp α) :=
  Val.fst.measurable

@[fun_prop]
theorem mk.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (fun (p : Σ e : Exp α, IsVal e) => (Val.mk p.1 p.2 p.2.lc : Val α)) := by
  intro T hT
  obtain ⟨U, -, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hT
  exact MeasurableSpace.measurableSet_iInf.mpr fun _ => MeasurableSpace.measurableSet_top

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
