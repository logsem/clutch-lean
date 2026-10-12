module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.CoreMeasures

@[expose] public section

/-! # Discreteness lifting for ProbLang measure spaces -/

noncomputable section ProbLangDiscrete

open Classical MeasureTheory ProbabilityTheory ProbLang

namespace ProbLang

instance _root_.Option.instMeasurableSingletonClass
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Option α) where
  measurableSet_singleton
    | none => MeasurableSet.singleton_none
    | some x => by
        rw [show ({some x} : Set (Option α)) = (some : α → Option α) '' {x} by simp]
        exact MeasurableSet.image_some (MeasurableSet.singleton x)

instance LocHeap.instMeasurableSingletonClass
    {V : Type _} [MeasurableSpace V] [MeasurableSingletonClass V] :
    MeasurableSingletonClass (LocHeap V) where
  measurableSet_singleton m := by
    have hsing : ({m} : Set (LocHeap V))
                  = (fun (n : LocHeap V) (ℓ : Loc) => n[ℓ]?) ⁻¹' {fun ℓ => m[ℓ]?} := by
      ext n
      refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
      exact Std.ExtTreeMap.ext_getElem? (congrFun h)
    rw [hsing]
    exact (Measurable.of_comap_le le_rfl) (MeasurableSet.singleton _)

instance State.instMeasurableSingletonClass
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (State α) where
  measurableSet_singleton σ := by
    have hsing : ({σ} : Set (State α))
                  = (fun τ : State α => (τ.heap, τ.tapes)) ⁻¹' {(σ.heap, σ.tapes)} := by
      ext τ
      refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
      obtain ⟨hh, ht⟩ := Prod.mk.inj h
      cases σ; cases τ; congr
    rw [hsing]
    exact (Measurable.of_comap_le le_rfl) (MeasurableSet.singleton _)

instance Cfg.instMeasurableSingletonClass
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Cfg α) where
  measurableSet_singleton c := by
    have hsing : ({c} : Set (Cfg α))
                  = (fun c' : Cfg α => (c'.expr, c'.state)) ⁻¹' {(c.expr, c.state)} := by
      ext c'
      refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
      obtain ⟨he, hs⟩ := Prod.mk.inj h
      cases c; cases c'; congr
    rw [hsing]
    exact (Measurable.of_comap_le le_rfl) (MeasurableSet.singleton _)

end ProbLang

/-! ## Sanity check: `DiscreteMeasurableSpace` synthesizes -/

section SynthCheck
variable {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] [Countable rT]
example : DiscreteMeasurableSpace (ProbLang.BaseLit rT) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Pat rT)     := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Exp rT)     := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Val rT)     := inferInstance
example : DiscreteMeasurableSpace (ProbLang.EctxItem rT) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.LocHeap (ProbLang.Val rT)) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.LocHeap ProbLang.Tape) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.State rT) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Cfg rT)   := inferInstance
end SynthCheck

/-! ## Default `LawfulProbLangℝ` instance on `Int` -/
instance instProbLangℝInt : ProbLang.LawfulProbLangℝ Int where
  instDecidableEq := inferInstance
  unifUnit := (PMF.uniformOfFinset ({0, 1} : Finset Int) (by decide)).toMeasure
  unifUnit_isProbabilityMeasure := PMF.toMeasure.isProbabilityMeasure _
  unifUnitSupport := ↑({0, 1} : Finset Int)
  unifUnitSupportMeasurable := .of_discrete
  unifUnitIsConcentrated := by
    rw [PMF.toMeasure_apply_eq_zero_iff _ (.of_discrete), PMF.support_uniformOfFinset]
    exact disjoint_compl_right
  realLt a b := decide (a < b)
  realLe a b := decide (a ≤ b)
  measurable_realLt := .of_discrete
  measurable_realLe := .of_discrete
  -- On the discrete `Int` instantiation the "reals" are the integers themselves.
  realAdd a b := a + b
  realNeg a := -a
  realOfInt z := z
  realOfRat q := q.floor
  -- On the discrete `Int` instantiation an "integer real" has no fractional part.
  realFrac _ := 0
  measurable_realAdd := .of_discrete
  measurable_realNeg := .of_discrete
  measurable_realFrac := .of_discrete

end ProbLangDiscrete
