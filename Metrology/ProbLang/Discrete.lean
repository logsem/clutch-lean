module

public import Metrology.ProbLang.CoreMeasures

@[expose] public section

/-! # Discrete ProbLang: measurable singletons

Lifts `MeasurableSingletonClass` from `rT` to `Option`, `LocHeap`, `State` and `Cfg`, so `{ρ}` is
measurable for every configuration `ρ`. -/

noncomputable section ProbLangDiscrete

open Measurable (of_comap_le)
open MeasurableSet (singleton_none image_some)
open Std.ExtTreeMap (ext_getElem?)

/-- A type with a measurable injection into a type with measurable singletons has them too. -/
theorem measurableSingletonClass_of_injective {X Y : Type _} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] {f : X → Y} (hf : Measurable f)
    (hinj : f.Injective) : MeasurableSingletonClass X where
  measurableSet_singleton x := by
    rw [show ({x} : Set X) = f ⁻¹' {f x} by ext; simp [hinj.eq_iff]]
    exact hf (measurableSet_singleton _)

namespace ProbLang

variable {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Measurable singletons of `Option`, `LocHeap`, `State` and `Cfg` -/

/-- `Option α` has measurable singletons if `α` does. -/
instance _root_.Option.instMeasurableSingletonClass : MeasurableSingletonClass (Option α) where
  measurableSet_singleton
    | none => singleton_none
    | some x => by
        rw [show ({some x} : Set (Option α)) = (some : α → Option α) '' {x} by simp]
        exact image_some (measurableSet_singleton x)

/-- `LocHeap α` has measurable singletons if `α` does. -/
instance LocHeap.instMeasurableSingletonClass : MeasurableSingletonClass (LocHeap α) :=
  measurableSingletonClass_of_injective (of_comap_le le_rfl) fun _ _ h => ext_getElem? (congrFun h)

/-- `State α` has measurable singletons if `α` does. -/
instance State.instMeasurableSingletonClass : MeasurableSingletonClass (State α) :=
  measurableSingletonClass_of_injective (of_comap_le le_rfl) fun σ τ h => by
    cases σ
    cases τ
    simp_all

/-- `Cfg α` has measurable singletons if `α` does. -/
instance Cfg.instMeasurableSingletonClass : MeasurableSingletonClass (Cfg α) :=
  measurableSingletonClass_of_injective (of_comap_le le_rfl) fun c c' h => by
    cases c
    cases c'
    simp_all

/-! ## Check: `DiscreteMeasurableSpace` holds for all ProbLang types over countable `rT` -/

section SynthCheck

variable {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] [Countable rT]

example : DiscreteMeasurableSpace (BaseLit rT) := inferInstance
example : DiscreteMeasurableSpace (Pat rT) := inferInstance
example : DiscreteMeasurableSpace (Exp rT) := inferInstance
example : DiscreteMeasurableSpace (Val rT) := inferInstance
example : DiscreteMeasurableSpace (EctxItem rT) := inferInstance
example : DiscreteMeasurableSpace (LocHeap (Val rT)) := inferInstance
example : DiscreteMeasurableSpace (LocHeap Tape) := inferInstance
example : DiscreteMeasurableSpace (State rT) := inferInstance
example : DiscreteMeasurableSpace (Cfg rT) := inferInstance

end SynthCheck

end ProbLang
end ProbLangDiscrete
