module

public import Metrology.ProbLang.CoreMeasures

@[expose] public section

/-! # Discrete ProbLang: measurable singletons

Lifts `MeasurableSingletonClass` from `rT` to `Option`, `List`, `Tape`, `LocHeap`, `RvCell`,
`State` and `Cfg`. -/

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

/-! ## Measurable singletons of `Option`, `List`, `Tape`, `LocHeap`, `RvCell`, `State` and
`Cfg` -/

/-- `Option α` has measurable singletons if `α` does. -/
instance _root_.Option.instMeasurableSingletonClass : MeasurableSingletonClass (Option α) where
  measurableSet_singleton
    | none => singleton_none
    | some x => by
        rw [show ({some x} : Set (Option α)) = (some : α → Option α) '' {x} by simp]
        exact image_some (measurableSet_singleton x)

/-- `List α` has measurable singletons if `α` does. -/
instance _root_.List.instMeasurableSingletonClass : MeasurableSingletonClass (List α) where
  measurableSet_singleton l := by
    have hinj : (List.toSigma : List α → Σ n, Fin n → α).Injective := fun l l' h => by
      simpa [List.toSigma] using congrArg (fun p : Σ n, Fin n → α => List.ofFn p.2) h
    rw [show ({l} : Set (List α)) = List.toSigma ⁻¹' {List.toSigma l} by ext; simp [hinj.eq_iff]]
    refine List.measurable_toSigma ?_
    rw [show ({List.toSigma l} : Set (Σ n, Fin n → α)) =
      Sigma.mk (β := fun n => Fin n → α) l.length '' {l.get} by simp [List.toSigma]]
    exact (MeasurableEmbedding.sigmaMk _).measurableSet_image' (measurableSet_singleton _)

/-- `Tape α` has measurable singletons if `α` does. -/
instance Tape.instMeasurableSingletonClass : MeasurableSingletonClass (Tape α) :=
  measurableSingletonClass_of_injective Tape.measurable_toTuple Tape.toTuple_injective

/-- `LocHeap α` has measurable singletons if `α` does. -/
instance LocHeap.instMeasurableSingletonClass : MeasurableSingletonClass (LocHeap α) :=
  measurableSingletonClass_of_injective (of_comap_le le_rfl) fun _ _ h => ext_getElem? (congrFun h)

/-- `RvCell α` has measurable singletons if `α` does. -/
instance RvCell.instMeasurableSingletonClass : MeasurableSingletonClass (RvCell α) :=
  measurableSingletonClass_of_injective RvCell.measurable_toTuple fun c c' h => by
    cases c
    cases c'
    simp_all [RvCell.toTuple]

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

end ProbLang
end ProbLangDiscrete
