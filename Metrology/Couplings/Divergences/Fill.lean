module

public import Metrology.Couplings.Divergence

/-! Filling the lost mass of sub-probability measures before comparing them (Rocq `FillDiv`). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- A set of `Option X` is measurable when its points under `some` are. -/
instance Option.instMeasurableSpace : MeasurableSpace (Option X) :=
  .map some ‹_›

@[fun_prop]
theorem measurable_some : Measurable (some : X → Option X) :=
  fun _ ↦ id

namespace MeasureTheory.Measure

/-- `μ` on `Option X`, with the lost mass `1 - μ univ` on `none`. -/
noncomputable def withBot (μ : Measure X) : Measure (Option X) :=
  μ.map some + (1 - μ Set.univ) • dirac none

instance isProbabilityMeasure_withBot (μ : Measure X) [IsSubProbabilityMeasure μ] :
    IsProbabilityMeasure μ.withBot :=
  ⟨by
    simpa [withBot, map_apply measurable_some .univ] using
      add_tsub_cancel_of_le (IsSubProbabilityMeasure.measure_le_one (μ := μ) .univ)⟩

end MeasureTheory.Measure

namespace GradedDivergence

variable {B : Type v} (D : GradedDivergence.{u} B)

/-- Comparing the measures with their lost mass filled in on `none`. -/
def onWithBot : GradedDivergence.{u} B :=
  fun b _ _ μ ν ↦ D b μ.withBot ν.withBot

/-- The left measure may first grow to a sub-probability measure. -/
def leftUp : GradedDivergence.{u} B :=
  fun b _ _ μ ν ↦ ∃ μ', μ ≤ μ' ∧ IsSubProbabilityMeasure μ' ∧ D b μ' ν

/-- The fill of a divergence: grow the left measure, then fill in the lost mass on both sides
(Rocq `FillDiv`). -/
def fill : GradedDivergence.{u} B :=
  D.onWithBot.leftUp

variable {D}

/-! ## Laws -/

instance isGraded_onWithBot [LE B] [Top B] [D.IsGraded] : D.onWithBot.IsGraded where
  mono _ _ hb _ _ _ _ _ _ h := IsGraded.mono (D := D) hb h
  top {_} _ μ ν _ _ := IsGraded.top (D := D) μ.withBot ν.withBot

instance isReflexive_onWithBot [Zero B] [D.IsReflexive] : D.onWithBot.IsReflexive where
  refl {_} _ μ _ := IsReflexive.refl (D := D) μ.withBot

instance isGraded_leftUp [LE B] [Top B] [D.IsGraded] : D.leftUp.IsGraded where
  mono _ _ hb _ _ _ _ _ _ := fun ⟨μ', hμ, _, h⟩ ↦ ⟨μ', hμ, ‹_›, IsGraded.mono hb h⟩
  top {_} _ μ _ _ _ := ⟨μ, le_rfl, ‹_›, IsGraded.top _ _⟩

instance isReflexive_leftUp [Zero B] [D.IsReflexive] : D.leftUp.IsReflexive where
  refl {_} _ μ _ := ⟨μ, le_rfl, ‹_›, IsReflexive.refl μ⟩

/-- The zero measure grows to the right measure itself. -/
instance isZeroLeft_leftUp [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B] [Top B]
    [D.IsGraded] [D.IsReflexive] : D.leftUp.IsZeroLeft where
  zero_left b {_} _ ν _ := ⟨ν, Measure.zero_le ν, ‹_›, IsGraded.mono zero_le (IsReflexive.refl ν)⟩

instance isLeftAntitone_leftUp : D.leftUp.IsLeftAntitone where
  left_anti _ _ _ _ _ _ _ _ hμ := fun ⟨μ', hμ', h⟩ ↦ ⟨μ', hμ.trans hμ', h⟩

instance isGraded_fill [LE B] [Top B] [D.IsGraded] : D.fill.IsGraded :=
  isGraded_leftUp

instance isReflexive_fill [Zero B] [D.IsReflexive] : D.fill.IsReflexive :=
  isReflexive_leftUp

instance isZeroLeft_fill [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B] [Top B]
    [D.IsGraded] [D.IsReflexive] : D.fill.IsZeroLeft :=
  isZeroLeft_leftUp

instance isLeftAntitone_fill : D.fill.IsLeftAntitone :=
  isLeftAntitone_leftUp

end GradedDivergence
