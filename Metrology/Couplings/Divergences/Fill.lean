module

public import Metrology.Couplings.Divergence

/-! Filling the lost mass of sub-probability measures before comparing them (Rocq `FillDiv`). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

namespace MeasureTheory.Measure

/-- `μ` on `Option X`, with the lost mass `1 - μ univ` on `none` (Rocq `dcomplete`). -/
noncomputable def withBot (μ : Measure X) : Measure (Option X) :=
  μ.map some + (1 - μ Set.univ) • dirac none

/-- Filling the lost mass makes a sub-probability measure a probability measure. -/
instance isProbabilityMeasure_withBot (μ : Measure X) [IsSubProbabilityMeasure μ] :
    IsProbabilityMeasure μ.withBot :=
  ⟨by
    simpa [withBot, map_apply measurable_some .univ] using
      add_tsub_cancel_of_le (IsSubProbabilityMeasure.measure_le_one .univ)⟩

end MeasureTheory.Measure

section Kernel

variable {Y : Type*} [MeasurableSpace Y]

namespace ProbabilityTheory.Kernel

/-- The kernel `κ` with its lost mass at each point sent to `none` (Rocq `dcomplete`). -/
noncomputable def withBot (κ : Kernel X Y) : Kernel X (Option Y) where
  toFun x := (κ x).withBot
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp only [Measure.withBot, Measure.add_apply, Measure.map_apply measurable_some hs,
      Measure.smul_apply, smul_eq_mul]
    exact (κ.measurable_coe (measurable_some hs)).add
      ((measurable_const.sub (κ.measurable_coe .univ)).mul_const _)

theorem withBot_apply (κ : Kernel X Y) (x : X) : κ.withBot x = (κ x).withBot := rfl

/-- Filling the lost mass makes a sub-Markov kernel Markov. -/
instance isMarkovKernel_withBot (κ : Kernel X Y) [IsSubMarkovKernel κ] : IsMarkovKernel κ.withBot :=
  ⟨fun x ↦ by rw [withBot_apply]; infer_instance⟩

/-- The sub-Markov kernel forgetting `none`. -/
noncomputable def dropBot : Kernel (Option X) X where
  toFun o := o.elim 0 dirac
  measurable' := measurable_option_elim measurable_dirac 0

/-- Forgetting `none` loses no more than the whole mass. -/
instance isSubMarkovKernel_dropBot : IsSubMarkovKernel (dropBot : Kernel (Option X) X) :=
  ⟨fun o ↦ by cases o <;> simp [dropBot] <;> infer_instance⟩

theorem dropBot_comp_withBot (κ : Kernel X Y) : dropBot ∘ₖ κ.withBot = κ := by
  ext x s hs
  have hm := (dropBot : Kernel (Option Y) Y).measurable_coe hs
  rw [Kernel.comp_apply' _ _ _ hs, withBot_apply, Measure.withBot, lintegral_add_measure,
    MeasureTheory.lintegral_map hm measurable_some, lintegral_smul_measure, lintegral_dirac' _ hm]
  simp only [dropBot, Kernel.coe_mk, Option.elim_none, Option.elim_some, Measure.coe_zero,
    Pi.zero_apply, smul_zero, add_zero]
  simp_rw [dirac_apply' _ hs]
  exact lintegral_indicator_one hs

end ProbabilityTheory.Kernel

end Kernel

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
abbrev fill : GradedDivergence.{u} B :=
  D.onWithBot.leftUp

variable {D}

/-! ## Laws -/

/-- Filling lost mass preserves gradedness. -/
instance isGraded_onWithBot [LE B] [Top B] [D.IsGraded] : D.onWithBot.IsGraded where
  mono _ _ hb := IsGraded.mono (D := D) hb
  top μ ν := IsGraded.top μ.withBot ν.withBot

/-- Filling lost mass preserves reflexivity. -/
instance isReflexive_onWithBot [Zero B] [D.IsReflexive] : D.onWithBot.IsReflexive where
  refl μ _ := IsReflexive.refl μ.withBot

/-- Growing the left measure preserves gradedness. -/
instance isGraded_leftUp [LE B] [Top B] [D.IsGraded] : D.leftUp.IsGraded where
  mono _ _ hb := fun ⟨μ', hμ, _, h⟩ ↦ ⟨μ', hμ, ‹_›, IsGraded.mono hb h⟩
  top μ _ := ⟨μ, le_rfl, ‹_›, IsGraded.top _ _⟩

/-- Growing the left measure preserves reflexivity. -/
instance isReflexive_leftUp [Zero B] [D.IsReflexive] : D.leftUp.IsReflexive where
  refl μ _ := ⟨μ, le_rfl, ‹_›, IsReflexive.refl μ⟩

/-- The zero measure grows to the right measure itself. -/
instance isZeroLeft_leftUp [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B] [Top B]
    [D.IsGraded] [D.IsReflexive] : D.leftUp.IsZeroLeft where
  zero_left b {_} _ ν _ := ⟨ν, Measure.zero_le ν, ‹_›, IsGraded.mono zero_le (IsReflexive.refl ν)⟩

/-- Growing the left measure is antitone in the left argument. -/
instance isLeftAntitone_leftUp : D.leftUp.IsLeftAntitone where
  left_anti _ := fun hμ ⟨μ', hμ', h⟩ ↦ ⟨μ', hμ.trans hμ', h⟩

end GradedDivergence
