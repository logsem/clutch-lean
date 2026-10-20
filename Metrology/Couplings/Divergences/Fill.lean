module

public import Metrology.Couplings.Divergence

/-! # Filling lost mass
`withBot` puts the lost mass on a fresh point `none` and `Kernel.dropBot` forgets it (used by
`BindLaw.massEq`); `fill D` is the Rocq `FillDiv`. Filling before comparing composes whenever `D`
composes along Markov kernels (`isComposable_onWithBot`); the laws of `fill klDivergence` are in
`FillKl`. -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ## Filling measures -/

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

/-- `none` is a measurable point of `Option X`. -/
theorem _root_.measurableSet_none : MeasurableSet ({none} : Set (Option X)) := by
  have : ({none} : Set (Option X)) = (fun o : Option X ↦ o.elim true fun _ ↦ false) ⁻¹' {true} := by
    ext o
    cases o <;> simp
  rw [this]
  exact measurable_option_elim measurable_const true (measurableSet_singleton true)

/-- Off `none`, filling changes nothing. -/
theorem withBot_apply_of_none_notMem (μ : Measure X) {s : Set (Option X)} (hs : MeasurableSet s)
    (hn : none ∉ s) : μ.withBot s = μ (some ⁻¹' s) := by
  simp [withBot, map_apply measurable_some hs, dirac_apply' _ hs, hn]

/-- Integrating against a filled measure adds the lost mass times the value at `none`. -/
theorem lintegral_withBot (μ : Measure X) {f : Option X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ o, f o ∂μ.withBot = ∫⁻ x, f (some x) ∂μ + (1 - μ Set.univ) * f none := by
  rw [withBot, lintegral_add_measure, lintegral_map hf measurable_some, lintegral_smul_measure,
    lintegral_dirac' _ hf, smul_eq_mul]

/-- A probability measure loses no mass, so filling only relabels it. -/
theorem withBot_of_isProbabilityMeasure (μ : Measure X) [IsProbabilityMeasure μ] :
    μ.withBot = μ.map some := by
  simp [withBot]

/-- The relabelled measure lies below its filling. -/
theorem map_some_le_withBot (μ : Measure X) : μ.map some ≤ μ.withBot :=
  Measure.le_add_right le_rfl

/-- Two probability measures on `Option X` that agree off `none` are equal. -/
theorem ext_option {P P' : Measure (Option X)} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : ∀ s, MeasurableSet s → none ∉ s → P s = P' s) : P = P' := by
  ext s hs
  by_cases hn : none ∈ s
  · rw [← compl_compl s, prob_compl_eq_one_sub hs.compl, prob_compl_eq_one_sub hs.compl,
      h _ hs.compl fun h' ↦ h' hn]
  · exact h s hs hn

end MeasureTheory.Measure

/-! ## Filling kernels -/

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

/-- Forgetting `none` undoes filling. -/
theorem dropBot_comp_withBot (κ : Kernel X Y) : dropBot ∘ₖ κ.withBot = κ := by
  -- both sides agree on `s`: `some` contributes `κ x s`, `none` contributes `0`
  ext x s hs
  have hm := (dropBot : Kernel (Option Y) Y).measurable_coe hs
  rw [Kernel.comp_apply' _ _ _ hs, withBot_apply, Measure.withBot, lintegral_add_measure,
    MeasureTheory.lintegral_map hm measurable_some, lintegral_smul_measure, lintegral_dirac' _ hm]
  simp only [dropBot, Kernel.coe_mk, Option.elim_none, Option.elim_some, Measure.coe_zero,
    Pi.zero_apply, smul_zero, add_zero]
  simp_rw [dirac_apply' _ hs]
  exact lintegral_indicator_one hs

/-- Forgetting `none` on a relabelled measure gives the measure back. -/
theorem dropBot_comp_map_some (μ : Measure X) : dropBot ∘ₘ μ.map some = μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    MeasureTheory.lintegral_map ((dropBot : Kernel (Option X) X).measurable_coe hs)
      measurable_some]
  simp only [dropBot, Kernel.coe_mk, Option.elim_some]
  simp_rw [dirac_apply' _ hs]
  exact lintegral_indicator_one hs

/-- A measure on `Option X` above `μ.map some` forgets `none` to a measure above `μ`. -/
theorem le_dropBot_comp {μ : Measure X} {P : Measure (Option X)} (h : μ.map some ≤ P) :
    μ ≤ dropBot ∘ₘ P := by
  rw [← dropBot_comp_map_some μ]
  exact Measure.bind_mono_left h

/-- Filling the measure that forgets `none` gives back a probability measure on `Option X`. -/
theorem withBot_dropBot_comp (P : Measure (Option X)) [IsProbabilityMeasure P] :
    (dropBot ∘ₘ P).withBot = P := by
  have : IsSubProbabilityMeasure (dropBot ∘ₘ P) := isSubProbabilityMeasure_bind P _
  refine Measure.ext_option fun s hs hn ↦ ?_
  rw [Measure.withBot_apply_of_none_notMem _ hs hn,
    Measure.bind_apply (measurable_some hs) (Kernel.aemeasurable _)]
  have : (fun o ↦ dropBot o (some ⁻¹' s)) = s.indicator 1 := by
    funext o
    cases o with
    | none => simp [dropBot, hn]
    | some x =>
      simp only [dropBot, coe_mk, Option.elim_some, dirac_apply' _ (measurable_some hs)]
      rfl
  rw [this, lintegral_indicator_one hs]

/-- Forgetting `none` undoes filling a measure. -/
theorem dropBot_comp_withBot' (μ : Measure X) : dropBot ∘ₘ μ.withBot = μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.lintegral_withBot _ ((dropBot : Kernel (Option X) X).measurable_coe hs)]
  simp only [dropBot, coe_mk, Option.elim_some, Option.elim_none, Measure.coe_zero, Pi.zero_apply,
    mul_zero, add_zero]
  simp_rw [dirac_apply' _ hs]
  exact lintegral_indicator_one hs

/-- The kernel on `Option X` that fills `κ` at each point and keeps `none` at `none`. -/
noncomputable def liftBot (κ : Kernel X Y) : Kernel (Option X) (Option Y) where
  toFun o := o.elim (dirac none) fun x ↦ (κ x).withBot
  measurable' := measurable_option_elim κ.withBot.measurable _

@[simp] theorem liftBot_none (κ : Kernel X Y) : κ.liftBot none = dirac none := rfl

@[simp] theorem liftBot_some (κ : Kernel X Y) (x : X) : κ.liftBot (some x) = (κ x).withBot := rfl

/-- The filled kernel is Markov. -/
instance isMarkovKernel_liftBot (κ : Kernel X Y) [IsSubMarkovKernel κ] :
    IsMarkovKernel κ.liftBot :=
  ⟨fun o ↦ by cases o <;> simp only [liftBot_none, liftBot_some] <;> infer_instance⟩

/-- Filling a bind is binding the filled measure with the filled kernel. -/
theorem withBot_comp (κ : Kernel X Y) [IsSubMarkovKernel κ] (μ : Measure X)
    [IsSubProbabilityMeasure μ] : (κ ∘ₘ μ).withBot = κ.liftBot ∘ₘ μ.withBot := by
  have : IsSubProbabilityMeasure (κ ∘ₘ μ) := isSubProbabilityMeasure_bind μ _
  refine Measure.ext_option fun s hs hn ↦ ?_
  rw [Measure.withBot_apply_of_none_notMem _ hs hn, Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.lintegral_withBot _ (κ.liftBot.measurable_coe hs),
    Measure.bind_apply (measurable_some hs) (Kernel.aemeasurable _)]
  simp [Measure.withBot_apply_of_none_notMem _ hs hn, dirac_apply' _ hs, hn]

end ProbabilityTheory.Kernel

end Kernel

namespace GradedDivergence

/-! ## The fill of a divergence -/

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

/-! ## Laws for `onWithBot` and `leftUp` -/

/-- Filling lost mass preserves gradedness. -/
instance isGraded_onWithBot [LE B] [Top B] [D.IsGraded] : D.onWithBot.IsGraded where
  mono _ _ hb := IsGraded.mono (D := D) hb
  top μ ν := IsGraded.top μ.withBot ν.withBot

/-- Filling lost mass preserves reflexivity. -/
instance isReflexive_onWithBot [Zero B] [D.IsReflexive] : D.onWithBot.IsReflexive where
  refl μ _ := IsReflexive.refl μ.withBot

/-- Filling lost mass preserves closed budgets. -/
instance isBudgetClosed_onWithBot [LT B] [D.IsBudgetClosed] : D.onWithBot.IsBudgetClosed where
  of_forall_gt h := IsBudgetClosed.of_forall_gt (D := D) h

/-- A divergence that composes along Markov kernels between probability measures composes after
filling: filled kernels are Markov (Rocq `dcomplete_dbind`). -/
theorem isComposable_onWithBot [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B] [Top B]
    [D.IsGraded] [D.IsReflexive]
    (hcomp : ∀ ⦃b c : B⦄ {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
      ⦃μ₁ μ₂ : Measure X⦄ [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
      ⦃κ η : Kernel X Y⦄ [IsMarkovKernel κ] [IsMarkovKernel η],
      D b μ₁ μ₂ → (∀ x, D c (κ x) (η x)) → D (b + c) (κ ∘ₘ μ₁) (η ∘ₘ μ₂)) :
    D.onWithBot.IsComposable where
  comp b c X Y _ _ μ₁ μ₂ _ _ κ η _ _ hμ hκ := by
    change D _ _ _
    rw [Kernel.withBot_comp, Kernel.withBot_comp]
    refine hcomp hμ fun o ↦ ?_
    cases o with
    | none => exact IsGraded.mono zero_le (IsReflexive.refl _)
    | some x => exact hκ x

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
