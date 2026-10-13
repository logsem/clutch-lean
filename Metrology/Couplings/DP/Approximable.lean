module

public import Metrology.Couplings.DP.Discretize
public import Metrology.Couplings.DP.Divergence

/-! The DP divergences are approximable (Approximate Span Liftings, Thm. 4.10, by the dyadic
discretization of App. C.3). -/

@[expose] public section

open MeasureTheory Set Filter Topology GradedDivergence Discretize
open scoped ENNReal NNReal

universe u

namespace DPDiv

/-- On a finite space, the gap is a finite supremum over all events. -/
theorem gap_eq_sup' {N : ℕ} (ε : ℝ) (ρ₁ ρ₂ : Measure (ULift.{u} (Fin N))) :
    gap ε ρ₁ ρ₂ = Finset.univ.sup' Finset.univ_nonempty
      fun T : Set (ULift.{u} (Fin N)) ↦ ρ₁ T - ENNReal.ofReal (Real.exp ε) * ρ₂ T := by
  rw [Finset.sup'_eq_sup, Finset.sup_univ_eq_iSup, gap]
  exact iSup_congr fun T ↦ iSup_pos (ULift.measurableSet_fin T)

/-- The DP divergences are approximable (Thm. 4.10, App. C.3). -/
instance isApproximable_dp : (dp.{u}).IsApproximable where
  tendsto α X _ N f g _ _ μ₁ μ₂ _ _ hf hg := by
    rcases isEmpty_or_nonempty X with hX | hX
    · refine ⟨fun _ ↦ 0, fun _ ↦ isEmptyElim, fun _ j ↦ j.down.elim0,
        fun _ ↦ Subsingleton.measurable, fun _ ↦ Subsingleton.measurable, ?_⟩
      exact tendsto_const_nhds.congr fun n ↦ congrArg₂ (fun a b ↦ dp α a b)
        (congrArg μ₁.bind (funext isEmptyElim)) (congrArg μ₂.bind (funext isEmptyElim))
    refine ⟨_, disc f g, rep f g, measurable_disc f g hf hg, measurable_rep f g, ?_⟩
    have hlimf := tendsto_bind_disc hf hg hf (μ := μ₁) (cell_fst (g := g))
    have hlimg := tendsto_bind_disc hf hg hg (μ := μ₂) (cell_snd (f := f))
    have := isSubProbabilityMeasure_bind μ₁ f
    simp_rw [dp_apply, gap_eq_sup']
    refine Filter.Tendsto.finset_sup'_nhds_apply _ fun T _ ↦ ?_
    exact ENNReal.Tendsto.sub (hlimf T)
      (ENNReal.Tendsto.const_mul (hlimg T) (Or.inr ENNReal.ofReal_ne_top))
      (Or.inl (measure_ne_top _ _))

/-- The DP divergences are reflexive, continuous, approximable, composable and additive
(Thm. 4.10). -/
theorem dp_properties :
    (dp.{u}).IsReflexive ∧ (dp.{u}).IsContinuous ∧ (dp.{u}).IsApproximable ∧
      (dp.{u}).IsComposable ∧ (dp.{u}).IsAdditive :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end DPDiv
