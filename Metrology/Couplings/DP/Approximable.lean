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
    have := isSubProbabilityMeasure_bind (μ := μ₁) (f := f) inferInstance
    have := isSubProbabilityMeasure_bind (μ := μ₂) (f := g) inferInstance
    rcases eq_or_ne (μ₁.bind f) 0 with h0 | h0
    · -- the zero measure stays zero under discretization
      have hz (n : ℕ) : μ₁.bind (f ∘ rep f g n ∘ disc f g n) = 0 :=
        measure_eq_zero_iff_singleton.2 fun i ↦
          (bind_disc_singleton_eq_zero_iff hf hg hf μ₁ cell_fst n i).2
            (measure_eq_zero_iff_singleton.1 h0 i)
      simp only [h0, hz, dp_zero]
      exact tendsto_const_nhds
    -- otherwise the approximants are eventually nonzero and their gaps converge
    have hmass : ∀ᶠ n in atTop, μ₁.bind (f ∘ rep f g n ∘ disc f g n) ≠ 0 := by
      filter_upwards [(hlimf univ).eventually_ne (Measure.measure_univ_ne_zero.2 h0)] with n hn
      exact fun h ↦ hn (by simp [h])
    refine Tendsto.congr' (hmass.mono fun n hn ↦ (dp_of_ne_zero hn).symm) ?_
    rw [dp_of_ne_zero h0]
    refine continuous_coe_ennreal_ereal.continuousAt.tendsto.comp ?_
    simp_rw [gap_eq_sup']
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
