module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Mathlib.Topology.Instances.Irrational

@[expose] public section

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

namespace ProbLang
namespace TotalEris

noncomputable def irratErr : ℝ → ℝ≥0∞ :=
  {r : ℝ | ¬ Irrational r}.indicator (fun _ => 1)

@[simp]
theorem irratErr_of_irrational {r : ℝ} (h : Irrational r) : irratErr r = 0 := by
  rw [irratErr, Set.indicator_of_notMem (by simpa using h)]

@[simp]
theorem irratErr_of_not_irrational {r : ℝ} (h : ¬ Irrational r) : irratErr r = 1 := by
  rw [irratErr, Set.indicator_of_mem h]

theorem measurableSet_not_irrational : MeasurableSet {r : ℝ | ¬ Irrational r} :=
  (IsGδ.setOfPred_irrational.measurableSet).compl.congr (by ext r; simp)

theorem measurable_irratErr : Measurable irratErr :=
  measurable_const.indicator measurableSet_not_irrational

theorem irratErr_le_one (r : ℝ) : irratErr r ≤ 1 := by
  by_cases h : Irrational r <;> simp [h]

open MeasureTheory in
theorem lintegral_irratErr_eq_zero : ∫⁻ r, irratErr r ∂(LawfulProbLangℝ.unifUnit) = 0 := by
  rw [irratErr, lintegral_indicator_const measurableSet_not_irrational, one_mul]
  show volume.restrict (Set.Icc (0 : ℝ) 1) {r : ℝ | ¬ Irrational r} = 0
  rw [Measure.restrict_apply measurableSet_not_irrational]
  exact measure_mono_null Set.inter_subset_left <|
    ((Set.countable_range ((↑) : ℚ → ℝ)).mono fun _ => not_not.mp).measure_zero volume

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]

theorem twp_urand_irrational (E : CoPset) :
    [{ (True : IProp GF) }] pl(urand) @ E [{ r, RET .real r; ⌜Irrational r⌝ }] := by
  iintro %Φ - HΦ
  iapply twp_err_pos solve_not_value
  iintro %ε %Hε Herr
  iapply (twp_urand_exp measurable_irratErr ?Gexp) $$ Herr
  case Gexp => simp [lintegral_irratErr_eq_zero]
  iintro %r ⟨%-, Hcr⟩
  by_cases h : Irrational r
  · iapply HΦ $$ %r %h
  · iexfalso
    iapply ErrorCredit.contradict $$ Hcr
    rw [irratErr_of_not_irrational h]

end Wp

/-! ### Adequacy -/

theorem measurableSet_irrational_val :
    MeasurableSet {v : Val ℝ | ∃ r : ℝ, v = .real r ∧ Irrational r} := by
  have hval : {v : Val ℝ | ∃ r : ℝ, v = .real r ∧ Irrational r}
      = Val.fst ⁻¹' {e : Exp ℝ | ∃ r : ℝ, e = .lit (.real r) ∧ Irrational r} := by
    ext v; simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    exact ⟨fun ⟨r, hvr, hr⟩ => ⟨r, hvr ▸ rfl, hr⟩, fun ⟨r, hvr, hr⟩ => ⟨r, Val.ext hvr, hr⟩⟩
  have hexp : {e : Exp ℝ | ∃ r : ℝ, e = .lit (.real r) ∧ Irrational r}
      = (fun r : ℝ => (Exp.lit (.real r) : Exp ℝ)) '' {r | Irrational r} := by
    ext e; simp only [Set.mem_ofPred_eq, Set.mem_image]
    exact ⟨fun ⟨r, he, hr⟩ => ⟨r, hr, he.symm⟩, fun ⟨r, hr, he⟩ => ⟨r, he.symm, hr⟩⟩
  rw [hval]
  refine Val.fst.measurable ?_
  rw [hexp]
  exact (Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding).measurableSet_image'
    IsGδ.setOfPred_irrational.measurableSet

theorem urand_irrational_pgl (σ : State ℝ) :
    Pgl 0 (fun ρ => ∃ v : Val ℝ,
            ρ.expr = Exp.ofVal v ∧
            ∃ r : ℝ, v = .real r ∧ Irrational r)
      (limExec ⟨pl(urand), σ⟩) := by
  refine twp_pgl_lim (GF := erisGF)
    (φ := fun v => ∃ r : ℝ, v = .real r ∧ Irrational r)
    measurableSet_irrational_val ?_
  intro _; iintro _
  iapply twp_urand_irrational
  · itrivial
  iintro %r %hr !%
  exact ⟨r, rfl, hr⟩

/-- info: 'ProbLang.TotalEris.urand_irrational_pgl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(info) in
#print axioms urand_irrational_pgl

end TotalEris
end ProbLang
