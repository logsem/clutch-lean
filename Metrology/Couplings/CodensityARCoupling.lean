module

public import Metrology.Couplings.CodensityLifting
public import Metrology.Couplings.DP.Divergence
public import Metrology.Couplings.DPCouplings

/-! Codensity liftings and test-function approximate couplings. -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedDivergence
open scoped ENNReal NNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measurable function as a kernel into a point: the point with that mass. -/
noncomputable def massKernel {f : X → ℝ≥0∞} (hf : Measurable f) : Kernel X PUnit.{u + 1} :=
  ⟨fun x ↦ f x • dirac PUnit.unit, hf.smul_measure _⟩

@[simp] theorem massKernel_apply_univ {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    massKernel.{u} hf x .univ = f x := by
  simp [massKernel]

theorem isSubMarkovKernel_massKernel {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) :
    IsSubMarkovKernel (massKernel.{u} hf) where
  isSubProbabilityMeasure x := ⟨by simpa using hf1 x⟩

/-- Composing with a mass kernel integrates its function. -/
@[simp] theorem massKernel_comp_apply_univ {f : X → ℝ≥0∞} (hf : Measurable f) (μ : Measure X) :
    (massKernel.{u} hf ∘ₘ μ) .univ = ∫⁻ x, f x ∂μ := by
  simp [bind_apply .univ (massKernel.{u} hf).measurable.aemeasurable]

/-- An approximate coupling is the basic codensity lifting into a point that compares masses, with
`F` applied after the test. -/
theorem arCoupling_iff_basicCodensity {F : ℝ≥0∞ → ℝ≥0∞} {Φ : Set (X × Y)} {μ : Measure X}
    {ν : Measure Y} : ARCoupling F Φ μ ν ↔ BasicCodensity Unit (fun p q ↦ p .univ ≤ q .univ)
      (fun p q ↦ p .univ ≤ F (q .univ)) Φ μ ν := by
  constructor
  · intro h k l _ _ hkl
    rw [bind_apply .univ k.measurable.aemeasurable, bind_apply .univ l.measurable.aemeasurable]
    exact h ⟨fun x ↦ k x .univ, k.measurable_coe .univ,
      fun _ ↦ IsSubProbabilityMeasure.measure_univ_le_one⟩ ⟨fun y ↦ l y .univ,
      l.measurable_coe .univ, fun _ ↦ IsSubProbabilityMeasure.measure_univ_le_one⟩
      fun hab ↦ hkl hab
  · rintro h ⟨f, hf, hf1⟩ ⟨g, hg, hg1⟩ hfg
    have := isSubMarkovKernel_massKernel.{0} hf hf1
    have := isSubMarkovKernel_massKernel.{0} hg hg1
    simpa using h (k := massKernel.{0} hf) (l := massKernel.{0} hg) fun x y hxy ↦ by
      simpa using hfg hxy

theorem exp_coe_nnreal (ε : ℝ≥0) : ((ε : ℝ≥0∞) : EReal).exp = ENNReal.ofReal (Real.exp ε) := by
  rw [ENNReal.coe_nnreal_eq, EReal.coe_ennreal_ofReal, max_eq_left (NNReal.coe_nonneg ε),
    EReal.exp_coe]

/-- Measures related by the DP codensity lifting are related by the test-function DP coupling,
which only uses unit-grade tests into a point. -/
theorem GradedDivergence.Codensity.arCoupling_dp {ε : ℝ≥0} {δ : ℝ≥0∞} {R : Set (X × Y)}
    {μ : Measure X} {ν : Measure Y} (h : DPDiv.dp.{u}.Codensity (.ofAdd ε) δ R μ ν) :
    ARCoupling.DP ε δ R μ ν := by
  rintro ⟨f, hf, hf1⟩ ⟨g, hg, hg1⟩ hfg
  have := isSubMarkovKernel_massKernel.{u} hf hf1
  have := isSubMarkovKernel_massKernel.{u} hg hg1
  have htest : ∀ ⦃x y⦄, (x, y) ∈ R →
      DPDiv.dp (.ofAdd 0) (massKernel.{u} hf x) (massKernel.{u} hg y) ≤ 0 := by
    intro x y hxy
    rw [DPDiv.dp_le_iff]
    intro S _
    simp only [massKernel, Kernel.coe_mk, Measure.smul_apply, smul_eq_mul, toAdd_ofAdd,
      NNReal.coe_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul, add_zero]
    exact mul_le_mul_left (hfg hxy) _
  have hc := h htest
  rw [add_zero, ← ofAdd_add, add_zero, DPDiv.dp_le_iff] at hc
  simpa [DPF, exp_coe_nnreal] using hc .univ .univ

/-- A test-function DP coupling is in the DP codensity lifting: a test that the kernels pass with
slack `γ` becomes a `[0, 1]`-valued test function once `γ` is cut off. -/
theorem ARCoupling.DP.codensity {ε : ℝ≥0} {δ : ℝ≥0∞} {R : Set (X × Y)} {μ : Measure X}
    {ν : Measure Y} [IsSubProbabilityMeasure μ] (h : ARCoupling.DP ε δ R μ ν) :
    DPDiv.dp.{u}.Codensity (.ofAdd ε) δ R μ ν := by
  intro I _ β γ k l _ _ hkl
  rw [DPDiv.dp_le_iff]
  intro S hS
  set c := ENNReal.ofReal (Real.exp (Multiplicative.toAdd β : ℝ≥0))
  have hkS := k.measurable_coe hS
  have hlS := l.measurable_coe hS
  have hfg := h ⟨fun x ↦ k x S - γ, hkS.sub measurable_const,
      fun _ ↦ tsub_le_self.trans (IsSubProbabilityMeasure.measure_le_one S)⟩
    ⟨fun y ↦ min 1 (c * l y S), measurable_const.min (measurable_const.mul hlS),
      fun _ ↦ min_le_left _ _⟩
    fun {x y} hxy ↦ le_min (tsub_le_self.trans (IsSubProbabilityMeasure.measure_le_one S))
      (tsub_le_iff_right.2 (DPDiv.dp_le_iff.1 (hkl hxy) S hS))
  rw [bind_apply hS k.measurable.aemeasurable, bind_apply hS l.measurable.aemeasurable]
  calc ∫⁻ x, k x S ∂μ
      ≤ ∫⁻ x, (k x S - γ) + γ ∂μ := lintegral_mono fun _ ↦ le_tsub_add
    _ ≤ ∫⁻ x, k x S - γ ∂μ + γ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
        gcongr
        exact mul_le_of_le_one_right' IsSubProbabilityMeasure.measure_univ_le_one
    _ ≤ ENNReal.ofReal (Real.exp ε) * ∫⁻ y, min 1 (c * l y S) ∂ν + δ + γ := by
        simpa [DPF, exp_coe_nnreal] using add_le_add_left hfg γ
    _ ≤ ENNReal.ofReal (Real.exp ε) * c * ∫⁻ y, l y S ∂ν + (δ + γ) := by
        rw [mul_assoc, ← lintegral_const_mul _ hlS, add_assoc]
        gcongr
        exact min_le_right _ _
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, toAdd_mul, toAdd_ofAdd,
          NNReal.coe_add]

/-- Test-function DP couplings are exactly the DP codensity lifting. -/
theorem arCoupling_dp_iff_codensity {ε : ℝ≥0} {δ : ℝ≥0∞} {R : Set (X × Y)} {μ : Measure X}
    {ν : Measure Y} [IsSubProbabilityMeasure μ] :
    ARCoupling.DP ε δ R μ ν ↔ DPDiv.dp.{u}.Codensity (.ofAdd ε) δ R μ ν :=
  ⟨ARCoupling.DP.codensity, Codensity.arCoupling_dp⟩

namespace DPDiv

/-- The DP divergence is generated by tests into a point, i.e. by `[0, 1]`-valued test functions
(Prop. 9). -/
theorem isGenerated_dp : dp.{u}.IsGenerated PUnit.{u + 1} := by
  intro α I _ μ ν _ _
  refine le_antisymm (iSup₂_le fun S hS ↦ ?_) (iSup₂_le fun k _ ↦ IsSubstitutive.bind_le α k μ ν)
  have hf : Measurable (S.indicator fun _ ↦ (1 : ℝ≥0∞)) := measurable_const.indicator hS
  have := isSubMarkovKernel_massKernel.{u} hf fun _ ↦ Set.indicator_le_self' (by simp) _
  refine le_iSup₂_of_le (massKernel hf) this (le_iSup₂_of_le .univ .univ ?_)
  simp [lintegral_indicator_const hS]

end DPDiv
