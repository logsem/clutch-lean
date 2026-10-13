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
    rw [← EReal.coe_ennreal_zero, DPDiv.dp_le_iff]
    intro S _
    simp only [massKernel, Kernel.coe_mk, Measure.smul_apply, smul_eq_mul, toAdd_ofAdd,
      NNReal.coe_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul, add_zero]
    exact mul_le_mul_left (hfg hxy) _
  have hc := h htest
  rw [add_zero, ← ofAdd_add, add_zero, DPDiv.dp_le_iff] at hc
  have hε : ((ε : ℝ≥0∞) : EReal).exp = ENNReal.ofReal (Real.exp ε) := by
    rw [ENNReal.coe_nnreal_eq, EReal.coe_ennreal_ofReal, max_eq_left (NNReal.coe_nonneg ε),
      EReal.exp_coe]
  simpa [DPF, hε] using hc .univ .univ
