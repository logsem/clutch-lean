module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod

/-! General facts about measures. -/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {X X' X'' Y Z Φ Ψ : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace X'']
  [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace Φ] [MeasurableSpace Ψ]

/-- Pushing forward commutes with a commuting square. -/
theorem map_map_of_comm {ρ : Φ → X} {h : X → X''} {l : Φ → Ψ} {ρ' : Ψ → X''}
    (hc : ∀ φ, h (ρ φ) = ρ' (l φ)) (μ : Measure Φ) (hρ : Measurable ρ := by fun_prop)
    (hh : Measurable h := by fun_prop) (hl : Measurable l := by fun_prop)
    (hρ' : Measurable ρ' := by fun_prop) :
    (μ.map ρ).map h = (μ.map l).map ρ' := by
  rw [map_map hh hρ, map_map hρ' hl]
  exact congrArg (μ.map ·) (funext hc)

@[fun_prop]
theorem _root_.Measurable.measure_prod {f : Z → Measure X} {g : Z → Measure Y}
    (hf : Measurable f) (hg : Measurable g) [∀ z, IsFiniteMeasure (f z)]
    [∀ z, IsFiniteMeasure (g z)] : Measurable fun z ↦ (f z).prod (g z) := by
  have hf' : Measurable fun z ↦ (⟨f z, inferInstance⟩ : FiniteMeasure X) := hf.subtype_mk
  have hg' : Measurable fun z ↦ (⟨g z, inferInstance⟩ : FiniteMeasure Y) := hg.subtype_mk
  exact FiniteMeasure.measurable_fun_prod.comp (hf'.prodMk hg')

/-- Pushing forward a bind is binding the pushed-forward kernel. -/
theorem map_bind_eq {κ : Φ → Measure X} {k : X → Y} (μ : Measure Φ)
    (hκ : Measurable κ := by fun_prop) (hk : Measurable k := by fun_prop) :
    (μ.bind κ).map k = μ.bind fun φ ↦ (κ φ).map k := by
  rw [bind, bind, ← join_map_map hk, map_map (measurable_map k hk) hκ]
  rfl

/-- Binding a pushed-forward measure is binding along the composite kernel. -/
theorem bind_map_eq {d : Φ → X} {h : X → Measure Y} (μ : Measure Φ)
    (hd : Measurable d := by fun_prop) (hh : Measurable h := by fun_prop) :
    (μ.map d).bind h = μ.bind (h ∘ d) := by
  rw [bind, bind, map_map hh hd]

/-- Binding commutes with a commuting square of kernels. -/
theorem bind_map_of_comm {ρ : Φ → X} {h : X → Measure X'} {κ : Φ → Measure Ψ} {ρ' : Ψ → X'}
    (hc : ∀ φ, h (ρ φ) = (κ φ).map ρ') (μ : Measure Φ) (hρ : Measurable ρ := by fun_prop)
    (hh : Measurable h := by fun_prop) (hκ : Measurable κ := by fun_prop)
    (hρ' : Measurable ρ' := by fun_prop) :
    (μ.map ρ).bind h = (μ.bind κ).map ρ' := by
  rw [bind_map_eq μ hρ hh, map_bind_eq μ hκ hρ']
  exact congrArg μ.bind (funext hc)

/-- The supremum of an increasing sequence of measures is computed setwise. -/
theorem iSup_apply_of_monotone {μ : ℕ → Measure X} (hμ : Monotone μ) {s : Set X}
    (hs : MeasurableSet s) : (⨆ n, μ n) s = ⨆ n, μ n s := by
  let ν : Measure X := ofMeasurable (fun s _ ↦ ⨆ n, μ n s) (by simp) fun f hf hd ↦ by
    simp_rw [measure_iUnion hd hf, ENNReal.tsum_eq_iSup_sum]
    rw [iSup_comm]
    exact iSup_congr fun _ ↦ (ENNReal.finsetSum_iSup_of_monotone fun k _ _ h ↦ hμ h (f k)).symm
  have hμν : ⨆ n, μ n ≤ ν := iSup_le fun n ↦ le_iff.2 fun t ht ↦ by
    rw [ofMeasurable_apply _ ht]
    exact le_iSup (μ · t) n
  refine le_antisymm ?_ (iSup_le fun n ↦ le_iff'.1 (le_iSup μ n) s)
  exact (le_iff'.1 hμν s).trans_eq (ofMeasurable_apply _ hs)

/-- Integrals against an increasing sequence of measures converge (monotone convergence). -/
theorem lintegral_iSup_of_monotone {μ : ℕ → Measure X} (hμ : Monotone μ) {f : X → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x, f x ∂(⨆ n, μ n) = ⨆ n, ∫⁻ x, f x ∂μ n := by
  refine le_antisymm ?_ (iSup_le fun n ↦ lintegral_mono' (le_iSup μ n) le_rfl)
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  refine iSup_le fun k ↦ ?_
  have : (SimpleFunc.eapprox f k).lintegral (⨆ n, μ n) =
      ⨆ n, (SimpleFunc.eapprox f k).lintegral (μ n) := by
    simp only [SimpleFunc.lintegral, iSup_apply_of_monotone hμ (SimpleFunc.measurableSet_fiber _ _),
      ENNReal.mul_iSup]
    exact ENNReal.finsetSum_iSup_of_monotone fun _ _ _ h ↦ mul_le_mul_right (hμ h _) _
  exact this.trans_le (iSup_mono fun n ↦ lintegral_eapprox_le_lintegral hf k)

/-- Binding is monotone in the measure. -/
theorem bind_mono_left {μ μ' : Measure X} (h : μ ≤ μ') {f : X → Measure Y}
    (hf : Measurable f := by fun_prop) : μ.bind f ≤ μ'.bind f := le_iff.2 fun s hs ↦ by
  rw [bind_apply hs hf.aemeasurable, bind_apply hs hf.aemeasurable]
  exact lintegral_mono' h le_rfl

/-- Binding commutes with the supremum of an increasing sequence of measures. -/
theorem iSup_bind_of_monotone {μ : ℕ → Measure X} (hμ : Monotone μ) {f : X → Measure Y}
    (hf : Measurable f := by fun_prop) : (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  have hmono : Monotone fun n ↦ (μ n).bind f := fun _ _ h ↦ bind_mono_left (hμ h) hf
  ext s hs
  rw [iSup_apply_of_monotone hmono hs, bind_apply hs hf.aemeasurable,
    lintegral_iSup_of_monotone hμ (f := (f · s)) ((measurable_coe hs).comp hf)]
  simp_rw [bind_apply hs hf.aemeasurable]

/-- Pushing forward commutes with the supremum of an increasing sequence of measures. -/
theorem map_iSup_of_monotone {μ : ℕ → Measure X} (hμ : Monotone μ) {f : X → Y}
    (hf : Measurable f := by fun_prop) : (⨆ n, μ n).map f = ⨆ n, (μ n).map f := by
  simp_rw [← bind_dirac_eq_map _ hf]
  exact iSup_bind_of_monotone hμ

end MeasureTheory.Measure
