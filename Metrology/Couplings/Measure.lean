module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod

/-! General facts about measures. -/

@[expose] public section

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

/-- Binding commutes with a commuting square of kernels. -/
theorem bind_map_of_comm {ρ : Φ → X} {h : X → Measure X'} {κ : Φ → Measure Ψ} {ρ' : Ψ → X'}
    (hc : ∀ φ, h (ρ φ) = (κ φ).map ρ') (μ : Measure Φ) (hρ : Measurable ρ := by fun_prop)
    (hh : Measurable h := by fun_prop) (hκ : Measurable κ := by fun_prop)
    (hρ' : Measurable ρ' := by fun_prop) :
    (μ.map ρ).bind h = (μ.bind κ).map ρ' := by
  ext A hA
  have hhA : Measurable fun x ↦ h x A := (measurable_coe hA).comp hh
  rw [bind_apply hA hh.aemeasurable, lintegral_map hhA hρ, map_apply hρ' hA,
    bind_apply (hρ' hA) hκ.aemeasurable]
  congr 1
  funext φ
  rw [hc, map_apply hρ' hA]

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
  ext A hA
  have hκk : Measurable fun φ ↦ (κ φ).map k := by fun_prop
  rw [map_apply hk hA, bind_apply (hk hA) hκ.aemeasurable, bind_apply hA hκk.aemeasurable]
  simp only [map_apply hk hA]

/-- Binding a pushed-forward measure is binding along the composite kernel. -/
theorem bind_map_eq {d : Φ → X} {h : X → Measure Y} (μ : Measure Φ)
    (hd : Measurable d := by fun_prop) (hh : Measurable h := by fun_prop) :
    (μ.map d).bind h = μ.bind (h ∘ d) := by
  ext A hA
  rw [bind_apply hA hh.aemeasurable, bind_apply hA (hh.comp hd).aemeasurable]
  exact lintegral_map ((measurable_coe hA).comp hh) hd

end MeasureTheory.Measure
