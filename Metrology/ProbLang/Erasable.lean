module

public import Metrology.ProbLang.Exec

@[expose] public section

/-!
# Erasable state distributions

A state distribution is `Erasable` if sampling the state from it leaves every `execN m` unchanged
(Clutch `erasable.v`, but on whole configurations; see `ErasableExpr` for the projected form).
-/

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure

/-- Sampling the initial state from `μ` does not change `execN m` at any budget `m`. -/
def Erasable (μ : Measure (State rT)) (σ : State rT) : Prop :=
  ∀ e m, μ.bind (fun σ' => execN m ⟨e, σ'⟩) = execN m ⟨e, σ⟩

/-- A Dirac state distribution is erasable. -/
theorem Erasable.dret (σ : State rT) : Erasable (dirac σ) σ := by
  intro e m
  rw [dirac_bind (by measurability)]

end ProbLang
