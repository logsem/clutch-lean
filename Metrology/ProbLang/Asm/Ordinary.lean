module

public import Metrology.ProbLang.Asm.Step
public import Metrology.ProbLang.DetStep

/-! # Ordinary program transitions under the foreign-call kernel -/

@[expose] public section

namespace ProbLang.Asm

open MeasureTheory MeasureTheory.Measure

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

section

variable (env : FfiEnv rT)

/-- Every enabled base-language transition has exactly the same foreign-kernel distribution. -/
theorem primStepWith_eq_primStep_of_nonzero (ρ : Cfg rT)
    (hne : primStep ρ ≠ 0) : primStepWith env ρ = primStep ρ := by
  unfold primStepWith primStep
  cases hd : ρ.expr.decomp with
  | mk K redex =>
    cases redex <;> try rfl
    all_goals exact absurd (by simp [primStep, hd, headStep]) hne

/-- A base-language step that is a point mass stays that point mass under `primStepWith`. -/
theorem primStepWith_eq_dirac_of_primStep {ρ ρ' : Cfg rT}
    (h : primStep ρ = dirac ρ') : primStepWith env ρ = dirac ρ' :=
  h ▸ primStepWith_eq_primStep_of_nonzero env ρ (by rw [h]; exact dirac_ne_zero)

/-- A base-language pure step remains the same pure transition under a foreign-call environment. -/
theorem pureStep_with {e₁ e₂ : Exp rT} (h : PureStep e₁ e₂) (σ : State rT) :
    primStepWith env ⟨e₁, σ⟩ = dirac ⟨e₂, σ⟩ := by
  exact primStepWith_eq_dirac_of_primStep env (h.det σ)

/-- Storing into an allocated cell steps to unit under `primStepWith`. -/
theorem store_step_with (σ : State rT) (l : Loc) (old value : Val rT)
    (hlookup : σ.heap[l]? = some old) :
    primStepWith env ⟨.store (.lit (.loc l)) (Exp.ofVal value), σ⟩ =
      dirac ⟨.lit .unit, σ.update_heap (·.insert l value)⟩ := by
  have hd : (Exp.store (.lit (.loc l)) (Exp.ofVal value)).decompItem = none := by
    simp only [Exp.decompItem, Exp.toVal?_ofVal]
    rfl
  have hbase : primStep ⟨.store (.lit (.loc l)) (Exp.ofVal value), σ⟩ =
      dirac ⟨.lit .unit, σ.update_heap (·.insert l value)⟩ := by
    rw [primStep_eq_headStep hd]
    simp [headStep, Exp.asValM, Exp.toVal?_ofVal, hlookup]
  exact primStepWith_eq_dirac_of_primStep env hbase

/-- Allocation steps to a fresh location under `primStepWith`. -/
theorem alloc_step_with (σ : State rT) (value : Val rT) :
    primStepWith env ⟨.alloc (Exp.ofVal value), σ⟩ =
      dirac ⟨.lit (.loc σ.heap.fresh), σ.update_heap (·.insert σ.heap.fresh value)⟩ := by
  have hd : (Exp.alloc (Exp.ofVal value)).decompItem = none := by
    simp [Exp.decompItem, Exp.toVal?_ofVal]
  have hbase : primStep ⟨.alloc (Exp.ofVal value), σ⟩ =
      dirac ⟨.lit (.loc σ.heap.fresh), σ.update_heap (·.insert σ.heap.fresh value)⟩ := by
    rw [primStep_eq_headStep hd]
    simp [headStep, Exp.asValM, Exp.toVal?_ofVal]
  exact primStepWith_eq_dirac_of_primStep env hbase

end

end ProbLang.Asm
