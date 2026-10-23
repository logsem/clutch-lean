module

public import Metrology.ProbLang.Asm.Step
public import Metrology.ProbLang.DetStep

/-! # Ordinary program transitions under the foreign-call kernel -/

@[expose] public section

namespace ProbLang.Asm

open MeasureTheory MeasureTheory.Measure

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- Every enabled base-language transition has exactly the same foreign-kernel distribution. -/
theorem primStepWith_eq_primStep_of_nonzero (env : FfiEnv rT) (ρ : Cfg rT)
    (hne : primStep ρ ≠ 0) : primStepWith env ρ = primStep ρ := by
  unfold primStepWith primStep
  cases hd : ρ.expr.decomp with
  | mk K redex =>
    cases redex <;> try rfl
    all_goals
      exfalso
      apply hne
      simp [primStep, hd, headStep]

/-- A base-language pure step remains the same pure transition under a foreign-call environment. -/
theorem pureStep_with (env : FfiEnv rT) {e₁ e₂ : Exp rT} (h : PureStep e₁ e₂) (σ : State rT) :
    primStepWith env ⟨e₁, σ⟩ = dirac ⟨e₂, σ⟩ := by
  rw [primStepWith_eq_primStep_of_nonzero env _ (h.safe σ), h.det σ]

/-- A store into an allocated cell retains its actual ordinary-language transition in the FFI. -/
theorem store_step_with (env : FfiEnv rT) (σ : State rT) (l : Loc) (old value : Val rT)
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
  rw [primStepWith_eq_primStep_of_nonzero env _ (by rw [hbase]; exact dirac_ne_zero), hbase]

/-- Fresh allocation has the actual ordinary-language transition under the explicit FFI kernel. -/
theorem alloc_step_with (env : FfiEnv rT) (σ : State rT) (value : Val rT) :
    primStepWith env ⟨.alloc (Exp.ofVal value), σ⟩ =
      dirac ⟨.lit (.loc σ.heap.fresh), σ.update_heap (·.insert σ.heap.fresh value)⟩ := by
  have hd : (Exp.alloc (Exp.ofVal value)).decompItem = none := by
    simp [Exp.decompItem, Exp.toVal?_ofVal]
  have hbase : primStep ⟨.alloc (Exp.ofVal value), σ⟩ =
      dirac ⟨.lit (.loc σ.heap.fresh), σ.update_heap (·.insert σ.heap.fresh value)⟩ := by
    rw [primStep_eq_headStep hd]
    simp [headStep, Exp.asValM, Exp.toVal?_ofVal]
  rw [primStepWith_eq_primStep_of_nonzero env _ (by rw [hbase]; exact dirac_ne_zero), hbase]

end ProbLang.Asm
