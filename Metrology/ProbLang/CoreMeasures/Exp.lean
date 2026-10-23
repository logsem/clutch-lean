module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Pat
public import Metrology.ProbLang.CoreMeasures.Shapes

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen

@[expose] public section

noncomputable section ProbLangMeasures

/-! # Measurable space on expressions

The σ-algebra on `Exp`, from the `MeasurableSpace` deriving handler (`CylinderGen.lean`). -/

namespace ProbLang.Exp

deriving instance MeasurableSpace for Exp

end Exp
end ProbLang

/-! ## Reading literals

Measurable readers of integer and real literals, and measurable eliminators on `Exp`. -/

namespace ProbLang

open scoped ENNReal

variable {rT : Type _} [MeasurableSpace rT]

/-- Read a literal expression through `value`, with a default for non-literals. -/
def Exp.asLit (default : ℝ≥0∞) (value : BaseLit rT → ℝ≥0∞) : Exp rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ Exp.lit.π

/-- `Exp.asLit` is measurable when `value` is. -/
@[fun_prop]
theorem Exp.measurable_asLit (default : ℝ≥0∞) (value : BaseLit rT → ℝ≥0∞)
    (Hm : Measurable value) : Measurable (Exp.asLit default value) := by
  unfold Exp.asLit; fun_prop

/-- Read an integer literal through `value`, with a default for other literals. -/
def BaseLit.asInt (default : ℝ≥0∞) (value : Int → ℝ≥0∞) : BaseLit rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ BaseLit.int.π

/-- `BaseLit.asInt` is measurable. -/
@[fun_prop]
theorem BaseLit.measurable_asInt (default : ℝ≥0∞) (value : Int → ℝ≥0∞) :
    Measurable (BaseLit.asInt (rT := rT) default value) := by unfold asInt; fun_prop

/-- Read a real literal through `value`, with a default for other literals. -/
def BaseLit.asReal (default : ℝ≥0∞) (value : rT → ℝ≥0∞) : BaseLit rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ BaseLit.real.π

/-- `BaseLit.asReal` is measurable when `value` is. -/
@[fun_prop]
theorem BaseLit.measurable_asReal (default : ℝ≥0∞) (value : rT → ℝ≥0∞) (hv : Measurable value) :
    Measurable (BaseLit.asReal default value) := by unfold asReal; fun_prop

/-- Eliminating an integer literal through `g` is measurable. -/
theorem measurable_litInt_elim (g : Int → ℝ≥0∞) :
    Measurable (fun e : Exp rT => match e with | .lit (.int n) => g n | _ => 0) := by
  convert_to Measurable (Exp.asLit 0 (BaseLit.asInt 0 g))
  swap
  fun_prop
  ext e
  cases e <;> try rfl
  case lit b => cases b <;> rfl

/-- Eliminating a real literal through `g` is measurable. -/
theorem measurable_litReal_elim (g : rT → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun e : Exp rT => match e with | .lit (.real r) => g r | _ => 0) := by
  convert_to Measurable (Exp.asLit 0 (BaseLit.asReal 0 g))
  swap
  fun_prop
  ext e
  cases e <;> try rfl
  case lit r => cases r <;> rfl

end ProbLang

end ProbLangMeasures
