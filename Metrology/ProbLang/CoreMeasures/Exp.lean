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

The σ-algebra on `Exp`, derived with the `MeasurableSpace` deriving handler (`CylinderGen.lean`);
it makes every constructor a measurable embedding. -/

namespace ProbLang.Exp

deriving instance MeasurableSpace for Exp

end Exp
end ProbLang
end ProbLangMeasures
