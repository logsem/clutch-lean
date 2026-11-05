module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.BaseLit
public import Metrology.ProbLang.CoreMeasures.Shapes

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen

@[expose] public section

noncomputable section ProbLangMeasures

/-! # Measurable space on patterns

The σ-algebra on `Pat`, from the `MeasurableSpace` deriving handler (`CylinderGen.lean`). -/

namespace ProbLang.Pat

deriving instance MeasurableSpace for Pat

end Pat
end ProbLang
end ProbLangMeasures
