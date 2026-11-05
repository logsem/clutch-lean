module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Discrete
public import Metrology.ProbLang.CoreMeasures.Shapes

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen

@[expose] public section

noncomputable section ProbLangMeasures

/-! # Measurable space on base literals

The cylinder σ-algebra on `BaseLit rT`, derived by `CylinderGen.lean`. -/

namespace ProbLang.BaseLit

deriving instance MeasurableSpace for BaseLit

end BaseLit
end ProbLang
end ProbLangMeasures
