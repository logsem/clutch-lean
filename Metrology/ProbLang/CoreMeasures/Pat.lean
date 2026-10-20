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

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-! # Measurable space on patterns

The σ-algebra on `Pat`, derived with the `MeasurableSpace` deriver (`CylinderGen.lean`), which
also generates `Shape`, `Leaves` and their measurability lemmas. -/

namespace ProbLang.Pat

deriving instance MeasurableSpace for Pat

end Pat
end ProbLang
end ProbLangMeasures
