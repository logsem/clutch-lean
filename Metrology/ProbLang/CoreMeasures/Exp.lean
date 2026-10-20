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

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-! # Measurable space on expressions

Derives the σ-algebra on `Exp`. -/

namespace ProbLang.Exp

/-! ### Generated definitions

`Shape`, `Leaves`, the σ-algebra and its measurability lemmas, derived with
`MeasurableSpace` (`CylinderGen.lean`). -/

deriving instance MeasurableSpace for Exp

end Exp
end ProbLang
end ProbLangMeasures
