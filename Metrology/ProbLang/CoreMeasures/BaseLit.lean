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

/-! # Measure space on base lits -/

namespace ProbLang.BaseLit

/-! Deriving `MeasurableSpace` (`CylinderGen.lean`) generates the cylinder σ-algebra, the
constructor embeddings and projections, their measurability lemmas, and the `casesOn` keystones
`measurable_casesOn` / `measurable_casesOn_param`. -/

deriving instance MeasurableSpace for BaseLit

end BaseLit
end ProbLang
end ProbLangMeasures
