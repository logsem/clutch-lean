module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.Shapes

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen

@[expose] public section

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-! # Measurable space on evaluation-context items

Derives the σ-algebra on `EctxItem`. -/

namespace ProbLang.EctxItem

/-! Deriving `MeasurableSpace` generates the cylinder σ-algebra, measurable constructors, embeddings
and projections, and the lemmas `measurable_casesOn(_param)` (functions by `casesOn`). -/

deriving instance MeasurableSpace for EctxItem

end EctxItem
end ProbLang
end ProbLangMeasures
