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

Gives `EctxItem` (one frame of an evaluation context `Ectx`) its σ-algebra by `deriving`. -/

namespace ProbLang.EctxItem

-- The handler generates the cylinder σ-algebra, constructor embeddings, projections and
-- `measurable_casesOn(_param)`.
deriving instance MeasurableSpace for EctxItem

end EctxItem
end ProbLang
end ProbLangMeasures
