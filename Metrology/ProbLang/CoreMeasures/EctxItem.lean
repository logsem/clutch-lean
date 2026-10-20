module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.Shapes

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen

@[expose] public section

-- TODO move this to the semantics file once we have that.

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-! # Measure space on evaluation-context items

Derives the σ-algebra on `EctxItem`. -/

namespace ProbLang.EctxItem

/-! Deriving `MeasurableSpace` generates the cylinder σ-algebra, measurable constructors, embeddings
and projections, and the `casesOn` keystones `measurable_casesOn` / `measurable_casesOn_param`. -/

deriving instance MeasurableSpace for EctxItem
