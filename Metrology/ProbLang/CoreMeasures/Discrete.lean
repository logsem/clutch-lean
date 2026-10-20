module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax

meta import Metrology.Meta

@[expose] public section

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-! # Measurable spaces on syntax atoms

The discrete (⊤) σ-algebra on variables, locations, labels, operators and types. -/

instance instMeasurableSpaceVar : MeasurableSpace Var := ⊤

instance instMeasurableSpaceLoc : MeasurableSpace Loc := ⊤

instance instMeasurableSpaceLbl : MeasurableSpace Lbl := ⊤

instance instMeasurableSpaceUnOp : MeasurableSpace UnOp := ⊤

instance instMeasurableSpaceBinOp : MeasurableSpace BinOp := ⊤

instance instMeasurableSpaceTy : MeasurableSpace Ty := ⊤

end ProbLangMeasures
