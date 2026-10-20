module

public import Metrology.ProbLang.CoreMeasures.Shapes
public import Metrology.ProbLang.CoreMeasures.BaseLit
public import Metrology.ProbLang.CoreMeasures.Pat
public import Metrology.ProbLang.CoreMeasures.Exp
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.EctxItem
public import Metrology.ProbLang.CoreMeasures.State
public import Metrology.ProbLang.CoreMeasures.Cfg
public import Metrology.ProbLang.CoreMeasures.Recurrences

/-!
# Measurable structure of ProbLang syntax

- `Discrete`: the `⊤` σ-algebra on atoms.
- `Shapes` and `CylinderGen`: the `deriving MeasurableSpace` handler, with `T ≃ Σ shape, leaves`.
- `BaseLit`, `Pat`, `Exp`, `EctxItem`: instances derived with it.
- `Val`: the comap of `Val.fst`. `State`: heaps. `Cfg`: tapes, states and configurations.
- `ArmTactics`: `apply_arms`, which applies `T.measurable_cases`/`measurable_struct_rec` with the
  arms read off a definition.
- `Recurrences`: measurability of substitution, opening, `decomp`, `eval` and `tryMatch`.
-/
