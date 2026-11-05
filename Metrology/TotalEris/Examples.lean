module

public import Metrology.TotalEris.Examples.Basic
public import Metrology.TotalEris.Examples.Sample
public import Metrology.TotalEris.Examples.BiasedWalk
public import Metrology.TotalEris.Examples.Coins
public import Metrology.TotalEris.Examples.GeometricTotal
public import Metrology.TotalEris.Examples.Irrational
public import Metrology.TotalEris.Examples.TwoWorlds
public import Metrology.TotalEris.Examples.Samplers
public import Metrology.TotalEris.Examples.SteppingDisplayTest
public import Metrology.TotalEris.Examples.WpTacticsTest

@[expose] public section

/-! # TotalEris examples

Imported from `Metrology` so every example, including the regression suites, stays in the default
build. `Examples.RandomWalk`, with its intended `sorry`, is imported from `Metrology` directly so
the release leaves it out. -/
