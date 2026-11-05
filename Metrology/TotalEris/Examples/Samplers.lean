module

public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
public import Metrology.TotalEris.Examples.Samplers.HalfBernNegExp
public import Metrology.TotalEris.Examples.Samplers.BernIter
public import Metrology.TotalEris.Examples.Samplers.NegExp
public import Metrology.TotalEris.Examples.Samplers.Selector
public import Metrology.TotalEris.Examples.Samplers.Gauss
public import Metrology.TotalEris.Examples.Samplers.GaussianAdequacy
public import Metrology.TotalEris.Examples.Samplers.GaussianConcentration
public import Metrology.TotalEris.Examples.Samplers.GaussianSum
public import Metrology.TotalEris.Examples.Samplers.Gaussian

@[expose] public section

/-! # Gaussian samplers

`RealDecrTrial` feeds `HalfBernNegExp`, `NegExp`, and `Selector`; these combine with `BernIter` to
build `Gauss`, adequacy, and concentration, while Laplace awaits real scaling in `BinOp.eval`. -/
