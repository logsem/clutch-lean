module

public import Metrology.Micrometer.Examples.RandomizedResponse.Basic
public import Metrology.Micrometer.Examples.RandomizedResponse.Dp
public import Metrology.Micrometer.Examples.RandomizedResponse.Zcdp
public import Metrology.Micrometer.Examples.RandomizedResponse.Tcdp
public import Metrology.Micrometer.Examples.RandomizedResponse.Renyi
public import Metrology.Micrometer.Examples.RandomizedResponse.Curve
public import Metrology.Micrometer.Examples.RandomizedResponse.Chi2
public import Metrology.Micrometer.Examples.RandomizedResponse.FillKl
public import Metrology.Micrometer.Examples.RandomizedResponse.Twice
public import Metrology.Micrometer.Examples.RandomizedResponse.Adaptive
public import Metrology.Micrometer.Examples.RandomizedResponse.AdaptiveChi2

/-! # Randomized response, one file per divergence

`Basic` proves one round and the `k`-round loop in any lifting (`rrCount_isPrivate`); each other
file supplies one coupling of the draws and reads off its divergence. `Twice` (two bits) and
`Adaptive` (Rényi-2; χ² in `AdaptiveChi2`) are separate programs. -/

@[expose] public section

end
