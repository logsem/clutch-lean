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

/-!
# Gaussian samplers

Aggregator for the `urand`-based Gauss sampler stack (all `sorry`-free, `rT = ℝ`), bottom-up:

```
RealDecrTrial ── decreasing trial (urand init, real `<` compare, twp_urand_exp presample)
  ├── HalfBernNegExp (LeHalf, BNEHalf)  ── concrete base-½ Bernoulli
  ├── NegExp                            ── negative-exponential sampler
  └── Selector (C, Bii, S, S0, B)       ── integer-part selection
BernoulliGeometric (AbstractBernoulli, GeometricTrial)
  └── BernIter (AbstractBernoulliI, IterTrial, AbstractBernoulli.toAbstractBernoulliI)
Gauss (G1, G2)  ← BNEHalf, GeometricTrial, IterTrial, B
  └── Gaussian (Gauss)                       ── real assembly + sign flip ⇒ N(0,1)
        └── GaussianAdequacy  ← DistributionAdequacy
              └── GaussianConcentration          ── Chebyshev/Chernoff/Mills tails
```

Laplace is still not included: its value reconstruction needs real scaling by
powers of two, which `BinOp.eval` does not yet have (real `+`, unary `-` and the
`toReal` coercion do exist).
-/
