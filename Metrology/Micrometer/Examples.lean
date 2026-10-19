module

public import Metrology.Micrometer.Examples.OTP
public import Metrology.Micrometer.Examples.ContinuousOTP
public import Metrology.Micrometer.Examples.Presample
public import Metrology.Micrometer.Examples.SkipZero
public import Metrology.Micrometer.Examples.AbsorbingExit
public import Metrology.Micrometer.Examples.Retry
public import Metrology.Micrometer.Examples.RandomizedResponse
public import Metrology.Micrometer.Examples.RandomizedResponseLoop
public import Metrology.Micrometer.Examples.PublicChoice
public import Metrology.Micrometer.Examples.NoisyCount
public import Metrology.Micrometer.Examples.ContextualDp
public import Metrology.Micrometer.Examples.RandomizedResponseRenyi
public import Metrology.Micrometer.Examples.RandomizedResponseCurve
public import Metrology.Micrometer.Examples.RandomizedResponseAdaptive
public import Metrology.Micrometer.Examples.RandomizedResponseZcdp
public import Metrology.Micrometer.Examples.RandomizedResponseTcdp
public import Metrology.Micrometer.Examples.RandomizedResponseChi2
public import Metrology.Micrometer.Examples.GaussianZcdp
public import Metrology.Micrometer.Examples.Switching
public import Metrology.Couplings.Examples

/-! # Examples, by divergence and by program-logic rule

Each file proves a short refinement in Micrometer and reads a standard statement off it through
adequacy. Lifting-level examples (no programs) live in `Couplings/Examples`.

| Divergence | Examples |
| --- | --- |
| equality (any lifting) | `OTP`, `ContinuousOTP`, `Presample` |
| total variation | `SkipZero`, `Retry`, `AbsorbingExit`, `Switching` |
| pure DP | `RandomizedResponse`, `RandomizedResponseLoop`, `PublicChoice`, `NoisyCount`, `ContextualDp` |
| Rényi at one order | `RandomizedResponseRenyi`, `RandomizedResponseAdaptive`, `Couplings.Examples.AdaptiveRenyi` |
| Rényi curve | `RandomizedResponseCurve` |
| zCDP | `RandomizedResponseZcdp`, `RandomizedResponseLoop`, `GaussianZcdp`, `Couplings.Examples.GaussianComposition` |
| tCDP | `RandomizedResponseTcdp` |
| χ² | `RandomizedResponseChi2` |
| KL | `Couplings.Examples.KLCoinFlips` (lifting level only) |

| Rule | Examples |
| --- | --- |
| coupling draws by a bijection | `OTP`, `ContinuousOTP` (continuous samples) |
| presampling with tapes | `Presample` |
| spending a credit on one draw | `SkipZero`, `RandomizedResponse` |
| absorbing exit, capped credits | `AbsorbingExit` |
| amplification | `Retry` |
| recursion (`rec`, induction on the unfolded loop) | `RandomizedResponseLoop` |
| non-canonical bind laws | `PublicChoice` (`dpChoice`), `RandomizedResponseAdaptive` (escort) |
| programs as mechanisms (`progMech_isPrivate`) | `RandomizedResponseLoop`, `RandomizedResponseZcdp` |
| conversions between divergences | `RandomizedResponseZcdp`, `RandomizedResponseTcdp`, `RandomizedResponseCurve` |
| samplers given by a spec | `GaussianZcdp`, `NoisyCount` |
| contextual refinement | `ContextualDp` |
-/

@[expose] public section

end
