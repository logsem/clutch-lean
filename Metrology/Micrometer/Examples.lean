module

public import Metrology.Micrometer.Examples.OTP
public import Metrology.Micrometer.Examples.ContinuousOTP
public import Metrology.Micrometer.Examples.Presample
public import Metrology.Micrometer.Examples.SkipZero
public import Metrology.Micrometer.Examples.AbsorbingExit
public import Metrology.Micrometer.Examples.Retry
public import Metrology.Micrometer.Examples.RandomizedResponse
public import Metrology.Micrometer.Examples.PublicChoice
public import Metrology.Micrometer.Examples.LeakyRR
public import Metrology.Micrometer.Examples.NoisyCount
public import Metrology.Micrometer.Examples.ContextualDp
public import Metrology.Micrometer.Examples.GaussianZcdp
public import Metrology.Micrometer.Examples.Switching
public import Metrology.Couplings.Examples

/-! # Examples, by divergence and by program-logic rule

Each file proves a short refinement in Micrometer and reads a standard statement off it through
adequacy. Lifting-level examples (no programs) live in `Couplings/Examples`.

By divergence (`RR` is `RandomizedResponse`):
* equality (any lifting): `OTP`, `ContinuousOTP`, `Presample`
* total variation: `SkipZero`, `Retry`, `AbsorbingExit`, `Switching`
* pure DP: `RR.Dp`, `PublicChoice`, `NoisyCount`, `ContextualDp`
* approximate DP: `LeakyRR`
* Rényi at one order: `RR.Renyi`, `RR.Adaptive`, `Couplings.Examples.AdaptiveRenyi`
* Rényi curve: `RR.Curve`
* zCDP: `RR.Zcdp`, `RR.Twice`, `GaussianZcdp`, `Couplings.Examples.GaussianComposition`
* tCDP: `RR.Tcdp`
* χ²: `RR.Chi2`
* KL: `Couplings.Examples.KLCoinFlips` (lifting level only)

By rule:
* coupling draws by a bijection: `OTP`, `ContinuousOTP` (continuous samples)
* presampling with tapes: `Presample`
* spending a credit on one draw: `SkipZero`, `RR.Basic`, `LeakyRR` (δ)
* absorbing exit, capped credits: `AbsorbingExit`
* amplification: `Retry`
* recursion (`rec`, `rel_fold`, induction on the unfolded loop): `Retry`, `RR.Basic`,
  `GaussianZcdp`
* one proof in any lifting (`rr_refines_of`, `rrCount_refines_of`, `rrCount_isPrivate`):
  `RR.Basic`, instantiated by `RR.Dp`, `RR.Zcdp`, `RR.Tcdp`, `RR.Renyi`, `RR.Curve`, `RR.Chi2`
* non-canonical bind laws: `PublicChoice` (`dpChoice`), `RR.Adaptive` (escort)
* programs as mechanisms (`progMech_isPrivate`): `RR.Basic`, `RR.Dp`, `RR.Twice`,
  `PublicChoice`, `LeakyRR`
* conversions between divergences: `RR.Twice`, `RR.Tcdp`, `RR.Curve`
* samplers given by a spec: `GaussianZcdp`, `NoisyCount`
* contextual refinement: `ContextualDp`, `ContinuousOTP`
* weakest preconditions against a spec (`wp_*`, `tp_*`): `RR.Basic`, `RR.Dp`, `RR.Twice`,
  `NoisyCount`, `GaussianZcdp`, `Switching`
-/

@[expose] public section

end
