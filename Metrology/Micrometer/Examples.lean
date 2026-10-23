module

public import Metrology.Micrometer.Examples.OTP
public import Metrology.Micrometer.Examples.ContinuousOTP
public import Metrology.Micrometer.Examples.ContinuousRules
public import Metrology.Micrometer.Examples.Presample
public import Metrology.Micrometer.Examples.SkipZero
public import Metrology.Micrometer.Examples.AbsorbingExit
public import Metrology.Micrometer.Examples.Retry
public import Metrology.Micrometer.Examples.RandomizedResponse
public import Metrology.Micrometer.Examples.PublicChoice
public import Metrology.Micrometer.Examples.PublicChoiceZcdp
public import Metrology.Micrometer.Examples.LeakyRR
public import Metrology.Micrometer.Examples.NoisyCount
public import Metrology.Micrometer.Examples.ContextualDp
public import Metrology.Micrometer.Examples.GaussianZcdp
public import Metrology.Micrometer.Examples.Switching
public import Metrology.Couplings.Examples

/-! # Examples, by divergence, by program-logic rule, and by exit

Each file proves a short Micrometer refinement and reads a standard statement off it by adequacy.
Start with `RR.Basic`, one proof in any lifting. Lifting-only examples: `Couplings.Examples`.

By divergence (`RR` is `RandomizedResponse`):
* equality (any lifting): `OTP`, `ContinuousOTP`, `Presample` (one direction)
* total variation: `SkipZero`, `Retry`, `AbsorbingExit`, `Switching` (specs in `SwitchingListMap`,
  `SwitchingPRP`)
* pure DP: `RR.Dp`, `PublicChoice`, `NoisyCount`, `ContextualDp`
* approximate DP: `LeakyRR`
* Rényi at one order: `RR.Renyi`, `RR.Adaptive`, `Couplings.Examples.AdaptiveRenyi`
* Rényi curve: `RR.Curve`
* zCDP: `RR.Zcdp`, `RR.Twice`, `GaussianZcdp`, `Couplings.Examples.GaussianComposition`,
  `PublicChoiceZcdp` (from two-way pure DP)
* tCDP: `RR.Tcdp`
* χ²: `RR.Chi2`, `RR.AdaptiveChi2`
* KL: `RR.FillKl` (filled KL, in the logic; also read off Rényi and zCDP),
  `RR.AdaptiveFillKl` (adaptive, chain rule), `Couplings.Examples.KLCoinFlips`,
  `Couplings.Examples.AdaptiveFillKl` (lifting level)

By rule:
* coupling draws by a bijection: `OTP`, `ContinuousOTP` (continuous samples)
* continuous draws by credits, laws, and against `rand N` (`⌊N u⌋`): `ContinuousRules`
* presampling with tapes: `Presample`
* spending a credit on one draw: `SkipZero`, `RR.Basic`, `LeakyRR` (δ)
* absorbing exit, capped credits: `AbsorbingExit`
* amplification: `Retry`
* recursion (`rec`, `rel_fold`, induction on the unfolded loop): `Retry`, `RR.Basic`,
  `GaussianZcdp`
* one proof in any lifting (`rr_refines_of`, `rrCount_refines_of`, `rrCount_isPrivate`):
  `RR.Basic`, instantiated by `RR.Dp`, `RR.Zcdp`, `RR.Tcdp`, `RR.Renyi`, `RR.Curve`, `RR.Chi2`
* non-canonical bind laws: `PublicChoice` (`dpChoice`), `RR.Adaptive` (escort),
  `RR.AdaptiveChi2` (`escortPower`), `RR.AdaptiveFillKl` (`fillKl`)
* programs as mechanisms (`progMech_isPrivate`): `RR.Dp`, `RR.Twice`, `PublicChoice`, `LeakyRR`
  (`RR.Basic` states `IsPrivate` directly from `rrCount_div`)
* conversions between divergences: `RR.Twice`, `RR.Tcdp`, `RR.Curve`
* samplers given by a spec: `GaussianZcdp`, `NoisyCount`
* contextual refinement: `ContextualDp`, `ContinuousOTP`
* weakest preconditions against a spec (`wp_*`, `tp_*`): `RR.Basic`, `RR.Dp`, `RR.Twice`,
  `NoisyCount`, `GaussianZcdp`, `Switching`

By exit (the adequacy theorem that leaves the logic):
* `approximates_coupling`, `approximates_div`: a relational refinement from `↯b b` gives a coupling
  or a divergence bound (`RR.Basic`; `SkipZero`)
* `refines_coupling`: a relational refinement at budget 0 (`OTP`)
* `wp_adequacy`, `wp_adequacy_div`: a weakest precondition against a spec `⤇ e'` (`RR.Twice`,
  `RR.Dp`); `wp_adequacy_budget_lim` takes a limit of credits (`Switching`)
* `progMech_isPrivate`: a refinement for every pair of inputs gives `Mechanism.IsPrivate` (`RR.Dp`)
* `refines_ctx_dp`, `refines_sound_fresh`: contextual refinement (`ContextualDp`,
  `ContinuousOTP`)

Naming: lowercase `_dp`, `_zcdp` states a divergence between two runs; uppercase `_DP`, `_zCDP`
is the mechanism definition (Approximate Span Liftings, Def. 2.1–2.5; `Mechanism.DP`, `.zCDP`, ...).
-/

@[expose] public section

end
