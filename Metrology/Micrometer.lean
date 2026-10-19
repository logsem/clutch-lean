module

public meta import Metrology.Meta.Discrete
public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Micrometer.Lifting
public import Metrology.Micrometer.CappedCredits
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Micrometer.ContinuousSampler
public import Metrology.Micrometer.CouplingRules
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.Interp
public import Metrology.Micrometer.AppRelRules
public import Metrology.Micrometer.ChoiceRules
public import Metrology.Micrometer.SpecAdvRules
public import Metrology.Micrometer.RelTactics
public import Metrology.Micrometer.Compatibility
public import Metrology.Micrometer.Fundamental
public import Metrology.Micrometer.Adequacy
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.AdequacyTV
public import Metrology.Micrometer.Soundness
public import Metrology.Micrometer.Mechanism
public import Metrology.Micrometer.Examples.OTP
public import Metrology.Micrometer.Examples.Switching
public import Metrology.Micrometer.Examples.ContinuousOTP
public import Metrology.Micrometer.Examples.RandomizedResponse
public import Metrology.Micrometer.Examples.RandomizedResponseZcdp
public import Metrology.Micrometer.Examples.RandomizedResponseLoop
public import Metrology.Micrometer.Examples.GaussianZcdp
public import Metrology.Micrometer.Examples.SkipZero
public import Metrology.Micrometer.Examples.AbsorbingExit
public import Metrology.Micrometer.Examples.Presample
public import Metrology.Micrometer.Examples.PublicChoice
public import Metrology.Micrometer.Examples.Retry
public import Metrology.Micrometer.Examples.NoisyCount
public import Metrology.Micrometer.RelTacticsTest
public import Metrology.Micrometer.BindLawTest

@[expose] public section

/-!
# Micrometer

Top-level re-export of Micrometer, our approximate relational verification framework.
It ports the Approxis framework from `clutch/theories/approxis/approxis.v`.
-/
