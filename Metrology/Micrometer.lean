module

public meta import Metrology.Meta.Discrete
public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Micrometer.Lifting
public import Metrology.Micrometer.CappedCredits
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Micrometer.ContinuousSampler
public import Metrology.Micrometer.CouplingRules
public import Metrology.Micrometer.CouplingRulesLaw
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.Interp
public import Metrology.Micrometer.AppRelRules
public import Metrology.Micrometer.SpecAdvRules
public import Metrology.Micrometer.RelTactics
public import Metrology.Micrometer.Compatibility
public import Metrology.Micrometer.Fundamental
public import Metrology.Micrometer.Adequacy
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.AdequacyTV
public import Metrology.Micrometer.Soundness
public import Metrology.Micrometer.Mechanism
public import Metrology.Micrometer.Examples
public import Metrology.Micrometer.RelTacticsTest
public import Metrology.Micrometer.BindLawTest

@[expose] public section

/-!
# Micrometer

Top-level re-export of Micrometer, our approximate relational verification framework.
It ports the Approxis framework from `clutch/theories/approxis/approxis.v`.
-/
