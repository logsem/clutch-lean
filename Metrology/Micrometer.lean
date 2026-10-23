module

public meta import Metrology.Meta.Discrete

-- `specCoupl`, `progCoupl`, `wp` and the lifting lemmas
public import Metrology.Micrometer.MicrometerWpGS
public import Metrology.Micrometer.SpecCoupl
public import Metrology.Micrometer.ProgCoupl
public import Metrology.Micrometer.Wp
public import Metrology.Micrometer.WpRules
public import Metrology.Micrometer.WpLifting
public import Metrology.Micrometer.WpEctxLifting
public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Micrometer.Lifting

-- primitive and coupling rules
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Micrometer.Asm
public import Metrology.Micrometer.UnifInt
public import Metrology.Micrometer.CouplingRules
public import Metrology.Micrometer.CouplingRulesLaw
public import Metrology.Micrometer.SpecAdvRules
public import Metrology.Micrometer.ContinuousSampler
public import Metrology.Micrometer.ContinuousCouplings
public import Metrology.Micrometer.CappedCredits

-- tactics
public import Metrology.Micrometer.OpenInv
public import Metrology.Micrometer.WpTactics

-- relational model, compatibility lemmas and the fundamental theorem
public import Metrology.Micrometer.LRel
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.Interp
public import Metrology.Micrometer.BinLogRelated
public import Metrology.Micrometer.AppRelRulesPure
public import Metrology.Micrometer.AppRelRules
public import Metrology.Micrometer.RelTactics
public import Metrology.Micrometer.Compatibility
public import Metrology.Micrometer.CompatibilityState
public import Metrology.Micrometer.FundamentalBase
public import Metrology.Micrometer.FundamentalCompat
public import Metrology.Micrometer.FundamentalOps
public import Metrology.Micrometer.Fundamental

-- adequacy
public import Metrology.Micrometer.Adequacy
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.AdequacyTV
public import Metrology.Micrometer.BinLogRelatedCtx
public import Metrology.Micrometer.Soundness
public import Metrology.Micrometer.Mechanism
public import Metrology.Micrometer.MechanismZcdp

-- examples and tests
public import Metrology.Micrometer.Examples
public import Metrology.Micrometer.RelTacticsTest
public import Metrology.Micrometer.BindLawTest

/-! # Micrometer

Umbrella import for the approximate relational program logic (a port of clutch's Approxis): the
`wp` modalities and their rules, the relational model and fundamental theorem, and adequacy. -/
