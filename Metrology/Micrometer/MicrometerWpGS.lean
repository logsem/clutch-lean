module

public import Metrology.Iris.SpecUpdate
public import Metrology.Iris.BudgetCredits
public import Metrology.Iris.Fixpoint
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Erasable
public import Metrology.ProbLang.Erasure
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

/-! # Micrometer ghost state

The ghost-state classes behind `wp`: `MicrometerWpGS` (invariants, program-state and spec
interpretations) and `BudgetGS` (the budget interpretation). -/

@[expose] public section

open Std Iris Iris.BI Iris.ProofMode OFE COFE ProbLang GradedLifting

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]

/-! ## Program state and spec

`L` is an explicit argument of `wp` (never a class parameter), so modality instances unify
without an `L` metavariable. -/

/-- The ghost state of `wp`: invariants, the program-state interpretation, and (from
`SpecUpdateGS`) the spec interpretation `specInterp`. -/
class MicrometerWpGS {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (GF : BundledGFunctors) extends SpecUpdateGS rT GF where
  /-- Whether later credits are available (adequacy uses `.hasNoLC`). -/
  hlc : HasLC
  /-- The invariant ghost state. -/
  invGS : InvGS_gen hlc GF
  /-- The authoritative program state, `appStateAuth` in `micrometerWpGS_of_components`. -/
  stateInterp : State rT → IProp GF

attribute [reducible, instance] MicrometerWpGS.invGS

/-! ## Budget -/

/-- The budget owned by the state interpretation of `wp` (clutch-dp's `●↯m`). It depends on the
budget type only, never on `L`. -/
class BudgetGS (B : Type) (GF : BundledGFunctors) where
  /-- The resource holding a given budget. -/
  interp : B → IProp GF

/-- The resource `wp` owns for budget `b`. -/
abbrev budgetInterp {B : Type} {GF : BundledGFunctors} [BudgetGS B GF] (b : B) : IProp GF :=
  BudgetGS.interp b

/-- With budget credits, the budget resource is the authoritative credit `bcAuth`. -/
instance BudgetGS.ofBudgetCredit {B : Type} [AddCommMonoid B] {GF : BundledGFunctors}
    [BudgetCreditGS B GF] : BudgetGS B GF :=
  ⟨bcAuth⟩

end ProbLang
