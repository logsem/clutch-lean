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

/-! The Micrometer ghost-state classes: the program logic's invariants, state and budget. -/

@[expose] public section

open Std Iris Iris.BI Iris.ProofMode OFE COFE ProbLang GradedLifting

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]

/-! ## Ghost state classes

`L` is an explicit argument of `wp` (never a class parameter), so modality instances unify
without an `L` metavariable. -/

/-- The ghost state of `wp`: spec updates, invariants and the program-state interpretation. -/
class MicrometerWpGS {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (GF : BundledGFunctors) extends SpecUpdateGS rT GF where
  /-- Whether later credits are available (adequacy uses `.hasNoLC`). -/
  hlc : HasLC
  /-- The invariant ghost state. -/
  invGS : InvGS_gen hlc GF
  /-- The authoritative program state, `appStateAuth` in `micrometerWpGS_of_components`. -/
  stateInterp : State rT → IProp GF

attribute [reducible, instance] MicrometerWpGS.invGS

/-- The budget owned by the state interpretation of `wp` (clutch-dp's `●↯m`). It depends on the
budget type only, never on `L`. -/
class BudgetGS (B : Type) (GF : BundledGFunctors) where
  interp : B → IProp GF

/-- The budget `wp` owns. -/
abbrev budgetInterp {B : Type} {GF : BundledGFunctors} [BudgetGS B GF] (b : B) : IProp GF :=
  BudgetGS.interp b

/-- With budget credits the budget is the authoritative budget credit. -/
instance BudgetGS.ofBudgetCredit {B : Type} [AddCommMonoid B] {GF : BundledGFunctors}
    [BudgetCreditGS B GF] : BudgetGS B GF :=
  ⟨bcAuth⟩

end ProbLang
