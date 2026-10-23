module

public import Metrology.Iris.SpecUpdate
public import Metrology.Iris.BudgetCredits
public import Metrology.Iris.Fixpoint
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Erasure
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

/-! # Micrometer Ghost State -/

@[expose] public section

open Std Iris Iris.BI Iris.ProofMode OFE COFE ProbLang GradedLifting

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

/-- The ghost state of `wp`. -/
class MicrometerWpGS (GF : BundledGFunctors)
    extends SpecUpdateGS rT GF where
  hlc : HasLC
  invGS : InvGS_gen hlc GF
  stateInterp : State rT → IProp GF

attribute [reducible, instance] MicrometerWpGS.invGS

/-! ## Budget -/

/-- Ghost state for budget interpretation. -/
class BudgetGS (B : Type) (GF : BundledGFunctors) where
  interp : B → IProp GF

section Budget
variable {B : Type} {GF : BundledGFunctors}
open BudgetGS

/-- The resource `wp` owns for budget `b`. -/
abbrev budgetInterp [BudgetGS B GF] (b : B) : IProp GF := interp b

/-- `BudgetGS` of `BudgetCreditGS`, using `bcAuth` as the interpretation. -/
instance BudgetGS.ofBudgetCredit [AddCommMonoid B] [BudgetCreditGS B GF] : BudgetGS B GF := ⟨bcAuth⟩

end Budget

end ProbLang
