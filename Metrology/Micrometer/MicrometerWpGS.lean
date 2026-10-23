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

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- The ghost state of `wp`. -/
class MicrometerWpGS {rT : outParam Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (GF : BundledGFunctors) extends SpecUpdateGS rT GF where
  hlc : HasLC
  invGS : InvGS_gen hlc GF
  stateInterp : State rT → IProp GF

/-- `MicrometerWpGS.invGS`, with the measurable space and language read off the instance, not
searched for first. -/
@[reducible]
instance MicrometerWpGS.instInvGS {R : Type} {M : MeasurableSpace R} {P : LawfulProbLangℝ R}
    {GF : BundledGFunctors} [w : MicrometerWpGS (rT := R) GF] : InvGS_gen w.hlc GF := w.invGS

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
