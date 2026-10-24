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

open Std Iris Iris.BI Iris.ProofMode OFE COFE GradedLifting

namespace ProbLang

/-- The ghost state of `wp`. -/
class MicrometerWpGS {rT : outParam Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (GF : BundledGFunctors) extends SpecUpdateGS rT GF where
  /-- Whether the invariant ghost state allows later credits. -/
  hlc : HasLC
  /-- The invariant ghost state. -/
  invGS : InvGS_gen hlc GF
  /-- The interpretation of the program state. -/
  stateInterp : State rT → IProp GF

/-- The invariant ghost state of a `MicrometerWpGS` instance, as an `InvGS_gen` instance. -/
@[reducible]
instance MicrometerWpGS.instInvGS {R : Type} [MeasurableSpace R] [LawfulProbLangℝ R]
    {GF : BundledGFunctors} [w : MicrometerWpGS (rT := R) GF] : InvGS_gen w.hlc GF := w.invGS

/-! ## Budget -/

/-- Ghost state for budget interpretation. -/
class BudgetGS (B : Type) (GF : BundledGFunctors) where
  /-- The resource owned for a budget. -/
  interp : B → IProp GF

variable {B : Type} {GF : BundledGFunctors}

/-- The resource `wp` owns for budget `b`. -/
abbrev budgetInterp [BudgetGS B GF] (b : B) : IProp GF := BudgetGS.interp b

/-- `BudgetGS` of `BudgetCreditGS`, using `bcAuth` as the interpretation. -/
instance BudgetGS.ofBudgetCredit [AddCommMonoid B] [BudgetCreditGS B GF] : BudgetGS B GF := ⟨bcAuth⟩

end ProbLang
