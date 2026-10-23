module

public import Metrology.TotalEris.Glm
public import Metrology.Iris.AppProgram
public import Metrology.Iris.ErrorCredits
public import Metrology.ProbLang.Reals
public import Iris.Algebra.Auth

@[expose] public section

/-! # Eris ghost state definitions -/

open Iris Auth
open scoped ErrorCredit

namespace ProbLang

namespace TotalEris

/-- Concrete ghost-state class for Eris. -/
class ErisGS (rT : outParam (Type _)) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (hlc : outParam HasLC)
    (GF : BundledGFunctors) where
  /-- The program-state ghost state. -/
  appGS : AppGS rT GF
  /-- The error-credit ghost state. -/
  ecGS : ECGS GF
  /-- The invariant ghost state. -/
  invGS : InvGS_gen hlc GF

attribute [reducible, instance] ErisGS.appGS ErisGS.ecGS

/-- `ErisGS.invGS`, with the measurable space and language read off the instance, not searched
for first. -/
@[reducible]
instance ErisGS.instInvGS {R : Type _} {M : MeasurableSpace R} {P : LawfulProbLangℝ R}
    {hlc : HasLC} {GF : BundledGFunctors} [ErisGS R hlc GF] : InvGS_gen hlc GF := ErisGS.invGS

section ErisInstance

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- The Eris weakest-precondition state interpretation from the ghost-state components. -/
noncomputable instance erisWpGS_of_components : ErisWpGS (rT := rT) GF where
  hlc := hlc
  invGS := inferInstance
  stateInterp σ := appStateAuth σ
  errInterp ε := ecAuth ε

/-! ### Unfolding lemmas -/

/-- The state interpretation is the program-state authority. -/
@[simp] theorem erisWpGS_stateInterp_eq :
    (ErisWpGS.stateInterp : State rT → IProp GF) = appStateAuth := rfl

/-- The error interpretation is the error-credit authority. -/
@[simp] theorem erisWpGS_errInterp_eq :
    (ErisWpGS.errInterp (rT := rT) : ENNReal → IProp GF) = ecAuth := rfl

end ErisInstance

/-- The concrete `BundledGFunctors` for Eris. -/
noncomputable def erisGF : BundledGFunctors := fun
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (Auth ErrorCredit), by infer_instance⟩
  | 5 => ⟨constOF (SpecHeap ℝ), by infer_instance⟩
  | 6 => ⟨constOF SpecTapes, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

/-- `erisGF` carries the world-satisfaction ghost state. -/
instance : WsatGpreS erisGF where
  inv := { τ := 0, transp := by unfold erisGF; rfl }
  enabled := { τ := 1, transp := by unfold erisGF; rfl }
  disabled := { τ := 2, transp := by unfold erisGF; rfl }

/-- `erisGF` carries the later-credit ghost state. -/
instance : LcGpreS erisGF where
  lc_elem := { τ := 3, transp := by unfold erisGF; rfl }

/-- `erisGF` carries the invariant ghost state. -/
instance : InvGpreS erisGF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

/-- `erisGF` carries the error-credit ghost state. -/
instance : ECPreGS erisGF where
  ec := { τ := 4, transp := by unfold erisGF; rfl }

/-- `erisGF` carries the heap and tape ghost state. -/
instance : AppPreGS ℝ erisGF where
  heap := { τ := 5, transp := by unfold erisGF; rfl }
  tapes := { τ := 6, transp := by unfold erisGF; rfl }

end TotalEris
end ProbLang
