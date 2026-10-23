module

public import Metrology.LiveEris.Glm
public import Metrology.LiveEris.Credits
public import Metrology.Iris.AppProgram
public import Metrology.ProbLang.Reals
public import Iris.Algebra.Auth

@[expose] public section

/-! # LiveEris ghost state -/

open Iris Auth
open scoped ENNReal

namespace ProbLang
namespace LiveEris

/-- The two coordinates of a LiveEris credit vector: the failure budget, and the total budget for
failing or idling forever. -/
inductive Coord where
  | err
  | tot

/-- The credit vector of `ε` error credits and `δ` divergence credits. -/
abbrev creditVec (ε δ : ℝ≥0∞) : Coord → ℝ≥0∞
  | .err => ε
  | .tot => ε + δ

class LiveGS (rT : outParam (Type _)) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (hlc : outParam HasLC)
    (GF : BundledGFunctors) where
  appGS : AppGS rT GF
  lcGS : LCGS GF
  invGS : InvGS_gen hlc GF

attribute [reducible, instance] LiveGS.appGS LiveGS.lcGS

/-- `LiveGS.invGS`, with the measurable space and language read off the instance, not searched
for first. -/
@[reducible]
instance LiveGS.instInvGS {R : Type _} {M : MeasurableSpace R} {P : LawfulProbLangℝ R}
    {hlc : HasLC} {GF : BundledGFunctors} [LiveGS R hlc GF] : InvGS_gen hlc GF := LiveGS.invGS

section LiveInstance

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [LiveGS rT hlc GF]

@[reducible]
noncomputable instance liveWpGS_of_components : LiveWpGS rT Coord GF where
  hlc := hlc
  invGS := inferInstance
  stateInterp σ := appStateAuth σ
  creditInterp c := iprop(∃ δ, ⌜c .tot = c .err + δ⌝ ∗ creditAuth (c .err) δ)

@[simp] theorem liveWpGS_stateInterp_eq :
    (LiveWpGS.stateInterp : State rT → IProp GF) = appStateAuth := rfl

@[simp] theorem liveWpGS_creditInterp_eq :
    (LiveWpGS.creditInterp : (Coord → ℝ≥0∞) → IProp GF) =
      fun c => iprop(∃ δ, ⌜c .tot = c .err + δ⌝ ∗ creditAuth (c .err) δ) := rfl

end LiveInstance

noncomputable def liveGF : BundledGFunctors := fun
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (Auth LiveCredit), by infer_instance⟩
  | 5 => ⟨constOF (SpecHeap ℝ), by infer_instance⟩
  | 6 => ⟨constOF SpecTapes, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS liveGF where
  inv := { τ := 0, transp := by unfold liveGF; rfl }
  enabled := { τ := 1, transp := by unfold liveGF; rfl }
  disabled := { τ := 2, transp := by unfold liveGF; rfl }

instance : LcGpreS liveGF where
  lc_elem := { τ := 3, transp := by unfold liveGF; rfl }

instance : InvGpreS liveGF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : LCPreGS liveGF where
  lc := { τ := 4, transp := by unfold liveGF; rfl }

instance : AppPreGS ℝ liveGF where
  heap := { τ := 5, transp := by unfold liveGF; rfl }
  tapes := { τ := 6, transp := by unfold liveGF; rfl }

end LiveEris
end ProbLang
