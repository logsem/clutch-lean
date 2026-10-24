module

public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Iris.HeapFragment
public import Metrology.ProbLang.Asm.Specification
import Metrology.Iris.LocalBI

/-! # Importing plain assembly specifications into Micrometer -/

@[expose] public section

open Iris Iris.Std Iris.ProofMode

namespace ProbLang

open Asm MicrometerWpGS BIFUpdate
open LawfulSet (empty_subset)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsTopAbsorbing]
  {E : CoPset} {Φ : Val rT → IProp GF}

local bi IProp GF

/-- A return-valued assembly evaluation exchanges the owned footprint in one ProbLang step. -/
theorem wp_asm_of_eval (env : FfiEnv rT)
    (code : Code) (args : List BoundaryValue) (old new : Loc → Int) (value : BoundaryValue)
    (hlen : args.length = code.sig.args.length)
    (hinput : validFragment code args (integerHeap (callFootprint code args) old))
    (heval : env.machine.eval code args (callFootprint code args)
      (integerHeap (callFootprint code args) old) =
      some (.ret value (integerHeap (callFootprint code args) new)))
    (houtput : validFragment code args (integerHeap (callFootprint code args) new) ∧
      checkResult code.sig.toCallSig (boundaryArgs args) code.sig.result value.toVal =
        true) : iprop%
    appHeapFragment (integerValues (callFootprint code args) old) ∗
      ▷ (appHeapFragment (integerValues (callFootprint code args) new) -∗ Φ value.toVal) ⊢
        wpFor (primStepWith env) L E (.asm (.lit (.code code)) (argumentTuple args)) Φ := by
  iintro ⟨Hinput, HΦ⟩
  iapply wpFor_lift_atomic_step Exp.asm_toVal?_eq_none
  iintro %σ Hσ
  ihave %hlook := app_state_lookup_fragment _ $$ Hσ Hinput
  have hlookup : ∀ l ∈ callFootprint code args, σ.heap[l]? = some (.int (old l)) := by
    intro l hl
    apply hlook (l, .int (old l))
    exact List.mem_map.mpr ⟨l, (mem_footprintLocations _ l).mpr hl, rfl⟩
  have hdet : primStepWith env ⟨.asm (.lit (.code code)) (argumentTuple args), σ⟩ =
      MeasureTheory.Measure.dirac ⟨.ofVal value.toVal,
        σ.writeFragment (integerValues (callFootprint code args) new)⟩ :=
    primStepWith_asm_ret_of_eval env code args old new value hlen hinput heval houtput σ hlookup
  imod subset empty_subset with Hclose
  imod app_state_update_fragment (integerValues (callFootprint code args) old)
    (integerValues (callFootprint code args) new) (by simp) (integerValues_nodup _ old)
    $$ Hσ Hinput with ⟨Hσ', Houtput⟩
  imodintro
  iexists value.toVal, σ.writeFragment (integerValues (callFootprint code args) new)
  iframe %hdet
  iintro !>
  imod Hclose
  imodintro
  iframe Hσ'
  iapply HΦ $$ Houtput

/-- A total plain machine specification exchanges the owned footprint in one ProbLang step. -/
theorem wp_asm (env : FfiEnv rT) (law : LawfulAsmSemantics env.machine)
    (code : Code) (args : List BoundaryValue) (old new : Loc → Int) (value : BoundaryValue)
    (hlen : args.length = code.sig.args.length)
    (hinput : validFragment code args (integerHeap (callFootprint code args) old))
    (hentry : ∃ ι t, env.machine.Compat ι code args (integerHeap (callFootprint code args) old) t)
    (hspec : env.machine.Spec code args (callFootprint code args)
      (integerHeap (callFootprint code args) old)
      (.ret value (integerHeap (callFootprint code args) new)))
    (houtput : validFragment code args (integerHeap (callFootprint code args) new) ∧
      checkResult code.sig.toCallSig (boundaryArgs args) code.sig.result value.toVal =
        true) : iprop%
    appHeapFragment (integerValues (callFootprint code args) old) ∗
      ▷ (appHeapFragment (integerValues (callFootprint code args) new) -∗ Φ value.toVal) ⊢
        wpFor (primStepWith env) L E (.asm (.lit (.code code)) (argumentTuple args)) Φ := by
  apply wp_asm_of_eval env code args old new value hlen hinput _ houtput
  exact env.machine.eval_eq_some law ⟨hentry, True.intro, hspec⟩

end ProbLang
