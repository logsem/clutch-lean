module

public import Metrology.Micrometer.KernelTransport
public import Metrology.Micrometer.Wp
public import Metrology.ProbLang.Asm.Ordinary

/-! # Ordinary-program `wp` under the assembly FFI kernel -/

@[expose] public section

namespace ProbLang.MicrometerWpGS

open Iris Asm

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF]

/-- A `wp` for an ordinary program gives `wpFor` under any FFI environment's step. -/
theorem wp_ffi_of_wp (env : FfiEnv rT) {E : CoPset} {e : Exp rT}
    {Φ : Val rT → IProp GF} : wp L E e Φ ⊢ wpFor (primStepWith env) L E e Φ :=
  wpFor_transport fun ρ hρ => primStepWith_eq_primStep_of_nonzero env ρ hρ

end ProbLang.MicrometerWpGS
