module

public import Metrology.Micrometer.KernelTransport
public import Metrology.Micrometer.Wp
public import Metrology.ProbLang.Asm.Ordinary

/-! # Existing ordinary-program proofs under the assembly FFI kernel -/

@[expose] public section

namespace ProbLang.MicrometerWpGS

open Iris Iris.BI GradedLifting

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF]

/-- Existing guarded WP proofs for ordinary programs remain valid in any FFI environment. -/
theorem wp_ffi_of_wp (env : Asm.FfiEnv rT) {E : CoPset} {e : Exp rT}
    {Φ : Val rT → IProp GF} : wp L E e Φ ⊢ wpFor (Asm.primStepWith env) L E e Φ :=
  wpFor_transport fun ρ hρ => Asm.primStepWith_eq_primStep_of_nonzero env ρ hρ

end ProbLang.MicrometerWpGS
