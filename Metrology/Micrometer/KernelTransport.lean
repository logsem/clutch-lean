module

public import Metrology.Micrometer.KernelWp
import Metrology.Iris.LocalBI

/-! # Transporting the guarded weakest precondition across compatible kernels -/

@[expose] public section

namespace ProbLang.MicrometerWpGS

open Iris Iris.Std Iris.BI Iris.ProofMode GradedLifting
open MeasureTheory (Measure)
open BIFUpdate LawfulSet

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {step₁ step₂ : Cfg rT → Measure (Cfg rT)}
  {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF]

local bi IProp GF

/-- Program couplings transfer when every enabled source transition is preserved exactly. -/
theorem progCouplFor_transport
    (hstep : ∀ ρ, step₁ ρ ≠ 0 → step₂ ρ = step₁ ρ)
    {e e' : Exp rT} {σ σ' : State rT} {b : B}
    {Z : Exp rT → State rT → Exp rT → State rT → B → IProp GF} :
    progCouplFor step₁ L e σ e' σ' b Z ⊢ progCouplFor step₂ L e σ e' σ' b Z := by
  iintro H
  icases H with ⟨%law, %n, %μ, %μ₀, %ν₀, %f, %f', %R, %Hred, %Hf, %Hf', %Hhead,
    %Hside, %Heras, HCont⟩
  have heq := hstep ⟨e, σ⟩ Hred
  have hred₂ : step₂ ⟨e, σ⟩ ≠ 0 := by
    rw [heq]
    exact Hred
  iapply progCouplFor_intro_map law hred₂ Hf.1 (heq.trans Hf.2) Hf'.1 Hf'.2 Hhead Hside Heras
  iexact HCont

variable [BudgetGS B GF]

/-- The actual guarded WP transports along preservation of every enabled source transition. -/
theorem wpFor_transport (hstep : ∀ ρ, step₁ ρ ≠ 0 → step₂ ρ = step₁ ρ)
    {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wpFor step₁ L E e Φ ⊢ wpFor step₂ L E e Φ := by
  have Hloeb : ⊢ iprop(∀ E (e : Exp rT) Φ,
      wpFor step₁ L E e Φ -∗ wpFor step₂ L E e Φ) := by
    iapply loeb_wand
    iintro !> IH %E %e %Φ HW
    iapply wpFor_unfold
    iintro %σ %e' %σ' %b Hres
    imod wpFor_unfold_mp $$ HW %σ %e' %σ' %b Hres with HW
    imodintro
    iapply specCoupl_bind subset_refl
    iframe HW
    iintro %σ₂ %ρ₂ %b₂ HZ
    cases hvalue : e.toVal? with
    | some v =>
      iapply specCoupl_ret
      iexact HZ
    | none =>
      iapply specCoupl_ret
      ihave HCpl := progCouplFor_transport hstep $$ HZ
      iapply progCouplFor_mono
      iframe HCpl
      iintro %e₃ %σ₃ %e₃' %σ₃' %b₃ HLater
      iintro !>
      iapply specCoupl_mono
      iframe HLater
      iintro %σ₄ %ρ₄ %b₄ HF
      imod HF with ⟨Hσ, Hs, Hb, Hwp⟩
      imodintro
      iframe Hσ Hs Hb
      iapply IH $$ %E %e₃ %Φ Hwp
  iintro HW
  iapply Hloeb $$ %E %e %Φ HW

end ProbLang.MicrometerWpGS
