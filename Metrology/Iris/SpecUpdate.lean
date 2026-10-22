module

public import Metrology.Iris.SpecProgram
public import Metrology.ProbLang.Exec
public import Iris.Instances.Lib.FUpd
import Metrology.Iris.LocalBI

@[expose] public section

/-!
# Spec-side update modality

The modality `specUpdate E P`: take some deterministic steps of the right program under `|={E}=>`
and give `P`. It comes with bind, monotonicity and framing rules; the `step_*` rules in
`SpecRules.lean` produce it.
-/

open Std Iris Iris.Std Iris.BI COFE ProbLang MeasureTheory.Measure

namespace ProbLang

/-- The abstract interpretation of a spec configuration, extended by `MicrometerWpGS`. -/
class SpecUpdateGS (rT : Type _) [LawfulProbLangℝ rT] (GF : BundledGFunctors) where
  /-- The proposition interpreting a spec configuration. -/
  specInterp : Cfg rT → IProp GF

open SpecUpdateGS

section SpecUpdate

/-! ## Definitions -/

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] [iSpec : SpecUpdateGS rT GF]
variable {n m : Nat} {E E1 E2 : CoPset} {P Q R : IProp GF}
local bi IProp GF

variable (rT) in
/-- Update of the spec side by exactly `n` deterministic steps. -/
def specUpdateN (n : Nat) (E : CoPset) (P : IProp GF) : IProp GF := iprop%
  ∀ (ρ : Cfg rT), specInterp ρ -∗ |={E}=> ∃ ρ', ⌜pexecN n ρ = dirac ρ'⌝ ∗ specInterp ρ' ∗ P

variable (rT) in
/-- Update of the spec side by some number of deterministic steps. -/
abbrev specUpdate (E : CoPset) (P : IProp GF) : IProp GF := iprop%
  ∀ (ρ : Cfg rT), specInterp ρ -∗ |={E}=> (∃ ρ' n, ⌜pexecN n ρ = dirac ρ'⌝ ∗ specInterp ρ' ∗ P)

/-- Forgetting the step count turns `specUpdateN` into `specUpdate`. -/
theorem specUpdateN_specUpdate :
    specUpdateN rT n E P ⊢ specUpdate rT E P := by
  unfold specUpdateN specUpdate
  iintro H %ρ Hρ
  imod H $$ %ρ Hρ with ⟨%ρ', %hstep, Hρ', HP⟩
  imodintro
  iexists ρ', n
  iframe
  ipureintro
  assumption

/-! ## Return and bind -/

/-- Zero steps: `P` holds straight away. -/
theorem specUpdateN_zero : P ⊢ specUpdateN rT 0 E P := by
  unfold specUpdateN
  iintro HP %ρ Hρ !>
  iexists ρ
  iframe
  ipureintro
  rfl

/-- Return: `P` already holds, so take no spec steps. -/
theorem specUpdate_ret : P ⊢ specUpdate rT E P := by
  iintro _
  iapply specUpdateN_specUpdate
  iapply specUpdateN_zero $$ [$]

/-- Bind: run `n` steps, then `m` more; step counts add. -/
theorem specUpdateN_bind (HE : E1 ⊆ E2) : iprop%
    specUpdateN rT n E1 P ∗ (P -∗ specUpdateN rT m E2 Q) ⊢ specUpdateN rT (n + m) E2 Q := by
  unfold specUpdateN
  iintro ⟨Hn, Hm⟩ %ρ Hρ
  imod BIFUpdate.subset HE with Hclose
  imod Hn $$ %ρ Hρ with ⟨%ρ', %hexec₁, Hs, HP⟩
  imod Hclose with -
  imod Hm $$ HP %ρ' Hs with ⟨%ρ'', %hexec₂, Hs, HQ⟩
  imodintro
  iexists ρ''
  iframe
  ipureintro
  exact pexecN_det_trans hexec₁ hexec₂

/-- Bind: chain two spec updates. -/
theorem specUpdate_bind (HE : E1 ⊆ E2) : iprop%
    specUpdate rT E1 P ∗ (P -∗ specUpdate rT E2 Q) ⊢ specUpdate rT E2 Q := by
  unfold specUpdate
  iintro ⟨H₁, H₂⟩ %ρ Hρ
  imod BIFUpdate.subset HE with Hclose
  imod H₁ $$ %ρ Hρ with ⟨%ρ', %n₁, %hexec₁, Hs, HP⟩
  imod Hclose with -
  imod H₂ $$ HP %ρ' Hs with ⟨%ρ'', %n₂, %hexec₂, Hs, HQ⟩
  imodintro
  iexists ρ'', n₁ + n₂
  iframe
  ipureintro
  exact pexecN_det_trans hexec₁ hexec₂

/-! ## Monotonicity, fancy updates and framing -/

/-- Monotonicity of `specUpdateN` along a fancy update. -/
theorem specUpdateN_mono_fupd : iprop%
    specUpdateN rT n E P ∗ (P ={E}=∗ Q) ⊢ specUpdateN rT n E Q := by
  unfold specUpdateN
  iintro ⟨HP, HPQ⟩ %ρ Hρ
  imod HP $$ %ρ Hρ with ⟨%ρ', %hstep, Hρ', HPres⟩
  imod HPQ $$ HPres with HQres
  imodintro
  iexists ρ'
  iframe
  ipureintro
  assumption

/-- Monotonicity of `specUpdate` along a fancy update. -/
theorem specUpdate_mono_fupd : iprop%
    specUpdate rT E P ∗ (P ={E}=∗ Q) ⊢ specUpdate rT E Q := by
  unfold specUpdate
  iintro ⟨HP, HPQ⟩ %ρ Hρ
  imod HP $$ %ρ Hρ with ⟨%ρ', %n, %hstep, Hρ', HPres⟩
  imod HPQ $$ HPres with HQres
  imodintro
  iexists ρ', n
  iframe
  ipureintro
  assumption

/-- Monotonicity of `specUpdateN` in the postcondition. -/
theorem specUpdateN_mono : iprop%
    specUpdateN rT n E P ∗ (P -∗ Q) ⊢ specUpdateN rT n E Q := by
  iintro ⟨HP, HPQ⟩
  iapply specUpdateN_mono_fupd
  iframe
  iintro _ !>
  iapply HPQ $$ [$]

/-- Monotonicity of `specUpdate` in the postcondition. -/
theorem specUpdate_mono : iprop%
    specUpdate rT E P ∗ (P -∗ Q) ⊢ specUpdate rT E Q := by
  iintro ⟨HP, HPQ⟩
  iapply specUpdate_mono_fupd
  iframe HP
  iintro _ !>
  iapply HPQ $$ [$]

/-- A fancy update in front of `specUpdateN` can be absorbed. -/
theorem fupd_specUpdateN : iprop%
    (|={E}=> specUpdateN rT n E P) ⊢ specUpdateN rT n E P := by
  unfold specUpdateN
  iintro H %ρ Hρ
  imod H
  iapply H $$ [$]

/-- A fancy update in front of `specUpdate` can be absorbed. -/
theorem fupd_specUpdate : iprop%
    (|={E}=> specUpdate rT E P) ⊢ specUpdate rT E P := by
  unfold specUpdate
  iintro H %ρ Hρ
  imod H
  iapply H $$ [$]

/-- Frame a resource `R` around `specUpdateN`. -/
theorem specUpdateN_frame_l : iprop%
    R ∗ specUpdateN rT n E P ⊢ specUpdateN rT n E iprop(P ∗ R) := by
  iintro ⟨HR, HP⟩
  iapply specUpdateN_mono
  iframe
  iintro _
  iframe

/-- Frame a resource `R` around `specUpdate`. -/
theorem specUpdate_frame_l :
    iprop(R ∗ specUpdate rT E P) ⊢ specUpdate rT E iprop(P ∗ R) := by
  iintro ⟨HR, HP⟩
  iapply specUpdate_mono
  iframe HP
  iintro _
  iframe

end SpecUpdate

/-- The default `SpecUpdateGS`, interpreting a configuration by `Cfg.specAuth`. -/
instance defaultSpecUpdateGS {rT : Type _} [LawfulProbLangℝ rT]
    {GF} [SpecGS rT GF] : SpecUpdateGS rT GF where
  specInterp := Cfg.specAuth

end ProbLang
