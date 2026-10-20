module

public import Metrology.Iris.SpecProgram
public import Metrology.ProbLang.Exec
public import Iris.Instances.Lib.FUpd

@[expose] public section

/-!
# Spec-side update modality

`specUpdate E P`: from any spec configuration, take some deterministic spec steps
(`pexecN n ρ = dirac ρ'`) under `|={E}=>` and give `P`. The `step_*` rules in `SpecRules.lean`
produce it.
-/

open Std Iris Iris.Std Iris.BI COFE ProbLang MeasureTheory.Measure Measurable

namespace ProbLang

/-- The interpretation of a spec configuration used by `specUpdate` and by `wp`'s state
interpretation; kept abstract so `MicrometerWpGS` can extend it. -/
class SpecUpdateGS (rT : Type _) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (GF : BundledGFunctors) where
  specInterp : Cfg rT → IProp GF

open SpecUpdateGS

section SpecUpdate

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] [iSpec : SpecUpdateGS rT GF]

/-- Update of the spec side by `n` deterministic steps; rules that know their step count state it
here, and `specUpdateN_specUpdate` forgets `n`, which is all `wp` needs. -/
def specUpdateN (rT : Type _) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] [SpecUpdateGS rT GF]
    (n : Nat) (E : CoPset) (P : IProp GF) :
    IProp GF := iprop%
  ∀ (ρ : Cfg rT), specInterp ρ -∗ |={E}=> ∃ ρ', ⌜pexecN n ρ = dirac ρ'⌝ ∗ specInterp ρ' ∗ P

/-- Update of the spec side by some number of deterministic steps. -/
abbrev specUpdate (rT : Type _) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] [SpecUpdateGS rT GF]
    (E : CoPset) (P : IProp GF) :
    IProp GF := iprop%
  ∀ (ρ : Cfg rT), specInterp ρ -∗ |={E}=> (∃ ρ' n, ⌜pexecN n ρ = dirac ρ'⌝ ∗ specInterp ρ' ∗ P)

theorem specUpdateN_specUpdate {n : Nat} {E : CoPset} {P : IProp GF} :
    specUpdateN rT n E P ⊢ specUpdate rT E P := by
  unfold specUpdateN specUpdate
  iintro H %ρ Hρ
  imod H $$ %ρ Hρ with ⟨%ρ', %hstep, Hρ', HP⟩
  imodintro
  iexists ρ', n
  iframe
  ipureintro
  assumption

theorem specUpdateN_zero {E : CoPset} {P : IProp GF} : P ⊢ specUpdateN rT 0 E P := by
  unfold specUpdateN
  iintro HP %ρ Hρ !>
  iexists ρ
  iframe
  ipureintro
  rfl

theorem specUpdate_ret {E : CoPset} {P : IProp GF} : P ⊢ specUpdate rT E P := by
  iintro _
  iapply specUpdateN_specUpdate
  iapply specUpdateN_zero $$ [$]

theorem specUpdateN_bind {n m : Nat} {E1 E2 : CoPset} {P Q : IProp GF} (HE : E1 ⊆ E2) : iprop%
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

theorem specUpdate_bind {E1 E2 : CoPset} {P Q : IProp GF} (HE : E1 ⊆ E2) : iprop%
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

theorem specUpdateN_mono_fupd {n : Nat} {E : CoPset} {P Q : IProp GF} : iprop%
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

theorem specUpdate_mono_fupd {E : CoPset} {P Q : IProp GF} : iprop%
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

theorem specUpdateN_mono {n : Nat} {E : CoPset} {P Q : IProp GF} : iprop%
    specUpdateN rT n E P ∗ (P -∗ Q) ⊢ specUpdateN rT n E Q := by
  iintro ⟨HP, HPQ⟩
  iapply specUpdateN_mono_fupd
  iframe
  iintro _ !>
  iapply HPQ $$ [$]

theorem specUpdate_mono {E : CoPset} {P Q : IProp GF} : iprop%
    specUpdate rT E P ∗ (P -∗ Q) ⊢ specUpdate rT E Q := by
  iintro ⟨HP, HPQ⟩
  iapply specUpdate_mono_fupd
  iframe HP
  iintro _ !>
  iapply HPQ $$ [$]

theorem fupd_specUpdateN {n : Nat} {E : CoPset} {P : IProp GF} : iprop%
    (|={E}=> specUpdateN rT n E P) ⊢ specUpdateN rT n E P := by
  unfold specUpdateN
  iintro H %ρ Hρ
  imod H
  iapply H $$ [$]

theorem fupd_specUpdate {E : CoPset} {P : IProp GF} : iprop%
    (|={E}=> specUpdate rT E P) ⊢ specUpdate rT E P := by
  unfold specUpdate
  iintro H %ρ Hρ
  imod H
  iapply H $$ [$]

theorem specUpdateN_frame_l {n : Nat} {E : CoPset} {R P : IProp GF} : iprop%
    R ∗ specUpdateN rT n E P ⊢ specUpdateN rT n E iprop(P ∗ R) := by
  iintro ⟨HR, HP⟩
  iapply specUpdateN_mono
  iframe
  iintro _
  iframe

theorem specUpdate_frame_l {E : CoPset} {R P : IProp GF} :
    iprop(R ∗ specUpdate rT E P) ⊢@{IProp GF} specUpdate rT E iprop(P ∗ R) := by
  iintro ⟨HR, HP⟩
  iapply specUpdate_mono
  iframe HP
  iintro _
  iframe

end SpecUpdate

/-- The default `SpecUpdateGS`, interpreting a configuration by `Cfg.specAuth`. -/
instance defaultSpecUpdateGS {rT : Type _} [LawfulProbLangℝ rT]
    [MeasurableSingletonClass rT] {GF} [SpecGS rT GF] : SpecUpdateGS rT GF where
  specInterp := Cfg.specAuth

end ProbLang
