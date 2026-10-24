module

public import Metrology.Code.OTP
public import Metrology.Couplings.Divergences.Dp
public import Metrology.Couplings.Divergences.Tv
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.AppRelRules
public import Metrology.Micrometer.Compatibility
public import Metrology.Micrometer.RelTactics
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # One-time pad over `ℤ/N`, refining the ideal sampler in any graded lifting

Main result `otp_div_gen`: the encryption and the ideal sampler are at divergence `0` in every
sound lifting. -/

open scoped ENNReal

namespace ProbLang
open Iris Iris.BI Iris.ProofMode MicrometerWpGS GradedLifting GradedDivergence

namespace OTP

open _root_.Int (emod_nonneg emod_lt_of_pos emod_eq_of_lt emod_sub_emod add_emod_emod)

variable {rT : Type}

/-! ## The bijection: adding the key modulo `N` -/

/-- Reduction modulo `N` lands in `[0, N)`. -/
private theorem emod_bounds (a : Int) {N : Int} (hN : 0 < N) : 0 ≤ a % N ∧ a % N < N :=
  ⟨emod_nonneg _ hN.ne', emod_lt_of_pos _ hN⟩

section AddMod

variable (m N n : Int)

/-- Adds the key `m` modulo `N`. -/
def addMod : Int := (m + n) % N

/-- `addMod m N` maps `[0, N)` into itself. -/
theorem addMod_dom (hN : 0 < N) : ∀ k : Int, 0 ≤ k → k < N → 0 ≤ addMod m N k ∧ addMod m N k < N :=
  fun _ _ _ => emod_bounds _ hN

/-- Adding `m` modulo `N` is a bijection on `[0, N)`. -/
theorem addMod_bij (hN : 0 < N) :
    ∀ m' : Int, 0 ≤ m' → m' < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ addMod m N n = m' := by
  intro m' hm'0 hm'N
  refine ⟨(m' - m) % N, ⟨emod_bounds _ hN, ?_⟩, ?_⟩
  · unfold addMod
    rw [add_emod_emod, _root_.add_sub_cancel, emod_eq_of_lt hm'0 hm'N]
  · rintro n ⟨⟨hn0, hnN⟩, hadd⟩
    unfold addMod at hadd
    rw [← hadd, emod_sub_emod, add_sub_cancel_left, emod_eq_of_lt hn0 hnN]

/-- Adding `-m` undoes adding `m`, used for the reverse refinement. -/
theorem addMod_addMod_neg (hn0 : 0 ≤ n) (hnN : n < N) :
    addMod m N (addMod (-m) N n) = n := by
  rw [addMod, addMod, add_emod_emod, add_neg_cancel_left, emod_eq_of_lt hn0 hnN]

end AddMod

/-! ## The refinement in the logic

`rel_couple_UU` couples the two draws along `addMod`, at no cost. -/

variable [MeasurableSpace rT] [LawfulProbLangℝ rT] {hlc : HasLC} {GF : BundledGFunctors}
local bi IProp GF

section Refines

variable [MicrometerRGS rT hlc GF]

/-- The encryption refines the ideal sampler in any lawful lifting. -/
theorem otp_refines_gen {B : Type} [AddCommMonoid B] [PartialOrder B]
    [CanonicallyOrderedAdd B] [OrderTop B] {L : GradedLifting.{0} B} [BudgetCreditGS B GF]
    [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind]
    (m N : Int) (hN : 0 < N) : ⊢ REL[L] (otpEnc (rT := rT) m N) << otpIdeal N : lrel_int := by
  rel_couple_UU (addMod m N) (addMod_dom m N hN) (addMod_bij m N hN)
  iintro %n %_
  rel_pures
  rw [addMod]
  rel_values

/-- The ideal sampler refines the encryption in any lawful lifting. -/
theorem otp_refines_rev_gen {B : Type} [AddCommMonoid B]
    [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B] {L : GradedLifting.{0} B}
    [BudgetCreditGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]
    [L.HasBind] (m N : Int) (hN : 0 < N) :
    ⊢ REL[L] (otpIdeal (rT := rT) N) << otpEnc m N : lrel_int := by
  rel_couple_UU (addMod (-m) N) (addMod_dom (-m) N hN) (addMod_bij (-m) N hN)
  iintro %n ⟨%hn0, %hnN⟩
  rel_pures
  rw [show (m + addMod (-m) N n) % N = n from addMod_addMod_neg m N n hn0 hnN]
  rel_values

/-- The encryption refines the ideal sampler in codensity tv. -/
theorem otp_refines [BudgetCreditGS ℝ≥0∞ GF] (m N : Int) (hN : 0 < N) :
    ⊢ REL[codensity tv] (otpEnc (rT := rT) m N) << otpIdeal N : lrel_int :=
  otp_refines_gen m N hN

/-- The ideal sampler refines the encryption in codensity tv. -/
theorem otp_refines_rev [BudgetCreditGS ℝ≥0∞ GF] (m N : Int) (hN : 0 < N) :
    ⊢ REL[codensity tv] (otpIdeal (rT := rT) N) << otpEnc m N : lrel_int :=
  otp_refines_rev_gen m N hN

end Refines

/-! ## Adequacy: exiting the logic

The limit distributions of `otpEnc m N` and `otpIdeal N` are coupled by integer
equality with zero error. -/

section Generic

variable {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  [Nontrivial B] {L : GradedLifting.{0} B} [L.IsLawful] [L.HasBind] [L.IsReflexive]
  [L.IsSupportLocal] [L.IsTopAbsorbing] [L.IsZeroLeft] [L.IsLeftContinuous] [L.IsBudgetClosed]

/-- The encryption and the ideal sampler are coupled at budget `0` in any lifting. -/
theorem otp_adequate_gen (GF' : BundledGFunctors) [RefinesPreGS rT B GF'] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    L.Rel 0 (adequacyRel (· = ·)) (limExecV ⟨otpEnc m N, σ⟩) (limExecV ⟨otpIdeal N, σ'⟩) :=
  refines_coupling (GF := GF') (fun _ _ => lrel_int) _ _ _ σ σ' (fun _ _ => lrel_int_car_eq)
    fun _ _ => otp_refines_gen m N hN

/-- The ideal sampler and the encryption are coupled at budget `0` in any lifting. -/
theorem otp_adequate_rev_gen (GF' : BundledGFunctors) [RefinesPreGS rT B GF'] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    L.Rel 0 (adequacyRel (· = ·)) (limExecV ⟨otpIdeal N, σ⟩) (limExecV ⟨otpEnc m N, σ'⟩) :=
  refines_coupling (GF := GF') (fun _ _ => lrel_int) _ _ _ σ σ' (fun _ _ => lrel_int_car_eq)
    fun _ _ => otp_refines_rev_gen m N hN

/-- The encryption and the ideal sampler are coupled at budget `0` in the codensity tv lifting. -/
theorem otp_adequate (GF' : BundledGFunctors) [RefinesPreGS rT ℝ≥0∞ GF'] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    (codensity tv).Rel 0 (adequacyRel (· = ·))
      (limExecV ⟨otpEnc m N, σ⟩) (limExecV ⟨otpIdeal N, σ'⟩) :=
  otp_adequate_gen GF' m N hN σ σ'

/-- The ideal sampler and the encryption are coupled at budget `0` in the codensity tv lifting. -/
theorem otp_adequate_rev (GF' : BundledGFunctors) [RefinesPreGS rT ℝ≥0∞ GF'] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    (codensity tv).Rel 0 (adequacyRel (· = ·))
      (limExecV ⟨otpIdeal N, σ⟩) (limExecV ⟨otpEnc m N, σ'⟩) :=
  otp_adequate_rev_gen GF' m N hN σ σ'

/-! ### Closed statements at the concrete model `MicrometerFunctor rT` -/

section Closed

variable (m N : Int) (hN : 0 < N) (σ σ' : State rT)

include hN

/-- The encryption and the ideal sampler are coupled at budget `0` in any lifting, with the ghost
state `MicrometerFunctor rT B`. -/
theorem otp_adequate_closed_gen :
    L.Rel 0 (adequacyRel (· = ·)) (limExecV ⟨otpEnc m N, σ⟩) (limExecV ⟨otpIdeal N, σ'⟩) :=
  otp_adequate_gen (MicrometerFunctor rT B) m N hN σ σ'

/-- The ideal sampler and the encryption are coupled at budget `0` in any lifting, with the ghost
state `MicrometerFunctor rT B`. -/
theorem otp_adequate_rev_closed_gen :
    L.Rel 0 (adequacyRel (· = ·)) (limExecV ⟨otpIdeal N, σ⟩) (limExecV ⟨otpEnc m N, σ'⟩) :=
  otp_adequate_rev_gen (MicrometerFunctor rT B) m N hN σ σ'

/-- The encryption and the ideal program are at divergence zero. -/
theorem otp_div_gen {D : GradedDivergence.{0} B} [L.IsSound D] :
    D 0 (limExecV ⟨otpEnc m N, σ⟩) (limExecV ⟨otpIdeal N, σ'⟩) :=
  IsSound.sound ((otp_adequate_closed_gen (L := L) m N hN σ σ').mono le_rfl adequacyRel_eq_subset)

/-- The encryption and the ideal sampler are coupled at budget `0` in the codensity tv lifting,
with the ghost state `MicrometerFunctor rT ℝ≥0∞`. -/
theorem otp_adequate_closed :
    (codensity tv).Rel 0 (adequacyRel (· = ·))
      (limExecV ⟨otpEnc m N, σ⟩) (limExecV ⟨otpIdeal N, σ'⟩) :=
  otp_adequate_closed_gen m N hN σ σ'

/-- The ideal sampler and the encryption are coupled at budget `0` in the codensity tv lifting,
with the ghost state `MicrometerFunctor rT ℝ≥0∞`. -/
theorem otp_adequate_rev_closed :
    (codensity tv).Rel 0 (adequacyRel (· = ·))
      (limExecV ⟨otpIdeal N, σ⟩) (limExecV ⟨otpEnc m N, σ'⟩) :=
  otp_adequate_rev_closed_gen m N hN σ σ'

/-! ## Differential privacy -/

/-- The encryption and the ideal sampler are `(0, 0)`-differentially private. -/
theorem otp_dp : dp.{0} (0, 0) (limExecV ⟨otpEnc m N, σ⟩) (limExecV ⟨otpIdeal N, σ'⟩) :=
  otp_div_gen (L := codensity dp) m N hN σ σ'

end Closed

end Generic

end OTP

end ProbLang
