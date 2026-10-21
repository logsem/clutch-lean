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

Main result `otp_div_gen` (divergence 0 in every sound lifting). Suffixes: `_gen` any lifting,
none = codensity tv, `_closed` at `MicrometerFunctor`, `_rev` the ideal sampler on the left. -/

open scoped ENNReal

namespace ProbLang
open Iris Iris.BI Iris.ProofMode OFE COFE MicrometerWpGS GradedLifting GradedDivergence

namespace OTP

open _root_.Int (emod_nonneg emod_lt_of_pos emod_add_emod emod_eq_of_lt emod_sub_emod add_emod_emod
  sub_add_cancel add_sub_cancel)
open Exp (ofVal_of_toVal_some)

variable {rT : Type}

/-! ## The bijection: adding the key modulo `N` -/

theorem emod_bounds (a : Int) {N : Int} (hN : 0 < N) : 0 ≤ a % N ∧ a % N < N :=
  ⟨emod_nonneg _ hN.ne', emod_lt_of_pos _ hN⟩

section AddMod

variable (m N n : Int)

/-- Adds the key `m` modulo `N`. -/
def addMod : Int := (n + m) % N

theorem addMod_dom (hN : 0 < N) : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ addMod m N n ∧ addMod m N n < N :=
  fun _ _ _ => emod_bounds _ hN

/-- Adding `m` modulo `N` is a bijection on `[0, N)`. -/
theorem addMod_bij (hN : 0 < N) :
    ∀ m' : Int, 0 ≤ m' → m' < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ addMod m N n = m' := by
  intro m' hm'0 hm'N
  refine ⟨(m' - m) % N, ⟨emod_bounds _ hN, ?_⟩, ?_⟩
  · unfold addMod
    rw [emod_add_emod, sub_add_cancel, emod_eq_of_lt hm'0 hm'N]
  · rintro n ⟨⟨hn0, hnN⟩, hadd⟩
    unfold addMod at hadd
    rw [← hadd, emod_sub_emod, add_sub_cancel, emod_eq_of_lt hn0 hnN]

/-- Adding `-m` undoes adding `m`, used for the reverse refinement. -/
theorem addMod_neg_inv (hn0 : 0 ≤ n) (hnN : n < N) : (m + (n + (-m)) % N) % N = n := by
  rw [add_emod_emod, show m + (n + -m) = n by ring, emod_eq_of_lt hn0 hnN]

end AddMod

/-! ## The output relation -/

/-- The two programs return the same integer. -/
def otpφ (v v' : Val rT) : Prop :=
  ∃ n : Int, v = .int n ∧ v' = .int n

theorem adequacyRel_otpφ_subset_eq (e₁ e₂ : Exp rT) : adequacyRel otpφ e₁ e₂ → e₁ = e₂ := by
  rintro ⟨v, v', hv, hv', n, rfl, rfl⟩
  exact (ofVal_of_toVal_some hv).symm.trans (ofVal_of_toVal_some hv')

/-! ## The refinement in the logic

`rel_couple_UU` couples the two draws along `addMod`, at no cost. -/

section Refinement

variable [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] {hlc : HasLC} {GF : BundledGFunctors}
  [MicrometerRGS rT hlc GF]
local bi IProp GF

section Generic

variable {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {L : GradedLifting.{0} B} [BudgetCreditGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] (m N : Int) (hN : 0 < N)

include hN

/-- The encryption refines the ideal sampler in any lawful lifting. -/
theorem otp_refines_gen : ⊢ REL[L] (otp_enc (rT := rT) m N) << otp_ideal N : lrel_int := by
  rel_couple_UU (addMod m N) (addMod_dom m N hN) (addMod_bij m N hN)
  iintro %n %_
  rel_pures
  rw [show (m + n) % N = addMod m N n by rw [addMod, add_comm]]
  rel_values

/-- The ideal sampler refines the encryption in any lawful lifting. -/
theorem otp_refines_rev_gen : ⊢ REL[L] (otp_ideal (rT := rT) N) << otp_enc m N : lrel_int := by
  rel_couple_UU (addMod (-m) N) (addMod_dom (-m) N hN) (addMod_bij (-m) N hN)
  iintro %n ⟨%hn0, %hnN⟩
  rel_pures
  rw [show (m + addMod (-m) N n) % N = n from addMod_neg_inv m N n hn0 hnN]
  rel_values

end Generic

section Tv

variable [BudgetCreditGS ℝ≥0∞ GF]

/-- The encryption refines the ideal sampler in codensity tv. -/
theorem otp_refines (m N : Int) (hN : 0 < N) :
    ⊢ REL[codensity tv] (otp_enc (rT := rT) m N) << otp_ideal N : lrel_int :=
  otp_refines_gen m N hN

/-- The ideal sampler refines the encryption in codensity tv. -/
theorem otp_refines_rev (m N : Int) (hN : 0 < N) :
    ⊢ REL[codensity tv] (otp_ideal (rT := rT) N) << otp_enc m N : lrel_int :=
  otp_refines_rev_gen m N hN

end Tv

end Refinement

/-! ## Adequacy: exiting the logic

The limit distributions of `otp_enc m N` and `otp_ideal N` are coupled by integer
equality with zero error. -/

variable [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

section Lrel

variable {hlc : HasLC} {GF : BundledGFunctors}
local bi IProp GF

theorem lrel_int_to_otpφ [MicrometerRGS rT hlc GF] (v v' : Val rT) :
    ⊢ lrel_int.car v v' -∗ ⌜otpφ v v'⌝ := by
  iunfold lrel_int
  iintro ⟨%n, %hv, %hv'⟩
  ipureintro
  exact ⟨n, hv, hv'⟩

end Lrel

section Generic

variable {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  [Nontrivial B] {L : GradedLifting.{0} B} [L.IsLawful] [L.HasBind] [L.IsReflexive]
  [L.IsSupportLocal] [L.IsTopAbsorbing] [L.IsZeroLeft] [L.IsLeftContinuous] [L.IsBudgetClosed]

/-- The encryption and the ideal sampler are coupled at budget `0` in any lifting. -/
theorem otp_adequate_gen (GF : BundledGFunctors) [RefinesPreGS rT B GF] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    L.Rel 0 (adequacyRel otpφ) (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  refines_coupling (GF := GF) (fun _ _ => lrel_int) otpφ _ _ σ σ' (fun _ _ => lrel_int_to_otpφ)
    fun _ _ => otp_refines_gen m N hN

/-- The ideal sampler and the encryption are coupled at budget `0` in any lifting. -/
theorem otp_adequate_rev_gen (GF : BundledGFunctors) [RefinesPreGS rT B GF] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    L.Rel 0 (adequacyRel otpφ) (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  refines_coupling (GF := GF) (fun _ _ => lrel_int) otpφ _ _ σ σ' (fun _ _ => lrel_int_to_otpφ)
    fun _ _ => otp_refines_rev_gen m N hN

section Closed

variable (m N : Int) (hN : 0 < N) (σ σ' : State rT)

include hN

/-- `otp_adequate_gen` at `MicrometerFunctor`. -/
theorem otp_adequate_closed_gen :
    L.Rel 0 (adequacyRel otpφ) (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  otp_adequate_gen (MicrometerFunctor rT B) m N hN σ σ'

/-- `otp_adequate_rev_gen` at `MicrometerFunctor`. -/
theorem otp_adequate_rev_closed_gen :
    L.Rel 0 (adequacyRel otpφ) (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  otp_adequate_rev_gen (MicrometerFunctor rT B) m N hN σ σ'

/-- The encryption and the ideal program are at divergence zero. -/
theorem otp_div_gen {D : GradedDivergence.{0} B} [L.IsSound D] :
    D 0 (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  IsSound.sound ((otp_adequate_closed_gen (L := L) m N hN σ σ').mono le_rfl
    adequacyRel_otpφ_subset_eq)

end Closed

end Generic

/-- `otp_adequate_gen` in codensity tv. -/
theorem otp_adequate (GF : BundledGFunctors) [RefinesPreGS rT ℝ≥0∞ GF] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    (codensity tv).Rel 0 (adequacyRel otpφ)
      (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  otp_adequate_gen GF m N hN σ σ'

/-- `otp_adequate_rev_gen` in codensity tv. -/
theorem otp_adequate_rev (GF : BundledGFunctors) [RefinesPreGS rT ℝ≥0∞ GF] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    (codensity tv).Rel 0 (adequacyRel otpφ)
      (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  otp_adequate_rev_gen GF m N hN σ σ'

section ClosedTv

variable (m N : Int) (hN : 0 < N) (σ σ' : State rT)

include hN

/-! ### Closed statements at the concrete model `MicrometerFunctor rT` -/

/-- `otp_adequate` at `MicrometerFunctor`. -/
theorem otp_adequate_closed :
    (codensity tv).Rel 0 (adequacyRel otpφ)
      (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  otp_adequate_closed_gen m N hN σ σ'

/-- `otp_adequate_rev` at `MicrometerFunctor`. -/
theorem otp_adequate_rev_closed :
    (codensity tv).Rel 0 (adequacyRel otpφ)
      (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  otp_adequate_rev_closed_gen m N hN σ σ'

/-! ## Differential privacy instance -/

/-- The encryption is `0`-differentially private with respect to the ideal program.
`tv δ` is `dp (0, δ)`, so this is `otp_div_gen` at `L := codensity tv`, `D := tv`. -/
theorem otp_dp : dp.{0} (0, 0) (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  otp_div_gen (L := codensity tv) (D := tv) m N hN σ σ'

end ClosedTv

end OTP

end ProbLang
