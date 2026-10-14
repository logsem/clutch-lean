module

public import Metrology.Micrometer.Compatibility
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.AppRelRules
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Code.OTP
public import Metrology.Couplings.CodensityTV
public import Metrology.Couplings.DP.Divergence

@[expose] public section

/-! # One-Time Pad refinement example, using modular addition as the combiner.

Every result holds for any graded divergence `Δ` with the classes its rules need (the `_gen`
statements); the `tv` statements and a `dp` statement are instances. -/

namespace ProbLang
open Iris Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS TVDiv

namespace OTP

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [IR : MicrometerRGS rT hlc GF]

/-! ### The bijection -/

def addMod (m N : Int) (n : Int) : Int := (n + m) % N

private theorem emod_bounds (a : Int) {N : Int} (hN : 0 < N) : 0 ≤ a % N ∧ a % N < N :=
  ⟨Int.emod_nonneg _ (Int.ne_of_gt hN), Int.emod_lt_of_pos _ hN⟩

theorem addMod_dom (m N : Int) (hN : 0 < N) :
    ∀ n : Int, 0 ≤ n → n < N → 0 ≤ addMod m N n ∧ addMod m N n < N :=
  fun _ _ _ => emod_bounds _ hN

theorem addMod_bij (m N : Int) (hN : 0 < N) :
    ∀ m' : Int, 0 ≤ m' → m' < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ addMod m N n = m' := by
  intro m' hm'0 hm'N
  refine ⟨(m' - m) % N, ⟨emod_bounds _ hN, ?_⟩, ?_⟩
  · unfold addMod
    rw [Int.emod_add_emod, Int.sub_add_cancel, Int.emod_eq_of_lt hm'0 hm'N]
  · rintro n ⟨⟨hn0, hnN⟩, hadd⟩
    unfold addMod at hadd
    rw [← hadd, Int.emod_sub_emod, Int.add_sub_cancel, Int.emod_eq_of_lt hn0 hnN]

/-! ### The OTP refinement -/

section Generic
variable {ι : Type} [Monoid ι] {Δ : GradedDivergence.{0} ι}

abbrev otpLam (m N : Int) : Exp rT := pl% fun k, (#(.int m) + k) % #(.int N)

def otpKLam (m N : Int) : Ectx rT := [EctxItem.appR (otpLam m N)]

private theorem refines_lit_int (n : Int) :
    ⊢@{IProp GF} REL[Δ] (pl(#(.int n)) : Exp rT) << pl(#(.int n)) : lrel_int := by
  iapply refines_ret (v1 := .int n) (v2 := .int n) rfl rfl
  iintro !>
  iapply lrel_int_lit

theorem otp_refines_gen [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft]
    (m N : Int) (hN : 0 < N) :
    ⊢@{IProp GF} REL[Δ] (otp_enc (rT := rT) m N) << (otp_ideal N) : lrel_int := by
  simp only [otp_enc, otp_ideal, Exp.close, Exp.closeRec, ↓reduceIte]
  show ⊢@{IProp GF} refines Δ ⊤
    ((otpKLam m N).fill pl(rand(#(.int N), #(.unit))))
    (Ectx.fill ([] : Ectx rT) pl(rand(#(.int N), #(.unit)))) lrel_int
  iapply refines_couple_rands_lr (addMod m N) (addMod_dom m N hN) (addMod_bij m N hN) hN
  iintro %n %_
  show ⊢@{IProp GF} refines Δ ⊤ (Ectx.fill ([] : Ectx rT) pl({otpLam m N} #(.int n))) _ lrel_int
  iapply refines_pure_l (Hex := pureExec_app_lam) ⟨IsVal.lit.toIsValue, by is_lc⟩
  inext
  let Kmod : Ectx rT := [EctxItem.binopL .mod (.int N)]
  show ⊢@{IProp GF} refines Δ ⊤ (Kmod.fill pl(#(.int m) + #(.int n))) _ lrel_int
  iapply refines_pure_l ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  inext
  show ⊢@{IProp GF} refines Δ ⊤
    (Ectx.fill ([] : Ectx rT) pl(#(.int (m + n)) % #(.int N))) _ lrel_int
  iapply refines_pure_l ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  inext
  rw [show (m + n) % N = addMod m N n by unfold addMod; ring_nf]
  exact refines_lit_int _

/-! ### Reverse direction -/

theorem addMod_neg_inv (m N n : Int) (hn0 : 0 ≤ n) (hnN : n < N) :
    (m + (n + (-m)) % N) % N = n := by
  rw [Int.add_emod_emod, show m + (n + -m) = n by ring, Int.emod_eq_of_lt hn0 hnN]

theorem otp_refines_rev_gen [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft]
    (m N : Int) (hN : 0 < N) :
    ⊢@{IProp GF} REL[Δ] (otp_ideal (rT := rT) N) << (otp_enc m N) : lrel_int := by
  simp only [otp_enc, otp_ideal, Exp.close, Exp.closeRec, ↓reduceIte]
  show ⊢@{IProp GF} refines Δ ⊤
    (Ectx.fill ([] : Ectx rT) pl(rand(#(.int N), #(.unit))))
    ((otpKLam m N).fill pl(rand(#(.int N), #(.unit)))) lrel_int
  iapply refines_couple_rands_lr (addMod (-m) N) (addMod_dom (-m) N hN) (addMod_bij (-m) N hN) hN
  iintro %n ⟨%hn0, %hnN⟩
  show ⊢@{IProp GF} refines Δ ⊤ _
    (Ectx.fill ([] : Ectx rT) pl({otpLam m N} #(.int (addMod (-m) N n)))) lrel_int
  iapply refines_pure_r (Hex := pureExec_app_lam) ⟨IsVal.lit.toIsValue, by is_lc⟩
  let Kmod : Ectx rT := [EctxItem.binopL .mod (.int N)]
  show ⊢@{IProp GF} refines Δ ⊤ _ (Kmod.fill pl(#(.int m) + #(.int (addMod (-m) N n)))) lrel_int
  iapply refines_pure_r ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  show ⊢@{IProp GF} refines Δ ⊤ _
    (Ectx.fill ([] : Ectx rT) pl(#(.int (m + addMod (-m) N n)) % #(.int N))) lrel_int
  iapply refines_pure_r ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  rw [show (m + addMod (-m) N n) % N = n from addMod_neg_inv m N n hn0 hnN]
  exact refines_lit_int n

end Generic

theorem otp_refines (m N : Int) (hN : 0 < N) :
    ⊢@{IProp GF} REL[tv] (otp_enc (rT := rT) m N) << (otp_ideal N) : lrel_int :=
  otp_refines_gen m N hN

theorem otp_refines_rev (m N : Int) (hN : 0 < N) :
    ⊢@{IProp GF} REL[tv] (otp_ideal (rT := rT) N) << (otp_enc m N) : lrel_int :=
  otp_refines_rev_gen m N hN

/-! ## Adequacy: exit the logic

The limit distributions of `otp_enc m N` and `otp_ideal N` are coupled by integer
equality with zero error. -/

def otpφ (v v' : Val rT) : Prop :=
  ∃ n : Int, v = .int n ∧ v' = .int n

theorem lrel_int_to_otpφ {GF : BundledGFunctors} [MicrometerRGS rT hlc GF] (v v' : Val rT) :
    ⊢@{IProp GF} lrel_int.car v v' -∗ ⌜otpφ v v'⌝ := by
  iintro Hint
  iunfold lrel_int at Hint
  icases Hint with ⟨%n, %hv, %hv'⟩
  ipureintro; exact ⟨n, hv, hv'⟩

omit [LawfulProbLangℝ rT] in
theorem adequacyRel_otpφ_subset_eq : adequacyRel otpφ ⊆ {p : Exp rT × Exp rT | p.1 = p.2} := by
  rintro ⟨e₁, e₂⟩ ⟨v, v', hv, hv', n, rfl, rfl⟩
  exact (Exp.ofVal_of_toVal_some hv).symm.trans (Exp.ofVal_of_toVal_some hv')

section Generic
variable {ι : Type} [Monoid ι] {Δ : GradedDivergence.{0} ι} [Δ.IsReflexive] [Δ.IsComposable]
  [Δ.IsZeroLeft] [Δ.IsMassBounded] [Δ.IsLeftContinuous]

theorem otp_adequate_gen (GF : BundledGFunctors) [RefinesPreGS rT GF] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    Δ.Codensity 1 0 (adequacyRel otpφ) (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  refines_coupling (GF := GF) (fun _ => lrel_int) otpφ _ _ σ σ' (fun _ => lrel_int_to_otpφ)
    fun _ => otp_refines_gen m N hN

theorem otp_adequate_rev_gen (GF : BundledGFunctors) [RefinesPreGS rT GF] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    Δ.Codensity 1 0 (adequacyRel otpφ) (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  refines_coupling (GF := GF) (fun _ => lrel_int) otpφ _ _ σ σ' (fun _ => lrel_int_to_otpφ)
    fun _ => otp_refines_rev_gen m N hN

theorem otp_adequate_closed_gen (m N : Int) (hN : 0 < N) (σ σ' : State rT) :
    Δ.Codensity 1 0 (adequacyRel otpφ) (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  otp_adequate_gen (MicrometerFunctor rT) m N hN σ σ'

theorem otp_adequate_rev_closed_gen (m N : Int) (hN : 0 < N) (σ σ' : State rT) :
    Δ.Codensity 1 0 (adequacyRel otpφ) (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  otp_adequate_rev_gen (MicrometerFunctor rT) m N hN σ σ'

/-- The encryption and the ideal program are at divergence zero. -/
theorem otp_div_gen (m N : Int) (hN : 0 < N) (σ σ' : State rT) :
    Δ 1 (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) ≤ 0 :=
  ((otp_adequate_closed_gen m N hN σ σ').mono_rel adequacyRel_otpφ_subset_eq).le_of_diag

end Generic

theorem otp_adequate (GF : BundledGFunctors) [RefinesPreGS rT GF] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    TVDiv.tv.{0}.Codensity 1 0 (adequacyRel otpφ)
      (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  otp_adequate_gen GF m N hN σ σ'

theorem otp_adequate_rev (GF : BundledGFunctors) [RefinesPreGS rT GF] (m N : Int)
    (hN : 0 < N) (σ σ' : State rT) :
    TVDiv.tv.{0}.Codensity 1 0 (adequacyRel otpφ)
      (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  otp_adequate_rev_gen GF m N hN σ σ'

/-! ## Closed statements at the concrete model `MicrometerFunctor rT` -/

theorem otp_adequate_closed (m N : Int) (hN : 0 < N) (σ σ' : State rT) :
    TVDiv.tv.{0}.Codensity 1 0 (adequacyRel otpφ)
      (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  otp_adequate_closed_gen m N hN σ σ'

theorem otp_adequate_rev_closed (m N : Int) (hN : 0 < N) (σ σ' : State rT) :
    TVDiv.tv.{0}.Codensity 1 0 (adequacyRel otpφ)
      (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  otp_adequate_rev_closed_gen m N hN σ σ'

/-! ## Differential privacy instance -/

/-- The encryption is `0`-differentially private with respect to the ideal program. -/
theorem otp_dp (m N : Int) (hN : 0 < N) (σ σ' : State rT) :
    DPDiv.dp.{0} 1 (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) ≤ 0 :=
  otp_div_gen m N hN σ σ'

end OTP

end ProbLang
