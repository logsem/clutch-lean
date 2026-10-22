module

public import Mathlib.Basic.ENNReal.Basic
public import Iris
public import Iris.Algebra.View
public import Iris.Instances.IProp.Instance
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Metrology.Iris.Algebra
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Error credits

The resource `↯ε` (total `●↯ε`) over `ℝ≥0∞` with validity `ε < 1`, as used by TotalEris.
Provides split/combine/supply rules, `contradict` (`1 ≤ ε` is absurd), and error amplification. -/

noncomputable section

open Std Iris COFE
open scoped ENNReal NNReal

/-! ## The camera of error credits -/

/-- Error credits: non-negative extended reals, valid when below `1`. -/
abbrev ErrorCredit : Type _ := ℝ≥0∞

instance : COFE ErrorCredit := COFE.ofDiscrete _
instance : OFE.Discrete ErrorCredit := ⟨id⟩
instance (x : ErrorCredit) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

/-- Error credits compose by addition. -/
instance : CMRA ErrorCredit where
  pcore _ := some 0
  op := (· + ·)
  ValidN _ ε := ε < 1
  Valid ε := ε < 1
  op_ne.ne _ _ _ h := by rw [h]
  pcore_ne _ := by rintro ⟨rfl⟩; exists 0
  validN_ne {_ _ _} := by rintro ⟨rfl⟩; exact id
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left {n x y} H := lt_of_add_lt_of_nonneg_left H zero_le
  assoc {_ _ _} := (add_assoc ..).symm
  comm {_ _} := (add_comm ..).symm
  pcore_op_left {_ _} := by rintro ⟨rfl⟩; simp
  pcore_idem := by simp
  pcore_op_mono {_ _} := by rintro ⟨rfl⟩ _; exists 0; simp
  extend _ h := ⟨_, _, OFE.discrete h, .rfl, .rfl⟩

instance : CMRA.Discrete ErrorCredit where
  discrete_valid := id

instance : UCMRA ErrorCredit where
  unit := 0
  unit_valid := by simp [CMRA.Valid]
  unit_left_id := by simp [CMRA.op]
  pcore_unit := by simp [CMRA.pcore]

/-- Inclusion of error credits is `≤`. -/
theorem ErrorCredit.included_iff {ε₁ ε₂ : ErrorCredit} : ε₁ ≼ ε₂ ↔ ε₁ ≤ ε₂ := by
  refine ⟨?_, (⟨ε₂ - ε₁, add_tsub_cancel_of_le · |>.symm⟩)⟩
  rintro ⟨ε₃, rfl⟩
  exact le_self_add

/-- Step-indexed form of `ErrorCredit.included_iff`. -/
theorem ErrorCredit.includedN_iff {ε₁ ε₂ : ErrorCredit} : ε₁ ≼{n} ε₂ ↔ ε₁ ≤ ε₂ :=
  ErrorCredit.included_iff

instance {ε : ErrorCredit} : CMRA.Cancelable ε where
  cancelableN {n ε₁ ε₂} := by
    simp [CMRA.ValidN, CMRA.op, OFE.Dist]
    intro h1 h2
    refine (ENNReal.add_right_inj ?_).mp h2
    rintro rfl; simp at h1

/-- A local update of error credits that moves credits between the two sides. -/
theorem ErrorCredit.localUpdate {ε₁ ε₂ ε₁' ε₂' : ErrorCredit} (h1 : ε₂' ≤ ε₂)
    (h2 : ε₁ + ε₂' = ε₁' + ε₂) : (ε₁, ε₂) ~l~> (ε₁', ε₂') := by
  rintro n (_|ε) <;> simp only [OFE.Dist, CMRA.op?, CMRA.ValidN, CMRA.op]
  · rintro H rfl
    symm at h2
    obtain rfl : ε₁' = ε₂' := ENNReal.add_left_inj H.ne_top |>.mp (by grind)
    exact ⟨Std.lt_of_le_of_lt h1 H, rfl⟩
  · rintro H rfl
    have hnt : ε₂ ≠ ∞ := by rintro rfl; simp at H
    obtain rfl : (ε + ε₂') = ε₁' :=
      ENNReal.add_left_inj hnt |>.mp (.trans (add_rotate ..).symm h2)
    refine ⟨?_, by grind⟩
    refine Std.lt_of_le_of_lt ?_ H
    rw [add_comm]
    exact add_le_add_left h1 ε

/-! ## Ghost state and notation -/

instance : Iris.IsUnit (◯ 0 : Auth ErrorCredit) where
  unit_valid := Auth.frag_valid.mpr (by simp [CMRA.Valid])
  unit_left_id := by simp [CMRA.op]
  pcore_unit := by simp [CMRA.pcore, CMRA.core]

/-- Ghost-state resource for error credits. -/
class ECPreGS (GF : BundledGFunctors) where
  ec : ElemG GF (constOF (Auth ErrorCredit))

attribute [reducible, instance] ECPreGS.ec

/-- `ECPreGS` together with its ghost name. -/
class ECGS (GF : BundledGFunctors) extends ECPreGS GF where
  γec : GName

section Resources

variable {GF : BundledGFunctors} [IEC : ECGS GF]

/-- Authoritative total of error credits, written `●↯ ε`. -/
def ecAuth (ε : ℝ≥0∞) : IProp GF := iOwn (E := IEC.ec) IEC.γec (● ε)
/-- Ownership of `ε` error credits, written `↯ε`. -/
def ec (ε : ℝ≥0∞) : IProp GF := iOwn (E := IEC.ec) IEC.γec (◯ ε)
notation "↯ " r:50 => ec r
notation "●↯ " r:50 => ecAuth r

instance : CMRA.Discrete (Auth ErrorCredit) := by infer_instance
instance : OFE.DiscreteE (◯ r : Auth ErrorCredit) := Auth.frag_discrete

end Resources

/-! ## Rules for `↯ε` and `●↯ε` -/

namespace ErrorCredit

variable {GF : BundledGFunctors} [IEC : ECGS GF]
local bi IProp GF

/-- Equal credit amounts are interchangeable. -/
theorem ext {ε₁ ε₂} (he : ε₁ = ε₂) : ↯ε₁ ⊢ ↯ε₂ := by simp [he]

/-- Equal authoritative totals are interchangeable. -/
theorem extAuth {ε₁ ε₂} (he : ε₁ = ε₂) : ●↯ ε₁ ⊢ ●↯ ε₂ := by simp [he]

/-- Credits split additively. -/
theorem split {ε₁ ε₂} : ↯(ε₁ + ε₂) ⊢ ↯ε₁ ∗ ↯ε₂ := by
  unfold ec
  iintro Hε
  iapply iOwn_op
  simp [CMRA.op]
  iexact Hε

/-- Take `ε₁` credits out of `ε₂`, keeping the difference. -/
theorem difference {ε₁ ε₂} (Hwf : ε₁ ≤ ε₂) : ↯ε₂ ⊢ ↯ε₁ ∗ ↯(ε₂ - ε₁) := by
  iintro H
  iapply split
  iapply ext (add_tsub_cancel_of_le Hwf).symm $$ H

/-- Credits combine additively. -/
theorem combine {ε₁ ε₂} : ↯ε₁ ∗ ↯ε₂ ⊢ ↯(ε₁ + ε₂) := by
  unfold ec
  iintro ⟨H1, H2⟩
  icombine H1 H2 as Hε
  iexact Hε

instance {ε₁ ε₂} : Iris.ProofMode.CombineSepAs (↯ε₁ : IProp GF) (↯ε₂) (↯(ε₁ + ε₂)) where
  combine_sep_as := combine

/-- Zero credits can always be allocated. -/
theorem zero : ⊢ |==> ↯0 := iOwn_unit

/-- Owned credits never exceed the authoritative total. -/
theorem supply_bound {εₛ ε} : ⊢ ●↯ εₛ -∗ ↯ε -∗ ⌜ε ≤ εₛ⌝ := by
  unfold ec ecAuth
  iintro Hs Hε
  icombine Hs Hε gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  exact includedN_iff.mp ((Auth.auth_both_valid.mp hv).1 0)

/-- Spending `ε` credits decreases the authoritative total by `ε`. -/
theorem supply_decrease {εₛ ε} : ⊢ ●↯ εₛ -∗ ↯ε -∗ |==> ●↯ (εₛ - ε) := by
  iintro Hs Hε
  ihave %hle := supply_bound $$ Hs Hε
  unfold ec ecAuth
  ihave Hc := iOwn_op |>.mpr $$ [$Hs $Hε]
  refine iOwn_update <| Auth.auth_update_dealloc ?_
  simp only [UCMRA.unit]
  refine localUpdate zero_le ?_
  simpa [add_zero] using (tsub_add_cancel_of_le hle).symm

/-- Allocating `ε₂` credits increases the authoritative total, while it stays below `1`. -/
theorem supply_increase {ε₁ ε₂ : ℝ≥0∞} (h : ε₁ + ε₂ < 1) :
    ●↯ ε₁ ⊢ |==> (●↯ (ε₁ + ε₂) ∗ ↯ε₂) := by
  unfold ec ecAuth
  have hupd : (● ε₁) ~~> (● ε₁ + ε₂) • (◯ ε₂ : Auth ℝ≥0∞) := by
    refine Auth.auth_update_alloc <| (local_update_unital_discrete ..).mpr ?_
    simp only [CMRA.Valid, CMRA.op, UCMRA.unit, zero_add, forall_apply_eq_imp_iff]
    exact fun _ => ⟨h, add_comm _ _⟩
  iintro Hε
  imod (iOwn_update hupd) $$ Hε with H
  imodintro
  iapply iOwn_op
  iexact H

/-- Fewer credits can be obtained from more. -/
theorem weaken {ε₁ ε₂ : ℝ≥0∞} (h : ε₂ ≤ ε₁) : ↯ε₁ ⊢ ↯ε₂ := by
  iintro Hε
  rw [← tsub_add_cancel_of_le h]
  ihave ⟨-, H⟩ := split $$ Hε
  iexact H

/-- Owned credits are below `1`. -/
theorem valid {ε : ℝ≥0∞} : ↯ε ⊢ ⌜ε < 1⌝ := by
  unfold ec
  iintro Hε
  ihave Hv := iOwn_cmraValid $$ Hε
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  exact Auth.frag_valid.mp hv

/-- Owning at least `1` credit is contradictory. -/
theorem contradict {ε : ℝ≥0∞} (h : 1 ≤ ε) : ↯ε ⊢ False := by
  iintro Hε
  ihave %hle := valid $$ Hε
  exact absurd h (Std.not_le.mpr hle)

instance ec_timeless (ε : ℝ≥0∞) : BI.Timeless (↯ε : IProp GF) := iOwn_timeless

/-! ## Error amplification

If `↯ε` can always be traded for `↯(k * ε)` on the way to `P`, then `↯ε` proves `P`: iterating
the trade reaches `1` credit, which `contradict` refutes. -/

namespace Induction

/-- For `ε > 0` and `k > 1`, some power `kⁿ` lifts `ε` to at least `1`. -/
theorem err_amp_power {ε : ℝ≥0∞} {k : ℝ≥0} (hε : 0 < ε) (hk : 1 < k) :
    ∃ n : ℕ, 1 ≤ ε * (k : ℝ≥0∞) ^ n := by
  obtain rfl | hε' := eq_or_ne ε ∞
  · exact ⟨0, by simp⟩
  · lift ε to ℝ≥0 using hε' with ε
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ε⁻¹ (by exact_mod_cast hk)
    have hlift : (1 : ℝ≥0) ≤ ε * k ^ n := by
      rw [mul_comm]
      refine (inv_le_iff_one_le_mul₀ ?_).mp hn.le
      exact_mod_cast hε
    exact ⟨n, by exact_mod_cast hlift⟩

/-- For `ε > 0` and `k > 1`, some `n` makes `n(k-1)ε + ε' ≥ 1` (pure arithmetic). -/
theorem err_amp_mult {ε ε' : ℝ≥0∞} {k : ℝ≥0} (hε : 0 < ε) (hle : ε ≤ ε') (hk : 1 < k) :
    ∃ n : ℕ, 1 ≤ (n : ℝ≥0∞) * ((k : ℝ≥0∞) - 1) * ε + ε' := by
  obtain rfl | hεne := eq_or_ne ε ∞
  · exact ⟨0, by simp [top_le_iff.mp hle]⟩
  · lift ε to ℝ≥0 using hεne with ε
    obtain ⟨n, hn⟩ := exists_nat_ge ((k - 1) * ε)⁻¹
    refine ⟨n, le_add_right ?_⟩
    have h1 : (1 : ℝ≥0) ≤ n * (k - 1) * ε := by
      rw [mul_assoc]
      refine (inv_le_iff_one_le_mul₀ ?_).mp hn
      exact mul_pos (tsub_pos_of_lt hk) (by exact_mod_cast hε)
    have hcoe : ((k : ℝ≥0∞) - 1) = ((k - 1 : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
    rw [hcoe]
    exact_mod_cast h1

/-- Error amplification: a spending proof that works at `k * ε` credits works at `ε`. -/
theorem simple {ε : ℝ≥0∞} {k : ℝ≥0} {P : IProp GF} (hε : 0 < ε) (hk : 1 < k) :
    □ ((↯(k * ε) -∗ P) ∗ ↯ε -∗ P) ⊢ ↯ε -∗ P := by
  suffices haux : ∀ ε', ε ≤ ε' → □ ((↯(k * ε) -∗ P) ∗ ↯ε -∗ P) ⊢ ↯ε' -∗ P by
    iapply haux _ le_rfl
  iintro %ε' %hle #Hamp Hε
  -- Each round gains `(k-1)ε`; `err_amp_mult` picks `n` rounds that reach `1` credit.
  obtain ⟨n, hn⟩ := err_amp_mult hε hle hk
  iinduction n generalizing %ε' %hle %hn Hε with
  | zero =>
    iexfalso
    simp at hn
    iapply contradict hn $$ Hε
  | succ n IH =>
    have hk1 : (1 : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by exact_mod_cast hk.le
    have hkε : (k : ℝ≥0∞) * ε = ((k : ℝ≥0∞) - 1) * ε + ε := by
      conv_lhs => rw [← tsub_add_cancel_of_le hk1, add_mul, one_mul]
    have hε' : ε' = (ε' - ε) + ε := (tsub_add_cancel_of_le hle).symm
    set ε'' : ℝ≥0∞ := ε' + ((k : ℝ≥0∞) - 1) * ε
    have hε'' : (ε' - ε) + (k : ℝ≥0∞) * ε = ε'' := by
      rw [hkε, ← add_assoc, add_right_comm, ← hε']
    have hn' : 1 ≤ (n : ℝ≥0∞) * ((k : ℝ≥0∞) - 1) * ε + ε'' := by
      refine hn.trans (Std.le_of_eq ?_)
      show _ = _ * _ + (ε' + _)
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_mul,
          add_assoc, add_comm (_ * ε) ε', ← add_assoc]
    rw [hε']
    ihave ⟨Hε₁, Hε₂⟩ := split $$ Hε
    iapply Hamp
    iframe Hε₂
    iintro Hε
    icombine Hε₁ Hε as Hε₃
    iapply IH $$ %ε'' %(hle.trans le_self_add) %hn'
    iapply ext hε'' $$ Hε₃

/-- External-entailment form of `simple`. -/
theorem external_simple {ε : ℝ≥0∞} {k : ℝ≥0} {P : IProp GF} (hε : 0 < ε) (hk : 1 < k)
    (hamp : (↯(k * ε) -∗ P) ∗ ↯ε ⊢ P) : ↯ε ⊢ P := by
  iapply simple hε hk
  iintro !> H
  iapply hamp $$ H

/-- Amplification by an arbitrary larger credit amount `ε'`. -/
theorem increasing {ε : ℝ≥0∞} {ε' : ℝ≥0} {P : IProp GF} (hε : 0 < ε) (hε' : ε < ε') :
    □ ((↯ε' -∗ P) ∗ ↯ε -∗ P) ⊢ ↯ε -∗ P := by
  iintro #Hamp Hε
  let k' : ℝ≥0∞ := ε' / ε
  have hk1 : 1 < k' := ENNReal.lt_div_iff_mul_lt (by simp) (by simp) |>.mpr (by simp [hε'])
  have hk' : k' ≠ ∞ := ENNReal.div_ne_top ENNReal.coe_ne_top (Std.ne_of_lt hε).symm
  have hkeq : ε' = k' * ε := by
    dsimp [k']
    have hεε : ε / ε = 1 := ENNReal.div_self (Std.ne_of_lt hε).symm (LT.lt.ne_top hε')
    simp [ENNReal.mul_comm_div, hεε]
  lift k' to ℝ≥0 using hk' with k
  have hk : 1 < k := ENNReal.one_lt_coe_iff.mp hk1
  iapply simple hε hk $$ [] Hε
  iintro !> ⟨Hc, Hε⟩
  iapply Hamp
  iframe Hε
  iintro Hε
  iapply Hc
  iapply ext hkeq $$ Hε

/-- Amplification, with the amplification step quantified over every positive `ε'`. -/
theorem amplifying {ε : ℝ≥0∞} {k : ℝ≥0} {P : IProp GF} (hε : 0 < ε) (hk : 1 < k) :
    □ (∀ {ε' : ℝ≥0∞}, ⌜0 < ε'⌝ -∗ □ (↯(k * ε') -∗ P) -∗ ↯ε' -∗ P)
      ⊢ ↯ε -∗ P := by
  iintro #Hamp Hε
  obtain ⟨n, hn⟩ := err_amp_power hε hk
  iinduction n generalizing %ε %hε %hn Hε with
  | zero =>
    iexfalso
    simp at hn
    iapply contradict hn $$ Hε
  | succ n IH =>
    iapply Hamp $$ %_ %hε [] Hε
    iintro !> Hε
    iapply IH $$ %(k * ε)
      %(ENNReal.mul_pos_iff.mpr ⟨ENNReal.coe_pos.mpr (pos_of_gt hk), pos_of_gt hε⟩)
      %(hn.trans (_root_.le_of_eq (by ring))) Hε

/-- External-entailment form of `amplifying`. -/
theorem amp_external {ε : ℝ≥0∞} {k : ℝ≥0} {P : IProp GF}
    (hε : 0 < ε) (hk : 1 < k)
    (hamp : ∀ {ε'}, 0 < ε' → □ (↯((k : ℝ≥0∞) * ε') -∗ P) ∗ ↯ε' ⊢ P) :
    ↯ε ⊢ P := by
  iapply amplifying hε hk
  iintro !> %ε' %hε' #H Hε
  iapply hamp hε'
  isplitr [Hε] <;> first | iexact H | iexact Hε

end Induction

end ErrorCredit

/-! ## Allocation -/

/-- Allocate fresh error-credit ghost state holding `ε < 1` credits. -/
theorem ec_alloc {GF : BundledGFunctors} [IEC : ECPreGS GF] (ε : ℝ≥0∞) (h : ε < 1) :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      ecAuth (IEC := { toECPreGS := IEC, γec := γ }) ε ∗
      ec (IEC := { toECPreGS := IEC, γec := γ }) ε := by
  unfold ec ecAuth
  imod (iOwn_alloc (E := IEC.ec) ((● ε) • (◯ ε)) (Auth.auth_both_valid_2 h .rfl)) with ⟨%γ, Hγ⟩
  imodintro
  iexists γ
  iapply iOwn_op
  iexact Hγ

end
