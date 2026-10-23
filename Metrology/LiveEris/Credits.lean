module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Iris
public import Iris.Algebra.Auth
public import Iris.Instances.IProp.Instance
public import Iris.ProofMode.InstancesUpdates
import Metrology.Iris.LocalBI

@[expose] public section

/-!
# Error and divergence credits

The credit resource of LiveEris: an error credit `↯ε` paired with a divergence credit `↻δ`,
as a product of two bounded credit algebras.
-/

noncomputable section

open Iris COFE
open ENNReal

namespace ProbLang
namespace LiveEris

/-- A nonnegative credit amount, valid when it is strictly below `b`. -/
@[ext]
structure CreditBelow (b : ℝ≥0∞) where
  /-- The amount of credit. -/
  val : ℝ≥0∞

namespace CreditBelow

variable {b : ℝ≥0∞}

instance : COFE (CreditBelow b) := COFE.ofDiscrete _
instance : OFE.Discrete (CreditBelow b) := ⟨id⟩
instance (x : CreditBelow b) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : CMRA (CreditBelow b) where
  pcore _ := some ⟨0⟩
  op x y := ⟨x.val + y.val⟩
  ValidN _ x := x.val < b
  Valid x := x.val < b
  op_ne.ne _ _ _ h := by rw [h]
  pcore_ne _ := by rintro ⟨rfl⟩; exists ⟨0⟩
  validN_ne {_ _ _} := by rintro ⟨rfl⟩; exact id
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left {_ _ _} H := lt_of_le_of_lt le_self_add H
  assoc {_ _ _} := by ext; exact (add_assoc ..).symm
  comm {_ _} := by ext; exact add_comm ..
  pcore_op_left {_ _} := by rintro ⟨rfl⟩; ext; exact zero_add _
  pcore_idem := by simp
  pcore_op_mono {_ _} := by rintro ⟨rfl⟩ _; exists ⟨0⟩; simp
  extend _ h := ⟨_, _, OFE.discrete h, .rfl, .rfl⟩

instance : CMRA.Discrete (CreditBelow b) where
  discrete_valid := id

instance [NeZero b] : UCMRA (CreditBelow b) where
  unit := ⟨0⟩
  unit_valid := pos_iff_ne_zero.mpr (NeZero.ne b)
  unit_left_id := by intro _; ext; exact zero_add _
  pcore_unit := rfl

@[simp] theorem op_val (x y : CreditBelow b) : (x • y).val = x.val + y.val := rfl

@[simp] theorem unit_val [NeZero b] : (UCMRA.unit : CreditBelow b).val = 0 := rfl

@[simp] theorem valid_iff (x : CreditBelow b) : ✓ x ↔ x.val < b := .rfl

@[simp] theorem validN_iff {n} (x : CreditBelow b) : ✓{n} x ↔ x.val < b := .rfl

theorem included_iff {x y : CreditBelow b} : x ≼ y ↔ x.val ≤ y.val := by
  refine ⟨?_, fun h => ⟨⟨y.val - x.val⟩, CreditBelow.ext (add_tsub_cancel_of_le h).symm⟩⟩
  rintro ⟨z, rfl⟩
  exact le_self_add

theorem includedN_iff {n} {x y : CreditBelow b} : x ≼{n} y ↔ x.val ≤ y.val :=
  included_iff

theorem local_update {x₁ x₂ x₁' x₂' : CreditBelow b} (h1 : x₂'.val ≤ x₂.val)
    (h2 : x₁.val + x₂'.val = x₁'.val + x₂.val) : (x₁, x₂) ~l~> (x₁', x₂') := by
  rintro n (_ | z) <;> simp only [OFE.Dist, CMRA.op?, validN_iff]
  · rintro H rfl
    have hx : x₂'.val = x₁'.val := (ENNReal.add_right_inj H.ne_top).mp (h2.trans (add_comm _ _))
    exact ⟨hx ▸ lt_of_le_of_lt h1 H, CreditBelow.ext hx.symm⟩
  · rintro H rfl
    simp only [op_val] at h2 H
    have hz : z.val + x₂'.val = x₁'.val := by
      refine (ENNReal.add_right_inj (ne_top_of_le_ne_top H.ne_top le_self_add)).mp ?_
      rw [← add_assoc, h2, add_comm]
    refine ⟨hz ▸ lt_of_le_of_lt ?_ H, CreditBelow.ext ?_⟩
    · rw [add_comm]; gcongr
    · simp only [op_val]; rw [← hz, add_comm]

end CreditBelow

instance : NeZero (∞ : ℝ≥0∞) := ⟨ENNReal.top_ne_zero⟩

/-- The LiveEris credit: an error credit (valid below 1) paired with a divergence credit (valid
when finite). -/
abbrev LiveCredit : Type := CreditBelow 1 × CreditBelow ∞

/-- The credit pair holding `ε` error credit and `δ` divergence credit. -/
abbrev credits (ε δ : ℝ≥0∞) : LiveCredit := (⟨ε⟩, ⟨δ⟩)

theorem credits_op (ε₁ δ₁ ε₂ δ₂ : ℝ≥0∞) :
    credits ε₁ δ₁ • credits ε₂ δ₂ = credits (ε₁ + ε₂) (δ₁ + δ₂) := rfl

theorem credits_valid {ε δ : ℝ≥0∞} : (✓ credits ε δ) ↔ ε < 1 ∧ δ < ∞ := .rfl

theorem credits_included {ε₁ δ₁ ε₂ δ₂ : ℝ≥0∞} :
    credits ε₁ δ₁ ≼ credits ε₂ δ₂ ↔ ε₁ ≤ ε₂ ∧ δ₁ ≤ δ₂ :=
  Prod.inc_def.trans (and_congr CreditBelow.included_iff CreditBelow.included_iff)

theorem credits_includedN {n} {ε₁ δ₁ ε₂ δ₂ : ℝ≥0∞} :
    credits ε₁ δ₁ ≼{n} credits ε₂ δ₂ ↔ ε₁ ≤ ε₂ ∧ δ₁ ≤ δ₂ :=
  Prod.incN_def.trans (and_congr CreditBelow.includedN_iff CreditBelow.includedN_iff)

theorem credits_unit : (UCMRA.unit : LiveCredit) = credits 0 0 := rfl

instance : IsUnit (◯ credits 0 0 : Auth LiveCredit) :=
  inferInstanceAs (IsUnit (UCMRA.unit : Auth LiveCredit))

/-- The ghost-state resources needed to allocate LiveEris credits. -/
class LCPreGS (GF : BundledGFunctors) where
  /-- The ghost map holding the credit algebra. -/
  lc : ElemG GF (constOF (Auth LiveCredit))

attribute [reducible, instance] LCPreGS.lc

/-- The ghost-state resources of LiveEris credits, with the credit ghost name fixed. -/
class LCGS (GF : BundledGFunctors) extends LCPreGS GF where
  /-- The ghost name of the credit resource. -/
  γlc : GName

variable {GF : BundledGFunctors} [ILC : LCGS GF]

section Resources

/-- The authoritative credit supply. -/
def creditAuth (ε δ : ℝ≥0∞) : IProp GF := iOwn (E := ILC.lc) ILC.γlc (● credits ε δ)

/-- A fragment of the credit supply. -/
def creditFrag (ε δ : ℝ≥0∞) : IProp GF := iOwn (E := ILC.lc) ILC.γlc (◯ credits ε δ)

scoped notation "↯ " r:50 => creditFrag r 0
scoped notation "↻ " r:50 => creditFrag 0 r

instance : CMRA.Discrete (Auth LiveCredit) := by infer_instance
instance {r : LiveCredit} : OFE.DiscreteE (◯ r : Auth LiveCredit) := Auth.frag_discrete

instance creditFrag_timeless (ε δ : ℝ≥0∞) : BI.Timeless (creditFrag ε δ : IProp GF) :=
  iOwn_timeless

end Resources

namespace Credit

variable {ε₁ δ₁ ε₂ δ₂ : ℝ≥0∞}
local bi IProp GF

theorem frag_ext (hε : ε₁ = ε₂) (hδ : δ₁ = δ₂) :
    creditFrag ε₁ δ₁ ⊢ creditFrag ε₂ δ₂ := by
  simp [hε, hδ]

theorem auth_ext (hε : ε₁ = ε₂) (hδ : δ₁ = δ₂) :
    creditAuth ε₁ δ₁ ⊢ creditAuth ε₂ δ₂ := by
  simp [hε, hδ]

theorem frag_split :
    creditFrag (ε₁ + ε₂) (δ₁ + δ₂) ⊢ creditFrag ε₁ δ₁ ∗ creditFrag ε₂ δ₂ := by
  unfold creditFrag
  rw [← credits_op, Auth.frag_op]
  exact iOwn_op.mp

theorem frag_combine :
    creditFrag ε₁ δ₁ ∗ creditFrag ε₂ δ₂ ⊢ creditFrag (ε₁ + ε₂) (δ₁ + δ₂) := by
  unfold creditFrag
  iintro ⟨H1, H2⟩
  icombine H1 H2 as H
  iexact H

instance : ProofMode.CombineSepAs (creditFrag ε₁ δ₁ : IProp GF)
    (creditFrag ε₂ δ₂) (creditFrag (ε₁ + ε₂) (δ₁ + δ₂)) where
  combine_sep_as := frag_combine

theorem frag_sep {ε δ} : creditFrag ε δ ⊣⊢ ↯ε ∗ ↻δ :=
  ⟨(frag_ext (add_zero ε).symm (zero_add δ).symm).trans frag_split,
   frag_combine.trans (frag_ext (add_zero ε) (zero_add δ))⟩

theorem err_split {ε₁ ε₂} : ↯(ε₁ + ε₂) ⊢ ↯ε₁ ∗ ↯ε₂ :=
  (frag_ext rfl (add_zero 0).symm).trans frag_split

theorem err_combine {ε₁ ε₂} : ↯ε₁ ∗ ↯ε₂ ⊢ ↯(ε₁ + ε₂) :=
  frag_combine.trans (frag_ext rfl (add_zero 0))

theorem div_split {δ₁ δ₂} : ↻(δ₁ + δ₂) ⊢ ↻δ₁ ∗ ↻δ₂ :=
  (frag_ext (add_zero 0).symm rfl).trans frag_split

theorem div_combine {δ₁ δ₂} : ↻δ₁ ∗ ↻δ₂ ⊢ ↻(δ₁ + δ₂) :=
  frag_combine.trans (frag_ext (add_zero 0) rfl)

theorem frag_weaken (hε : ε₂ ≤ ε₁) (hδ : δ₂ ≤ δ₁) :
    creditFrag ε₁ δ₁ ⊢ creditFrag ε₂ δ₂ := by
  iintro H
  ihave H := frag_ext (tsub_add_cancel_of_le hε).symm (tsub_add_cancel_of_le hδ).symm $$ H
  ihave ⟨-, H⟩ := frag_split $$ H
  iexact H

theorem err_weaken {ε₁ ε₂ : ℝ≥0∞} (h : ε₂ ≤ ε₁) : ↯ε₁ ⊢ ↯ε₂ :=
  frag_weaken h le_rfl

theorem div_weaken {δ₁ δ₂ : ℝ≥0∞} (h : δ₂ ≤ δ₁) : ↻δ₁ ⊢ ↻δ₂ :=
  frag_weaken le_rfl h

theorem zero : ⊢ |==> creditFrag 0 0 := iOwn_unit

theorem frag_valid {ε δ : ℝ≥0∞} : creditFrag ε δ ⊢ ⌜ε < 1 ∧ δ < ∞⌝ := by
  unfold creditFrag
  iintro H
  ihave Hv := iOwn_cmraValid $$ H
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  exact Auth.frag_valid.mp hv

theorem err_contradict {ε : ℝ≥0∞} (h : 1 ≤ ε) : ↯ε ⊢ False := by
  iintro H
  ihave %⟨hlt, _⟩ := frag_valid $$ H
  exact absurd h (not_le.mpr hlt)

theorem auth_valid {εₛ δₛ : ℝ≥0∞} : creditAuth εₛ δₛ ⊢ ⌜εₛ < 1 ∧ δₛ < ∞⌝ := by
  unfold creditAuth
  iintro H
  ihave Hv := iOwn_cmraValid $$ H
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  exact Auth.auth_valid.mp hv

theorem supply_bound {εₛ δₛ ε δ : ℝ≥0∞} :
    ⊢ creditAuth εₛ δₛ -∗ creditFrag ε δ -∗ ⌜ε ≤ εₛ ∧ δ ≤ δₛ⌝ := by
  unfold creditFrag creditAuth
  iintro Hs H
  icombine Hs H gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  exact credits_includedN.mp ((Auth.auth_both_valid.mp hv).1 0)

theorem div_bound {εₛ δₛ δ : ℝ≥0∞} :
    ⊢ creditAuth εₛ δₛ -∗ ↻δ -∗ ⌜δ ≤ δₛ⌝ := by
  iintro Hs H
  ihave %⟨-, h⟩ := supply_bound $$ Hs H
  ipureintro
  exact h

theorem supply_decrease {εₛ δₛ ε δ : ℝ≥0∞} :
    ⊢ creditAuth εₛ δₛ -∗ creditFrag ε δ -∗ |==> creditAuth (εₛ - ε) (δₛ - δ) := by
  iintro Hs H
  ihave %⟨hε, hδ⟩ := supply_bound $$ Hs H
  unfold creditFrag creditAuth
  ihave Hc := iOwn_op |>.mpr $$ [$Hs $H]
  refine iOwn_update <| Auth.auth_update_dealloc ?_
  refine LocalUpdate.prod' (CreditBelow.local_update zero_le ?_)
    (CreditBelow.local_update zero_le ?_)
  · simpa using (tsub_add_cancel_of_le hε).symm
  · simpa using (tsub_add_cancel_of_le hδ).symm

theorem supply_increase {εₛ δₛ ε δ : ℝ≥0∞} (hε : εₛ + ε < 1) (hδ : δₛ + δ < ∞) :
    creditAuth εₛ δₛ ⊢ |==> (creditAuth (εₛ + ε) (δₛ + δ) ∗ creditFrag ε δ) := by
  unfold creditFrag creditAuth
  have Hupd :
      (● credits εₛ δₛ) ~~> (● credits (εₛ + ε) (δₛ + δ)) • (◯ credits ε δ : Auth LiveCredit) := by
    refine Auth.auth_update_alloc <| (local_update_unital_discrete ..).mpr ?_
    rintro ⟨⟨z₁⟩, ⟨z₂⟩⟩ ⟨_, _⟩ h
    change credits εₛ δₛ = credits (0 + z₁) (0 + z₂) at h
    simp only [credits, Prod.mk.injEq, CreditBelow.mk.injEq, zero_add] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨hε, hδ⟩, Prod.ext (CreditBelow.ext (add_comm _ _)) (CreditBelow.ext (add_comm _ _))⟩
  iintro H
  imod (iOwn_update Hupd) $$ H with H
  imodintro
  iapply iOwn_op $$ H

theorem supply_convert {εₛ δₛ ε : ℝ≥0∞} :
    ⊢ creditAuth εₛ δₛ -∗ ↯ε -∗ |==> (creditAuth (εₛ - ε) (δₛ + ε) ∗ ↻ε) := by
  iintro Hs H
  ihave %⟨hε, _⟩ := supply_bound $$ Hs H
  ihave %⟨hεₛ, hδₛ⟩ := auth_valid $$ Hs
  imod supply_decrease $$ Hs H with Hs
  have hδ : δₛ - 0 + ε < ∞ := by
    simpa using ENNReal.add_lt_top.mpr ⟨hδₛ, lt_of_le_of_lt hε (hεₛ.trans ENNReal.one_lt_top)⟩
  imod supply_increase (ε := 0) (δ := ε) (by simpa using lt_of_le_of_lt tsub_le_self hεₛ) hδ
    $$ Hs with ⟨Hs, H⟩
  imodintro
  iframe H
  iapply auth_ext (add_zero _) (by simp) $$ Hs

end Credit

theorem credit_alloc {GF : BundledGFunctors} [ILC : LCPreGS GF] (ε δ : ℝ≥0∞) (hε : ε < 1)
    (hδ : δ < ∞) :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      creditAuth (ILC := { toLCPreGS := ILC, γlc := γ }) ε δ ∗
      creditFrag (ILC := { toLCPreGS := ILC, γlc := γ }) ε δ := by
  unfold creditFrag creditAuth
  imod (iOwn_alloc (E := ILC.lc) ((● credits ε δ) • (◯ credits ε δ))
    (Auth.auth_both_valid_2 ⟨hε, hδ⟩ (credits_included.mpr ⟨le_rfl, le_rfl⟩))) with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply iOwn_op $$ H

end LiveEris
end ProbLang
