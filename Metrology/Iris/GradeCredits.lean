module

public import Mathlib.Algebra.Group.Defs
public import Iris
public import Iris.Algebra.View
public import Iris.Instances.IProp.Instance
public import Iris.Algebra.Auth

/-! Grade credits: an authoritative grade budget `●↯g s` and spendable fragments `↯g α` over a
commutative monoid of grades (clutch-dp's `↯m` with multiplicative privacy grades). -/

@[expose] public section

noncomputable section

open Std Iris COFE

/-- Grades as a camera: the operation is the grade product, with unit `1` and no validity bound. -/
def GradeCredit (ι : Type) : Type := ι

namespace GradeCredit

variable {ι : Type} [CommMonoid ι]

instance : CommMonoid (GradeCredit ι) := inferInstanceAs (CommMonoid ι)
instance [IsCancelMul ι] : IsCancelMul (GradeCredit ι) := inferInstanceAs (IsCancelMul ι)

instance : COFE (GradeCredit ι) := COFE.ofDiscrete _
instance : OFE.Discrete (GradeCredit ι) := ⟨id⟩
instance (x : GradeCredit ι) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : CMRA (GradeCredit ι) where
  pcore _ := some 1
  op := (· * ·)
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [h]
  pcore_ne _ := by rintro ⟨rfl⟩; exists 1
  validN_ne _ := id
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := id
  validN_op_left _ := trivial
  assoc := (mul_assoc ..).symm
  comm := mul_comm ..
  pcore_op_left {_ _} := by rintro ⟨rfl⟩; exact one_mul _
  pcore_idem := by simp
  pcore_op_mono {_ _} := by rintro ⟨rfl⟩ _; exact ⟨1, congrArg some (one_mul 1).symm⟩
  extend _ h := ⟨_, _, OFE.discrete h, .rfl, .rfl⟩

instance : CMRA.Discrete (GradeCredit ι) where
  discrete_valid := id

instance : UCMRA (GradeCredit ι) where
  unit := 1
  unit_valid := trivial
  unit_left_id := one_mul _
  pcore_unit := rfl

instance (r : GradeCredit ι) : OFE.DiscreteE (◯ r : Auth (GradeCredit ι)) := Auth.frag_discrete

theorem included_iff {β s : GradeCredit ι} : β ≼ s ↔ ∃ r, s = β * r := .rfl

/-- Spending `β` out of the budget `s = β * r` leaves `r`, by cancellation. -/
theorem localUpdate [IsCancelMul ι] {s β r : GradeCredit ι} (h : s = β * r) :
    (s, β) ~l~> (r, 1) := by
  rintro n (_ | z) - (hs : s = _)
  · exact ⟨trivial, mul_left_cancel (a := β) (h.symm.trans (hs.trans (mul_one β).symm))⟩
  · exact ⟨trivial, (mul_left_cancel (a := β) (h.symm.trans hs)).trans (one_mul z).symm⟩

end GradeCredit

class GradeCreditPreGS (ι : Type) [CommMonoid ι] (GF : BundledGFunctors) where
  gc : ElemG GF (constOF (Auth (GradeCredit ι)))

attribute [reducible, instance] GradeCreditPreGS.gc

class GradeCreditGS (ι : Type) [CommMonoid ι] (GF : BundledGFunctors)
    extends GradeCreditPreGS ι GF where
  γgc : GName

section Resources

variable {ι : Type} [CommMonoid ι] {GF : BundledGFunctors} [IGC : GradeCreditGS ι GF]

/-- The authoritative grade budget. -/
def gcAuth (s : ι) : IProp GF := iOwn (E := IGC.gc) IGC.γgc (● (s : GradeCredit ι))

/-- A spendable grade credit. -/
def gc (α : ι) : IProp GF := iOwn (E := IGC.gc) IGC.γgc (◯ (α : GradeCredit ι))

notation "↯g " r:50 => gc r
notation "●↯g " r:50 => gcAuth r

end Resources

namespace GradeCredit

variable {ι : Type} [CommMonoid ι] {GF : BundledGFunctors} [IGC : GradeCreditGS ι GF]

/-- The fragment of a product is the product of the fragments. -/
theorem frag_mul {α β : ι} :
    (◯ (α * β) : Auth (GradeCredit ι)) =
      (◯ α : Auth (GradeCredit ι)) • (◯ β : Auth (GradeCredit ι)) :=
  Auth.frag_op

theorem split {α β : ι} : ↯g (α * β) ⊢@{IProp GF} ↯g α ∗ ↯g β := by
  unfold gc
  rw [frag_mul]
  iintro H
  iapply iOwn_op
  iexact H

theorem combine {α β : ι} : ↯g α ∗ ↯g β ⊢@{IProp GF} ↯g (α * β) := by
  unfold gc
  rw [frag_mul]
  iintro ⟨H1, H2⟩
  icombine H1 H2 as H
  iexact H

/-- A credit for `α * β` covers a credit for `α`. -/
theorem weaken {α β : ι} : ↯g (α * β) ⊢@{IProp GF} ↯g α := by
  iintro H
  ihave ⟨H, -⟩ := split $$ H
  iexact H

/-- A fragment divides the budget. -/
theorem supply_bound {s β : ι} : ⊢@{IProp GF} ●↯g s -∗ ↯g β -∗ ⌜∃ r, s = β * r⌝ := by
  unfold gc gcAuth
  iintro Hs Hβ
  icombine Hs Hβ gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  exact included_iff.mp ((CMRA.inc_iff_incN 0).mpr ((Auth.auth_both_valid.mp hv).1 0))

/-- Spending a fragment `β` divides it out of the budget. -/
theorem supply_decrease [IsCancelMul ι] {s β : ι} :
    ⊢@{IProp GF} ●↯g s -∗ ↯g β -∗ |==> ∃ r, ⌜s = β * r⌝ ∗ ●↯g r := by
  iintro Hs Hβ
  ihave %⟨r, hr⟩ := supply_bound $$ Hs Hβ
  unfold gc gcAuth
  ihave Hc := iOwn_op |>.mpr $$ [$Hs $Hβ]
  imod iOwn_update (Auth.auth_update_dealloc (localUpdate (r := r) hr)) $$ Hc with H
  imodintro
  iexists r
  iframe %hr H

instance gc_timeless (α : ι) : BI.Timeless (↯g α : IProp GF) := iOwn_timeless

end GradeCredit

theorem gc_alloc {ι : Type} [CommMonoid ι] {GF : BundledGFunctors} [IGC : GradeCreditPreGS ι GF]
    (α : ι) :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      gcAuth (IGC := { toGradeCreditPreGS := IGC, γgc := γ }) α ∗
      gc (IGC := { toGradeCreditPreGS := IGC, γgc := γ }) α := by
  unfold gc gcAuth
  imod (iOwn_alloc (E := IGC.gc) ((● (α : GradeCredit ι)) • (◯ (α : GradeCredit ι)))
    (Auth.auth_both_valid_2 trivial .rfl)) with ⟨%γ, Hγ⟩
  imodintro
  iexists γ
  iapply iOwn_op
  iexact Hγ

end
