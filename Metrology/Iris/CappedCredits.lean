module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Order.Defs.Unbundled
public import Iris.ProofMode
public import Iris.Algebra.Auth
public import Iris.Instances.IProp.Instance
public import Metrology.Iris.AuthCredit
import Metrology.Iris.LocalBI

/-!
# Capped credits

Budget credits valid only outside an upward-closed set `bad`: authority `●↯c s`, fragment `↯c c`
(Rocq `gcappedUR`). Main results: `supply_decrease`, `supply_increase`, `valid`. Not used by wp.
-/

@[expose] public section

open Iris

/-! ## The camera -/

/-- Budgets as a camera: the operation is `+`, with unit `0`, valid away from `bad`
(Rocq `gcappedUR`). -/
@[nolint unusedArguments]
def CappedCredit (B : Type*) (_bad : Set B) : Type _ := B

namespace CappedCredit

/-- A budget below a budget that is not bad is not bad. -/
theorem notMem_of_le {B : Type*} [LE B] {bad : Set B} [Fact (IsUpperSet bad)] {a b : B}
    (h : a ≤ b) (hb : b ∉ bad) : a ∉ bad :=
  fun ha ↦ hb ((Fact.out : IsUpperSet bad) h ha)

variable {B : Type*} [AddCommMonoid B] [LE B] [CanonicallyOrderedAdd B] {bad : Set B}

instance instAddCommMonoid : AddCommMonoid (CappedCredit B bad) :=
  inferInstanceAs (AddCommMonoid B)
instance instLE : LE (CappedCredit B bad) := inferInstanceAs (LE B)
instance instCanonicallyOrderedAdd : CanonicallyOrderedAdd (CappedCredit B bad) :=
  inferInstanceAs (CanonicallyOrderedAdd B)
instance instCOFE : COFE (CappedCredit B bad) := COFE.ofDiscrete _
instance instDiscrete : OFE.Discrete (CappedCredit B bad) := ⟨id⟩

variable [Fact (IsUpperSet bad)]

/-- Validity is `c ∉ bad`; it passes to pieces since `bad` is an upper set. -/
instance instCMRA : CMRA (CappedCredit B bad) :=
  CMRA.ofDiscreteTotal (fun _ ↦ 0) (· + ·) (· ∉ bad)
    (fun _ _ _ ↦ (add_assoc ..).symm) add_comm zero_add (fun _ ↦ rfl)
    (fun _ _ _ ↦ ⟨0, (zero_add 0).symm⟩)
    fun x _ ↦ notMem_of_le (bad := bad) (le_self_add (a := (x : B)))

instance instCMRADiscrete : CMRA.Discrete (CappedCredit B bad) := ⟨id⟩

variable {s c r : CappedCredit B bad}

/-- A capped credit is valid when it is not bad. -/
theorem valid_iff : ✓ c ↔ (c : B) ∉ bad := Iff.rfl

/-- Camera inclusion in a budget is the canonical order. -/
theorem included_iff : c ≼ s ↔ c ≤ s :=
  le_iff_exists_add.symm

variable [Fact ((0 : B) ∉ bad)]

/-- The unit `0` is valid since it is not bad. -/
instance instUCMRA : UCMRA (CappedCredit B bad) where
  unit := 0
  unit_valid := Fact.out (p := (0 : B) ∉ bad)
  unit_left_id := zero_add _
  pcore_unit := rfl

/-- Spending a cancelable `c` out of `s = c + r` leaves `r` (Rocq `gcapped_spend_local_update`). -/
theorem spend_local_update (hc : IsAddLeftRegular c) (h : s = c + r) : (s, c) ~l~> (r, 0) :=
  (local_update_unital_discrete ..).mpr fun _ hs hz ↦
    ⟨notMem_of_le (bad := bad) (show (r : B) ≤ s from h ▸ le_add_self) hs,
      (hc (h.symm.trans hz)).trans (zero_add _).symm⟩

/-- Adding `c` to a budget `s` with `s + c` valid hands out a fragment `c`. -/
theorem alloc_local_update (h : (s + c : B) ∉ bad) : (s, 0) ~l~> (s + c, c) :=
  (local_update_unital_discrete ..).mpr fun z _ hz ↦
    ⟨h, (congrArg (· + c) (hz.trans (zero_add z))).trans (add_comm z c)⟩

end CappedCredit

/-! ## Ghost state and the credit assertions -/

/-- The ghost-state slot for an authoritative capped-credit camera. -/
class CappedCreditPreGS (B : Type) [AddCommMonoid B] [LE B] [CanonicallyOrderedAdd B]
    (bad : outParam (Set B)) [Fact (IsUpperSet bad)] [Fact ((0 : B) ∉ bad)]
    (GF : BundledGFunctors) where
  cc : ElemG GF (constOF (Auth (CappedCredit B bad)))

attribute [reducible, instance] CappedCreditPreGS.cc

/-- A capped-credit camera with its ghost name. -/
class CappedCreditGS (B : Type) [AddCommMonoid B] [LE B] [CanonicallyOrderedAdd B]
    (bad : outParam (Set B)) [Fact (IsUpperSet bad)] [Fact ((0 : B) ∉ bad)]
    (GF : BundledGFunctors) extends CappedCreditPreGS B bad GF where
  γcc : GName

section Resources

variable {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] {bad : Set B}
  [Fact (IsUpperSet bad)] [Fact ((0 : B) ∉ bad)] {GF : BundledGFunctors}
  [ICC : CappedCreditGS B bad GF]

/-- The authoritative capped budget. -/
def ccAuth (s : B) : IProp GF := iOwn (E := ICC.cc) ICC.γcc (● (s : CappedCredit B bad))

/-- A spendable capped credit. -/
def cc (c : B) : IProp GF := iOwn (E := ICC.cc) ICC.γcc (◯ (c : CappedCredit B bad))

notation "↯c " c:50 => cc c
notation "●↯c " s:50 => ccAuth s

/-! ## Credit rules -/

namespace CappedCredit

local bi IProp GF

/-! ### Splitting and combining -/

/-- A credit splits into two credits (Rocq `gccredit_split`). -/
theorem split {a b : B} : ↯c (a + b) ⊢ ↯c a ∗ ↯c b :=
  AuthCredit.frag_split

/-- Two credits combine into one. -/
theorem combine {a b : B} : ↯c a ∗ ↯c b ⊢ ↯c (a + b) :=
  AuthCredit.frag_combine

/-- Proof mode combines credits by adding them. -/
instance combineSepAs_cc {a b : B} :
    ProofMode.CombineSepAs (↯c a : IProp GF) (↯c b) (↯c (a + b)) where
  combine_sep_as := combine

/-- A credit can be weakened to a smaller one. -/
theorem weaken {a b : B} (hb : b ≤ a) : ↯c a ⊢ ↯c b := by
  obtain ⟨c, rfl⟩ := exists_add_of_le hb
  exact split.trans BI.sep_elim_left

/-- The zero credit is free. -/
theorem zero : ⊢ |==> ↯c (0 : B) :=
  AuthCredit.frag_unit

/-! ### Validity -/

/-- A credit is never bad (Rocq `gccredit_valid`). -/
theorem valid {c : B} : ↯c c ⊢ ⌜c ∉ bad⌝ := by
  unfold cc
  iintro Hc
  ihave Hv := iOwn_cmraValid $$ Hc
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  exact Auth.frag_valid.mp hv

/-- A bad credit is contradictory (Rocq `gccredit_ge_top_False`). -/
theorem contradict {c : B} (h : c ∈ bad) : ↯c c ⊢ False := by
  iintro Hc
  ihave %hc := valid $$ Hc
  exact absurd h hc

/-! ### Spending and allocating against the authority -/

/-- A credit never exceeds the authoritative budget (Rocq `gcsupply_bound`). -/
theorem supply_bound {s c : B} : ⊢ ●↯c s -∗ ↯c c -∗ ⌜c ≤ s⌝ := by
  unfold cc ccAuth
  iintro Hs Hc
  ihave %h := AuthCredit.supply_bound (E := ICC.cc) (γ := ICC.γcc) (s := (s : CappedCredit B bad))
    (c := (c : CappedCredit B bad)) $$ Hs Hc
  ipureintro
  exact included_iff.mp h

/-- Spending a cancelable credit `c` takes it out of the budget (Rocq `gcsupply_decrease`). -/
theorem supply_decrease {s c : B} (hc : IsAddLeftRegular c) :
    ⊢ ●↯c s -∗ ↯c c -∗ |==> ∃ r, ⌜s = c + r⌝ ∗ ●↯c r := by
  iintro Hs Hc
  ihave %hcs := supply_bound $$ Hs Hc
  obtain ⟨r, hr⟩ := exists_add_of_le hcs
  unfold cc ccAuth
  imod AuthCredit.supply_decrease (E := ICC.cc) (γ := ICC.γcc)
    (spend_local_update (s := (s : CappedCredit B bad)) hc hr) $$ [$Hs $Hc] with H
  imodintro
  iexists r
  iframe %hr H

/-- When every valid budget cancels, any credit can be spent. -/
theorem supply_decrease_of_valid (hcancel : ∀ c ∉ bad, IsAddLeftRegular c) {s c : B} :
    ⊢ ●↯c s -∗ ↯c c -∗ |==> ∃ r, ⌜s = c + r⌝ ∗ ●↯c r := by
  iintro Hs Hc
  ihave %hc := valid $$ Hc
  iapply supply_decrease (hcancel c hc) $$ Hs Hc

/-- Growing the budget by `c` hands out a credit `c`, as long as the new budget is not bad. -/
theorem supply_increase {s c : B} (h : s + c ∉ bad) :
    ●↯c s ⊢ |==> (●↯c (s + c) ∗ ↯c c) := by
  unfold cc ccAuth
  iintro Hs
  iapply AuthCredit.supply_increase (E := ICC.cc) (γ := ICC.γcc) (s := (s : CappedCredit B bad))
    (s' := ((s + c : B) : CappedCredit B bad)) (c := (c : CappedCredit B bad))
    (alloc_local_update h) $$ Hs

/-- A credit splits off any smaller credit. -/
theorem difference [Sub B] [OrderedSub B] {a b : B} (h : b ≤ a) :
    ↯c a ⊢ ↯c b ∗ ↯c (a - b) := by
  simpa only [add_tsub_cancel_of_le h] using split (a := b) (b := a - b)

/-- Credits are timeless. -/
instance timeless_cc (c : B) : BI.Timeless (↯c c : IProp GF) := iOwn_timeless

/-- The authoritative budget is timeless. -/
instance timeless_ccAuth (s : B) : BI.Timeless (●↯c s : IProp GF) := iOwn_timeless

end CappedCredit

end Resources

/-- Allocating a fresh valid budget `b` yields both the authority and a credit `b`
(Rocq `gccredit_alloc`). -/
theorem cc_alloc {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
    {bad : Set B} [Fact (IsUpperSet bad)] [Fact ((0 : B) ∉ bad)] {GF : BundledGFunctors}
    [ICC : CappedCreditPreGS B bad GF] {b : B} (hb : b ∉ bad) :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      ccAuth (ICC := { toCappedCreditPreGS := ICC, γcc := γ }) b ∗
      cc (ICC := { toCappedCreditPreGS := ICC, γcc := γ }) b := by
  unfold cc ccAuth
  imod AuthCredit.alloc (E := ICC.cc) (b := (b : CappedCredit B bad)) hb with ⟨%γ, H⟩
  imodintro
  iexists γ
  iexact H
