module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Basic
public import Iris.ProofMode
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Iris.Instances.IProp.Instance
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Basic.ENNReal.Basic
import Metrology.Iris.ErrorCredits
public import Metrology.Iris.AuthCredit
import Metrology.Iris.LocalBI

/-!
# Budget credits

The credit camera Micrometer's wp uses: authority `●↯b s` in the state interpretation, fragments
`↯b c` held by the user (Rocq `gconeUR`). Main results: `split`/`combine`, `supply_decrease`,
`supply_increase`, `bc_alloc`.
-/

@[expose] public section

open Iris

/-! ## The camera -/

/-- Budgets as a camera: the operation is `+`, with unit `0` and no validity bound. -/
def BudgetCredit (B : Type*) : Type _ := B

namespace BudgetCredit

variable {B : Type*} [AddCommMonoid B]

instance instAddCommMonoid : AddCommMonoid (BudgetCredit B) := inferInstanceAs (AddCommMonoid B)
instance instCOFE : COFE (BudgetCredit B) := COFE.ofDiscrete _
instance instDiscrete : OFE.Discrete (BudgetCredit B) := ⟨id⟩
instance instCMRA : CMRA (BudgetCredit B) := CommMonoidLike.instCMRA
instance instUCMRA : UCMRA (BudgetCredit B) := CommMonoidLike.instUCMRA
instance instCMRADiscrete : CMRA.Discrete (BudgetCredit B) := CommMonoidLike.instDiscrete

instance instLE [LE B] : LE (BudgetCredit B) := inferInstanceAs (LE B)
instance instCanonicallyOrderedAdd [LE B] [CanonicallyOrderedAdd B] :
    CanonicallyOrderedAdd (BudgetCredit B) :=
  inferInstanceAs (CanonicallyOrderedAdd B)

variable {s c r t : BudgetCredit B}

/-- Camera inclusion in a budget is the canonical order. -/
theorem included_iff [LE B] [CanonicallyOrderedAdd B] : c ≼ s ↔ c ≤ s :=
  le_iff_exists_add.symm

/-- Spending a cancelable `c` out of `s = c + r` leaves `r` (Rocq `gcone_spend_local_update`). -/
theorem spend_local_update (hc : IsAddLeftRegular c) (h : s = c + r) : (s, c) ~l~> (r, 0) :=
  discrete_unital_triv_local_update (fun _ ↦ trivial) fun hz ↦
    (hc (h.symm.trans hz)).trans (zero_add _).symm

/-- Spending `c` out of `s = c + t` cannot leave any `r ≠ t`, so the spend needs cancellation
(Rocq `gcone_spend_needs_cancel`). -/
theorem not_spend_local_update_of_ne (h : s = c + t) (hne : r ≠ t) : ¬(s, c) ~l~> (r, 0) :=
  fun hup ↦ hne <| ((local_update_unital_discrete ..).mp hup t trivial h).2.trans (zero_add t)

/-- Adding `c` to the budget hands out a fragment `c` (Rocq `gcone_alloc_local_update`). -/
theorem alloc_local_update : (s, 0) ~l~> (s + c, c) :=
  discrete_unital_triv_local_update (fun _ ↦ trivial) fun {z} hz ↦
    (congrArg (· + c) (hz.trans (zero_add z))).trans (add_comm z c)

end BudgetCredit

/-! ## Ghost state and the resources `●↯b`, `↯b` -/

/-- The ghost-state slot for an authoritative budget camera. -/
class BudgetCreditPreGS (B : Type) [AddCommMonoid B] (GF : BundledGFunctors) where
  bc : ElemG GF (constOF (Auth (BudgetCredit B)))

attribute [reducible, instance] BudgetCreditPreGS.bc

/-- A budget camera with its ghost name. -/
class BudgetCreditGS (B : Type) [AddCommMonoid B] (GF : BundledGFunctors)
    extends BudgetCreditPreGS B GF where
  γbc : GName

section Resources

variable {B : Type} [AddCommMonoid B] {GF : BundledGFunctors} [IBC : BudgetCreditGS B GF]

/-- The authoritative budget. -/
def bcAuth (s : B) : IProp GF := iOwn (E := IBC.bc) IBC.γbc (● (s : BudgetCredit B))

/-- A spendable budget credit. -/
def bc (c : B) : IProp GF := iOwn (E := IBC.bc) IBC.γbc (◯ (c : BudgetCredit B))

notation "↯b " c:50 => bc c
notation "●↯b " s:50 => bcAuth s

namespace BudgetCredit

local bi IProp GF

/-- Credits are timeless. -/
instance timeless_bc (c : B) : BI.Timeless (↯b c : IProp GF) := iOwn_timeless

/-- The authoritative budget is timeless. -/
instance timeless_bcAuth (s : B) : BI.Timeless (●↯b s : IProp GF) := iOwn_timeless

/-! ### Splitting and combining credits -/

/-- A credit splits into two credits. -/
theorem split {a b : B} : ↯b (a + b) ⊢ ↯b a ∗ ↯b b :=
  AuthCredit.frag_split

/-- Two credits combine into one. -/
theorem combine {a b : B} : ↯b a ∗ ↯b b ⊢ ↯b (a + b) :=
  AuthCredit.frag_combine

/-- Proof mode combines credits by adding them. -/
instance combineSepAs_bc {a b : B} :
    ProofMode.CombineSepAs (↯b a : IProp GF) (↯b b) (↯b (a + b)) where
  combine_sep_as := combine

/-- A credit can be weakened to a smaller one. -/
theorem weaken [LE B] [CanonicallyOrderedAdd B] {a b : B} (hb : b ≤ a) :
    ↯b a ⊢ ↯b b := by
  obtain ⟨c, rfl⟩ := exists_add_of_le hb
  exact split.trans BI.sep_elim_left

/-- The zero credit is free. -/
theorem zero : ⊢ |==> ↯b (0 : B) :=
  AuthCredit.frag_unit

/-! ### Authority and credits -/

/-- A credit never exceeds the authoritative budget. -/
theorem supply_bound [LE B] [CanonicallyOrderedAdd B] {s c : B} :
    ⊢ ●↯b s -∗ ↯b c -∗ ⌜c ≤ s⌝ := by
  unfold bc bcAuth
  iintro Hs Hc
  ihave %h := AuthCredit.supply_bound (E := IBC.bc) (γ := IBC.γbc) (s := (s : BudgetCredit B))
    (c := (c : BudgetCredit B)) $$ Hs Hc
  ipureintro
  exact included_iff.mp h

/-- Spending a cancelable credit `c` takes it out of the budget. -/
theorem supply_decrease [LE B] [CanonicallyOrderedAdd B] {s c : B}
    (hc : IsAddLeftRegular c) :
    ⊢ ●↯b s -∗ ↯b c -∗ |==> ∃ r, ⌜s = c + r⌝ ∗ ●↯b r := by
  iintro Hs Hc
  ihave %hcs := supply_bound $$ Hs Hc
  obtain ⟨r, hr⟩ := exists_add_of_le hcs
  unfold bc bcAuth
  imod AuthCredit.supply_decrease (E := IBC.bc) (γ := IBC.γbc) (spend_local_update hc hr)
    $$ [$Hs $Hc] with H
  imodintro
  iexists r
  iframe %hr H

/-- Growing the budget by `c` hands out a credit `c`. -/
theorem supply_increase {s c : B} : ⊢ ●↯b s -∗ |==> (●↯b (s + c) ∗ ↯b c) := by
  unfold bc bcAuth
  iintro Hs
  iapply AuthCredit.supply_increase (E := IBC.bc) (γ := IBC.γbc) (s := (s : BudgetCredit B))
    (s' := ((s + c : B) : BudgetCredit B)) (c := (c : BudgetCredit B)) alloc_local_update $$ Hs

/-- A credit splits off any smaller credit. -/
theorem difference [PartialOrder B] [CanonicallyOrderedAdd B] [Sub B] [OrderedSub B]
    {a b : B} (h : b ≤ a) :
    ↯b a ⊢ ↯b b ∗ ↯b (a - b) := by
  simpa only [add_tsub_cancel_of_le h] using split (a := b) (b := a - b)

/-- Amplify a slack credit `↯b (s ε)` until it covers `s 1`, with the caller supplying the exit
(Approxis `ec_ind_amp`). -/
theorem amplifying [Preorder B] [CanonicallyOrderedAdd B] {s : ENNReal →+o B} {ε : ENNReal}
    {k : NNReal} {P : IProp GF} (hε : 0 < ε) (hk : 1 < k) : iprop%
    □ (↯b (s 1) -∗ P) ⊢
      □ (∀ ε', ⌜0 < ε'⌝ -∗ □ (↯b (s ((k : ENNReal) * ε')) -∗ P) -∗ ↯b (s ε') -∗ P) -∗
      ↯b (s ε) -∗ P := by
  iintro #Hexit #Hamp Hε
  obtain ⟨n, hn⟩ := ENNReal.exists_pow_mul_ge_one hε hk
  iinduction n generalizing %ε %hε %hn Hε with
  | zero =>
    simp only [pow_zero, mul_one] at hn
    iapply Hexit $$ [Hε]
    iapply weaken (OrderHomClass.mono s hn) $$ Hε
  | succ n IH =>
    iapply Hamp $$ %_ %hε [] Hε
    iintro !> Hε
    iapply IH $$ %((k : ENNReal) * ε)
      %(ENNReal.mul_pos_iff.mpr ⟨ENNReal.coe_pos.mpr (pos_of_gt hk), pos_of_gt hε⟩)
      %(hn.trans (le_of_eq (by ring))) Hε

end BudgetCredit

end Resources

/-- Allocating a fresh budget `b` yields both the authority and a credit `b`. -/
theorem bc_alloc {B : Type} [AddCommMonoid B] {GF : BundledGFunctors}
    [IBC : BudgetCreditPreGS B GF] (b : B) :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      bcAuth (IBC := { toBudgetCreditPreGS := IBC, γbc := γ }) b ∗
      bc (IBC := { toBudgetCreditPreGS := IBC, γbc := γ }) b := by
  unfold bc bcAuth
  imod AuthCredit.alloc (E := IBC.bc) (b := (b : BudgetCredit B)) trivial with ⟨%γ, H⟩
  imodintro
  iexists γ
  iexact H
