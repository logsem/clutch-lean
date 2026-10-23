module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Basic
public import Iris.ProofMode
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Iris.Instances.IProp.Instance
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Basic.ENNReal.Basic
import Metrology.Iris.LocalBI

/-! # Authoritative credit ghost state

The `●`/`◯` rules over any discrete unital camera, shared by budget credits and capped credits. -/

@[expose] public section

open Iris

namespace AuthCredit

variable {A : Type} [UCMRA A] {GF : BundledGFunctors} {E : ElemG GF (constOF (Auth A))}
  {γ : GName}

local bi IProp GF

/-- A fragment of a sum splits into the two fragments. -/
theorem frag_split {a b : A} :
    iOwn (E := E) γ (◯ (a • b)) ⊢ iOwn (E := E) γ (◯ a) ∗ iOwn (E := E) γ (◯ b) := by
  rw [Auth.frag_op]
  exact iOwn_op.1

/-- Two fragments combine into the fragment of their sum. -/
theorem frag_combine {a b : A} :
    iOwn (E := E) γ (◯ a) ∗ iOwn (E := E) γ (◯ b) ⊢ iOwn (E := E) γ (◯ (a • b)) := by
  rw [Auth.frag_op]
  exact iOwn_op.2

/-- The unit fragment is free. -/
theorem frag_unit : ⊢ |==> iOwn (E := E) γ (◯ (UCMRA.unit : A)) :=
  iOwn_unit (ε := UCMRA.unit)

/-- A fragment is included in the authority. -/
theorem supply_bound [CMRA.Discrete A] {s c : A} :
    ⊢ iOwn (E := E) γ (● s) -∗ iOwn (E := E) γ (◯ c) -∗ ⌜c ≼ s⌝ := by
  iintro Hs Hc
  icombine Hs Hc gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  exact (Auth.auth_both_valid_discrete.mp hv).1

/-- A local update that removes a fragment from the authority. -/
theorem supply_decrease {s c r : A} (h : (s, c) ~l~> (r, UCMRA.unit)) :
    iOwn (E := E) γ (● s) ∗ iOwn (E := E) γ (◯ c) ⊢ |==> iOwn (E := E) γ (● r) :=
  iOwn_update_op (Auth.auth_update_dealloc h)

/-- A local update that hands out a fragment from the authority. -/
theorem supply_increase {s s' c : A} (h : (s, UCMRA.unit) ~l~> (s', c)) :
    iOwn (E := E) γ (● s) ⊢ |==> (iOwn (E := E) γ (● s') ∗ iOwn (E := E) γ (◯ c)) := by
  have hup : (● s : Auth A) ~~> (● s' : Auth A) • ◯ c := Auth.auth_update_alloc h
  iintro Hs
  imod (iOwn_update hup) $$ Hs with H
  imodintro
  iapply iOwn_op $$ H

/-- Allocate an authority and a matching fragment for a valid element. -/
theorem alloc {b : A} (hb : ✓ b) :
    ⊢@{IProp GF} |==> ∃ γ : GName, iOwn (E := E) γ (● b) ∗ iOwn (E := E) γ (◯ b) := by
  imod (iOwn_alloc (E := E) ((● b) • (◯ b)) (Auth.auth_both_valid_2 hb .rfl)) with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply iOwn_op $$ H

end AuthCredit
