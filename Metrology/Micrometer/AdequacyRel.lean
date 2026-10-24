module

public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.Adequacy
public import Iris.Algebra.Auth
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.FUpd
import Metrology.Iris.LocalBI

/-! # Relational adequacy

A closed refinement relates the two limit outputs at budget `b` and bounds their divergence. -/

@[expose] public section

namespace ProbLang

open Iris hiding wp_mono
open Iris.BI Iris.ProofMode Auth
open MicrometerWpGS
open GradedLifting
open MeasureTheory.Measure (dirac map_dirac')
open Ectx (fill)
open Exp (ofVal)

/-! ## Ghost state that adequacy allocates -/

/-- A functor list `GF` with slots for every camera that refinement adequacy allocates, including a
budget camera over `B`. -/
class RefinesPreGS (rT : outParam Type) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (B : Type) [AddCommMonoid B] (GF : BundledGFunctors) where
  /-- The program heap and tape ghost state. -/
  [app : AppPreGS rT GF]
  /-- The spec thread, heap and tape ghost state. -/
  [spec : SpecPreGS rT GF]
  /-- The budget credit camera over `B`. -/
  [bc : BudgetCreditPreGS B GF]
  /-- The invariant and credit ghost state. -/
  [inv : InvGpreS GF]
  /-- The non-atomic invariant ghost state. -/
  [nainv : NaInvG GF]

namespace RefinesPreGS

attribute [reducible, instance] app spec bc inv nainv

end RefinesPreGS

section Closed

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT] {GF : BundledGFunctors}
local bi IProp GF

/-! ## Spec ownership in the empty context -/

section Spec

variable [SpecGS rT GF]

/-- Spec ownership of `e` is that of `e` in the empty context. -/
theorem spec_eq_fill_nil (e : Exp rT) : (iprop(⤇ e) : IProp GF) = iprop(⤇ fill [] e) :=
  rfl

variable (v : Val rT)

/-- Spec ownership of a value in the empty context is that of the value. -/
theorem spec_fill_nil_eq_ofVal :
    (iprop(⤇ fill [] v.1) : IProp GF) = iprop(⤇ ofVal v) :=
  rfl

/-- Spec ownership of a value in the empty context gives the postcondition of `wp_adequacy`. -/
theorem spec_fill_nil_exists : ⤇ fill [] v.1 ⊢ ∃ v', ⤇ ofVal v' ∗ ⌜v = v'⌝ := by
  rw [spec_fill_nil_eq_ofVal]
  iintro Hj
  iexists v
  iframe Hj
  ipureintro
  rfl

end Spec

/-! ## Adequacy for closed refinements -/

section Coupling

variable {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  [Nontrivial B] {L : GradedLifting.{0} B} [L.IsLawful] [L.IsZeroLeft] [L.IsLeftContinuous]
  [L.IsBudgetClosed] [RefinesPreGS rT B GF]
  (A : ∀ (_ : MicrometerRGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF), lrel rT GF)

variable (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT)

/-- A refinement from `↯b b`, proved for every ghost-state instance, gives a lifting at budget `b`
of the two limit outputs (clutch-dp's `adequacy_rel.v`). -/
theorem approximates_coupling (b : B) (HA : ∀ IR IBC v v', ⊢ (A IR IBC).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS B GF),
      ⊢ ↯b b -∗ refines L ⊤ e e' (A IR IBC)) :
    L.Rel b (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) := by
  refine wp_adequacy_budget_lim (GF := GF) e e' σ σ' b φ fun IGS IBC b' hb' => ?_
  -- Adequacy gives a credit b' > b. Split it as b + r: the user's proof takes ↯b b, and r > 0
  -- becomes the credit threaded through refines.
  obtain ⟨r, rfl⟩ := le_iff_exists_add.1 hb'.le
  have hr : (0 : B) < r := pos_iff_ne_zero.2 fun h => by simp [h] at hb'
  iintro He' Herr
  -- Allocate a non-atomic invariant pool and build the ghost instance `Hlog` is applied at.
  imod NonAtomicInvariant.alloc with ⟨%γ, Htok⟩
  set IR : MicrometerRGS rT .hasNoLC GF := { micrometerGS := IGS, naInvG := _, nais := γ }
  icases BudgetCredit.split $$ Herr with ⟨Hb, Hr⟩
  ihave HlogR := Hlog IR IBC $$ Hb
  -- Run the refinement with the spec thread in the empty context `[]` and threaded credit `r`.
  iunfold refines at HlogR
  rw [spec_eq_fill_nil e']
  ispecialize HlogR $$ %([] : Ectx rT) %r He' Htok Hr %hr
  -- Postcondition weakening: drop the token and leftover credit, and get `φ` from `HA`.
  iapply wp_mono $$ HlogR
  intro v
  iintro ⟨%v', %_, Hspec, -, -, -, HAv⟩
  iexists v'
  rw [← spec_fill_nil_eq_ofVal v']
  iframe Hspec
  iapply HA IR IBC v v' $$ HAv

/-- The lifting at budget `0` of `approximates_coupling`, with no budget credits. -/
theorem refines_coupling (HA : ∀ IR IBC v v', ⊢ (A IR IBC).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS B GF),
      ⊢ refines L ⊤ e e' (A IR IBC)) :
    L.Rel 0 (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  approximates_coupling A φ e e' σ σ' 0 HA fun IR IBC => by
    iintro -
    iapply Hlog IR IBC

/-- A refinement at equal results from `↯b b` bounds the output divergence by `b`
(clutch-dp's `adequacy_rel.v`). -/
theorem approximates_div {D : GradedDivergence.{0} B} [L.IsSound D] (b : B)
    (HA : ∀ IR IBC v v', ⊢ (A IR IBC).car v v' -∗ ⌜v = v'⌝)
    (Hlog : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS B GF),
      ⊢ ↯b b -∗ refines L ⊤ e e' (A IR IBC)) :
    D b (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  IsSound.sound ((approximates_coupling A (· = ·) e e' σ σ' b HA Hlog).mono le_rfl
    adequacyRel_eq_subset)

end Coupling

/-! ## Relations that relate only equal values

The side condition of `approximates_div` and of the examples' adequacy. -/

section EqRelations

variable {hlc : HasLC}

/-- `lrel_int` relates only equal values. -/
theorem lrel_int_car_eq [MicrometerRGS rT hlc GF] (v v' : Val rT) :
    ⊢ lrel_int.car v v' -∗ ⌜v = v'⌝ := by
  unfold lrel_int
  iintro ⟨%n, %⟨rfl, rfl⟩⟩
  ipureintro
  rfl

/-- `lrel_bool` relates only equal values. -/
theorem lrel_bool_car_eq [MicrometerRGS rT hlc GF] (v v' : Val rT) :
    ⊢ lrel_bool.car v v' -∗ ⌜v = v'⌝ := by
  unfold lrel_bool
  iintro ⟨%b, %⟨rfl, rfl⟩⟩
  ipureintro
  rfl

/-- A product of relations between equal values relates only equal values. -/
theorem lrel_prod_car_eq [MicrometerRGS rT hlc GF] {A A' : lrel rT GF}
    (hA : ∀ v v', ⊢ A.car v v' -∗ ⌜v = v'⌝)
    (hA' : ∀ v v', ⊢ A'.car v v' -∗ ⌜v = v'⌝) (v v' : Val rT) :
    ⊢ (lrel_prod A A').car v v' -∗ ⌜v = v'⌝ := by
  unfold lrel_prod
  iintro ⟨%a, %a', %b, %b', %h, %h', Ha, Hb⟩
  ihave %rfl := hA a a' $$ Ha
  ihave %rfl := hA' b b' $$ Hb
  ipureintro
  exact Val.ext (h.trans h'.symm)

end EqRelations

/-! ## Support for the examples -/

/-- A value runs to itself. -/
theorem limExecV_of_isVal {e : Exp rT} (σ : State rT) (hv : IsVal e) :
    limExecV ⟨e, σ⟩ = dirac e := by
  rw [limExecV, limExec_of_isVal hv, asExpr, map_dirac' Cfg.measurable_expr]

end Closed

/-! ## A concrete functor list -/

section MicrometerFunctor

variable (rT : Type) [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable (B : Type) [AddCommMonoid B]

/-- A concrete `RefinesPreGS` functor list, with the budget camera over `B` in slot `7`. -/
noncomputable def MicrometerFunctor : BundledGFunctors := fun
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset)⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3 => ⟨AuthURF (constOF Credit)⟩
  | 4 => ⟨constOF (SpecHeap rT)⟩
  | 5 => ⟨constOF SpecTapes⟩
  | 6 => ⟨constOF (SpecProg rT)⟩
  | 7 => ⟨constOF (Auth (BudgetCredit B))⟩
  | 8 => ⟨NaInvF⟩
  | _ => ⟨constOF Unit⟩

/-! ### `RefinesPreGS` instances for `MicrometerFunctor` -/

/-- The invariant and credit ghost state sit in slots `0` to `3`. -/
instance : InvGpreS (MicrometerFunctor rT B) where
  toWsatGpreS := { inv := ⟨0, rfl⟩, enabled := ⟨1, rfl⟩, disabled := ⟨2, rfl⟩ }
  toLcGpreS := { lc_elem := ⟨3, rfl⟩ }

-- The program and spec heaps (and tapes) use the same camera, so they share slots 4 and 5;
-- separate ghost names keep them apart.
/-- The program heap and tapes sit in slots `4` and `5`. -/
instance : AppPreGS rT (MicrometerFunctor rT B) where
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

/-- The spec thread, heap and tapes sit in slots `6`, `4` and `5`. -/
instance : SpecPreGS rT (MicrometerFunctor rT B) where
  prog := ⟨6, rfl⟩
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

/-- The budget camera sits in slot `7`. -/
instance : BudgetCreditPreGS B (MicrometerFunctor rT B) where
  bc := ⟨7, rfl⟩

/-- The non-atomic invariant ghost state sits in slot `8`. -/
instance : NaInvG (MicrometerFunctor rT B) where
  inv := ⟨8, rfl⟩

/-- `MicrometerFunctor` carries every camera that refinement adequacy allocates. -/
instance : RefinesPreGS rT B (MicrometerFunctor rT B) where

end MicrometerFunctor

end ProbLang
