module

public import Metrology.Micrometer.RelTactics
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Smoke tests for the `rel_*` tactics -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS
open scoped AppGS

namespace ProbLang
namespace RelTacticsTest

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] {hlc : HasLC}
  {GF : BundledGFunctors} [MicrometerRGS rT hlc GF] {B : Type} [AddCommMonoid B]
  [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B] {L : GradedLifting.{0} B}
  [BudgetCreditGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]
  [L.HasBind]
local bi IProp GF

/-! ## Pure steps -/

/-- Pure steps on both sides, inside a non-empty context on the right. -/
example (n : Int) :
    ⊢ REL[L] (pl((fun x, x + #1) #n) : Exp rT) <<
      pl(fst((#(n + 1), #0))) : lrel_int := by
  rel_pure_l
  rel_pures_l
  rel_pure_r
  rel_values

/-- `rel_pure_l e` steps at the focus `e`, leaving the outer redex. -/
example (n : Int) :
    ⊢ REL[L] (pl(#n + (#1 + #2)) : Exp rT) << pl(#(n + 3)) :
      lrel_int := by
  rel_pure_l pl(#1 + #2)
  rel_pure_l
  rel_values

/-! ## Heap -/

/-- Allocation, load and store on both sides, under a context. -/
example :
    ⊢ REL[L] (pl(let r := alloc(#1); r ← #2; !r + #0) : Exp rT) <<
      pl(let r := alloc(#5); r ← #2; !r) : lrel_int := by
  rel_alloc_l l as Hl
  rel_store_l
  rel_load_l
  rel_alloc_r l' as Hl'
  rel_store_r
  rel_load_r
  rel_pures
  rel_values

/-! ## Sampling and couplings -/

/-- Coupling two unlabelled draws inside contexts, along the identity. -/
example :
    ⊢ REL[L] (pl(rand(#4, #()) + #0) : Exp rT) << pl(fst((rand(#4, #()), #0))) :
      lrel_int := by
  rel_couple_UU
  iintro %n %_
  rel_pures
  rel_values
  imodintro
  iunfold lrel_int
  iexists n
  ipureintro
  simp

/-- One-sided draws. -/
example :
    ⊢ REL[L] (pl(rand(#4, #()); #()) : Exp rT) << pl(rand(#3, #()); #()) :
      lrel_unit := by
  rel_rand_r
  iintro %m %_
  rel_rand_l
  iintro %n %_
  rel_pures
  rel_values

/-- Tapes: allocate, couple a labelled draw with an unlabelled one, then draw from a tape. -/
example :
    ⊢ REL[L] (pl(let α := tape(#4); rand(#4, α)) : Exp rT) <<
      pl(let α := tape(#4); rand(#4, #())) : lrel_int := by
  rel_alloctape_l α as Hα
  rel_alloctape_r α' as Hα'
  rel_pures
  rel_couple_TU α
  iframe Hα
  iintro %n Hα %_
  rel_values

/-- `rel_rand_l` draws from a presampled tape in the context. -/
example (α : Loc) :
    ⊢ appNatTape α 4 [2] -∗
      REL[L] (pl(rand(#4, #lbl α) + #0) : Exp rT) << pl(#2) : lrel_int := by
  iintro Hα
  rel_rand_l
  iintro %_
  rel_pures
  rel_values

/-! ## Contexts and binds -/

/-- `rel_bind_l` refocuses on a subprogram; `rel_apply_l` applies a user rule in context. -/
example (H : ∀ (K : Ectx rT) t, (REL[L] K.fill pl(#7) << t : lrel_int) ⊢
      REL[L] K.fill pl(#3 + #4) << t : lrel_int) :
    ⊢ REL[L] (pl(fst((#3 + #4, #0))) : Exp rT) << pl(#7) : lrel_int := by
  rel_bind_l pl(#3 + #4)
  rel_bind_r pl(#7)
  rel_apply_l H
  rel_pures
  rel_values

/-- `rel_bind` splits off a sub-refinement. -/
example (Hsub : ⊢ REL[L] (pl(#1 + #1) : Exp rT) << pl(#0 + #2) : lrel_int) :
    ⊢ REL[L] (pl(fst((#1 + #1, #0))) : Exp rT) << pl(fst((#0 + #2, #5))) :
      lrel_int := by
  rel_bind pl(#1 + #1) pl(#0 + #2)
  isplitr
  · iapply Hsub
  iintro %v %v' Hv
  rel_pures
  rel_values
  imodintro
  iexact Hv

/-- Context search under an abstract context tail. -/
example (K K' : Ectx rT) (H : ∀ e e', ⊢ REL[L] K.fill e << K'.fill e' : lrel_int) :
    ⊢ REL[L] K.fill pl(#1 + #1) << K'.fill pl(fst((#2, #0))) : lrel_int := by
  rel_pures
  iapply H

/-- A closed program spliced under binders. -/
def two : Exp rT := pl(#1 + #1)

/-- Stepping past `let x := &two` leaves no `openRec`/`closeRec` around the second `two`. -/
example :
    ⊢ REL[L] (pl(let x := &two; let y := &two; x + y) : Exp rT) << pl(#4) :
      lrel_int := by
  rel_pure_l pl(&two)
  rel_pure_l
  rel_pures_l
  rel_values

/-! ## Tape couplings -/

/-- An unlabelled draw coupled with a spec tape by `rel_couple_UT`. -/
example :
    ⊢ REL[L] (pl(rand(#4, #())) : Exp rT) <<
      pl(let α := tape(#4); rand(#4, α)) : lrel_int := by
  rel_alloctape_r α as Hα
  rel_pures_r
  rel_couple_UT α
  iframe Hα
  iintro %n Hα %_
  rel_values

/-- Two tapes, one on each side, coupled by `rel_couple_TT`. -/
example :
    ⊢ REL[L] (pl(let α := tape(#4); rand(#4, α)) : Exp rT) <<
      pl(let α := tape(#4); rand(#4, α)) : lrel_int := by
  rel_alloctape_l α as Hα
  rel_alloctape_r α' as Hα'
  rel_pures
  rel_couple_TT α α'
  iframe Hα Hα'
  iintro %n Hα Hα' %_
  rel_values

/-! ## Atomic rules, user rules and values -/

/-- The `_atomic` forms leave the rule's premise. -/
example (l : Loc) :
    ⊢ (l ↦ (.int 3 : Val rT)) -∗
      REL[L] (pl(!#loc l + #0) : Exp rT) << pl(#3) : lrel_int := by
  iintro Hl
  rel_load_l_atomic
  iexists _
  iframe Hl
  iintro Hl
  rel_pures
  rel_values

/-- `rel_apply_r` applies a user rule at a redex of the right program. -/
example (H : ∀ (K : Ectx rT) e, (REL[L] e << K.fill pl(#7) : lrel_int) ⊢
      REL[L] e << K.fill pl(#3 + #4) : lrel_int) :
    ⊢ REL[L] (pl(#7) : Exp rT) << pl(fst((#3 + #4, #0))) : lrel_int := by
  rel_apply_r H
  rel_pures
  rel_values

/-- `rel_arrow_val` reduces a refinement of closures to their applications. -/
example :
    ⊢ REL[L] (pl(fun x, x) : Exp rT) << pl(fun y, (fun z, z) y) :
      lrel_arr L lrel_int lrel_int := by
  rel_arrow_val
  iintro %v %v' Hv
  iunfold lrel_int at Hv
  icases Hv with ⟨%n, %rfl, %rfl⟩
  rel_pures
  rel_values

/-- Integer comparisons step from literals and from hypotheses in the context. -/
example (n : Int) (h : n ≠ 0) :
    ⊢ REL[L] (pl(if #n = #0 then #1 else #2) : Exp rT) <<
      pl(if #0 = #0 then #2 else #1) : lrel_int := by
  rel_pures
  rel_values

/-- Pairs of literals close by `rel_values`. -/
example :
    ⊢ REL[L] (pl((#1, #true)) : Exp rT) << pl((#1, #true)) :
      lrel_prod lrel_int lrel_bool := by
  rel_values

end RelTacticsTest
end ProbLang
