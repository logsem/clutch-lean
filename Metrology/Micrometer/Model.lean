module

public import Metrology.Micrometer.LRel
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-! # Monadic rules for `refines`

The update, bind and return rules of the refinement judgement (main: `refines_bind`), its rules
for non-atomic invariants, and functionality/injectivity of the `ref` and `tape` relations. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting Iris.NonAtomicInvariant MicrometerRGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

/-- Values are inhabited by `()`. -/
instance inhabited_val : Inhabited (Val rT) := ⟨.unit⟩

section Monadic
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF] {E : CoPset} {A : lrel rT GF}
  {e1 e2 : Exp rT} {P : IProp GF}
local bi IProp GF
open BIFUpdate (mono except0)
open LawfulSet (disjoint_diff_right subset_union_diff)
open CoPset (mem_full subseteq_top)
open _root_.ProbLang.Ectx (fill_comp)

/-! ### Updates in front of `refines` -/

/-- A `⊤` update before `refines` can be absorbed. -/
theorem fupd_refines {e t : Exp rT} :
    (|={⊤}=> refines L E e t A) ⊢ refines L E e t A := by
  unfold refines
  iintro >H
  iexact H

/-- `refines` eliminates `|={⊤}=>`. -/
instance elim_fupd_refines {io : InOut} (E : CoPset) (e t : Exp rT) (P : _)
    (A : lrel rT GF) :
    ElimModal True false io false iprop(|={⊤}=> P) P
      (refines L E e t A) (refines L E e t A) where
  elim_modal _ := calc
    _ ⊢ (|={⊤}=> P) ∗ (P -∗ refines L E e t A) := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ |={⊤}=> P ∗ (P -∗ refines L E e t A)   := fupd_frame_right
    _ ⊢ |={⊤}=> refines L E e t A              := mono wand_elim_right
    _ ⊢ refines L E e t A                      := fupd_refines

/-- `refines` eliminates `|==>`. -/
instance elim_bupd_refines {io : InOut} (E : CoPset) (e t : Exp rT) (P : _)
    (A : lrel rT GF) :
    ElimModal True false io false iprop(|==> P) P
      (refines L E e t A) (refines L E e t A) where
  elim_modal h :=
    (sep_mono_left (intuitionisticallyIf_mono BIUpdateFUpdate.fupd_of_bupd)).trans
      ((elim_fupd_refines (io := io) E e t P A).elim_modal h)

/-- `refines` is closed under `◇`. -/
instance is_except_0_refines (E : CoPset) (e t : Exp rT) (A : lrel rT GF) :
    IsExcept0 (refines L E e t A) where
  is_except0 := calc
    ◇ refines L E e t A ⊢ ◇ |={⊤}=> refines L E e t A := except0_mono fupd_intro
    _ ⊢ |={⊤}=> refines L E e t A := except0
    _ ⊢ refines L E e t A := fupd_refines

/-! ### Bind and return -/

/-- Sequence two refinements via evaluation-context framing. -/
theorem refines_bind [L.IsLawful] [L.IsTopAbsorbing] (K K' : Ectx rT)
    {A' : lrel rT GF} {e e' : Exp rT} : iprop%
    ⊢ refines L E e e' A -∗
      (∀ v v', A v v' -∗ refines L ⊤ (K.fill v.1) (K'.fill v'.1) A') -∗
      refines L E (K.fill e) (K'.fill e') A' := by
  unfold refines
  iintro Hm Hf %K'' %b Hj Hna Herr Hpos
  isimp only [fill_comp K'' K' e'] at Hj
  ispecialize Hm $$ %(K''.comp K') %b Hj Hna Herr Hpos
  iapply MicrometerWpGS.wp_bind
  iapply MicrometerWpGS.wp_mono
  -- Take the `wp` premise first: it pins the intermediate postcondition to the one of `Hm`,
  -- with the continuation `Hf` framed alongside it.
  swap
  · iapply MicrometerWpGS.wp_frame_l
    iframe Hf
    iexact Hm
  intro v
  change _ ⊢ wp L ⊤ (K.fill v.1) _
  iintro ⟨Hf, %v', %b', Hj, Hna, Herr, Hpos, HA⟩
  ispecialize Hf $$ %v %v' HA
  isimp only [← fill_comp K'' K' v'.1] at Hj
  iapply Hf $$ %K'' %b' Hj Hna Herr Hpos

/-- Values refine at `A` when `naOwnP E` updates to `naOwnP ⊤` together with `A v1 v2`. -/
theorem refines_ret_na {v1 v2 : Val rT} (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) : iprop%
    (naOwnP (rT := rT) E ={⊤}=∗ naOwnP (rT := rT) ⊤ ∗ A v1 v2) ⊢ refines L E e1 e2 A := by
  subst hv1 hv2
  unfold refines
  iintro HFA %K %b HK Hnais Herr Hpos
  iapply wp_value_fupd_of_toVal (e := v1.1) (Exp.toVal?_ofVal v1)
  imod HFA $$ Hnais with ⟨HF, HA⟩
  imodintro
  iexists v2, b
  iframe HK HF Herr Hpos HA

/-- Two values refine each other at `A` when they are related at `A` after a `⊤` update. -/
theorem refines_ret {v1 v2 : Val rT}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) :
    (|={⊤}=> A v1 v2) ⊢ refines L ⊤ e1 e2 A := by
  iintro HA
  iapply refines_ret_na hv1 hv2
  iintro Hna
  imod HA
  imodintro
  iframe Hna HA

/-- Values refine at `A` when a `⊤` update gives the missing `naOwnP (⊤ \ E)` and `A v1 v2`. -/
theorem refines_ret_na_compl {v1 v2 : Val rT}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) : iprop%
    (|={⊤}=> naOwnP (rT := rT) (⊤ \ E) ∗ A v1 v2) ⊢ refines L E e1 e2 A := by
  iintro HFA
  iapply refines_ret_na hv1 hv2
  iintro Hnais
  imod HFA with ⟨HF, HA⟩
  imodintro
  -- `naOwnP E ∗ naOwnP (⊤ \ E) ⊢ naOwnP ⊤`, since `E ∪ (⊤ \ E) = ⊤`.
  have hun := (own_union (GF := GF) (p := nais rT GF) (E2 := ⊤ \ E)
    disjoint_diff_right).mpr
  rw [subset_union_diff (s₂ := (⊤ : CoPset)) (fun _ _ => mem_full)] at hun
  iframe HA
  iapply hun
  iframe Hnais HF

/-! ### Non-atomic invariants -/

/-- Update the non-atomic mask from `E` to `F` before continuing the refinement at `F`. -/
theorem refines_na_update {F : CoPset} : iprop%
    (naOwnP (rT := rT) E ={⊤}=∗ naOwnP (rT := rT) F ∗ refines L F e1 e2 A) ⊢
    refines L E e1 e2 A := by
  unfold refines
  iintro Hupd %K %b Hj Hna Herr Hpos
  iapply MicrometerWpGS.fupd_wp
  imod Hupd $$ Hna with ⟨Hna, HR⟩
  imodintro
  iapply HR $$ %K %b Hj Hna Herr Hpos

/-- Allocate a non-atomic invariant `N` for `P` and continue the refinement. -/
theorem refines_na_alloc (N : Namespace) : iprop%
    ▷ P ∗ (naInvP (rT := rT) N P -∗ refines L E e1 e2 A) ⊢ refines L E e1 e2 A := by
  iintro ⟨HP, Hcont⟩
  iapply fupd_refines
  imod NonAtomicInvariant.inv_alloc $$ [$HP] with Hinv
  imodintro
  iapply Hcont $$ Hinv

/-- Open the non-atomic invariant `N` around a refinement, which then runs at mask `E \ N` with the
closing update. -/
theorem refines_na_inv {N : Namespace}
    (HNE : ↑N ⊆ E) : iprop%
    naInvP (rT := rT) N P ∗ (▷ P ∗ naCloseP (rT := rT) P N E -∗ refines L (E \ ↑N) e1 e2 A) ⊢
    refines L E e1 e2 A := by
  iintro ⟨Hinv, IH⟩
  iapply refines_na_update
  iintro Hnais
  imod inv_acc subseteq_top HNE $$ Hinv Hnais
    with ⟨HP, Hnais, Hclose⟩
  imodintro
  iframe Hnais
  iapply IH $$ [$HP $Hclose]

/-- Close the non-atomic invariant `N` by returning `▷ P`, continuing at mask `E`. -/
theorem refines_na_close {N : Namespace} : iprop%
    ▷ P ∗ naCloseP (rT := rT) P N E ∗ refines L E e1 e2 A ⊢ refines L (E \ ↑N) e1 e2 A := by
  iintro ⟨HP, Hclose, IH⟩
  iapply refines_na_update
  iintro HownFN
  imod Hclose $$ [$HP $HownFN] with HownF
  imodintro
  iframe

end Monadic

/-! ## Reference and tape relations are functional and injective -/

section SemtypesProperties
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF] {E : CoPset}
local bi IProp GF
open LawfulSet (subset_trans)
open _root_.ProbLang.Val (ext_iff)

/-- If two `logN` invariants have bodies that cannot hold together, they cannot both be opened, so
their names are equal; `hp` turns that into `l1 = l2`. -/
theorem fupd_eq_of_inv_excl {P1 P2 : IProp GF} {p1 p2 : Loc × Loc}
    {l1 l2 : Loc} (HE : ↑logN ⊆ E) (hp : p1 = p2 → l1 = l2)
    (hfalse : ⊢ P1 -∗ P2 -∗ False) :
    ⊢ inv (logN.@ p1) P1 -∗ inv (logN.@ p2) P2 -∗ |={E}=> ⌜l1 = l2⌝ := by
  by_cases h : l1 = l2
  · iintro - - !> !%; exact h
  have hN_disj : logN.@ p1 ## logN.@ p2 := ndot_ne_disjoint _ (mt hp h)
  have h1 : ↑(logN.@ p1) ⊆ E := subset_trans (nclose_subseteq _ _) HE
  have h2 : ↑(logN.@ p2) ⊆ E := subset_trans (nclose_subseteq _ _) HE
  have h2diff : ↑(logN.@ p2) ⊆ E \ ↑(logN.@ p1) :=
    fun p hp => CoPset.in_diff.mpr ⟨h2 p hp, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
  -- Open both invariants (their names are disjoint), then the two bodies give `▷ False`.
  iintro Hinv1 Hinv2
  iinv Hinv1 with HP1
  iinv Hinv2 with HP2
  ihave Hfalse : iprop% ▷ False $$ [HP1 HP2]
  · inext
    iapply hfalse $$ HP1 HP2
  imod Hfalse with %hf
  exact hf.elim

/-- Related values of a reference relation are both locations. -/
theorem lrel_ref_shape (A : lrel rT GF) (v1 v2 : Val rT) :
    (lrel_ref A).car v1 v2 ⊢ ⌜∃ l1 l2 : Loc, v1 = .loc l1 ∧ v2 = .loc l2⌝ := by
  unfold lrel_ref
  iintro ⟨%l1, %l2, %h1, %h2, -⟩ !%
  exact ⟨l1, l2, h1, h2⟩

variable (A : lrel rT GF) (l l1 l2 : Loc) (HE : ↑logN ⊆ E)
include HE

/-- Reference type is functional in the program-side location (Rocq `interp_ref_funct`). -/
theorem lrel_ref_funct :
    ⊢ (lrel_ref A).car (.loc l) (.loc l1) -∗
        (lrel_ref A).car (.loc l) (.loc l2) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_ref
  iintro ⟨%l', %l1', %h1, %h2, Hinv1⟩ ⟨%l'', %l2', %h3, %h4, Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨%wa1, %ws1, Hl1L, -⟩ ⟨%wa2, %ws2, Hl2L, -⟩
    iapply appHeapFrag_valid_2 $$ Hl1L Hl2L) $$ Hinv1 Hinv2

/-- Reference type is injective on the program-side location (Rocq `interp_ref_inj`). -/
theorem lrel_ref_inj :
    ⊢ (lrel_ref A).car (.loc l1) (.loc l) -∗
        (lrel_ref A).car (.loc l2) (.loc l) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_ref
  iintro ⟨%l1', %l', %h1, %h2, Hinv1⟩ ⟨%l2', %l'', %h3, %h4, Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨%wa1, %ws1, -, Hs1L, -⟩ ⟨%wa2, %ws2, -, Hs2L, -⟩
    iapply specHeapFrag_valid_2 $$ Hs1L Hs2L) $$ Hinv1 Hinv2

/-- Tape type is functional in the program-side location (Rocq `interp_tape_funct`). -/
theorem lrel_tape_funct :
    ⊢ (lrel_tape : lrel rT GF).car (.lbl l) (.lbl l1) -∗
        (lrel_tape : lrel rT GF).car (.lbl l) (.lbl l2) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_tape
  iintro ⟨%l', %l1', %z1, %h1, %h2, Hinv1⟩ ⟨%l'', %l2', %z2, %h3, %h4, Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨Hl1L, -⟩ ⟨Hl2L, -⟩
    iapply appTapesFrag_valid_2 $$ Hl1L Hl2L) $$ Hinv1 Hinv2

/-- Tape type is injective on the program-side location (Rocq `interp_tape_inj`). -/
theorem lrel_tape_inj :
    ⊢ (lrel_tape : lrel rT GF).car (.lbl l1) (.lbl l) -∗
        (lrel_tape : lrel rT GF).car (.lbl l2) (.lbl l) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_tape
  iintro ⟨%l1', %l', %z1, %h1, %h2, Hinv1⟩ ⟨%l2', %l'', %z2, %h3, %h4, Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨-, Hs1L⟩ ⟨-, Hs2L⟩
    iapply specTapesFrag_valid_2 $$ Hs1L Hs2L) $$ Hinv1 Hinv2

end SemtypesProperties

end ProbLang
