module

public import Metrology.Micrometer.LRel
import Metrology.ProbLang.Syntax.Notation

/-! Properties of the semantic types and the monadic rules of the refinement judgement. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

/-- Values are inhabited by `()`. -/
instance inhabited_val : Inhabited (Val rT) := ⟨.unit⟩

/-! ### Semantic property lemmas -/

section SemtypesProperties
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

/-- If two `logN` invariants have bodies that cannot hold together, they cannot both be opened, so
their names are equal; `hp` turns that into `l1 = l2`. -/
theorem fupd_eq_of_inv_excl {E : CoPset} {P1 P2 : IProp GF} {p1 p2 : Loc × Loc}
    {l1 l2 : Loc} (HE : (↑logN : CoPset) ⊆ E) (hp : p1 = p2 → l1 = l2)
    (hfalse : ⊢ P1 -∗ P2 -∗ False) :
    ⊢ Iris.inv (logN.@ p1) P1 -∗ Iris.inv (logN.@ p2) P2 -∗ |={E}=> ⌜l1 = l2⌝ := by
  by_cases h : l1 = l2
  · iintro - - !> !%; exact h
  have hN_disj : logN.@ p1 ## logN.@ p2 := ndot_ne_disjoint _ (mt hp h)
  have h1 : (↑(logN.@ p1) : CoPset) ⊆ E := LawfulSet.subset_trans (nclose_subseteq _ _) HE
  have h2 : (↑(logN.@ p2) : CoPset) ⊆ E := LawfulSet.subset_trans (nclose_subseteq _ _) HE
  have h2diff : (↑(logN.@ p2) : CoPset) ⊆ E \ (↑(logN.@ p1) : CoPset) :=
    fun p hp => CoPset.in_diff.mpr ⟨h2 p hp, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
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

/-- Reference type is functional in the program-side location (Rocq `interp_ref_funct`). -/
theorem lrel_ref_funct {E : CoPset} (A : lrel rT GF) (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢ (lrel_ref A).car (.loc l) (.loc l1) -∗
        (lrel_ref A).car (.loc l) (.loc l2) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_ref
  iintro ⟨%l', %l1', %h1, %h2, Hinv1⟩ ⟨%l'', %l2', %h3, %h4, Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [Val.ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨%wa1, %ws1, Hl1L, -⟩ ⟨%wa2, %ws2, Hl2L, -⟩
    iapply appHeapFrag_valid_2 $$ Hl1L Hl2L) $$ Hinv1 Hinv2

/-- Reference type is injective on the program-side location (Rocq `interp_ref_inj`). -/
theorem lrel_ref_inj {E : CoPset} (A : lrel rT GF) (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢ (lrel_ref A).car (.loc l1) (.loc l) -∗
        (lrel_ref A).car (.loc l2) (.loc l) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_ref
  iintro ⟨%l1', %l', %h1, %h2, Hinv1⟩ ⟨%l2', %l'', %h3, %h4, Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [Val.ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨%wa1, %ws1, -, Hs1L, -⟩ ⟨%wa2, %ws2, -, Hs2L, -⟩
    iapply specHeapFrag_valid_2 $$ Hs1L Hs2L) $$ Hinv1 Hinv2

/-- Tape type is functional in the program-side location (Rocq `interp_tape_funct`). -/
theorem lrel_tape_funct {E : CoPset} (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢ (lrel_tape (rT := rT) (GF := GF)).car (.lbl l) (.lbl l1) -∗
        (lrel_tape (rT := rT) (GF := GF)).car (.lbl l) (.lbl l2) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_tape
  iintro ⟨%l', %l1', %z1, %h1, %h2, Hinv1⟩ ⟨%l'', %l2', %z2, %h3, %h4, Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [Val.ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨Hl1L, -⟩ ⟨Hl2L, -⟩
    iapply appTapesFrag_valid_2 $$ Hl1L Hl2L) $$ Hinv1 Hinv2

/-- Tape type is injective on the program-side location (Rocq `interp_tape_inj`). -/
theorem lrel_tape_inj {E : CoPset} (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢ (lrel_tape (rT := rT) (GF := GF)).car (.lbl l1) (.lbl l) -∗
        (lrel_tape (rT := rT) (GF := GF)).car (.lbl l2) (.lbl l) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_tape
  iintro ⟨%l1', %l', %z1, %h1, %h2, Hinv1⟩ ⟨%l2', %l'', %z2, %h3, %h4, Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [Val.ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨-, Hs1L⟩ ⟨-, Hs2L⟩
    iapply specTapesFrag_valid_2 $$ Hs1L Hs2L) $$ Hinv1 Hinv2

end SemtypesProperties

/-! ## Monadic layer -/

section Monadic
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

/-- A `⊤` update before `refines` can be absorbed. -/
theorem fupd_refines {E : CoPset} {e t : Exp rT} {A : lrel rT GF} :
    iprop(|={⊤}=> refines L E e t A) ⊢ refines L E e t A := by
  unfold refines
  iintro >H
  iexact H

/-- Sequence two refinements via evaluation-context framing. -/
theorem refines_bind [L.IsLawful] [L.IsTopAbsorbing] (K K' : Ectx rT) {E : CoPset}
    {A A' : lrel rT GF} {e e' : Exp rT} :
    ⊢ refines L E e e' A -∗
      (∀ v v', A v v' -∗ refines L ⊤ (K.fill v.1) (K'.fill v'.1) A') -∗
      refines L E (K.fill e) (K'.fill e') A' := by
  unfold refines
  iintro Hm Hf %K'' %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K'' K' e'] at Hj
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
  isimp only [← Ectx.fill_comp K'' K' v'.1] at Hj
  iapply Hf $$ %K'' %b' Hj Hna Herr Hpos

/-- Values refine at `A` when `naOwnP E` updates to `naOwnP ⊤` together with `A v1 v2`. -/
theorem refines_ret_na {E : CoPset} {e1 e2 : Exp rT} {v1 v2 : Val rT} {A : lrel rT GF}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) :
    iprop(naOwnP (rT := rT) E ={⊤}=∗ naOwnP (rT := rT) ⊤ ∗ A v1 v2)
      ⊢ refines L E e1 e2 A := by
  subst hv1 hv2
  unfold refines
  iintro HFA %K %b HK Hnais Herr Hpos
  iapply wp_value_fupd_of_toVal (e := v1.1) (Exp.toVal?_ofVal v1)
  imod HFA $$ Hnais with ⟨HF, HA⟩
  imodintro
  iexists v2, b
  iframe HK HF Herr Hpos HA

/-- Values refine at `A` when a `⊤` update gives the missing `naOwnP (⊤ \ E)` and `A v1 v2`. -/
theorem refines_ret_na_compl {E : CoPset} {e1 e2 : Exp rT} {v1 v2 : Val rT} {A : lrel rT GF}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) :
    iprop(|={⊤}=> naOwnP (rT := rT) ((⊤ : CoPset) \ E) ∗ A v1 v2)
      ⊢ refines L E e1 e2 A := by
  iintro HFA
  iapply refines_ret_na hv1 hv2
  iintro Hnais
  imod HFA with ⟨HF, HA⟩
  imodintro
  have hun := (Iris.NonAtomicInvariant.own_union (GF := GF)
    (p := MicrometerRGS.nais (rT := rT) GF) (E2 := (⊤ : CoPset) \ E)
    LawfulSet.disjoint_diff_right).mpr
  rw [LawfulSet.subset_union_diff (s₂ := (⊤ : CoPset)) (fun _ _ => CoPset.mem_full)] at hun
  iframe HA
  iapply hun
  iframe Hnais HF

/-- Two values refine each other at `A` when they are related at `A` after a `⊤` update. -/
theorem refines_ret {e1 e2 : Exp rT} {v1 v2 : Val rT} {A : lrel rT GF}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) :
    iprop(|={⊤}=> A v1 v2) ⊢ refines L (⊤ : CoPset) e1 e2 A := by
  iintro HA
  iapply refines_ret_na hv1 hv2
  iintro Hna
  imod HA
  imodintro
  iframe Hna HA

/-- `refines` eliminates `|={⊤}=>`. -/
instance elim_fupd_refines {io : InOut} (E : CoPset) (e t : Exp rT)
    (P : IProp GF) (A : lrel rT GF) :
    ElimModal True false io false (iprop(|={⊤}=> P)) P
      (refines L E e t A) (refines L E e t A) where
  elim_modal _ := calc
    _ ⊢ (|={⊤}=> P) ∗ (P -∗ refines L E e t A) := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ |={⊤}=> P ∗ (P -∗ refines L E e t A)   := fupd_frame_right
    _ ⊢ |={⊤}=> refines L E e t A              := BIFUpdate.mono wand_elim_right
    _ ⊢ refines L E e t A                      := fupd_refines

/-- `refines` eliminates `|==>`. -/
instance elim_bupd_refines {io : InOut} (E : CoPset) (e t : Exp rT)
    (P : IProp GF) (A : lrel rT GF) :
    ElimModal True false io false (iprop(|==> P)) P
      (refines L E e t A) (refines L E e t A) where
  elim_modal h :=
    (sep_mono_left (intuitionisticallyIf_mono BIUpdateFUpdate.fupd_of_bupd)).trans
      ((elim_fupd_refines (io := io) E e t P A).elim_modal h)

/-- `refines` is closed under `◇`. -/
instance is_except_0_refines (E : CoPset) (e t : Exp rT) (A : lrel rT GF) :
    IsExcept0 (refines L E e t A) where
  is_except0 := calc
    ◇ refines L E e t A ⊢ ◇ |={⊤}=> refines L E e t A := except0_mono fupd_intro
    _ ⊢ |={⊤}=> refines L E e t A := BIFUpdate.except0
    _ ⊢ refines L E e t A := fupd_refines

/-- Update the non-atomic mask from `E` to `F` before continuing the refinement at `F`. -/
theorem refines_na_update {E F : CoPset} {e1 e2 : Exp rT} {A : lrel rT GF} :
    iprop(naOwnP (rT := rT) E ={⊤}=∗ naOwnP (rT := rT) F ∗ refines L F e1 e2 A)
      ⊢ refines L E e1 e2 A := by
  unfold refines
  iintro Hupd %K %b Hj Hna Herr Hpos
  iapply MicrometerWpGS.fupd_wp
  imod Hupd $$ Hna with ⟨Hna, HR⟩
  imodintro
  iapply HR $$ %K %b Hj Hna Herr Hpos

/-- Allocate a non-atomic invariant `N` for `P` and continue the refinement. -/
theorem refines_na_alloc {P : IProp GF} (N : Namespace) {E : CoPset} {e1 e2 : Exp rT}
    {A : lrel rT GF} :
    iprop% (▷ P) ∗ (naInvP (rT := rT) N P -∗ refines L E e1 e2 A)
      ⊢ refines L E e1 e2 A := by
  iintro ⟨HP, Hcont⟩
  iapply fupd_refines
  imod Iris.NonAtomicInvariant.inv_alloc $$ [$HP] with Hinv
  imodintro
  iapply Hcont $$ Hinv

/-- Open the non-atomic invariant `N` around a refinement, which then runs at mask `E \ N` with the
closing update. -/
theorem refines_na_inv {P : IProp GF} {E : CoPset} {N : Namespace} {e1 e2 : Exp rT} {A : lrel rT GF}
    (HNE : (↑N : CoPset) ⊆ E) :
    iprop% naInvP (rT := rT) N P ∗
        ((▷ P) ∗ naCloseP (rT := rT) P N E -∗ refines L (E \ ↑N) e1 e2 A)
      ⊢ refines L E e1 e2 A := by
  iintro ⟨Hinv, IH⟩
  iapply refines_na_update
  iintro Hnais
  imod Iris.NonAtomicInvariant.inv_acc CoPset.subseteq_top HNE $$ Hinv Hnais
    with ⟨HP, Hnais, Hclose⟩
  imodintro
  iframe Hnais
  iapply IH $$ [$HP $Hclose]

/-- Close the non-atomic invariant `N` by returning `▷ P`, continuing at mask `E`. -/
theorem refines_na_close {P : IProp GF} {E : CoPset} {N : Namespace} {e1 e2 : Exp rT}
    {A : lrel rT GF} :
    iprop% (▷ P) ∗ naCloseP (rT := rT) P N E ∗ refines L E e1 e2 A
      ⊢ refines L (E \ ↑N) e1 e2 A := by
  iintro ⟨HP, Hclose, IH⟩
  iapply refines_na_update
  iintro HownFN
  imod Hclose $$ [$HP $HownFN] with HownF
  imodintro
  iframe

end Monadic

end ProbLang
