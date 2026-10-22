module

public meta import Metrology.Meta.Discrete
public import Iris
public import Iris.Instances.Lib.FUpd

@[expose] public section

/-! # Pulling `∀` into a fupd of plain propositions

`BIFUpdatePlainly` only gives `fupd_plainly_sForall_2`; the strong form below is not derivable
from the class, but holds in the `IProp GF` model because `■ P` means `P` at the unit resource.
-/
open Iris Iris.Std Iris.BI Iris.ProofMode

namespace ProbLang
namespace TotalEris

variable {GF : BundledGFunctors} [InvGS_gen .hasNoLC GF] {E : CoPset} {α : Type _}

/-- A family of fupds of plain propositions combines into one fupd of the conjunction. -/
theorem iProp_fupd_plainly_forall_2_no_lc
    {Φ : α → IProp GF} [∀ x, Plain (Φ x)] :
    (∀ x, iprop(|={E}=> Φ x)) ⊢ iprop(|={E}=> ∀ x, Φ x) := by
  simp only [fupd, uPred_fupd, le_upd_unfold_no_le.to_eq]
  iintro H ⟨Hwsat, HE⟩
  -- `#` duplicates the spatial context; sound because the asserted proposition is plain.
  ihave #>HP : ◇ ■ (∀ x, Φ x) $$ [H Hwsat HE]
  · iapply (except0_forall.mpr.trans (except0_mono plainly_forall.mpr) :
      iprop((∀ x, ◇ ■ Φ x)) ⊢ iprop(◇ ■ ∀ x, Φ x))
    iintro %x
    imod H $$ %x [$Hwsat $HE] with ⟨-, -, HΦx⟩
    iapply (except0_mono Plain.plain) $$ HΦx
  imodintro
  iframe Hwsat HE
  iapply except0_intro
  iapply plainly_elim $$ HP

/-- If each `x` with `R x` gives `|={E}=> ⌜P x⌝`, then `|={E}=> ⌜∀ x, R x → P x⌝`. -/
theorem iProp_fupd_plainly_forall_pure_impl_no_lc
    {R : α → Prop} {P : α → Prop} :
    (∀ x, iprop(⌜R x⌝ -∗ |={E}=> ⌜P x⌝)) ⊢@{IProp GF} iprop(|={E}=> ⌜∀ x, R x → P x⌝) := by
  iintro H
  ihave H' : iprop(∀ x, |={E}=> ⌜R x → P x⌝) $$ [H]
  · iintro %x
    by_cases hR : R x
    · imod H $$ %x [//] with %hP
      imodintro
      ipureintro
      exact fun _ => hP
    · imodintro
      ipureintro
      exact (absurd · hR)
  imod iProp_fupd_plainly_forall_2_no_lc $$ H' with H
  imodintro
  iapply pure_forall.mpr $$ H

end TotalEris
end ProbLang
