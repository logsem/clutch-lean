module

public import Iris.BI.Updates
public import Iris.ProofMode

@[expose] public section

open Std Iris.Std Iris.BI Iris.ProofMode

namespace Iris

section StepFUpd

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

open Iris.BI.BIBase

theorem fupd_laterN_to_step_fupdN (E : CoPset) (n : Nat) {Q : PROP} : iprop%
    (|={E}=> ▷^[n+1] Q) ⊢ |={E}[E]▷=>^[n+1] Q :=
  (BIFUpdate.mono (step_fupdN_intro Std.LawfulSet.subset_refl)).trans BIFUpdate.trans

theorem step_fupd_except0 (E1 E2 : CoPset) {P : PROP} : iprop%
    (|={E1}[E2]▷=> ◇ P) ⊢ |={E1}[E2]▷=> P :=
  BIFUpdate.mono (later_mono fupd_except0)

theorem step_fupdN_except0 (E1 E2 : CoPset) {P : PROP} (n : Nat) : iprop%
    (|={E1}[E2]▷=>^[n+1] ◇ P) ⊢ |={E1}[E2]▷=>^[n+1] P :=
  calc _ ⊢ |={E1}[E2]▷=>^[n] |={E1}[E2]▷=> ◇ P := (step_fupdN_add (n := n) (m := 1)).mp
    _ ⊢ |={E1}[E2]▷=>^[n] |={E1}[E2]▷=> P := step_fupdN_mono (step_fupd_except0 E1 E2)
    _ ⊢ |={E1}[E2]▷=>^[n+1] P := (step_fupdN_add (n := n) (m := 1)).mpr

theorem fupd_pure_wand_intro [BIAffine PROP] {p : Prop} {P : PROP} : iprop%
    (⌜p⌝ -∗ |={∅}=> P) ⊢ |={∅}=> (⌜p⌝ -∗ P) := by
  iintro HwP
  by_cases hp : p
  · imod HwP $$ %hp with HfP
    iintro !> -
    iexact HfP
  · iintro !> %hp'
    exact absurd hp' hp

theorem step_fupdN_pure_wand_intro (E : CoPset) (n : Nat) {p q : Prop} : iprop%
    (⌜p⌝ -∗ |={E}[E]▷=>^[n] ⌜q⌝) ⊢@{PROP} |={E}[E]▷=>^[n] (⌜p⌝ -∗ ⌜q⌝) := by
  iintro H
  by_cases hp : p
  · ispecialize H $$ %hp
    iapply step_fupdN_mono (wand_intro sep_elim_left) $$ [$]
  · iapply step_fupdN_intro Std.LawfulSet.subset_refl
    iintro !> %hp'
    exact absurd hp' hp

end StepFUpd

section StepFUpdPlain

variable {PROP : Type _} [Sbi PROP] [BIFUpdate PROP] [BIFUpdateSbi PROP] [BIAffine PROP]

open Iris.BI.BIBase

theorem fupd_step_fupdN_plain_forall_1 (Φ : A → PROP) [∀ x, Plain (Φ x)] (n : Nat) : iprop%
    (∀ x, |={∅}=> |={∅}[∅]▷=>^[n] Φ x) ⊢ |={∅}=> |={∅}[∅]▷=>^[n] ∀ x, Φ x := by
  cases n with
  | zero => simp only [Nat.repeat]; exact (fupd_plain_forall Std.LawfulSet.subset_refl).mpr
  | succ n =>
    calc _ ⊢ ∀ x, |={∅}=> ▷^[n+1] ◇ Φ x :=
        forall_mono fun _ => (BIFUpdate.mono step_fupdN_plain).trans BIFUpdate.trans
      _ ⊢ |={∅}=> ∀ x, ▷^[n+1] ◇ Φ x := (fupd_plain_forall Std.LawfulSet.subset_refl).mpr
      _ ⊢ |={∅}=> ▷^[n+1] ∀ x, ◇ Φ x := BIFUpdate.mono (laterN_forall (n+1)).mpr
      _ ⊢ |={∅}=> ▷^[n+1] ◇ ∀ x, Φ x := BIFUpdate.mono (laterN_mono (n+1) except0_forall.mpr)
      _ ⊢ |={∅}[∅]▷=>^[n+1] ◇ ∀ x, Φ x := fupd_laterN_to_step_fupdN ∅ n
      _ ⊢ |={∅}[∅]▷=>^[n+1] ∀ x, Φ x := step_fupdN_except0 ∅ ∅ n
      _ ⊢ |={∅}=> |={∅}[∅]▷=>^[n+1] ∀ x, Φ x := fupd_intro

theorem fupd_step_fupdN_plain_forall_2 {A B : Type _} (Ψ : A → B → PROP)
    [∀ a b, Plain (Ψ a b)] (n : Nat) : iprop%
    (∀ a b, |={∅}=> |={∅}[∅]▷=>^[n] Ψ a b) ⊢ |={∅}=> |={∅}[∅]▷=>^[n] ∀ a b, Ψ a b :=
  (forall_mono fun a => fupd_step_fupdN_plain_forall_1 (Ψ a) n).trans
    (fupd_step_fupdN_plain_forall_1 _ n)

theorem fupd_step_fupdN_plain_forall_3 {A B C : Type _} (Ψ : A → B → C → PROP)
    [∀ a b c, Plain (Ψ a b c)] (n : Nat) : iprop%
    (∀ a b c, |={∅}=> |={∅}[∅]▷=>^[n] Ψ a b c) ⊢ |={∅}=> |={∅}[∅]▷=>^[n] ∀ a b c, Ψ a b c :=
  (forall_mono fun a => fupd_step_fupdN_plain_forall_2 (Ψ a) n).trans
    (fupd_step_fupdN_plain_forall_1 _ n)

theorem fupd_step_fupdN_plain_forall_4 {A B C D : Type _} (Ψ : A → B → C → D → PROP)
    [∀ a b c d, Plain (Ψ a b c d)] (n : Nat) : iprop%
    (∀ a b c d, |={∅}=> |={∅}[∅]▷=>^[n] Ψ a b c d) ⊢
    |={∅}=> |={∅}[∅]▷=>^[n] ∀ a b c d, Ψ a b c d :=
  (forall_mono fun a => fupd_step_fupdN_plain_forall_3 (Ψ a) n).trans
    (fupd_step_fupdN_plain_forall_1 _ n)

end StepFUpdPlain

end Iris
