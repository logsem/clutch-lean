module

public import Iris.BI.Updates
public import Iris.ProofMode

@[expose] public section

/-! # Step-update lemmas

Pure facts and plain universals under `|={E}[E]▷=>^[n]`. -/

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

/-- A pure fact holds under an update followed by `n` step-updates at the empty mask. -/
theorem fupd_step_fupdN_pure {p : Prop} (n : Nat) (h : p) : ⊢@{PROP} |={∅}=> |={∅}[∅]▷=>^[n] ⌜p⌝ :=
  calc (emp : PROP) ⊢ ⌜p⌝ := pure_intro h
    _ ⊢ ▷^[n] ⌜p⌝ := laterN_intro n
    _ ⊢ |={∅}[∅]▷=>^[n] ⌜p⌝ := step_fupdN_intro Std.LawfulSet.subset_refl
    _ ⊢ |={∅}=> |={∅}[∅]▷=>^[n] ⌜p⌝ := fupd_intro

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

/-- Pure facts that follow from a guard, for every triple, hold after `n` step-updates. -/
theorem step_fupdN_pure_imp_forall₃ {A B C : Type _} {G q : A → B → C → Prop} {n : Nat} : iprop%
    (∀ a b c, ⌜G a b c⌝ -∗ |={∅}=> |={∅}[∅]▷=>^[n] ⌜q a b c⌝) ⊢@{PROP}
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜∀ a b c, G a b c → q a b c⌝ := by
  classical
  have hpure : (∀ a b c, ⌜G a b c → q a b c⌝) ⊢@{PROP} ⌜∀ a b c, G a b c → q a b c⌝ :=
    (forall_mono fun a => (forall_mono fun b => pure_forall.2).trans pure_forall.2).trans
      pure_forall.2
  refine .trans ?_ ((fupd_step_fupdN_plain_forall_3
    (fun a b c => iprop(⌜G a b c → q a b c⌝)) n).trans (BIFUpdate.mono (step_fupdN_mono hpure)))
  iintro H %a %b %c
  by_cases hG : G a b c
  · ispecialize H $$ %a %b %c %hG
    imod H
    iintro !>
    iapply step_fupdN_mono (pure_mono fun h _ => h) $$ H
  · iapply fupd_step_fupdN_pure n fun h => absurd h hG

/-- The four-variable version of `step_fupdN_pure_imp_forall₃`. -/
theorem step_fupdN_pure_imp_forall₄ {A B C D : Type _} {G q : A → B → C → D → Prop} {n : Nat} :
    iprop% (∀ a b c d, ⌜G a b c d⌝ -∗ |={∅}=> |={∅}[∅]▷=>^[n] ⌜q a b c d⌝) ⊢@{PROP}
    |={∅}=> |={∅}[∅]▷=>^[n] ⌜∀ a b c d, G a b c d → q a b c d⌝ := by
  classical
  have hpure : (∀ a b c d, ⌜G a b c d → q a b c d⌝) ⊢@{PROP}
      ⌜∀ a b c d, G a b c d → q a b c d⌝ :=
    (forall_mono fun a => (forall_mono fun b => (forall_mono fun c => pure_forall.2).trans
      pure_forall.2).trans pure_forall.2).trans pure_forall.2
  refine .trans ?_ ((fupd_step_fupdN_plain_forall_4
    (fun a b c d => iprop(⌜G a b c d → q a b c d⌝)) n).trans
    (BIFUpdate.mono (step_fupdN_mono hpure)))
  iintro H %a %b %c %d
  by_cases hG : G a b c d
  · ispecialize H $$ %a %b %c %d %hG
    imod H
    iintro !>
    iapply step_fupdN_mono (pure_mono fun h _ => h) $$ H
  · iapply fupd_step_fupdN_pure n fun h => absurd h hG

end StepFUpdPlain

end Iris
