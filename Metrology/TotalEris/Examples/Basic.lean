module

public import Metrology.TotalEris
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # TotalEris smoke tests -/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS

namespace ProbLang
namespace TotalEris

variable {rT : Type _} [LawfulProbLangℝ rT] [Countable rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi IProp GF

/-- `tglWp_value` -/
example (E : CoPset) (v : Val rT) :
    ⊢ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iapply tglWp_value
  itrivial

/-- `twp_alloc` -/
example (E : CoPset) (v : Val rT) :
    ⊢ tglWp E (.alloc (.ofVal v))
      (fun w => iprop(∃ l : Loc,
        ⌜w = .loc l⌝ ∗ appHeapFrag l v)) := by
  iapply twp_alloc
  iintro %l $
  itrivial

/-- `twp_rand_tape` -/
example (E : CoPset) (l : Loc) (z : Int)
    (n : { z' : Int // 0 ≤ z' ∧ z' < z })
    (ns : List { z' : Int // 0 ≤ z' ∧ z' < z }) :
    ⊢ l ↪ₐ ⟨z, n :: ns⟩ -∗
      tglWp E (pl(rand(#z, #lbl l)))
        (fun w : Val rT => iprop(⌜w = .int n.val⌝ ∗ l ↪ₐ ⟨z, ns⟩)) := by
  iintro Hl
  iapply twp_rand_tape
  iframe Hl
  iintro $
  itrivial

/-- `twp_rand_tape_empty` -/
example (E : CoPset) (l : Loc) (z : Int) (Hz : 0 < z) :
    ⊢ l ↪ₐ ⟨z, []⟩ -∗
      tglWp E (pl(rand(#z, #lbl l)))
        (fun w : Val rT => iprop(∃ n : Int,
          ⌜0 ≤ n ∧ n < z⌝ ∗ ⌜w = .int n⌝ ∗ l ↪ₐ ⟨z, []⟩)) := by
  iintro Hl
  iapply (twp_rand_tape_empty Hz)
  iframe Hl
  iintro %n $ %Hbnd
  iframe %Hbnd
  itrivial

/-- `tglWp_mono` -/
example (E : CoPset) (v : Val rT) :
    ⊢ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝ ∗ ⌜w = v⌝))
      -∗ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iintro HW
  iapply tglWp_mono (Φ := fun w => iprop(⌜w = v⌝ ∗ ⌜w = v⌝))
  · intro w; iintro ⟨$, -⟩
  · iexact HW

/-- `tglWp_fupd` -/
example (E : CoPset) (v : Val rT) :
    ⊢ tglWp E (.ofVal v) (fun w => iprop(|={E}=> ⌜w = v⌝))
      -∗ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) :=
  entails_wand tglWp_fupd

/-- `tglWp_wand` -/
example (E : CoPset) (v : Val rT) :
    ⊢ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜w = v ∨ w = v⌝)) := by
  iintro HW
  iapply tglWp_wand
  iframe HW
  iintro %w %Hw !%
  exact .inl Hw

/-- `tglWp_strong_mono` -/
example (E : CoPset) (v : Val rT) :
    ⊢ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(|={E}=> ⌜w = v⌝)) := by
  iintro HW
  iapply tglWp_strong_mono
  iframe HW
  iintro %w %Hw !> !> //

/-- `tglWp_bind_value` -/
example (E : CoPset) (v : Val rT) (K : Ectx rT) :
    ⊢ tglWp E (.ofVal v) (fun w =>
        tglWp E (K.fill (.ofVal w)) (fun w' => iprop(⌜w' = v⌝))) -∗
      tglWp E (K.fill (Exp.ofVal v)) (fun w' => iprop(⌜w' = v⌝)) :=
  entails_wand tglWp_bind_value

/-- `ErrorCredit.Induction.increasing` -/
example [ECGS GF] (ε : ENNReal) (ε' : NNReal) (P : IProp GF)
    (hε : 0 < ε) (hε' : ε < ε') :
    ⊢ iprop(□ ((↯(ε' : ENNReal) -∗ P) ∗ ↯ε -∗ P)) -∗
      iprop(↯ε -∗ P) :=
  entails_wand (ErrorCredit.Induction.increasing hε hε')

/-- `tglWp_bind` -/
example (E : CoPset) (e : Exp rT) (K : Ectx rT) (φ : Val rT → Prop) :
    ⊢ tglWp E e (fun v =>
        tglWp E (K.fill (.ofVal v)) (fun w => iprop(⌜φ w⌝))) -∗
      tglWp E (K.fill e) (fun w => iprop(⌜φ w⌝)) :=
  entails_wand tglWp_bind

/-- `(λ x. !x) (alloc v) ⇓ v` -/
example (E : CoPset) (v : Val rT) :
    ⊢ tglWp E
      (pl((fun x, !x) (alloc({Exp.ofVal v}))) : Exp rT)
      (fun w => iprop(⌜w = v⌝)) := by
  twp_bind (Exp.alloc (Exp.ofVal v))
  iapply twp_alloc
  iintro %l Hl
  twp_pures
  iapply twp_load
  iframe Hl
  iintro - //

/-- `fupd_tglWp` -/
example (E : CoPset) (v : Val rT) :
    ⊢ iprop(|={E}=> tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝))) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) :=
  entails_wand fupd_tglWp

/-- `tglWp_frame_left` -/
example (E : CoPset) (v : Val rT) (R : Prop) (HR : R) :
    ⊢ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜R⌝ ∗ ⌜w = v⌝)) := by
  iintro HW
  iapply tglWp_frame_left
  iframe HW %HR

/-- `twp_rand_exp` with `F 0 = 0`, `F 1 = ε` -/
example (E : CoPset) (ε : ENNReal) :
    ⊢ ↯ε -∗
      tglWp E (pl(rand(#2, #())))
        (fun w : Val rT => iprop(∃ n : Int, ⌜0 ≤ n ∧ n < 2 ∧
          w = .int n⌝)) := by
  iintro Hcr
  let F : ℕ → ENNReal := fun n => if n = 0 then 0 else ε
  have htoNat : (2 : Int).toNat = 2 := rfl
  have hF : ∑ n ∈ Finset.range 2, F n = ε := by simp [F, Finset.sum_range_succ]
  have hsplit : ((2 : ℕ) : ENNReal) = 1 + 1 := by norm_num
  have HSum : (∑ n ∈ Finset.range (2 : Int).toNat, F n) / ((2 : Int).toNat : ENNReal) ≤ ε := by
    rw [ENNReal.div_le_iff' (by simp) (by simp), htoNat, hF, hsplit, add_mul, one_mul]
    exact le_self_add
  iapply (twp_rand_exp (Hz := by decide) (HSum := HSum)) $$ Hcr
  iintro %n ⟨%Hn, -⟩
  iexists n
  ipureintro
  exact ⟨Hn.1, Hn.2, rfl⟩

/-- `twp_rand_exp` with zero error -/
example (E : CoPset) (ε : ENNReal) :
    ⊢ ↯ε -∗
      tglWp E (pl(rand(#1, #())))
        (fun w : Val rT => iprop(⌜w = .int 0⌝)) := by
  iintro Hε
  iapply (twp_rand_exp (ε₂ := fun _ => 0) (Hz := by decide) (HSum := by simp)) $$ Hε
  iintro %n ⟨%⟨Hn₁, Hn₂⟩, -⟩
  interval_cases n
  itrivial

/-! ## Adequacy -/

section AdequacySmokeTests

variable {GF : BundledGFunctors}
  [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]

/-- `twp_tgl` -/
example (v : Val rT) (σ : State rT) (φ : Val rT → Prop) (hφ : φ v)
    (hφm : MeasurableSet {v : Val rT | φ v}) :
    Tgl (limExec ⟨Exp.ofVal v, σ⟩) φ 0 := by
  refine twp_tgl (GF := GF) hφm ?_
  intro _
  iintro -
  iapply tglWp_value
  ipureintro
  exact hφ

/-- `Tgl.termination_ineq` -/
example (v : Val rT) (σ : State rT) :
    1 ≤ (limExec ⟨Exp.ofVal v, σ⟩) Set.univ := by
  have h : Tgl (limExec ⟨Exp.ofVal v, σ⟩) (fun _ => True) 0 := by
    refine twp_tgl (GF := GF)
      (φ := fun _ => True) (MeasurableSet.const True) ?_
    intro _
    iintro -
    iapply tglWp_value
    itrivial
  simpa using Tgl.termination_ineq h

/-- `twp_tgl_limit` -/
example (v : Val rT) (σ : State rT) (φ : Val rT → Prop) (hφ : φ v)
    (hφm : MeasurableSet {v : Val rT | φ v}) :
    Tgl (limExec ⟨Exp.ofVal v, σ⟩) φ 0 := by
  refine twp_tgl_limit (GF := GF) hφm ?_
  intro _ _ _
  iintro -
  iapply tglWp_value
  ipureintro
  exact hφ

/-- `twp_pgl_lim` -/
example (v : Val rT) (σ : State rT) (φ : Val rT → Prop) (hφ : φ v)
    (hφm : MeasurableSet {v : Val rT | φ v}) :
    Pgl 0 (fun ρ => ∃ w, ρ.expr = Exp.ofVal w ∧ φ w)
      (limExec ⟨Exp.ofVal v, σ⟩) := by
  refine twp_pgl_lim (GF := GF) hφm ?_
  intro _
  iintro -
  iapply tglWp_value
  ipureintro
  exact hφ

end AdequacySmokeTests

end TotalEris
end ProbLang
