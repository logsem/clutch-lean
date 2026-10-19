module

public import Metrology.Micrometer.Examples.RandomizedResponseZcdp
public import Metrology.Code.RandomizedResponseLoop
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Algebra.Regular.Prod

@[expose] public section

/-! # Randomized response in a loop

`rrCount b k` counts the `true` reports of `k` rounds; the refinement spends one credit per round
by induction on `k`, in any lifting, giving `(k ln 3, 0)`-DP and `(k ln 3, 0)`-zCDP. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp codensity zcdpDivergence zcdpLifting)
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-! ## The relational proof, in any lifting -/

section Rel

variable {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
  [BudgetCreditGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]
  [L.HasBind]

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
/-- The loop refines itself at equal counts, spending `↯b c` per iteration, given a refinement
of one round at `c`. -/
theorem rrCount_refines_of (c : B)
    (hrr : ∀ b b', ⊢@{IProp GF} ↯b c -∗ REL[L] (rr (rT := rT) b) << (rr b') : lrel_bool)
    (b b' : Bool) (k : ℕ) :
    ⊢@{IProp GF} ↯b (k • c) -∗ REL[L] (rrCount (rT := rT) b k) << (rrCount b' k) : lrel_int := by
  induction k with
  | zero =>
    iintro -
    simp only [rrCount]
    rel_pures
    rel_values
  | succ k ih =>
    rw [succ_nsmul]
    iintro Hb
    icases BudgetCredit.split $$ Hb with ⟨Hk, H1⟩
    simp only [rrCount]
    rel_pure_l 5
    rel_pure_r 5
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = k by omega]
    rel_bind (rrCount b k) (rrCount b' k)
    isplitl [Hk]
    · iapply ih $$ Hk
    iintro %v %v' Hv
    iunfold lrel_int at Hv
    icases Hv with ⟨%n, %⟨rfl, rfl⟩⟩
    rel_bind (rr b) (rr b')
    isplitl [H1]
    · iapply hrr $$ H1
    iintro %w %w' Hw
    iunfold lrel_bool at Hw
    icases Hw with ⟨%d, %⟨rfl, rfl⟩⟩
    cases d <;> rel_pures <;> rel_values

end Rel

/-- The budget `(k ln 3, 0)` of `k` rounds. -/
noncomputable abbrev loopBudget (k : ℕ) : ℝ≥0∞ × ℝ≥0∞ := (k * ENNReal.ofReal (Real.log 3), 0)

/-- `k` rounds at `(ln 3, 0)` cost `(k ln 3, 0)`. -/
theorem nsmul_budget (k : ℕ) : k • budget = loopBudget k := by
  rw [Prod.smul_mk, nsmul_eq_mul, smul_zero]

/-- The loop refines itself at equal counts in the dp lifting, spending `(ln 3, 0)` per
iteration. -/
theorem rrCount_refines {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b b' : Bool) (k : ℕ) :
    ⊢@{IProp GF} ↯b (loopBudget k) -∗
      REL[codensity dp] (rrCount (rT := rT) b k) << (rrCount b' k) : lrel_int :=
  nsmul_budget k ▸ rrCount_refines_of budget rr_refines b b' k

/-- The loop refines itself at equal counts in the zCDP lifting, spending `(ln 3, 0)` per
iteration. -/
theorem rrCount_refines_zcdp {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b b' : Bool) (k : ℕ) :
    ⊢@{IProp GF} ↯b (loopBudget k) -∗
      REL[zcdpLifting] (rrCount (rT := rT) b k) << (rrCount b' k) : lrel_int :=
  nsmul_budget k ▸ rrCount_refines_of budget
    (rr_refines_of budget isAddLeftRegular_budget rr_zcdp_coupling) b b' k

/-! ## Adequacy: exit the logic -/

/-- The loop of `k` rounds is `(k ln 3, 0)`-DP for any two private bits, through
`rrCount_refines`. -/
theorem rrCount_dp_of (GF : BundledGFunctors) [RefinesPreGS rT (ℝ≥0∞ × ℝ≥0∞) GF]
    (b b' : Bool) (k : ℕ) (σ σ' : State rT) :
    dp (loopBudget k) (limExecV ⟨rrCount b k, σ⟩) (limExecV ⟨rrCount b' k, σ'⟩) :=
  approximates_div (GF := GF) (fun _ _ ↦ lrel_int) _ _ σ σ' _ (fun _ _ ↦ lrel_int_car_eq)
    fun _ _ ↦ rrCount_refines b b' k

/-- The loop of `k` rounds is `(k ln 3, 0)`-zCDP for any two private bits, through
`rrCount_refines_zcdp`. -/
theorem rrCount_zcdp_of (GF : BundledGFunctors) [RefinesPreGS rT (ℝ≥0∞ × ℝ≥0∞) GF]
    (b b' : Bool) (k : ℕ) (σ σ' : State rT) :
    zcdpDivergence (loopBudget k) (limExecV ⟨rrCount b k, σ⟩) (limExecV ⟨rrCount b' k, σ'⟩) :=
  approximates_div (GF := GF) (L := zcdpLifting) (fun _ _ ↦ lrel_int) _ _ σ σ' _
    (fun _ _ ↦ lrel_int_car_eq) fun _ _ ↦ rrCount_refines_zcdp b b' k

/-- The loop of `k` rounds on private bits, started from state `σ`. -/
noncomputable abbrev rrCountMech (k : ℕ) (σ : State rT) : Mechanism Bool (Exp rT) :=
  progMech (rrCount · k) σ

/-- Randomized response in a loop of `k` rounds is `(k ln 3, 0)`-DP for any two bits
(Def. 2.1). -/
theorem rrCount_DP (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).DP ⊤ (k * ENNReal.ofReal (Real.log 3)) 0 :=
  progMech_isPrivate (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) (L := codensity dp) _ σ (loopBudget k)
    (fun _ _ ↦ lrel_int) (fun _ _ ↦ lrel_int_car_eq) fun b b' _ _ _ ↦ rrCount_refines b b' k

/-- Randomized response in a loop of `k` rounds is `(k ln 3, 0)`-zCDP for any two bits
(Def. 2.4). -/
theorem rrCount_zCDP (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).zCDP ⊤ (k * ENNReal.ofReal (Real.log 3)) 0 :=
  progMech_isPrivate (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) (L := zcdpLifting) _ σ (loopBudget k)
    (fun _ _ ↦ lrel_int) (fun _ _ ↦ lrel_int_car_eq) fun b b' _ _ _ ↦ rrCount_refines_zcdp b b' k

end RandomizedResponse
end ProbLang
