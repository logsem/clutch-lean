module

public import Metrology.TotalEris
public import Metrology.Code.RandomWalk
import Metrology.Iris.LocalBI

@[expose] public section

/-!
# Uniform 1D random walk (total correctness)

Uniform 1D random walk, stubbed because `rand 1` only descends.
-/

open Iris ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS

namespace ProbLang
namespace TotalEris
namespace Examples

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi IProp GF

/-! ## `finalPos` and the RSM scaffold -/

/-- Step `0` moves down, `1` moves up; position `0` is absorbing. -/
def finalPos (p₀ : Nat) : List (Fin 2) → Nat
  | [] => p₀
  | x :: xs =>
      match p₀ with
      | 0 => 0
      | n + 1 =>
          if x = 0 then finalPos n xs
          else finalPos (n + 2) xs

variable (p₀ : Nat) (li : List (Fin 2))

/-- Appending a step to the list moves the final position by that step. -/
theorem finalPos_append (i : Fin 2) :
    finalPos p₀ (li ++ [i]) =
      match finalPos p₀ li with
      | 0 => 0
      | n + 1 => if i = 0 then n else n + 2 := by
  induction li generalizing p₀ with
  | nil => simp [finalPos]
  | cons a tl IH =>
    obtain _ | n := p₀
    · simp [finalPos]
    · fin_cases a <;> simpa [finalPos] using IH _

/-- The final position as an extended nonnegative real, the ranking function. -/
noncomputable def finalPosRsm : ENNReal :=
  (finalPos p₀ li : ENNReal)

/-- The walk has reached the absorbing position `0`. -/
def termCond : Prop := finalPos p₀ li = 0

/-- A down step from a positive position preserves the termination condition. -/
theorem termCond_cons_zero :
    termCond (p₀ + 1) (0 :: li) ↔ termCond p₀ li := by
  simp [termCond, finalPos]

/-- An up step from a positive position shifts the start by two. -/
theorem termCond_cons_one :
    termCond (p₀ + 1) (1 :: li) ↔ termCond (p₀ + 2) li := by
  simp [termCond, finalPos]

/-- Away from termination, a down step strictly decreases the final position. -/
theorem finalPos_dec_aux :
    ¬ termCond p₀ li → finalPos p₀ (li ++ [0]) < finalPos p₀ li := by
  intro h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h
  rw [finalPos_append, hn]
  simp

/-- From position `1`, some step strictly decreases the final position. -/
theorem finalPos_dec :
    ¬ termCond 1 li → ∃ c : Fin 2, finalPos 1 (li ++ [c]) < finalPos 1 li :=
  fun h => ⟨0, finalPos_dec_aux 1 li h⟩

/-! ## Termination spec -/

/-- The random walk terminates, with its proof stubbed. -/
theorem unifRw1d_terminate (E : CoPset) :
    ⊢ tglWp (rT := rT) E unifRw1d
      (fun v => iprop(⌜v = .unit⌝)) := by
  -- Stub: rand 1 only descends; see module docstring.
  sorry

end Examples
end TotalEris
end ProbLang
