module

public import Metrology.TotalEris
public import Metrology.Code.RandomWalk
import Metrology.Iris.LocalBI

@[expose] public section

/-!
# Uniform 1D random walk (total correctness)

Stub: `unifRw1d_terminate` is `sorry`. `rand 1` samples `{0}` deterministically, so this program
only descends; the faithful walk needs `rand 2` and a `twp_presample_rsm` rule (unported `εAmp`,
`kwf`, error induction).
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

theorem finalPos_append (p₀ : Nat) (li : List (Fin 2)) (i : Fin 2) :
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

noncomputable def finalPosRsm (p₀ : Nat) (li : List (Fin 2)) : ENNReal :=
  (finalPos p₀ li : ENNReal)

def termCond (p₀ : Nat) (li : List (Fin 2)) : Prop := finalPos p₀ li = 0

theorem termCond_cons_zero (p₀ : Nat) (li : List (Fin 2)) :
    termCond (p₀ + 1) (0 :: li) ↔ termCond p₀ li := by
  simp [termCond, finalPos]

theorem termCond_cons_one (p₀ : Nat) (li : List (Fin 2)) :
    termCond (p₀ + 1) (1 :: li) ↔ termCond (p₀ + 2) li := by
  simp [termCond, finalPos]

theorem finalPos_dec_aux (p₀ : Nat) (li : List (Fin 2)) :
    ¬ termCond p₀ li → finalPos p₀ (li ++ [0]) < finalPos p₀ li := by
  intro h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h
  rw [finalPos_append, hn]
  simp

theorem finalPos_dec (li : List (Fin 2)) :
    ¬ termCond 1 li → ∃ c : Fin 2, finalPos 1 (li ++ [c]) < finalPos 1 li :=
  fun h => ⟨0, finalPos_dec_aux 1 li h⟩

/-! ## Termination spec -/

theorem unifRw1d_terminate (E : CoPset) :
    ⊢ tglWp (rT := rT) E unifRw1d
      (fun v => iprop(⌜v = .unit⌝)) := by
  sorry

end Examples
end TotalEris
end ProbLang
