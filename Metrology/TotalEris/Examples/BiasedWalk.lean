module

public import Metrology.TotalEris
public import Metrology.Code.RandomWalk
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi IProp GF

def walkCost (u m : ℕ) (a x : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (((u : ℝ) / (m - u)) ^ (a - x).toNat)

theorem walk_beq_int_lit {n m : ℤ} : ((BaseLit.int n : BaseLit rT) == BaseLit.int m) = (n == m) :=
  rfl

theorem walkCost_avg {u m : ℕ} (hum : u < m) {a x : ℤ} (hxa : x < a) :
    (∑ r ∈ Finset.range m, walkCost u m a (if r < u then x + 1 else x - 1)) /
      (m : ℝ≥0∞) ≤ walkCost u m a x := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, (a - x).toNat = e + 1 := ⟨(a - x).toNat - 1, by omega⟩
  have h1 : (a - (x + 1)).toNat = e := by omega
  have h2 : (a - (x - 1)).toNat = e + 2 := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hum.le,
    Finset.sum_congr (s₁ := Finset.range u) rfl (g := fun _ => walkCost u m a (x + 1))
      fun r hr => by simp [Finset.mem_range.mp hr],
    Finset.sum_congr (s₁ := Finset.Ico u m) rfl (g := fun _ => walkCost u m a (x - 1))
      fun r hr => by simp [not_lt.mpr (Finset.mem_Ico.mp hr).1]]
  simp only [Finset.sum_const, Finset.card_range, Nat.card_Ico, nsmul_eq_mul, walkCost, h1, h2,
    he]
  have hmu : (0 : ℝ) < m - u := by
    have : (u : ℝ) < m := by exact_mod_cast hum
    linarith
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [← ENNReal.ofReal_natCast u, ← ENNReal.ofReal_natCast (m - u),
    ← ENNReal.ofReal_natCast m,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_div_of_pos hm]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [Nat.cast_sub hum.le, div_eq_iff hm.ne']
  set ρ : ℝ := (u : ℝ) / (m - u) with hρdef
  have hρ : ((m : ℝ) - u) * ρ = u := by rw [hρdef]; field_simp
  linear_combination (ρ ^ (e + 1) - ρ ^ e) * hρ

theorem twp_biasedWalk (E : CoPset) {u m : ℕ} (hum : u < m) (a : ℤ) (n : ℕ) (x : ℤ)
    (hx : x ≤ a) :
    iprop(↯(walkCost u m a x)) ⊢
      tglWp E (Exp.app (Exp.app (biasedWalk (rT := rT) u m a) pl(#int (n : ℤ))) pl(#x))
        (fun v : Val rT => iprop(⌜v.1 = .lit (.bool false)⌝)) := by
  induction n generalizing x with
  | zero =>
    iintro Herr
    by_cases hxa : x = a
    · iexfalso
      iapply ErrorCredit.contradict (by simp [walkCost, hxa]) $$ Herr
    twp_pures
    rw [walk_beq_int_lit, beq_eq_false_iff_ne.mpr hxa]
    twp_pures
    twp_value
    ipureintro
    rfl
  | succ k IH =>
    iintro Herr
    by_cases hxa : x = a
    · iexfalso
      iapply ErrorCredit.contradict (by simp [walkCost, hxa]) $$ Herr
    twp_pures
    rw [walk_beq_int_lit, beq_eq_false_iff_ne.mpr hxa]
    twp_pures
    twp_bind pl(rand(#int (m : ℤ), #()))
    let F : ℕ → ℝ≥0∞ := fun r => walkCost u m a (if r < u then x + 1 else x - 1)
    have HSum : (∑ r ∈ Finset.range (m : ℤ).toNat, F r) / ((m : ℤ).toNat : ℝ≥0∞) ≤
        walkCost u m a x := by
      rw [Int.toNat_natCast]
      exact walkCost_avg hum (lt_of_le_of_ne hx hxa)
    iapply (twp_rand_exp' (z := m) (ε₂ := F) (Hz := by omega) (HSum := HSum)) $$ Herr
    iintro %r ⟨%⟨Hr₁, Hr₂⟩, Hcr⟩
    simp only [Exp.ofVal]
    twp_pure
    twp_pure
    by_cases hru : r < u
    · rw [decide_eq_true hru]
      twp_pure
      twp_pure
      twp_pure
      rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega]
      simp only [Exp.ofVal]
      twp_bind (Exp.app (Exp.app (biasedWalk (rT := rT) u m a) pl(#int (k : ℤ)))
        pl(#(x + 1)))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH (x + 1) (by omega)
      iapply ErrorCredit.ext (by simp [F, show r.toNat < u by omega]) $$ Hcr
    · rw [decide_eq_false hru]
      twp_pure
      twp_pure
      twp_pure
      rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega]
      simp only [Exp.ofVal]
      twp_bind (Exp.app (Exp.app (biasedWalk (rT := rT) u m a) pl(#int (k : ℤ)))
        pl(#(x - 1)))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH (x - 1) (by omega)
      iapply ErrorCredit.ext (by simp [F, show ¬r.toNat < u by omega]) $$ Hcr

theorem twp_biasedWalk_zero (E : CoPset) {u m : ℕ} (hum : u < m) (a n : ℕ) :
    iprop(↯(ENNReal.ofReal (((u : ℝ) / (m - u)) ^ a))) ⊢
      tglWp E (Exp.app (Exp.app (biasedWalk (rT := rT) u m a) pl(#int (n : ℤ)))
        pl(#0)) (fun v : Val rT => iprop(⌜v.1 = .lit (.bool false)⌝)) := by
  iintro Herr
  iapply twp_biasedWalk E hum a n 0 (by omega)
  iapply ErrorCredit.ext (by simp [walkCost]) $$ Herr

end
end Examples
end TotalEris
end ProbLang
