module

public import Metrology.TotalEris
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Code.Geometric
import Metrology.Iris.LocalBI

@[expose] public section

/-!
# Geometric distribution (total correctness)

`geometric ()` terminates almost surely with a non-negative integer, by error induction. -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi IProp GF

abbrev geoPost : Val rT → IProp GF :=
  fun w => iprop(∃ m : Int, ⌜w = .int m ∧ 0 ≤ m⌝)

theorem geo_nonneg_pos_err (E : CoPset) (ε : ENNReal) (hε : 0 < ε) :
    iprop(↯ε) ⊢ tglWp E (Exp.app geometric pl(#())) (geoPost (rT := rT)) := by
  refine ErrorCredit.Induction.external_simple (k := (3/2 : NNReal)) hε (by norm_num) ?_
  iintro ⟨IH, Herr⟩
  twp_pures
  twp_bind pl(rand(#2, #()))
  let F : ℕ → ENNReal := fun n => if n = 0 then 0 else (3/2 : NNReal) * ε
  have htoNat : (2 : Int).toNat = 2 := rfl
  have hF : ∑ n ∈ Finset.range 2, F n = (3/2 : NNReal) * ε := by
    simp [F, Finset.sum_range_succ]
  have hsplit : ((2 : ℕ) : ENNReal) = (3/2 : NNReal) + (1/2 : NNReal) := by
    rw [← ENNReal.coe_add]
    norm_num
  have hsum : (∑ n ∈ Finset.range (2 : Int).toNat, F n) / ((2 : Int).toNat : ENNReal) ≤ ε := by
    rw [ENNReal.div_le_iff' (by simp) (by simp), htoNat, hF, hsplit, add_mul]
    exact le_add_right le_rfl
  iapply twp_rand_exp (by decide) hsum $$ Herr
  iintro %n ⟨%⟨hn₀, hn₂⟩, Hcr⟩
  simp only [Exp.ofVal]
  interval_cases n
  · twp_pures
    twp_value
    iexists 0
    itrivial
  · twp_pure
    twp_pure
    twp_bind (Exp.app geometric pl(#()))
    iapply ErisWpGS.tglWp_wand (Φ := geoPost)
    isplitl [Hcr IH]
    · iapply IH
      iapply ErrorCredit.ext (show F (Int.toNat 1) = ((3/2 : NNReal) : ENNReal) * ε from rfl) $$ Hcr
    iintro %w ⟨%m, %⟨rfl, hm⟩⟩
    twp_pures
    twp_value
    iexists (m + 1)
    ipureintro
    exact ⟨rfl, by omega⟩

theorem geo_nonneg (E : CoPset) :
    ⊢ tglWp E (Exp.app geometric pl(#())) (geoPost (rT := rT)) := by
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Herr
  iapply geo_nonneg_pos_err E ε hε $$ Herr

theorem geo_nonneg_depth (E : CoPset) (k : ℕ) :
    iprop(↯((2⁻¹ : ENNReal) ^ k)) ⊢
      tglWp E (Exp.app geometric pl(#())) (geoPost (rT := rT)) := by
  induction k with
  | zero =>
    iintro Herr
    iexfalso
    iapply ErrorCredit.contradict (by simp) $$ Herr
  | succ k IH =>
    iintro Herr
    twp_pures
    twp_bind pl(rand(#2, #()))
    let F : ℕ → ENNReal := fun n => if n = 0 then 0 else (2⁻¹ : ENNReal) ^ k
    have hsum : (∑ n ∈ Finset.range (2 : Int).toNat, F n) / ((2 : Int).toNat : ENNReal) ≤
        (2⁻¹ : ENNReal) ^ (k + 1) := by
      simp [F, Finset.sum_range_succ, pow_succ, div_eq_mul_inv]
    iapply twp_rand_exp (by decide) hsum $$ Herr
    iintro %n ⟨%⟨hn₀, hn₂⟩, Hcr⟩
    simp only [Exp.ofVal]
    interval_cases n
    · twp_pures
      twp_value
      iexists 0
      itrivial
    · twp_pure
      twp_pure
      twp_bind (Exp.app geometric pl(#()))
      iapply ErisWpGS.tglWp_wand (Φ := geoPost)
      isplitl [Hcr]
      · iapply IH
        iapply ErrorCredit.ext (show F (Int.toNat 1) = (2⁻¹ : ENNReal) ^ k from rfl) $$ Hcr
      iintro %w ⟨%m, %⟨rfl, hm⟩⟩
      twp_pures
      twp_value
      iexists (m + 1)
      ipureintro
      exact ⟨rfl, by omega⟩

theorem geo_nonneg_of_depth (E : CoPset) :
    ⊢ tglWp E (Exp.app geometric pl(#())) (geoPost (rT := rT)) := by
  have hlim : Filter.liminf (fun k : ℕ => (2⁻¹ : ENNReal) ^ k) Filter.atTop = 0 :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)).liminf_eq
  iapply fupd_tglWp
  imod ErrorCredit.zero with Herr
  imodintro
  iapply twp_err_liminf Filter.univ_mem solve_not_value
  isplitl [Herr]
  · iapply ErrorCredit.ext hlim.symm $$ Herr
  · iintro %k - Hk
    iapply geo_nonneg_depth E k $$ Hk

/-! ## Adequacy -/

def geoPredicate (v : Val rT) : Prop :=
  ∃ m : Int, v = .int m ∧ 0 ≤ m

theorem measurableSet_geoPredicate :
    MeasurableSet {v : Val rT | geoPredicate v} := by
  refine Set.Countable.measurableSet
    (Set.Countable.mono ?_ (Set.countable_range fun m : Int => (.int m : Val rT)))
  rintro v ⟨m, rfl, _⟩
  exact ⟨m, rfl⟩

theorem geo_tgl [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF] (σ : State rT) :
    Tgl (limExec ⟨Exp.app geometric pl(#()), σ⟩) geoPredicate 0 := by
  refine twp_tgl (GF := GF) measurableSet_geoPredicate ?_
  intro _
  have hwp : ⊢
      tglWp ⊤ (Exp.app geometric pl(#())) fun v => iprop(⌜geoPredicate v⌝) :=
    (geo_nonneg ⊤).trans
      (ErisWpGS.tglWp_mono fun _ => by iintro ⟨%m, %hm⟩; ipureintro; exact ⟨m, hm⟩)
  iintro -
  iapply hwp

/-- The geometric sampler almost-surely terminates. -/
theorem geo_mass_one [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF] (σ : State rT) :
    1 ≤ (limExec ⟨Exp.app geometric pl(#()), σ⟩) Set.univ := by
  simpa using Tgl.termination_ineq (geo_tgl (GF := GF) σ)

end Examples
end TotalEris
end ProbLang
