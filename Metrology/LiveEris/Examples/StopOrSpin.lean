module

public import Metrology.LiveEris.CreditRules
public import Metrology.LiveEris.Tactics
public import Metrology.LiveEris.Adequacy
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-!
# Stop or spin

A loop that stops with probability 1/2, retries with probability 1/4, and otherwise falls into a
deterministic infinite loop. It never fails, and runs forever with probability at most 1/3.
-/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.LiveEris ProbLang.LiveEris.LiveWpGS
open scoped ENNReal

namespace ProbLang.LiveEris.Examples

@[pl_fold]
def spin {rT : Type _} : Exp rT := pl% rec spin u := spin u

pl_closed spin

@[pl_fold]
def stopOrSpin {rT : Type _} : Exp rT := pl%
  rec loop u :=
    if rand(#2, #()) = #0 then #()
    else (if rand(#2, #()) = #0 then loop u else &spin u)

theorem stopOrSpin_lc {rT : Type _} : (stopOrSpin : Exp rT).IsLocallyClosed :=
  Exp.lcb_imp_lc (by rfl)

variable {rT : Type _} {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSpace rT]
    [LawfulProbLangℝ rT]
  [LiveGS rT hlc GF]
local bi IProp GF

theorem lwp_spin (Q : State rT → State rT → Prop) (E : CoPset) (Φ : Val rT → IProp GF) :
    iprop(↻1) ⊢ lwp Q E (Exp.app spin pl(#())) Φ := by
  have H : ⊢ iprop(∀ Ψ : Val rT → IProp GF,
      ↻1 -∗ lwp Q E (Exp.app (spin (rT := rT)) pl(#())) Ψ) := by
    iapply loeb_wand_intuitionistically
    iintro !> #IH %Ψ Hd
    live_pure_excused
    iframe Hd
    inext
    iintro Hd
    live_pure
    live_bind (Exp.app (spin (rT := rT)) pl(#()))
    iapply IH $$ Hd
  iintro Hd
  iapply H $$ %Φ Hd

theorem avg_two {a b c : ℝ≥0∞} (h : a + b ≤ 2 * c) :
    (∑ n ∈ Finset.range (2 : ℤ).toNat, (if n = 0 then a else b)) / ((2 : ℤ).toNat : ℝ≥0∞) ≤ c := by
  simp only [show (2 : ℤ).toNat = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, Nat.one_ne_zero, ↓reduceIte, Nat.cast_ofNat]
  exact ENNReal.div_le_of_le_mul (by rw [mul_comm]; exact h)

theorem two_mul_half_pow (j : ℕ) : (2 : ℝ≥0∞) * 2⁻¹ ^ (j + 1) = 2⁻¹ ^ j := by
  rw [pow_succ, mul_comm, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
    mul_one]

theorem half_pow_le_one (j : ℕ) : (2⁻¹ : ℝ≥0∞) ^ j ≤ 1 :=
  pow_le_one₀ zero_le (ENNReal.inv_le_one.2 one_le_two)

theorem liminf_half_pow : Filter.liminf (fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ k) Filter.atTop = 0 :=
  (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)).liminf_eq

theorem two_third_le_one : (2 : ℝ≥0∞) * 3⁻¹ ≤ 1 := by
  calc (2 : ℝ≥0∞) * 3⁻¹ ≤ 3 * 3⁻¹ := by gcongr; norm_num
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top

theorem third_le_one : (3⁻¹ : ℝ≥0∞) ≤ 1 := ENNReal.inv_le_one.2 (by norm_num)

theorem third_add_one : (3⁻¹ : ℝ≥0∞) + 1 ≤ 2 * (2 * 3⁻¹) := by
  have h3 : (3 : ℝ≥0∞) * 3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top
  apply le_of_eq
  calc (3⁻¹ : ℝ≥0∞) + 1 = 3⁻¹ + 3 * 3⁻¹ := by rw [h3]
    _ = 2 * (2 * 3⁻¹) := by ring

/-- An `lwp` provable with `↯(ε k)` for every `k` needs no error credits when `ε` has liminf `0`. -/
theorem lwp_of_err_liminf_zero {Q : State rT → State rT → Prop} {E : CoPset} {e : Exp rT}
    {Φ : Val rT → IProp GF} {ε : ℕ → ℝ≥0∞} (hlim : Filter.liminf ε Filter.atTop = 0)
    (Hnv : e.toVal? = none) :
    iprop(∀ k, ↯(ε k) -∗ lwp Q E e Φ) ⊢ lwp Q E e Φ := by
  iintro Hwp
  iapply fupd_lwp
  imod Credit.zero with H0
  imodintro
  ihave ⟨He, -⟩ := Credit.frag_sep.1 $$ H0
  iapply lwp_err_liminf Filter.univ_mem Hnv
  isplitl [He]
  · iapply Credit.frag_ext hlim.symm rfl $$ He
  · iintro %k - Hk
    iapply Hwp $$ Hk

theorem lwp_stopOrSpin_depth (Q : State rT → State rT → Prop) (E : CoPset) (k : ℕ) :
    iprop(↯((2⁻¹ : ℝ≥0∞) ^ (2 * k)) ∗ ↻(3⁻¹)) ⊢
      lwp Q E (Exp.app stopOrSpin pl(#())) (fun v => iprop(⌜v = .unit⌝)) := by
  induction k with
  | zero =>
    iintro ⟨He, -⟩
    iexfalso
    iapply Credit.err_contradict (by simp) $$ He
  | succ k IH =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    iintro ⟨He, Hd⟩
    ihave Hcr := Credit.frag_sep.2 $$ [$He $Hd]
    live_pure
    live_pure
    live_bind (pl(rand(#2, #())) : Exp rT)
    iapply (lwp_rand_credit (F := fun n => if n = 0 then 0 else (2⁻¹ : ℝ≥0∞) ^ (2 * k + 1))
      (G := fun n => if n = 0 then 0 else 2 * 3⁻¹) (by norm_num)
      (fun n => by split <;> first | exact zero_le | exact half_pow_le_one _)
      (fun n => by split <;> first | exact zero_le | exact two_third_le_one)
      (avg_two (by rw [zero_add, two_mul_half_pow]))
      (avg_two (by rw [zero_add]))) $$ Hcr
    iintro %n ⟨%Hn, Hcr⟩
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · live_pures
      live_value
      ipureintro; rfl
    · live_pures
      ihave Hcr := Credit.frag_ext (ε₂ := (2⁻¹ : ℝ≥0∞) ^ (2 * k + 1)) (δ₂ := 2 * 3⁻¹)
        (by simp) (by simp) $$ Hcr
      live_bind (pl(rand(#2, #())) : Exp rT)
      iapply (lwp_rand_credit (F := fun n => if n = 0 then (2⁻¹ : ℝ≥0∞) ^ (2 * k) else 0)
        (G := fun n => if n = 0 then 3⁻¹ else 1) (by norm_num)
        (fun n => by split <;> first | exact zero_le | exact half_pow_le_one _)
        (fun n => by split <;> first | exact third_le_one | exact le_rfl)
        (avg_two (by rw [add_zero, two_mul_half_pow]))
        (avg_two third_add_one)) $$ Hcr
      iintro %n ⟨%Hn, Hcr⟩
      obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
      · live_pure
        live_pure
        live_bind (Exp.app (stopOrSpin (rT := rT)) pl(#()))
        iapply lwp_wand
        isplitl [Hcr]
        · iapply IH
          iapply Credit.frag_sep.1
          iapply Credit.frag_ext (by simp) (by simp) $$ Hcr
        · iintro %v %rfl
          live_value
          ipureintro; rfl
      · live_pure
        live_pure
        live_bind (Exp.app (spin (rT := rT)) pl(#()))
        iapply lwp_spin
        iapply Credit.frag_ext (by simp) (by simp) $$ Hcr

theorem lwp_stopOrSpin (Q : State rT → State rT → Prop) (E : CoPset) :
    iprop(↻(3⁻¹)) ⊢
      lwp Q E (Exp.app stopOrSpin pl(#())) (fun v => iprop(⌜v = .unit⌝)) := by
  have hlim : Filter.liminf (fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ (2 * k)) Filter.atTop = 0 := by
    simp_rw [pow_mul]
    exact (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (pow_lt_one₀ zero_le (by norm_num) two_ne_zero)).liminf_eq
  iintro Hd
  iapply lwp_of_err_liminf_zero hlim (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w)
  iintro %k Hk
  iapply lwp_stopOrSpin_depth
  iframe

/-! ## What adequacy gives -/

theorem measurableSet_eq_unit {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT] :
    MeasurableSet {v : Val rT | v = .unit} := by
  have h := (MeasurableSet.singleton (Exp.ofVal (Val.unit : Val rT))).preimage Exp.ofVal.measurable
  convert h using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨fun h => h ▸ rfl, fun h => Val.ext h⟩

theorem one_sub_third : (1 : ℝ≥0∞) - 3⁻¹ = 2 / 3 := by
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  rw [ENNReal.div_eq_inv_mul, ← mul_add_one, show (2 : ℝ≥0∞) + 1 = 3 by norm_num,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- Stop-or-spin never returns anything but `()`. -/
theorem stopOrSpin_safe (σ : State ℝ) :
    limExec ⟨Exp.app stopOrSpin pl(#()), σ⟩ (badVal (· = .unit)) = 0 :=
  nonpos_iff_eq_zero.mp <| limExec_bad_le measurableSet_eq_unit fun k =>
    lwp_adequacy_safety (GF := liveGF) (Q := fun _ _ => False) (δ := 3⁻¹) measurableSet_eq_unit
      (by simp) (fun [LiveGS ℝ .hasNoLC liveGF] => sep_elim_right.trans (lwp_stopOrSpin _ ⊤)) k

/-- Stop-or-spin terminates, returning `()`, with probability at least `2/3`. -/
theorem stopOrSpin_terminates (σ : State ℝ) :
    2 / 3 ≤ limExec ⟨Exp.app stopOrSpin pl(#()), σ⟩ (goodVal (· = .unit)) := by
  have h := lwp_adequacy_liveness (GF := liveGF) (σ := σ) (Q := fun _ _ => False) (ε := 0)
    (δ := 3⁻¹) (P := fun _ => False) (by simp) measurableSet_eq_unit (fun _ _ h => h) (by simp)
    (fun [LiveGS ℝ .hasNoLC liveGF] => sep_elim_right.trans (lwp_stopOrSpin _ ⊤)) 1
  rw [zero_add, one_sub_third] at h
  exact limExec_good_ge measurableSet_eq_unit h

end ProbLang.LiveEris.Examples
