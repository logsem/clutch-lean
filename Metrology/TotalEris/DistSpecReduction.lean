module

public import Metrology.TotalEris.ErisGS
public meta import Metrology.TotalEris.Triple
import Metrology.ProbLang.Syntax.Notation
public import Metrology.TotalEris.TotalPrimitiveLaws
public import Metrology.TotalEris.ErrorRules
public import Metrology.FromMathlib.LusinContinuous
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Reduced correctness specifications

`DistSpec` is the correctness specification for CTE samplers; `DistSpec_of_local` reduces it to
`DistSpecOn` for approximating pairs `(K, G)`, and `DistSpec_of_DistSpec*` to Lusin, lower
semicontinuous, simple, polynomial and smooth credit functions. -/

open Iris Iris.Std Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS ErrorCredit
open scoped ENNReal NNReal AppGS
open Polynomial

namespace ProbLang

-- TODO: Generalize from `ℝ` to `rT`, and Lusin's argument beyond real-valued samplers.
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
local bi IProp GF

variable (E : CoPset) (e : Exp ℝ) (μ : MeasureTheory.Measure ℝ)

/-- The spec that `e` samples from `μ`, for every measurable credit function `F`. -/
def DistSpec : Prop :=
  ∀ (F : ℝ → ℝ≥0∞), Measurable F →
    [{ ↯ ∫⁻ x, F x ∂μ }] e @ E [{ r, RET .real r; ↯ (F r) }]

/-- The spec for one credit function `G` on one set `K`, charging a full credit outside `K`. -/
def DistSpecOn (K : Set ℝ) (G : ℝ → ℝ≥0∞) : Prop :=
  [{ ↯ (∫⁻ x in K, G x ∂μ + μ Kᶜ) }] e @ E
    [{ r, RET .real r; ⌜r ∈ K⌝ ∗ ↯ (G r) }]

/-- The spec on every compact set for every continuous credit function. -/
def DistSpecLusin : Prop :=
  ∀ K F, IsCompact K → Continuous F → DistSpecOn (GF := GF) E e μ K F

/-- The spec for every lower semicontinuous credit function. -/
def DistSpecLSC : Prop :=
  ∀ G : ℝ → ℝ≥0∞, LowerSemicontinuous G →
    [{ ↯ ∫⁻ x, G x ∂μ }] e @ E [{ r, RET .real r; ↯ (G r) }]

/-- The spec for every simple credit function. -/
def DistSpecSimple : Prop :=
  ∀ s : MeasureTheory.SimpleFunc ℝ ℝ≥0∞,
    [{ ↯ ∫⁻ x, s x ∂μ }] e @ E [{ r, RET .real r; ↯ (s r) }]

/-- The spec on every compact set for every real polynomial credit function. -/
def DistSpecPoly : Prop :=
  ∀ K (p : ℝ[X]), IsCompact K →
    DistSpecOn (GF := GF) E e μ K fun x => ENNReal.ofReal (p.eval x)

/-- The spec on every compact set for every rational polynomial credit function. -/
def DistSpecRatPoly : Prop :=
  ∀ K (q : ℚ[X]), IsCompact K →
    DistSpecOn (GF := GF) E e μ K fun x => ENNReal.ofReal (aeval x q)

/-- The spec on every compact subset of `S` for every real polynomial credit function. -/
def DistSpecPolyOn (S : Set ℝ) : Prop :=
  ∀ K (p : ℝ[X]), IsCompact K → K ⊆ S →
    DistSpecOn (GF := GF) E e μ K fun x => ENNReal.ofReal (p.eval x)

/-- The spec on every compact subset of `S` for every rational polynomial credit function. -/
def DistSpecRatPolyOn (S : Set ℝ) : Prop :=
  ∀ K (q : ℚ[X]), IsCompact K → K ⊆ S →
    DistSpecOn (GF := GF) E e μ K fun x => ENNReal.ofReal (aeval x q)

open scoped ContDiff in
/-- The spec on every compact set for every smooth credit function. -/
def DistSpecSmooth : Prop :=
  ∀ K (G : ℝ → ℝ), IsCompact K → ContDiff ℝ ∞ G →
    DistSpecOn (GF := GF) E e μ K fun x => ENNReal.ofReal (G x)

variable {E e μ}

/-- A local spec for every approximating pair `(K, G)` in `P` gives `DistSpec`. -/
theorem DistSpec_of_local
    (P : Set ℝ → (ℝ → ℝ≥0∞) → Prop) (hv : e.toVal? = none)
    (hloc : ∀ F, Measurable F → ∀ ε, 0 < ε → ∃ K G, P K G ∧ (∀ x ∈ K, min (F x) 1 ≤ G x) ∧
      ∫⁻ x in K, G x ∂μ + μ Kᶜ ≤ ∫⁻ x, F x ∂μ + ε)
    (hS : ∀ K G, P K G → DistSpecOn (GF := GF) E e μ K G) : DistSpec (GF := GF) E e μ := by
  unfold DistSpecOn at hS
  unfold DistSpec
  iintro %F %hF %Φ Hamp HΦ
  iapply twp_err_pos_add hv $$ Hamp
  iintro %ε %Hε Hamp
  obtain ⟨K, G, hP, hFG, hGint⟩ := hloc F hF ε Hε
  ihave Hamp := weaken hGint $$ Hamp
  iapply hS K G hP $$ %Φ Hamp
  iintro %r ⟨%hr, HG⟩
  iapply HΦ
  rcases min_le_iff.1 (hFG r hr) with h | h
  · iapply weaken h $$ HG
  · iexfalso
    iapply contradict h $$ HG

/-- A spec for `G` on the whole line is a spec on `univ`. -/
theorem DistSpecOn_univ {G : ℝ → ℝ≥0∞}
    (h : [{ ↯ ∫⁻ x, G x ∂μ }] e @ E [{ r, RET .real r; ↯ (G r) }]) :
    DistSpecOn (GF := GF) E e μ Set.univ G := by
  unfold DistSpecOn
  iintro %Φ Hamp HΦ
  iapply h $$ %Φ [Hamp]
  · iapply weaken (by simp) $$ Hamp
  · iintro %r HG
    iapply HΦ
    iframe
    itrivial

/-- `DistSpec` gives the local spec for every measurable `G` on every measurable `K`. -/
theorem DistSpecOn_of_DistSpec
    {K : Set ℝ} {G : ℝ → ℝ≥0∞} (hK : MeasurableSet K) (hG : Measurable G)
    (h : DistSpec (GF := GF) E e μ) : DistSpecOn (GF := GF) E e μ K G := by
  classical
  unfold DistSpecOn
  iintro %Φ Hε HΦ
  iapply h (K.piecewise G 1) (hG.piecewise hK measurable_const) $$ %Φ [Hε]
  · iapply weaken (by rw [MeasureTheory.lintegral_piecewise hK]; simp) $$ Hε
  · iintro %r H
    by_cases hr : r ∈ K
    · isimp only [Set.piecewise_eq_of_mem _ _ _ hr] at H
      iapply HΦ
      iframe %hr
      iexact H
    · iexfalso
      iapply contradict (by simp [hr]) $$ H

/-- `DistSpec_of_local` with `K = univ`. -/
theorem DistSpec_of_global
    (C : (ℝ → ℝ≥0∞) → Prop) (hv : e.toVal? = none)
    (happrox : ∀ F, Measurable F → ∀ ε, 0 < ε → ∃ G, C G ∧ (∀ x, min (F x) 1 ≤ G x) ∧
      ∫⁻ x, G x ∂μ ≤ ∫⁻ x, F x ∂μ + ε)
    (hS : ∀ G, C G → [{ ↯ ∫⁻ x, G x ∂μ }] e @ E [{ r, RET .real r; ↯ (G r) }]) :
    DistSpec (GF := GF) E e μ :=
  DistSpec_of_local (fun K G => K = Set.univ ∧ C G) hv
    (fun F hF ε hε =>
      have ⟨G, hC, hle, hint⟩ := happrox F hF ε hε
      ⟨Set.univ, G, ⟨rfl, hC⟩, fun x _ => hle x, by simpa using hint⟩)
    (fun _ G ⟨hK, hC⟩ => hK ▸ DistSpecOn_univ (hS G hC))

open MeasureTheory in
/-- `DistSpec_of_local` where `K ⊆ S` may be assumed when `μ Sᶜ = 0`. -/
theorem DistSpec_of_local_support [IsFiniteMeasure μ]
    {S : Set ℝ} (hS : MeasurableSet S) (hμ : μ Sᶜ = 0)
    (P : Set ℝ → (ℝ → ℝ≥0∞) → Prop) (hP : ∀ K K' G, P K G → IsCompact K' → P (K ∩ K') G)
    (hv : e.toVal? = none)
    (hloc : ∀ F, Measurable F → ∀ ε, 0 < ε → ∃ K G, P K G ∧ (∀ x ∈ K, min (F x) 1 ≤ G x) ∧
      ∫⁻ x in K, G x ∂μ + μ Kᶜ ≤ ∫⁻ x, F x ∂μ + ε)
    (hSpec : ∀ K G, P K G → K ⊆ S → DistSpecOn (GF := GF) E e μ K G) :
    DistSpec (GF := GF) E e μ := by
  refine DistSpec_of_local (fun K G => P K G ∧ K ⊆ S) hv (fun F hF ε hε => ?_)
    fun K G ⟨hPKG, hKS⟩ => hSpec K G hPKG hKS
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K, G, hPKG, hle, hint⟩ := hloc F hF _ hε2
  obtain ⟨K', hK'S, hK', hK'ε⟩ := hS.exists_isCompact_sdiff_lt (measure_ne_top μ S) hε2.ne'
  have hK'c : μ K'ᶜ ≤ ε / 2 :=
    calc μ K'ᶜ ≤ μ (S \ K') + μ Sᶜ :=
          (measure_mono fun x hx => (em (x ∈ S)).imp (fun h => ⟨h, hx⟩) id).trans
            (measure_union_le _ _)
      _ ≤ ε / 2 := by rw [hμ, add_zero]; exact hK'ε.le
  refine ⟨K ∩ K', G, ⟨hP K K' G hPKG hK', Set.inter_subset_right.trans hK'S⟩,
    fun x hx => hle x hx.1, ?_⟩
  calc _ ≤ ∫⁻ x in K, G x ∂μ + μ Kᶜ + μ K'ᶜ := by
        rw [add_assoc, Set.compl_inter]
        exact add_le_add (lintegral_mono_set Set.inter_subset_left) (measure_union_le _ _)
    _ ≤ ∫⁻ x, F x ∂μ + ε / 2 + ε / 2 := add_le_add hint hK'c
    _ = ∫⁻ x, F x ∂μ + ε := by rw [add_assoc, ENNReal.add_halves]

/-- A real polynomial is approximated on `[a, b]` by a rational polynomial. -/
theorem exists_rat_polynomial_near (a b : ℝ) (p : ℝ[X]) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ[X], ∀ x ∈ Set.Icc a b, |p.eval x - aeval x q| < δ := by
  have hR {x} (hx : x ∈ Set.Icc a b) : |x| ≤ max |a| |b| := abs_le_max_abs_abs hx.1 hx.2
  induction p using Polynomial.induction_on' generalizing δ with
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁, hq₁⟩ := h₁ (half_pos hδ)
    obtain ⟨q₂, hq₂⟩ := h₂ (half_pos hδ)
    refine ⟨q₁ + q₂, fun x hx => ?_⟩
    calc _ ≤ |p₁.eval x - aeval x q₁| + |p₂.eval x - aeval x q₂| := by
          rw [eval_add, map_add, add_sub_add_comm]
          exact abs_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add (hq₁ x hx) (hq₂ x hx)
      _ = δ := add_halves δ
  | monomial n r =>
    have hM : 0 < max |a| |b| ^ n + 1 := by positivity
    obtain ⟨s, hs⟩ := exists_rat_near r (div_pos hδ hM)
    refine ⟨monomial n s, fun x hx => ?_⟩
    rw [eval_monomial, aeval_monomial, eq_ratCast, ← sub_mul, abs_mul, abs_pow]
    calc |r - s| * |x| ^ n ≤ |r - s| * (max |a| |b| ^ n + 1) := by
          gcongr
          exact pow_le_pow_left₀ (abs_nonneg x) (hR hx) n
            |>.trans (le_add_of_nonneg_right zero_le_one)
      _ < δ / (max |a| |b| ^ n + 1) * (max |a| |b| ^ n + 1) := by gcongr
      _ = δ := div_mul_cancel₀ _ hM.ne'

section approx
open MeasureTheory
variable (μ : Measure ℝ) [IsFiniteMeasure μ] {F : ℝ → ℝ≥0∞} (hF : Measurable F) {ε : ℝ≥0∞}
  (hε : 0 < ε)
include hF hε

/-- A measurable `min F 1` agrees with a continuous function on a compact set of large measure. -/
theorem exists_compact_continuous_eq :
    ∃ (K : Set ℝ) (g : C(ℝ, ℝ≥0)), IsCompact K ∧ μ Kᶜ ≤ ε ∧
      ∀ x ∈ K, (g x : ℝ≥0∞) = min (F x) 1 := by
  have hF₁ x : min (F x) 1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  obtain ⟨K, hK, hKε, hF₁K⟩ := (hF.min measurable_const).exists_isCompact_restrict μ hε
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hK.isClosed
    ⟨K.domRestrict fun x => (min (F x) 1).toNNReal,
      (ENNReal.continuousOn_toNNReal.comp hF₁K fun x _ => hF₁ x).domRestrict⟩
  exact ⟨K, g, hK, hKε, fun x hx => by
    simp [show g x = _ from DFunLike.congr_fun hg ⟨x, hx⟩, hF₁ x]⟩

/-- `min F 1` is matched on a compact set by a continuous function at small total cost. -/
theorem exists_compact_continuous_approx :
    ∃ K G, IsCompact K ∧ Continuous G ∧ (∀ x ∈ K, G x = min (F x) 1) ∧
      ∫⁻ x in K, G x ∂μ + μ Kᶜ ≤ ∫⁻ x, F x ∂μ + ε := by
  obtain ⟨K, g, hK, hKε, hgK⟩ := exists_compact_continuous_eq μ hF hε
  refine ⟨K, fun x => g x, hK, ENNReal.continuous_coe.comp g.continuous, hgK, ?_⟩
  calc _ = ∫⁻ x in K, min (F x) 1 ∂μ + μ Kᶜ := by rw [setLIntegral_congr_fun hK.measurableSet hgK]
    _ ≤ ∫⁻ x in K, F x ∂μ + ε := add_le_add (lintegral_mono fun _ => min_le_left _ _) hKε
    _ ≤ ∫⁻ x, F x ∂μ + ε := by grw [setLIntegral_le_lintegral]

/-- `min F 1` is bounded above by a simple function with small extra integral. -/
theorem exists_simpleFunc_approx :
    ∃ s : SimpleFunc ℝ ℝ≥0∞, (∀ x, min (F x) 1 ≤ s x) ∧
      ∫⁻ x, s x ∂μ ≤ ∫⁻ x, F x ∂μ + ε := by
  obtain ⟨c, hc0, hc⟩ := ENNReal.exists_nnreal_pos_mul_lt (measure_ne_top μ Set.univ) hε.ne'
  let t (y : ℝ≥0∞) : ℝ≥0 := (min y 1).toNNReal
  let φ (y : ℝ≥0∞) : ℝ≥0∞ := ((c * ⌈t y / c⌉₊ : ℝ≥0) : ℝ≥0∞)
  have ht y : (t y : ℝ≥0∞) = min y 1 :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
  have hφm : Measurable φ :=
    measurable_coe_nnreal_ennreal.comp (measurable_const.mul
      (measurable_from_nat.comp (Nat.measurable_ceil.comp
        ((ENNReal.measurable_toNNReal.comp (measurable_id.min measurable_const)).div_const c))))
  have hφr : (Set.range φ).Finite := by
    refine ((Set.finite_Iic ⌈1 / c⌉₊).image fun k : ℕ => ((c * k : ℝ≥0) : ℝ≥0∞)).subset ?_
    rintro _ ⟨y, rfl⟩
    refine ⟨⌈t y / c⌉₊, Nat.ceil_mono (div_le_div_of_nonneg_right ?_ c.2), rfl⟩
    simpa using ENNReal.toNNReal_mono ENNReal.one_ne_top (min_le_right y 1)
  let s : SimpleFunc ℝ ℝ≥0∞ :=
    ⟨φ ∘ F, fun y => (hφm.comp hF) (measurableSet_singleton y),
      hφr.subset (Set.range_comp_subset_range F φ)⟩
  have hlo y : t y ≤ c * ⌈t y / c⌉₊ := (div_le_iff₀' hc0).1 (Nat.le_ceil _)
  have hhi y : c * ⌈t y / c⌉₊ ≤ t y + c := by
    have := Nat.ceil_lt_add_one (zero_le : 0 ≤ t y / c)
    calc c * ⌈t y / c⌉₊ ≤ c * (t y / c + 1) := by gcongr
      _ = t y + c := by rw [mul_add, mul_div_cancel₀ _ hc0.ne', mul_one]
  refine ⟨s, fun x => (ht (F x)).symm.trans_le (ENNReal.coe_le_coe.2 (hlo _)), ?_⟩
  calc ∫⁻ x, s x ∂μ ≤ ∫⁻ x, (min (F x) 1 + c) ∂μ :=
        lintegral_mono fun x =>
          (ENNReal.coe_le_coe.2 (hhi _)).trans_eq (by rw [ENNReal.coe_add, ht])
    _ = ∫⁻ x, min (F x) 1 ∂μ + c * μ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ ∫⁻ x, F x ∂μ + ε := add_le_add (lintegral_mono fun _ => min_le_left _ _) hc.le

/-- `min F 1` is bounded above on a compact set by a real polynomial at small total cost. -/
theorem exists_compact_polynomial_approx :
    ∃ (K : Set ℝ) (p : ℝ[X]), IsCompact K ∧ (∀ x ∈ K, min (F x) 1 ≤ ENNReal.ofReal (p.eval x)) ∧
      ∫⁻ x in K, ENNReal.ofReal (p.eval x) ∂μ + μ Kᶜ ≤ ∫⁻ x, F x ∂μ + ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨c, hc0, hc⟩ := ENNReal.exists_nnreal_pos_mul_lt (measure_ne_top μ Set.univ) hε2.ne'
  obtain ⟨K, g, hK, hKε, hgK⟩ := exists_compact_continuous_eq μ hF hε2
  have hKI := hK.isBounded.subset_Icc_sInf_sSup
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (sInf K) (sSup K)
    (fun x => (g x : ℝ)) (NNReal.continuous_coe.comp g.continuous).continuousOn (c / 2)
    (by positivity)
  have hpK {x} (hx : x ∈ K) := abs_lt.1 (hp x (hKI hx))
  let q := p + C ((c : ℝ) / 2)
  have hlo : ∀ x ∈ K, min (F x) 1 ≤ ENNReal.ofReal (q.eval x) := fun x hx => by
    rw [← hgK x hx, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by simp [q]; linarith [hpK hx])
  have hup : ∀ x ∈ K, ENNReal.ofReal (q.eval x) ≤ min (F x) 1 + c := fun x hx => by
    rw [← hgK x hx, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal (p := c),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by simp [q]; linarith [hpK hx])
  refine ⟨K, q, hK, hlo, ?_⟩
  calc _ ≤ ∫⁻ x in K, (min (F x) 1 + c) ∂μ + ε / 2 :=
        add_le_add (setLIntegral_mono' hK.measurableSet hup) hKε
    _ = ∫⁻ x in K, min (F x) 1 ∂μ + c * μ K + ε / 2 := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ ∫⁻ x, F x ∂μ + ε / 2 + ε / 2 :=
        add_le_add (add_le_add
          ((lintegral_mono fun _ => min_le_left _ _).trans (setLIntegral_le_lintegral _ _))
          ((mul_le_mul' le_rfl (measure_mono (Set.subset_univ K))).trans hc.le)) le_rfl
    _ = ∫⁻ x, F x ∂μ + ε := by rw [add_assoc, ENNReal.add_halves]

/-- `min F 1` is bounded above on a compact set by a rational polynomial at small total cost. -/
theorem exists_compact_ratPolynomial_approx :
    ∃ (K : Set ℝ) (q : ℚ[X]), IsCompact K ∧
      (∀ x ∈ K, min (F x) 1 ≤ ENNReal.ofReal (aeval x q)) ∧
      ∫⁻ x in K, ENNReal.ofReal (aeval x q) ∂μ + μ Kᶜ ≤ ∫⁻ x, F x ∂μ + ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨c, hc0, hc⟩ := ENNReal.exists_nnreal_pos_mul_lt (measure_ne_top μ Set.univ) hε2.ne'
  obtain ⟨K, p, hK, hlo, hint⟩ := exists_compact_polynomial_approx μ hF hε2
  obtain ⟨q, hq⟩ := exists_rat_polynomial_near (sInf K) (sSup K) p
    (show 0 < (c : ℝ) / 4 by positivity)
  obtain ⟨d, hd₁, hd₂⟩ := exists_rat_btwn (show (c : ℝ) / 4 < 3 * c / 4 by
    have : (0 : ℝ) < c := hc0
    linarith)
  have hKI := hK.isBounded.subset_Icc_sInf_sSup
  have hQ {x} (hx : x ∈ K) : p.eval x ≤ aeval x (q + C d) ∧ aeval x (q + C d) ≤ p.eval x + c := by
    have := abs_lt.1 (hq x (hKI hx))
    simp only [map_add, aeval_C, eq_ratCast]
    constructor <;> linarith
  have hup : ∀ x ∈ K, ENNReal.ofReal (aeval x (q + C d)) ≤ ENNReal.ofReal (p.eval x) + c :=
    fun x hx => (ENNReal.ofReal_le_ofReal (hQ hx).2).trans <| by
      rw [← ENNReal.ofReal_coe_nnreal (p := c)]
      exact ENNReal.ofReal_add_le
  refine ⟨K, q + C d, hK, fun x hx => (hlo x hx).trans (ENNReal.ofReal_le_ofReal (hQ hx).1), ?_⟩
  calc _ ≤ ∫⁻ x in K, (ENNReal.ofReal (p.eval x) + c) ∂μ + μ Kᶜ :=
        add_le_add (setLIntegral_mono' hK.measurableSet hup) le_rfl
    _ = ∫⁻ x in K, ENNReal.ofReal (p.eval x) ∂μ + μ Kᶜ + c * μ K := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, add_right_comm]
    _ ≤ ∫⁻ x, F x ∂μ + ε / 2 + ε / 2 :=
        add_le_add hint ((mul_le_mul' le_rfl (measure_mono (Set.subset_univ K))).trans hc.le)
    _ = ∫⁻ x, F x ∂μ + ε := by rw [add_assoc, ENNReal.add_halves]

end approx

section reduced
variable [MeasureTheory.IsFiniteMeasure μ] (hv : e.toVal? = none)
include hv

/-- Lusin's theorem reduces `DistSpec` to continuous credit functions on compact sets. -/
theorem DistSpec_of_DistSpecLusin (hS : DistSpecLusin (GF := GF) E e μ) :
    DistSpec (GF := GF) E e μ :=
  DistSpec_of_local (fun K G => IsCompact K ∧ Continuous G) hv
    (fun _ hF _ hε =>
      have ⟨K, G, hK, hG, hFG, hGint⟩ := exists_compact_continuous_approx μ hF hε
      ⟨K, G, ⟨hK, hG⟩, fun x hx => (hFG x hx).ge, hGint⟩)
    (fun K G ⟨hK, hG⟩ => hS K G hK hG)

/-- Vitali–Carathéodory reduces `DistSpec` to lower semicontinuous credit functions. -/
theorem DistSpec_of_DistSpecLSC (hS : DistSpecLSC (GF := GF) E e μ) :
    DistSpec (GF := GF) E e μ :=
  DistSpec_of_global LowerSemicontinuous hv
    (fun F hF _ hε =>
      have ⟨G, hle, hG, hint⟩ :=
        MeasureTheory.exists_le_lowerSemicontinuous_lintegral_ge μ F hF hε.ne'
      ⟨G, hG, fun x => (min_le_left _ _).trans (hle x), hint⟩)
    hS

/-- Simple-function approximation reduces `DistSpec` to simple credit functions. -/
theorem DistSpec_of_DistSpecSimple (hS : DistSpecSimple (GF := GF) E e μ) :
    DistSpec (GF := GF) E e μ :=
  DistSpec_of_global (fun G => ∃ s : MeasureTheory.SimpleFunc ℝ ℝ≥0∞, ⇑s = G) hv
    (fun _ hF _ hε =>
      have ⟨s, hle, hint⟩ := exists_simpleFunc_approx μ hF hε
      ⟨s, ⟨s, rfl⟩, hle, hint⟩)
    (fun _ ⟨s, hs⟩ => hs ▸ hS s)

/-- Polynomial approximation reduces `DistSpec` to real polynomials on compact subsets of `S`. -/
theorem DistSpec_of_DistSpecPolyOn {S : Set ℝ} (hS : MeasurableSet S) (hμ : μ Sᶜ = 0)
    (hSpec : DistSpecPolyOn (GF := GF) E e μ S) : DistSpec (GF := GF) E e μ :=
  DistSpec_of_local_support hS hμ
    (fun K G => IsCompact K ∧ ∃ p : ℝ[X], G = fun x => ENNReal.ofReal (p.eval x))
    (fun _ _ _ ⟨hK, p, hG⟩ hK' => ⟨hK.inter hK', p, hG⟩) hv
    (fun _ hF _ hε =>
      have ⟨K, p, hK, hle, hint⟩ := exists_compact_polynomial_approx μ hF hε
      ⟨K, _, ⟨hK, p, rfl⟩, hle, hint⟩)
    (fun K _ ⟨hK, p, hG⟩ hKS => hG ▸ hSpec K p hK hKS)

/-- Rational polynomial approximation reduces `DistSpec` to rational polynomials on compact
subsets of `S`. -/
theorem DistSpec_of_DistSpecRatPolyOn {S : Set ℝ} (hS : MeasurableSet S) (hμ : μ Sᶜ = 0)
    (hSpec : DistSpecRatPolyOn (GF := GF) E e μ S) : DistSpec (GF := GF) E e μ :=
  DistSpec_of_local_support hS hμ
    (fun K G => IsCompact K ∧ ∃ q : ℚ[X],
      G = fun x => ENNReal.ofReal (aeval x q))
    (fun _ _ _ ⟨hK, q, hG⟩ hK' => ⟨hK.inter hK', q, hG⟩) hv
    (fun _ hF _ hε =>
      have ⟨K, q, hK, hle, hint⟩ := exists_compact_ratPolynomial_approx μ hF hε
      ⟨K, _, ⟨hK, q, rfl⟩, hle, hint⟩)
    (fun K _ ⟨hK, q, hG⟩ hKS => hG ▸ hSpec K q hK hKS)

/-- Weierstrass reduces `DistSpec` to real polynomials on compact sets. -/
theorem DistSpec_of_DistSpecPoly (hS : DistSpecPoly (GF := GF) E e μ) :
    DistSpec (GF := GF) E e μ :=
  DistSpec_of_DistSpecPolyOn hv .univ (by simp) fun K p hK _ => hS K p hK

/-- `DistSpec` follows from the spec for rational polynomials on compact sets. -/
theorem DistSpec_of_DistSpecRatPoly (hS : DistSpecRatPoly (GF := GF) E e μ) :
    DistSpec (GF := GF) E e μ :=
  DistSpec_of_DistSpecRatPolyOn hv .univ (by simp) fun K q hK _ => hS K q hK

/-- `DistSpec` follows from the spec for smooth credit functions on compact sets. -/
theorem DistSpec_of_DistSpecSmooth (hS : DistSpecSmooth (GF := GF) E e μ) :
    DistSpec (GF := GF) E e μ :=
  DistSpec_of_DistSpecPoly hv fun K p hK => hS K _ hK (by simpa using p.contDiff_aeval (𝕜 := ℝ) _)

/-- The Lusin form is equivalent to `DistSpec`. -/
theorem DistSpecLusin_iff : DistSpecLusin (GF := GF) E e μ ↔ DistSpec (GF := GF) E e μ :=
  ⟨DistSpec_of_DistSpecLusin hv, fun h _ _ hK hF =>
    DistSpecOn_of_DistSpec hK.measurableSet hF.measurable h⟩

/-- The lower semicontinuous form is equivalent to `DistSpec`. -/
theorem DistSpecLSC_iff : DistSpecLSC (GF := GF) E e μ ↔ DistSpec (GF := GF) E e μ :=
  ⟨DistSpec_of_DistSpecLSC hv, fun h G hG => h G hG.measurable⟩

/-- The simple-function form is equivalent to `DistSpec`. -/
theorem DistSpecSimple_iff : DistSpecSimple (GF := GF) E e μ ↔ DistSpec (GF := GF) E e μ :=
  ⟨DistSpec_of_DistSpecSimple hv, fun h s => h s s.measurable⟩

/-- The real-polynomial form is equivalent to `DistSpec`. -/
theorem DistSpecPoly_iff : DistSpecPoly (GF := GF) E e μ ↔ DistSpec (GF := GF) E e μ :=
  ⟨DistSpec_of_DistSpecPoly hv, fun h _ p hK =>
    DistSpecOn_of_DistSpec hK.measurableSet p.continuous.measurable.ennreal_ofReal h⟩

/-- The rational-polynomial form is equivalent to `DistSpec`. -/
theorem DistSpecRatPoly_iff : DistSpecRatPoly (GF := GF) E e μ ↔ DistSpec (GF := GF) E e μ :=
  ⟨DistSpec_of_DistSpecRatPoly hv, fun h _ q hK =>
    DistSpecOn_of_DistSpec hK.measurableSet
      (Polynomial.continuous_aeval q).measurable.ennreal_ofReal h⟩

/-- The smooth form is equivalent to `DistSpec`. -/
theorem DistSpecSmooth_iff : DistSpecSmooth (GF := GF) E e μ ↔ DistSpec (GF := GF) E e μ :=
  ⟨DistSpec_of_DistSpecSmooth hv, fun h _ _ hK hG =>
    DistSpecOn_of_DistSpec hK.measurableSet hG.continuous.measurable.ennreal_ofReal h⟩

/-- The real-polynomial form on subsets of `S` is equivalent to `DistSpec` when `μ Sᶜ = 0`. -/
theorem DistSpecPolyOn_iff {S : Set ℝ} (hS : MeasurableSet S) (hμ : μ Sᶜ = 0) :
    DistSpecPolyOn (GF := GF) E e μ S ↔ DistSpec (GF := GF) E e μ :=
  ⟨DistSpec_of_DistSpecPolyOn hv hS hμ, fun h _ p hK _ =>
    DistSpecOn_of_DistSpec hK.measurableSet p.continuous.measurable.ennreal_ofReal h⟩

/-- The rational-polynomial form on subsets of `S` is equivalent to `DistSpec` when `μ Sᶜ = 0`. -/
theorem DistSpecRatPolyOn_iff {S : Set ℝ} (hS : MeasurableSet S) (hμ : μ Sᶜ = 0) :
    DistSpecRatPolyOn (GF := GF) E e μ S ↔ DistSpec (GF := GF) E e μ :=
  ⟨DistSpec_of_DistSpecRatPolyOn hv hS hμ, fun h _ q hK _ =>
    DistSpecOn_of_DistSpec hK.measurableSet
      (Polynomial.continuous_aeval q).measurable.ennreal_ofReal h⟩

end reduced
