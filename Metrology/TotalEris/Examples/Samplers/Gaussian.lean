module

public import Metrology.TotalEris.DistributionAdequacy
public import Metrology.TotalEris.Examples.Samplers.Gauss
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Probability.Distributions.Gaussian.Real
import Metrology.Iris.LocalBI

@[expose] public section

/-! # The standard Gaussian sampler

`Gauss` flips a `FairCoin` to sign `G2`'s half-normal sample `x + k`. The symmetrised law is
`gaussianReal 0 1` (`gauss_credit_eq_gaussianReal`).
-/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.Examples
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
local bi IProp GF

section credit

/-- Heads (`true`) negates. A two-branch function rather than an `if`, so that
`GaussSign_true` / `GaussSign_false` are syntactic rewrites. -/
def GaussSign (y : ℝ) : Bool → ℝ
  | true => -y
  | false => y

@[simp] theorem GaussSign_true (y : ℝ) : GaussSign y true = -y := rfl

@[simp] theorem GaussSign_false (y : ℝ) : GaussSign y false = y := rfl

def GaussCredit (F : ℝ → ℝ≥0∞) : ℕ → ℝ → ℝ≥0∞ :=
  fun k r => FairCoinCreditV (fun b => F (GaussSign (r + (k : ℝ)) b))

def GaussCreditV (F : ℝ → ℝ≥0∞) : ℝ≥0∞ := G2CreditV (GaussCredit F)

theorem GaussCreditV_eq (F : ℝ → ℝ≥0∞) : GaussCreditV F = G2CreditV (GaussCredit F) := rfl

theorem GaussCredit_eq (F : ℝ → ℝ≥0∞) (k : ℕ) (r : ℝ) :
    GaussCredit F k r = FairCoinCreditV (fun b => F (GaussSign (r + (k : ℝ)) b)) := rfl

theorem measurable_gaussCredit {F : ℝ → ℝ≥0∞} (hFm : Measurable F) (k : ℕ) :
    Measurable (GaussCredit F k) := by
  show Measurable fun r : ℝ =>
    ENNReal.ofReal (1 / 2) * F (-(r + (k : ℝ))) + ENNReal.ofReal (1 / 2) * F (r + (k : ℝ))
  exact ((hFm.comp ((measurable_id.add_const _).neg)).const_mul _).add
    ((hFm.comp (measurable_id.add_const _)).const_mul _)

end credit

section specification

theorem twp_Gauss (E : CoPset) (F : ℝ → ℝ≥0∞) (hFm : Measurable F) :
    ⊢ ↯ (GaussCreditV F) -∗
      tglWp E pl(&Gauss #())
        (fun v : Val ℝ => iprop(∃ y : ℝ, ⌜v.1 = .lit (.real y)⌝ ∗ ↯ (F y))) := by
  iintro Hε
  twp_pure
  twp_bind pl(&G2 #())
  iapply (tglWp_wand)
  isplitl [Hε]
  · iapply (twp_G2 E (GaussCredit F) (measurable_gaussCredit hFm))
    iapply (ErrorCredit.ext (GaussCreditV_eq F))
    iexact Hε
  iintro %p ⟨%k, %r, -, %hpair, Hcr⟩
  obtain ⟨wp, _⟩ := p
  dsimp only at hpair; subst hpair
  -- `twp_pures` would run on into the coin's body, so take exactly the six steps up to it.
  iterate 6 twp_pure
  isimp only [FairCoin_openRec, FairCoin_closeRec, ProbLang.realAdd_real,
    ProbLang.realOfInt_real, Int.cast_natCast]
  twp_bind pl(&FairCoin #())
  iapply (tglWp_wand)
  isplitl [Hcr]
  · iapply (twp_FairCoin E (fun b => F (GaussSign (r + (k : ℝ)) b)))
    iapply (ErrorCredit.ext (GaussCredit_eq F k r))
    iexact Hcr
  iintro %vb ⟨%b, %hb, Hcb⟩
  obtain ⟨wb, _⟩ := vb
  dsimp only at hb; subst hb
  cases b with
  | true =>
    have hcb : (fun b : Bool => F (GaussSign (r + (k : ℝ)) b)) true
        = F (-(r + (k : ℝ))) := rfl
    twp_pures
    twp_value
    imodintro
    iexists (-(r + (k : ℝ)))
    rw [← hcb]
    iframe Hcb
    ipureintro
    rfl
  | false =>
    have hcb : (fun b : Bool => F (GaussSign (r + (k : ℝ)) b)) false
        = F (r + (k : ℝ)) := rfl
    twp_pures
    twp_value
    imodintro
    iexists (r + (k : ℝ))
    rw [← hcb]
    iframe Hcb
    ipureintro
    rfl

end specification

section targetMeasure

/-! ## The half-normal law -/

open MeasureTheory

theorem measurable_g2pdf (k : ℕ) : Measurable (G2pdf k) := by unfold G2pdf; fun_prop

/-- The law of `G2`'s sampled real `x + k`. -/
def halfNormal : Measure ℝ :=
  Measure.sum fun k : ℕ =>
    ((LawfulProbLangℝ.unifUnit).withDensity (G2pdf k)).map (fun x => x + (k : ℝ))

instance : IsProbabilityMeasure halfNormal := by
  constructor
  rw [halfNormal, Measure.sum_apply _ MeasurableSet.univ, ← G2pdf_total]
  exact tsum_congr fun k => by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

theorem halfNormal_credit_eq (F : ℝ → ℝ≥0∞) (hFm : Measurable F) :
    ∫⁻ y, F y ∂halfNormal = G2CreditV (fun k r => F (r + k)) := by
  rw [halfNormal, lintegral_sum_measure, G2CreditV]
  exact tsum_congr fun k => by
    rw [lintegral_map hFm (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul _ (measurable_g2pdf k) (by fun_prop)]
    simp only [Pi.mul_apply]

end targetMeasure

section halfNormal

/-! ## `halfNormal` in density form -/

open MeasureTheory

def halfDens (y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-y ^ 2 / 2) / Norm2)

theorem measurable_halfDens : Measurable halfDens := by unfold halfDens; fun_prop

theorem G2pdf_eq_halfDens (k : ℕ) (x : ℝ) : G2pdf k x = halfDens (x + (k : ℝ)) := rfl

theorem iUnion_Ioc_nat : (⋃ k : ℕ, Set.Ioc (k : ℝ) ((k : ℝ) + 1)) = Set.Ioi (0 : ℝ) := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro ⟨k, hk, -⟩
    exact lt_of_le_of_lt (Nat.cast_nonneg k) hk
  · intro hy
    have hceil : 1 ≤ ⌈y⌉₊ := Nat.one_le_ceil_iff.mpr hy
    have hcast : ((⌈y⌉₊ - 1 : ℕ) : ℝ) = (⌈y⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hceil, Nat.cast_one]
    refine ⟨⌈y⌉₊ - 1, ?_, ?_⟩
    · have hlt : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy.le
      rw [hcast]; linarith
    · have := Nat.le_ceil y
      rw [hcast]; linarith

/-- Half-open pieces are what tile `(0,∞)` disjointly. -/
theorem unifUnit_eq_restrict_Ioc :
    (LawfulProbLangℝ.unifUnit) = volume.restrict (Set.Ioc (0 : ℝ) 1) := by
  show volume.restrict (Set.Icc (0 : ℝ) 1) = _
  exact (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm

theorem halfNormal_eq_withDensity :
    halfNormal = (volume.restrict (Set.Ioi (0 : ℝ))).withDensity halfDens := by
  refine Measure.ext fun S hS => ?_
  rw [halfNormal, Measure.sum_apply _ hS, withDensity_apply _ hS,
    Measure.restrict_restrict hS]
  have hpiece : ∀ k : ℕ,
      (((LawfulProbLangℝ.unifUnit).withDensity (G2pdf k)).map (fun x => x + (k : ℝ))) S
        = ∫⁻ y in S ∩ Set.Ioc (k : ℝ) ((k : ℝ) + 1), halfDens y ∂volume := by
    intro k
    have hpreS : MeasurableSet ((fun x : ℝ => x + (k : ℝ)) ⁻¹' S) :=
      (measurable_id.add_const _) hS
    have hmp : MeasurePreserving (fun x : ℝ => x + (k : ℝ)) volume volume :=
      measurePreserving_add_right volume (k : ℝ)
    have hemb : MeasurableEmbedding (fun x : ℝ => x + (k : ℝ)) :=
      (Homeomorph.addRight (k : ℝ)).measurableEmbedding
    have hpre : (fun x : ℝ => x + (k : ℝ)) ⁻¹' (S ∩ Set.Ioc (k : ℝ) ((k : ℝ) + 1))
        = (fun x : ℝ => x + (k : ℝ)) ⁻¹' S ∩ Set.Ioc (0 : ℝ) 1 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc]
      constructor <;> rintro ⟨hxS, h1, h2⟩ <;> exact ⟨hxS, by linarith, by linarith⟩
    rw [Measure.map_apply (by fun_prop) hS, withDensity_apply _ hpreS,
      unifUnit_eq_restrict_Ioc, Measure.restrict_restrict hpreS]
    simp only [G2pdf_eq_halfDens]
    rw [← hpre, hmp.setLIntegral_comp_preimage_emb hemb halfDens]
  rw [tsum_congr hpiece]
  have hdisj : Pairwise (Function.onFun Disjoint
      fun k : ℕ => S ∩ Set.Ioc (k : ℝ) ((k : ℝ) + 1)) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨-, hi1, hi2⟩ ⟨-, hj1, hj2⟩
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      linarith
    · have : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      linarith
  rw [← lintegral_iUnion (fun k => hS.inter measurableSet_Ioc) hdisj,
    ← Set.inter_iUnion, iUnion_Ioc_nat]

theorem integral_Ioi_exp_eq_Norm2 :
    (∫ y in Set.Ioi (0 : ℝ), Real.exp (-y ^ 2 / 2)) = Norm2 := by
  have hint : IntegrableOn (fun y : ℝ => Real.exp (-y ^ 2 / 2)) (Set.Ioi 0) volume := by
    have h := integrableOn_Ioi_exp_neg_mul_sq_iff (b := 1 / 2).mpr (by norm_num)
    exact (integrableOn_congr_fun (fun y _ => Real.exp_eq_exp.mpr (by ring))
      measurableSet_Ioi).mp h
  have hmass : ∫⁻ y in Set.Ioi (0 : ℝ), halfDens y ∂volume = 1 := by
    have h := (measure_univ (μ := halfNormal))
    rw [halfNormal_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at h
    exact h
  have hofReal : ENNReal.ofReal (∫ y in Set.Ioi (0 : ℝ), Real.exp (-y ^ 2 / 2) / Norm2) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint.div_const _)
      (ae_restrict_of_forall_mem measurableSet_Ioi
        fun y _ => div_nonneg (Real.exp_pos _).le Norm2_pos.le)]
    exact hmass
  rw [integral_div] at hofReal
  exact (div_eq_one_iff_eq Norm2_pos.ne').mp (ENNReal.ofReal_eq_one.mp hofReal)

theorem Norm2_eq : Norm2 = Real.sqrt (2 * Real.pi) / 2 := by
  rw [← integral_Ioi_exp_eq_Norm2]
  have hcongr : (∫ y in Set.Ioi (0 : ℝ), Real.exp (-y ^ 2 / 2))
      = ∫ y in Set.Ioi (0 : ℝ), Real.exp (-(1 / 2 : ℝ) * y ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun y _ => Real.exp_eq_exp.mpr (by ring)
  rw [hcongr, integral_gaussian_Ioi]
  congr 2
  rw [div_div_eq_mul_div, mul_comm]
  norm_num

end halfNormal

section standardGaussian

/-! ## The symmetrised law is `gaussianReal 0 1` -/

open MeasureTheory ProbabilityTheory

theorem halfDens_eq_two_mul_gaussianPDF (y : ℝ) :
    halfDens y = 2 * gaussianPDF 0 1 y := by
  have hpi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hreal : Real.exp (-y ^ 2 / 2) / Norm2 = 2 * gaussianPDFReal 0 1 y := by
    rw [Norm2_eq, gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [div_div_eq_mul_div]
    field_simp
  rw [halfDens, hreal, gaussianPDF, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by norm_num)]

theorem gaussianPDF_neg (y : ℝ) : gaussianPDF 0 1 (-y) = gaussianPDF 0 1 y := by
  rw [gaussianPDF, gaussianPDF, gaussianPDFReal, gaussianPDFReal]
  congr 2
  rw [Real.exp_eq_exp.mpr (by ring : -(-y - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))
    = -(y - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))]

theorem ofReal_half_mul_two : ENNReal.ofReal (1 / 2) * 2 = 1 := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem gaussianPDF_eq_half_mul_halfDens (y : ℝ) :
    gaussianPDF 0 1 y = ENNReal.ofReal (1 / 2) * halfDens y := by
  rw [halfDens_eq_two_mul_gaussianPDF, ← mul_assoc, ofReal_half_mul_two, one_mul]

theorem lintegral_halfNormal (F : ℝ → ℝ≥0∞) (hFm : Measurable F) :
    ∫⁻ y, F y ∂halfNormal = ∫⁻ y in Set.Ioi (0 : ℝ), halfDens y * F y ∂volume := by
  rw [halfNormal_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ measurable_halfDens hFm]
  rfl

theorem gaussianReal_lintegral_split (F : ℝ → ℝ≥0∞) (hFm : Measurable F) :
    ∫⁻ y, F y ∂(gaussianReal 0 1)
      = ENNReal.ofReal (1 / 2) * (∫⁻ y, F (-y) ∂halfNormal)
        + ENNReal.ofReal (1 / 2) * ∫⁻ y, F y ∂halfNormal := by
  have hFneg : Measurable fun y : ℝ => F (-y) := hFm.comp measurable_neg
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hFm]
  show ∫⁻ y, gaussianPDF 0 1 y * F y ∂volume = _
  have hIic : ∫⁻ y in Set.Iic (0 : ℝ), gaussianPDF 0 1 y * F y ∂volume
      = ∫⁻ y in Set.Iio (0 : ℝ), gaussianPDF 0 1 y * F y ∂volume :=
    setLIntegral_congr Iio_ae_eq_Iic.symm
  have hsplit : ∫⁻ y, gaussianPDF 0 1 y * F y ∂volume
      = (∫⁻ y in Set.Ioi (0 : ℝ), gaussianPDF 0 1 y * F y ∂volume)
        + ∫⁻ y in Set.Iio (0 : ℝ), gaussianPDF 0 1 y * F y ∂volume := by
    rw [← hIic, ← Set.compl_Ioi]
    exact (lintegral_add_compl _ measurableSet_Ioi).symm
  have hneg : ∫⁻ y in Set.Iio (0 : ℝ), gaussianPDF 0 1 y * F y ∂volume
      = ∫⁻ y in Set.Ioi (0 : ℝ), gaussianPDF 0 1 y * F (-y) ∂volume := by
    have hmp : MeasurePreserving (fun y : ℝ => -y) volume volume :=
      Measure.measurePreserving_neg volume
    have hemb : MeasurableEmbedding (fun y : ℝ => -y) := (Homeomorph.neg ℝ).measurableEmbedding
    have hpre : (fun y : ℝ => -y) ⁻¹' Set.Ioi (0 : ℝ) = Set.Iio 0 := by
      ext y; simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, neg_pos]
    have h := hmp.setLIntegral_comp_preimage_emb hemb
      (fun z => gaussianPDF 0 1 z * F (-z)) (Set.Ioi 0)
    rw [hpre] at h
    simp only [neg_neg, gaussianPDF_neg] at h
    exact h
  have hhalf : ∀ G : ℝ → ℝ≥0∞, Measurable G →
      ∫⁻ y in Set.Ioi (0 : ℝ), gaussianPDF 0 1 y * G y ∂volume
        = ENNReal.ofReal (1 / 2) * ∫⁻ y, G y ∂halfNormal := by
    intro G hG
    rw [lintegral_halfNormal G hG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show gaussianPDF 0 1 y * G y = ENNReal.ofReal (1 / 2) * (halfDens y * G y)
    rw [gaussianPDF_eq_half_mul_halfDens, mul_assoc]
  rw [hsplit, hneg, hhalf F hFm, hhalf (fun y => F (-y)) hFneg, add_comm]

theorem gauss_credit_eq_gaussianReal (F : ℝ → ℝ≥0∞) (hFm : Measurable F) :
    ∫⁻ y, F y ∂(gaussianReal 0 1) = GaussCreditV F := by
  have hm1 : Measurable fun y : ℝ => ENNReal.ofReal (1 / 2) * F (-y) :=
    (hFm.comp measurable_neg).const_mul _
  have hcredit := halfNormal_credit_eq
    (fun y => ENNReal.ofReal (1 / 2) * F (-y) + ENNReal.ofReal (1 / 2) * F y)
    (hm1.add (hFm.const_mul _))
  have hGC : GaussCredit F = fun (k : ℕ) (r : ℝ) =>
      ENNReal.ofReal (1 / 2) * F (-(r + (k : ℝ))) + ENNReal.ofReal (1 / 2) * F (r + (k : ℝ)) := rfl
  rw [gaussianReal_lintegral_split F hFm, GaussCreditV, hGC, ← hcredit,
    lintegral_add_left hm1,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end standardGaussian

end

end Examples
end TotalEris
end ProbLang
