module

public import Metrology.TotalEris.TotalAdequacy
public import Metrology.TotalEris.ErrorRules
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.Invariants

/-!
# Distribution adequacy for TotalEris

A distribution spec `↯(∫⁻ F dμ) ⊢ twp e {{ v. ↯(F (gExp v)) }}` forces `e` to be distributed as `μ`.
`gExp` need not be an object-language operation: the Gaussian returns a pair `(x, k)` and samples `x + k`.
-/

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode OFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris

variable {GF : BundledGFunctors}

/-! ## General distribution adequacy, parameterised by a real extraction `gExp` -/

section General

variable (gExp : Exp ℝ → ℝ)

/-- Configurations that terminated at a value `v` with `gExp v.fst ∈ S`: the set inside `Tgl`. -/
def RSet' (S : Set ℝ) : Set (Cfg ℝ) :=
  {ρ : Cfg ℝ | ∃ v : Val ℝ, ρ.expr = Exp.ofVal v ∧ gExp v.fst ∈ S}

open MeasureTheory in
def IsDistSpec' (e : Exp ℝ) (μ : Measure ℝ) : Prop :=
  ∀ (F : ℝ → ℝ≥0∞), Measurable F → (∀ x, F x ≤ 1) →
    ∀ [ErisGS ℝ .hasNoLC GF], iprop(↯ (∫⁻ y, F y ∂μ)) ⊢@{IProp GF}
      tglWp ⊤ e (fun (v : Val ℝ) => iprop(↯ (F (gExp v.fst))))

variable {gExp}

theorem measurableSet_gExp_mem (hgExp : Measurable gExp) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet {v : Val ℝ | gExp v.fst ∈ S} :=
  Val.fst.measurable (hgExp hS)

theorem measurableSet_RSet' (hgExp : Measurable gExp) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (RSet' gExp S) :=
  measurableSet_TglCfgSet (measurableSet_gExp_mem hgExp hS)

theorem RSet'_union (A B : Set ℝ) : RSet' gExp (A ∪ B) = RSet' gExp A ∪ RSet' gExp B := by
  ext ρ
  simp only [RSet', Set.mem_ofPred_eq, Set.mem_union]
  grind

theorem RSet'_eq_preimage (S : Set ℝ) :
    RSet' gExp S = (fun ρ : Cfg ℝ => gExp ρ.expr) ⁻¹' S ∩ RSet' gExp Set.univ := by
  ext ρ
  simp only [RSet', Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ, and_true]
  constructor
  · rintro ⟨v, he, hr⟩
    exact ⟨by rw [he]; exact hr, v, he⟩
  · rintro ⟨hmem, v, he⟩
    exact ⟨v, he, by rw [he] at hmem; exact hmem⟩

open MeasureTheory in
/-- `IsDistSpec'` at `F = 𝟙_{Sᶜ}`: the residual credit is `↯1` off `S`, so the postcondition is pure. -/
theorem ray_pure_wp' (e : Exp ℝ) (μ : Measure ℝ)
    (hspec : IsDistSpec' (GF := GF) gExp e μ) {S : Set ℝ} (hS : MeasurableSet S) :
    ∀ [ErisGS ℝ .hasNoLC GF], iprop(↯ (μ Sᶜ)) ⊢@{IProp GF}
      tglWp ⊤ e (fun (v : Val ℝ) => iprop(⌜gExp v.fst ∈ S⌝)) := by
  intro _
  iintro Hε
  iapply (ErisWpGS.tglWp_mono
    (Φ := fun (v : Val ℝ) => iprop(↯ (Sᶜ.indicator (fun _ => 1) (gExp v.fst)))) ?weak)
  case weak =>
    intro v
    iintro Hcr
    by_cases hr : gExp v.fst ∈ S
    · ipureintro; exact hr
    · iexfalso
      iapply ErrorCredit.contradict $$ Hcr
      simp [Set.indicator_of_mem (show gExp v.fst ∈ Sᶜ from hr)]
  iapply (hspec (Sᶜ.indicator (fun _ => 1)) (measurable_const.indicator hS.compl) ?le1)
  case le1 => intro x; by_cases hx : x ∈ Sᶜ <;> simp [Set.indicator, hx]
  rw [lintegral_indicator_const hS.compl, one_mul]
  iexact Hε

open MeasureTheory in
/-- The CDF of `gExp (result)` is pinned to that of `μ` by the lower bounds on `S` and `Sᶜ`. -/
theorem twp_dist_adequacy' [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF]
    (hgExp : Measurable gExp) (e : Exp ℝ) (σ : State ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hspec : IsDistSpec' (GF := GF) gExp e μ) :
    (limExec ⟨e, σ⟩).map (fun ρ => gExp ρ.expr) = μ := by
  set ν := limExec ⟨e, σ⟩
  have hmg : Measurable (fun ρ : Cfg ℝ => gExp ρ.expr) := hgExp.comp Cfg.measurable_expr
  have hUniv_le : ν Set.univ ≤ 1 := limExec_leq_mass (fun n => execN_univ_le_one n ⟨e, σ⟩)
  have hlower : ∀ S, MeasurableSet S → μ S ≤ ν (RSet' gExp S) := by
    intro S hS
    have htgl : 1 - μ Sᶜ ≤ ν (RSet' gExp S) :=
      twp_tgl (measurableSet_gExp_mem hgExp hS) (ray_pure_wp' e μ hspec hS)
    rwa [← prob_compl_eq_one_sub hS.compl, compl_compl] at htgl
  have hRSetUniv1 : ν (RSet' gExp Set.univ) = 1 := by
    refine le_antisymm ((measure_mono (Set.subset_univ _)).trans hUniv_le) ?_
    simpa using hlower Set.univ MeasurableSet.univ
  have hpin : ∀ S, MeasurableSet S → ν (RSet' gExp S) = μ S := by
    intro S hS
    have hdisj : Disjoint (RSet' gExp S) (RSet' gExp Sᶜ) := by
      rw [Set.disjoint_left]
      rintro ρ ⟨v, he, hs⟩ ⟨v', he', hs'⟩
      exact (show gExp ρ.expr ∈ Sᶜ by rw [he']; exact hs') (by rw [he]; exact hs)
    have hsum : ν (RSet' gExp S) + ν (RSet' gExp Sᶜ) = 1 := by
      rw [← measure_union hdisj (measurableSet_RSet' hgExp hS.compl), ← RSet'_union,
        Set.union_compl_self, hRSetUniv1]
    have hcompl_ne_top : ν (RSet' gExp Sᶜ) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top ((measure_mono (Set.subset_univ _)).trans hUniv_le)
    refine le_antisymm ((ENNReal.add_le_add_iff_right hcompl_ne_top).mp ?_) (hlower S hS)
    calc ν (RSet' gExp S) + ν (RSet' gExp Sᶜ) = μ S + μ Sᶜ := by rw [hsum, prob_add_prob_compl hS]
      _ ≤ μ S + ν (RSet' gExp Sᶜ) := by gcongr; exact hlower Sᶜ hS.compl
  have hprob : IsProbabilityMeasure ν := by
    refine ⟨le_antisymm hUniv_le ?_⟩
    calc (1 : ℝ≥0∞) = ν (RSet' gExp Set.univ) := hRSetUniv1.symm
      _ ≤ ν Set.univ := measure_mono (Set.subset_univ _)
  have hnull : ν (RSet' gExp Set.univ)ᶜ = 0 := by
    rw [measure_compl (measurableSet_RSet' hgExp MeasurableSet.univ) (measure_ne_top _ _),
      measure_univ, hRSetUniv1, tsub_self]
  have hIic : ∀ b : ℝ, (ν.map (fun ρ => gExp ρ.expr)) (Set.Iic b) = μ (Set.Iic b) := by
    intro b
    rw [Measure.map_apply hmg measurableSet_Iic, ← measure_inter_conull hnull,
      ← RSet'_eq_preimage]
    exact hpin (Set.Iic b) measurableSet_Iic
  have : IsProbabilityMeasure (ν.map (fun ρ => gExp ρ.expr)) := inferInstance
  exact Measure.ext_of_Iic _ _ hIic

end General

/-! ## Bare-real special case -/

def realEmb : ℝ → Exp ℝ := fun r => Exp.lit (.real r)

open MeasureTheory in
theorem measurableEmbedding_realEmb : MeasurableEmbedding realEmb :=
  Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding

/-- The payload of a real literal; junk `0` elsewhere. -/
noncomputable def realOfExp : Exp ℝ → ℝ := Function.extend realEmb id (fun _ => 0)

open MeasureTheory in
theorem measurable_realOfExp : Measurable realOfExp :=
  measurableEmbedding_realEmb.measurable_extend measurable_id measurable_const

@[simp]
theorem realOfExp_real (r : ℝ) : realOfExp (Exp.lit (.real r)) = r := by
  show Function.extend realEmb id (fun _ => 0) (realEmb r) = r
  rw [measurableEmbedding_realEmb.injective.extend_apply]; rfl

open MeasureTheory in
theorem twp_dist_adequacy [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF]
    (e : Exp ℝ) (σ : State ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hspec : IsDistSpec' (GF := GF) realOfExp e μ) :
    (limExec ⟨e, σ⟩).map (fun ρ => realOfExp ρ.expr) = μ :=
  twp_dist_adequacy' measurable_realOfExp e σ μ hspec

end TotalEris
end ProbLang
