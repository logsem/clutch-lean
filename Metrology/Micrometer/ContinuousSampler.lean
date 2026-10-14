module

public import Metrology.Micrometer.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.CouplingRules
public import Metrology.Micrometer.AppRelRules

@[expose] public section

/-! # Continuous sampler rules -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
open scoped AppGS

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]
variable {ι : Type} [Monoid ι] {Δ : GradedDivergence.{0} ι}

/-! ## The real-literal injection

`urand` steps to `Cfg.uniformReal σ`, the pushforward of `unifUnit` along `r ↦ ⟨#(.real r), σ⟩`. -/

theorem Cfg.measurable_realLit (σ : State rT) :
    Measurable (fun r : rT => (⟨pl(#(.real r)), σ⟩ : Cfg rT)) :=
  Cfg.measurable_iff.mpr ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩

theorem Cfg.measurableEmbedding_realLit (σ : State rT) :
    MeasurableEmbedding (fun r : rT => (⟨pl(#(.real r)), σ⟩ : Cfg rT)) :=
  Cfg.measurableEquivProd.symm.measurableEmbedding.comp
    ((measurableEmbedding_prod_mk_right σ).comp
      (Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding))

theorem Cfg.realLit_image_eq (σ : State rT) :
    {ρ : Cfg rT | ∃ r, ρ = ⟨pl(#(.real r)), σ⟩ ∧ r ∈ LawfulProbLangℝ.unifUnitSupport} =
    (fun r : rT => (⟨pl(#(.real r)), σ⟩ : Cfg rT)) '' LawfulProbLangℝ.unifUnitSupport := by
  ext ρ
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  exact ⟨fun ⟨r, h, hr⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, h.symm, hr⟩⟩

theorem Cfg.measurableSet_realLit_image (σ : State rT) :
    MeasurableSet {ρ : Cfg rT | ∃ r, ρ = ⟨pl(#(.real r)), σ⟩ ∧
      r ∈ LawfulProbLangℝ.unifUnitSupport} := by
  rw [Cfg.realLit_image_eq]
  exact (Cfg.measurableEmbedding_realLit σ).measurableSet_image.mpr
    LawfulProbLangℝ.unifUnitSupportMeasurable

theorem headReducible_urand (σ : State rT) : HeadReducible pl(urand) σ :=
  show Cfg.uniformReal σ ≠ 0 from MeasureTheory.IsProbabilityMeasure.ne_zero _

theorem reducible_urand (σ : State rT) : Reducible pl(urand) σ :=
  reducible_of_headReducible (by is_lc) (headReducible_urand σ)

theorem primStep_urand (σ : State rT) : primStep ⟨pl(urand), σ⟩ = Cfg.uniformReal σ :=
  primStep_eq_headStep
    (Exp.decompItem_none_of_lc_headReducible (by is_lc) (headReducible_urand σ))

theorem Cfg.concentrated_primStep_urand (σ : State rT) :
    Concentrated (primStep ⟨pl(urand), σ⟩)
      {ρ | ∃ r, ρ = ⟨pl(#(.real r)), σ⟩ ∧ r ∈ LawfulProbLangℝ.unifUnitSupport} := by
  rw [primStep_urand σ, Cfg.uniformReal, Cfg.realLit_image_eq]
  exact concentratedOn_map (Cfg.measurable_realLit σ)
    ((Cfg.measurableEmbedding_realLit σ).measurableSet_image.mpr
      LawfulProbLangℝ.unifUnitSupportMeasurable)
    LawfulProbLangℝ.unifUnitIsConcentrated

section Unary
variable {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS rT hlc GF] [GradeGS ι GF]
  [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft]

theorem wp_urand {E : CoPset} {Φ : Val rT → IProp GF} : iprop%
    (▷ ∀ r, ⌜r ∈ LawfulProbLangℝ.unifUnitSupport⌝ -∗ Φ (.real r)) ⊢ wp Δ E pl(urand) Φ := by
  iintro HΦ
  iapply wp_lift_atomic_step_concentrated Exp.urand_toVal?_eq_none
    Cfg.measurableSet_realLit_image Cfg.concentrated_primStep_urand
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro; exact reducible_urand σ₁
  iintro !> %e₂ %σ₂ %⟨r, heq, hr⟩
  cases heq
  imodintro
  simp only [Exp.toVal?_lit]
  iframe Hσ
  iapply HΦ $$ %r %hr

/-! ## Relational coupling of two continuous samplers

Unlike the discrete `unifInt_codensity_bij`, a bijection is not enough here:
`f` must be measure-preserving for `unifUnit`. -/

theorem Cfg.uniformReal_codensity_bij (σ σ' : State rT) (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f
      (LawfulProbLangℝ.unifUnit (T := rT)) (LawfulProbLangℝ.unifUnit (T := rT))) :
    Δ.Codensity 1 0
      {p : Cfg rT × Cfg rT | ∃ r, r ∈ LawfulProbLangℝ.unifUnitSupport ∧
        p.1 = ⟨pl(#(.real r)), σ⟩ ∧ p.2 = ⟨pl(#(.real (f r))), σ'⟩}
      (Cfg.uniformReal σ) (Cfg.uniformReal σ') := by
  have h := (GradedDivergence.codensity_graph (Δ := Δ) LawfulProbLangℝ.unifUnit
    hmp.measurable).concentrated_L LawfulProbLangℝ.unifUnitSupportMeasurable
    LawfulProbLangℝ.unifUnitIsConcentrated
  rw [hmp.map_eq] at h
  exact h.map (fun r _ ⟨hrr', hr⟩ => ⟨r, hr, rfl, hrr' ▸ rfl⟩) (Cfg.measurable_realLit σ)
    (Cfg.measurable_realLit σ')

/-- Exact coupling of two continuous samplers along a measure-preserving `f` (the `tv` instance
of `Cfg.uniformReal_codensity_bij`). -/
theorem Cfg.uniformReal_addCoupl_bij (σ σ' : State rT) (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f
      (LawfulProbLangℝ.unifUnit (T := rT)) (LawfulProbLangℝ.unifUnit (T := rT))) :
    AddCoupl 0
      {p : Cfg rT × Cfg rT | ∃ r, r ∈ LawfulProbLangℝ.unifUnitSupport ∧
        p.1 = ⟨pl(#(.real r)), σ⟩ ∧ p.2 = ⟨pl(#(.real (f r))), σ'⟩}
      (Cfg.uniformReal σ) (Cfg.uniformReal σ') :=
  (Cfg.uniformReal_codensity_bij (Δ := TVDiv.tv.{0}) σ σ' f hmp).addCoupl

theorem wp_couple_urand_urand (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f
      (LawfulProbLangℝ.unifUnit (T := rT)) (LawfulProbLangℝ.unifUnit (T := rT)))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(urand) ∗
    (∀ r, ⌜r ∈ LawfulProbLangℝ.unifUnitSupport⌝ -∗ ⤇ K.fill pl(#(.real (f r))) -∗ Φ (.real r)) ⊢
    wp Δ E pl(urand) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply wp_lift_prim_steps_coupl Exp.urand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree $$ Hs Hj
  subst Heq
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ => ∃ r, r ∈ LawfulProbLangℝ.unifUnitSupport ∧
    c₁ = ⟨pl(#(.real r)), σ₁⟩ ∧ c₂ = ⟨K.fill pl(#(.real (f r))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact reducible_urand σ₁
  isplitr; · ipureintro; exact Reducible.fill K (reducible_urand σ₁')
  isplitr
  · ipureintro
    rw [primStep_urand σ₁, primStep_fill Exp.urand_not_isValue, primStep_urand σ₁']
    exact (Cfg.uniformReal_codensity_bij σ₁ σ₁' f hmp).map_right
      (by rintro a b ⟨r, hr, rfl, rfl⟩; exact ⟨r, hr, rfl, rfl⟩) (Ectx.fillCfg.measurable K)
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨r, hrsupp, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update (e3 := K.fill pl(#(.real (f r)))) $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hε
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %r %hrsupp Hj'

end Unary

/-! ## The relational rule -/

section Relational
variable {hlc : HasLC} {GF : BundledGFunctors} [IR : MicrometerRGS rT hlc GF] [GradeGS ι GF]
  [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft]

theorem refines_couple_urands_lr {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f
      (LawfulProbLangℝ.unifUnit (T := rT)) (LawfulProbLangℝ.unifUnit (T := rT))) : iprop%
    (∀ r, ⌜r ∈ LawfulProbLangℝ.unifUnitSupport⌝ -∗
      refines Δ E (K.fill pl(#(.real r))) (K'.fill pl(#(.real (f r)))) A) ⊢
    refines Δ E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  iintro Hcnt
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K' pl(urand)] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_urand_urand f hmp (K2.comp K') _ _
  iframe Hj
  iintro %r %hrsupp HKres
  isimp only [← Ectx.fill_comp K2 K' pl(#(.real (f r)))] at HKres
  rw [show Exp.ofVal (.real r) = pl(#(.real r)) from rfl]
  iapply Hcnt $$ %r %hrsupp %K2 %ε HKres Hna Herr Hpos

end Relational

end ProbLang
