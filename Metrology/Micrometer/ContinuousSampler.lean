module

public import Metrology.Micrometer.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.CouplingRules
public import Metrology.Micrometer.AppRelRules

/-! # Continuous sampler rules

Program rules for `urand` (`wp_urand`) and its coupling along a measure-preserving map
(`wp_couple_urand_urand`, `refines_couple_urands_lr`). -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting
open scoped AppGS

namespace ProbLang

open LawfulProbLangℝ

variable {rT : Type} [LawfulProbLangℝ rT]
variable {B : Type} {L : GradedLifting.{0} B}

/-! ## The real-literal injection

`urand` steps to `Cfg.uniformReal σ`, the pushforward of `unifUnit` along `r ↦ ⟨#r, σ⟩`. -/

/-- Pairing a real literal with the state `σ` is measurable. -/
theorem Cfg.measurable_realLit (σ : State rT) :
    Measurable (fun r : rT => (⟨pl(#real r), σ⟩ : Cfg rT)) :=
  Cfg.measurable_iff.mpr ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩

/-- Pairing a real literal with the state `σ` is a measurable embedding. -/
theorem Cfg.measurableEmbedding_realLit (σ : State rT) :
    MeasurableEmbedding (fun r : rT => (⟨pl(#real r), σ⟩ : Cfg rT)) :=
  Cfg.measurableEquivProd.symm.measurableEmbedding.comp
    ((measurableEmbedding_prod_mk_right σ).comp
      (Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding))

/-- The configurations `⟨#r, σ⟩` with `r` in the support are the image of the support. -/
theorem Cfg.realLit_image_eq (σ : State rT) :
    {ρ : Cfg rT | ∃ r, ρ = ⟨pl(#real r), σ⟩ ∧ r ∈ unifUnitSupport} =
    (fun r : rT => (⟨pl(#real r), σ⟩ : Cfg rT)) '' unifUnitSupport := by
  ext
  simp [and_comm, eq_comm]

/-- The configurations `⟨#r, σ⟩` with `r` in the support form a measurable set. -/
theorem Cfg.measurableSet_realLit_image (σ : State rT) :
    MeasurableSet {ρ : Cfg rT | ∃ r, ρ = ⟨pl(#real r), σ⟩ ∧ r ∈ unifUnitSupport} := by
  rw [Cfg.realLit_image_eq]
  exact (Cfg.measurableEmbedding_realLit σ).measurableSet_image.mpr unifUnitSupportMeasurable

/-! ## Stepping `urand` -/

/-- `urand` head-reduces in every state. -/
theorem headReducible_urand (σ : State rT) : HeadReducible pl(urand) σ :=
  show Cfg.uniformReal σ ≠ 0 from MeasureTheory.IsProbabilityMeasure.ne_zero _

/-- `urand` reduces in every state. -/
theorem reducible_urand (σ : State rT) : Reducible pl(urand) σ :=
  reducible_of_headReducible (by is_lc) (headReducible_urand σ)

/-- One primitive step of `urand` is `Cfg.uniformReal σ`. -/
theorem primStep_urand (σ : State rT) : primStep ⟨pl(urand), σ⟩ = Cfg.uniformReal σ :=
  primStep_eq_headStep
    (Exp.decompItem_none_of_lc_headReducible (by is_lc) (headReducible_urand σ))

/-- The step of `urand` is concentrated on real literals from the support of `unifUnit`. -/
theorem Cfg.concentrated_primStep_urand (σ : State rT) :
    Concentrated (primStep ⟨pl(urand), σ⟩)
      {ρ | ∃ r, ρ = ⟨pl(#real r), σ⟩ ∧ r ∈ unifUnitSupport} := by
  rw [primStep_urand σ, Cfg.uniformReal, Cfg.realLit_image_eq]
  exact Concentrated.map (Cfg.measurable_realLit σ)
    ((Cfg.measurableEmbedding_realLit σ).measurableSet_image.mpr unifUnitSupportMeasurable)
    unifUnitIsConcentrated

/-! ## Relational coupling of two continuous samplers

Unlike the discrete `unifInt_rel_bij`, a bijection is not enough here:
`f` must be measure-preserving for `unifUnit`. -/

/-- Exact coupling of two continuous samplers along a measure-preserving `f`, for any lawful
reflexive `L`. -/
theorem Cfg.uniformReal_rel_bij [Zero B] [Add B] [Preorder B] [OrderTop B]
    [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] (σ σ' : State rT) (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f unifUnit unifUnit) :
    L.Rel 0
      (fun c₁ c₂ : Cfg rT => ∃ r, r ∈ unifUnitSupport ∧
        c₁ = ⟨pl(#real r), σ⟩ ∧ c₂ = ⟨pl(#real (f r)), σ'⟩)
      (Cfg.uniformReal σ) (Cfg.uniformReal σ') := by
  have h := (rel_graph (L := L) unifUnit hmp.measurable).restrict
    unifUnitSupportMeasurable unifUnitIsConcentrated
  rw [hmp.map_eq] at h
  exact h.map (fun r _ ⟨hrr', hr⟩ => ⟨r, hr, rfl, hrr' ▸ rfl⟩) (Cfg.measurable_realLit σ)
    (Cfg.measurable_realLit σ')

/-- Exact coupling of two continuous samplers along a measure-preserving `f` (the `tv` instance
of `Cfg.uniformReal_rel_bij`). -/
theorem Cfg.uniformReal_addCoupl_bij (σ σ' : State rT) (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f unifUnit unifUnit) :
    AddCoupl 0
      {p : Cfg rT × Cfg rT | ∃ r, r ∈ unifUnitSupport ∧
        p.1 = ⟨pl(#real r), σ⟩ ∧ p.2 = ⟨pl(#real (f r)), σ'⟩}
      (Cfg.uniformReal σ) (Cfg.uniformReal σ') :=
  (Cfg.uniformReal_rel_bij σ σ' f hmp).addCoupl

/-! ## Program rules -/

section Rules
variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSingletonClass rT]

section Unary
variable [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind]

/-- A program `urand` returns some `r` in the support of `unifUnit`, after a `▷`. -/
theorem wp_urand {E : CoPset} {Φ : Val rT → IProp GF} : iprop%
    (▷ ∀ r, ⌜r ∈ unifUnitSupport⌝ -∗ Φ (.real r)) ⊢ wp L E pl(urand) Φ := by
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

/-- Couple `urand ~ K[urand]` along a measure-preserving `f`, at no cost. -/
theorem wp_couple_urand_urand (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f unifUnit unifUnit)
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(urand) ∗
    (∀ r, ⌜r ∈ unifUnitSupport⌝ -∗ ⤇ K.fill pl(#real (f r)) -∗ Φ (.real r)) ⊢
    wp L E pl(urand) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply wp_lift_prim_steps_coupl Exp.urand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ => ∃ r, r ∈ unifUnitSupport ∧
    c₁ = ⟨pl(#real r), σ₁⟩ ∧ c₂ = ⟨K.fill pl(#real (f r)), σ₁'⟩
  iexists R, 0, b
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact reducible_urand σ₁
  isplitr; · ipureintro; exact Reducible.fill K (reducible_urand σ₁')
  isplitr
  · ipureintro
    rw [primStep_urand σ₁, primStep_fill Exp.urand_not_isValue, primStep_urand σ₁']
    exact (Cfg.uniformReal_rel_bij σ₁ σ₁' f hmp).map_right
      (by rintro _ _ ⟨r, hr, rfl, rfl⟩; exact ⟨r, hr, rfl, rfl⟩) (Ectx.fillCfg.measurable K)
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨r, hrsupp, heq1, heq2⟩
  cases heq1
  cases heq2
  iintro !> !>
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hb
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %r %hrsupp Hj'

end Unary

/-! ## The relational rule -/

section Relational
variable [MicrometerRGS rT hlc GF] [BudgetCreditGS B GF] [L.IsLawful] [L.IsReflexive]
  [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind]

/-- Relational form of `wp_couple_urand_urand`: couple the two `urand`s along a measure-preserving
`f`. -/
theorem refines_couple_urands_lr {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f unifUnit unifUnit) : iprop%
    (∀ r, ⌜r ∈ unifUnitSupport⌝ -∗
      refines L E (K.fill pl(#real r)) (K'.fill pl(#real (f r))) A) ⊢
    refines L E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  unfold refines
  iintro Hcnt %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K' pl(urand)] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_urand_urand f hmp (K2.comp K') _ _
  iframe Hj
  iintro %r %hrsupp HKres
  isimp only [← Ectx.fill_comp K2 K' pl(#real (f r))] at HKres
  rw [show Exp.ofVal (.real r) = pl(#real r) from rfl]
  iapply Hcnt $$ %r %hrsupp %K2 %b HKres Hna Herr Hpos

end Relational

end Rules

end ProbLang
