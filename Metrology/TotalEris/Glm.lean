module

public import Metrology.Iris.ErrorCredits
public import Metrology.Couplings.AdditiveCouplings
public import Metrology.Couplings.Couplings
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Erasable
public import Metrology.ProbLang.Erasure
public import Metrology.ProbLang.CtxStep
public import Metrology.ProbLang.Metatheory
public import Metrology.Iris.Fixpoint
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

namespace TotalEris

/-! # Graded lifting modality -/

/-- A graded lift of a predicate.

Given a predicate `φ` on a type `α`, `Pgl ε φ μ` says that `φ` is invalidated with
probability at most `ε` with respect to `μ`. -/
def Pgl {α : Type _} [MeasurableSpace α] (ε : ENNReal) (φ : α → Prop)
  (μ : MeasureTheory.Measure α) : Prop := μ {x | ¬ φ x} ≤ ε

namespace Pgl

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]

theorem mono_grading {ε ε' : ENNReal} {φ : α → Prop} {μ : MeasureTheory.Measure α}
    (hε : ε ≤ ε') (h : Pgl ε φ μ) : Pgl ε' φ μ := h.trans hε

theorem mono_pred {ε : ENNReal} {φ ψ : α → Prop} {μ : MeasureTheory.Measure α}
    (hφψ : ∀ a, φ a → ψ a) (h : Pgl ε φ μ) : Pgl ε ψ μ := by
  refine .trans (MeasureTheory.measure_mono ?_) h
  intro x hx hxφ; exact hx (hφψ x hxφ)

theorem zero_of_null {φ : α → Prop} (μ : MeasureTheory.Measure α)
    (Hnull : μ {x | ¬φ x} = 0) : Pgl 0 φ μ :=
  Hnull.le

theorem zero_possible [MeasurableSingletonClass α] {μ : MeasureTheory.Measure α}
    (h : IsAtomicSupport μ) : Pgl 0 (fun a => Possible a μ) μ := by
  show μ {x | ¬ Possible x μ} ≤ 0
  have hset : {x : α | ¬ Possible x μ} = {x | μ {x} = 0} := by
    ext x; simp [possible_iff_pos, pos_iff_ne_zero]
  rw [hset]; exact h.le

theorem of_concentrated {μ : MeasureTheory.Measure α} {φ : α → Prop}
    (h : Concentrated μ {x | φ x}) : Pgl 0 φ μ :=
  h.le

end Pgl

class ErisWpGS (GF : BundledGFunctors) where
  hlc : HasLC
  invGS : InvGS_gen hlc GF
  stateInterp : State rT → IProp GF
  errInterp : ENNReal → IProp GF

attribute [reducible, instance] ErisWpGS.invGS

namespace ErisWpGS
variable {GF : BundledGFunctors}

abbrev execStutter (P : ENNReal → IProp GF) (ε : ENNReal) : IProp GF :=
  iprop(⌜1 ≤ ε⌝ ∨ P ε)

theorem execStutter_free {P : ENNReal → IProp GF} {ε : ENNReal} :
    P ε ⊢ execStutter P ε :=
  or_intro_r

theorem execStutter_spend {P : ENNReal → IProp GF} {ε : ENNReal} (hε : 1 ≤ ε) :
    ⊢ execStutter P ε :=
  (pure_intro hε).trans or_intro_l

theorem execStutter_mono {P Q : ENNReal → IProp GF} {ε ε' : ENNReal} (hε : ε ≤ ε') :
    ((P ε -∗ Q ε') ∗ execStutter P ε) ⊢ execStutter Q ε' := by
  iintro ⟨HM, HS⟩
  icases HS with ⟨%HVac | HP⟩
  · ileft; ipureintro; exact HVac.trans hε
  · iright; iapply HM $$ HP

theorem execStutter_mono_pred {P Q : ENNReal → IProp GF} {ε : ENNReal} :
    ((P ε -∗ Q ε) ∗ execStutter P ε) ⊢ execStutter Q ε :=
  execStutter_mono le_rfl

variable [ErisWpGS (rT := rT) GF]

abbrev GlmState (rT : Type _) [LawfulProbLangℝ rT] : Type _ := Cfg rT × ENNReal

instance : COFE (GlmState rT) := COFE.ofDiscrete _
instance : OFE.Discrete (GlmState rT) := ⟨id⟩

abbrev glmPrimStep' (e₁ : Exp rT) (σ₁ : State rT) (ε : ENNReal)
    (Z : Cfg rT → ENNReal → IProp GF) : IProp GF :=
  iprop(∃ (R : Cfg rT → Prop) (ε₁ : ENNReal) (X₂ : Cfg rT → ENNReal) (r : ENNReal),
    ⌜Reducible e₁ σ₁⌝ ∗
    ⌜MeasurableSet {ρ | R ρ}⌝ ∗
    ⌜∀ ρ, X₂ ρ ≤ r⌝ ∗
    ⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(primStep ⟨e₁, σ₁⟩)) ≤ ε⌝ ∗
    ⌜Pgl ε₁ R (primStep ⟨e₁, σ₁⟩)⌝ ∗
    (∀ ρ, ⌜R ρ⌝ -∗ |={∅}=> execStutter (Z ρ) (X₂ ρ)))

/-- **Erasability step**: advance the *state* by any expression-erasable measure `μ`
(`ErasableExpr μ σ₁`), spending error per outcome. Tape presampling is a consumer that
instantiates `μ := tapePresample σ₁ α` and discharges `ErasableExpr` via
`ErasableExpr.tapePresample`. The measurability witness `⌜MeasurableSet {σ' | R σ'}⌝`
for the support predicate `R` is needed by total adequacy, to split the `μ`-mass on
`{R}` against its complement. The expression `e₁` is unchanged: an erasable step only
moves the state. -/
abbrev glmErasable' (e₁ : Exp rT) (σ₁ : State rT) (ε : ENNReal)
    (Φ : GlmState rT → IProp GF) : IProp GF :=
  iprop(∃ (μ : MeasureTheory.Measure (State rT)) (R : State rT → Prop) (ε₁ : ENNReal)
      (X₂ : State rT → ENNReal) (r : ENNReal),
    ⌜ErasableExpr μ σ₁⌝ ∗
    ⌜MeasurableSet {σ' | R σ'}⌝ ∗
    ⌜∀ σ', X₂ σ' ≤ r⌝ ∗
    ⌜ε₁ + (∫⁻ σ', X₂ σ' ∂μ) ≤ ε⌝ ∗
    ⌜Pgl ε₁ R μ⌝ ∗
    (∀ σ', ⌜R σ'⌝ -∗ |={∅}=> execStutter (fun ε'' => Φ (⟨e₁, σ'⟩, ε'')) (X₂ σ')))

theorem glmPrimStep'_strong_mono {e₁ : Exp rT} {σ₁ : State rT} {ε : ENNReal}
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} :
    iprop((∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε') ∗ glmPrimStep' e₁ σ₁ ε Z₁)
      ⊢ glmPrimStep' e₁ σ₁ ε Z₂ := by
  iintro ⟨HZ, HPS⟩
  icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
  iexists R, ε₁, X₂, r
  iframe %Hred %HRmeas %Hbnd %Hexp %Hpgl
  iintro %ρ HR
  imod HCont $$ %ρ HR with HS
  imodintro
  iapply execStutter_mono_pred
  iframe HS
  iintro HZ₁
  iapply HZ $$ HZ₁

theorem glmErasable'_strong_mono {e₁ : Exp rT} {σ₁ : State rT} {ε : ENNReal}
    {Φ Ψ : GlmState rT → IProp GF} :
    iprop((∀ s, Φ s -∗ Ψ s) ∗ glmErasable' e₁ σ₁ ε Φ)
      ⊢ glmErasable' e₁ σ₁ ε Ψ := by
  iintro ⟨HΦΨ, HSS⟩
  icases HSS with ⟨%μ, %R, %ε₁, %X₂, %r, %Heras, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
  iexists μ, R, ε₁, X₂, r
  iframe %Heras %HRmeas %Hbnd %Hexp %Hpgl
  iintro %σ' %HR
  imod HCont $$ %σ' %HR with HS
  imodintro
  iapply execStutter_mono_pred
  iframe HS
  iintro HΦ
  iapply HΦΨ $$ HΦ

abbrev glmCreditBump' (ρ : Cfg rT) (ε : ENNReal)
    (Φ : GlmState rT → IProp GF) : IProp GF :=
  iprop(∀ ε', ⌜ε < ε'⌝ -∗ |={∅}=> execStutter (fun ε'' => Φ (ρ, ε'')) ε')

theorem glmCreditBump'_strong_mono {ρ : Cfg rT} {ε : ENNReal}
    {Φ Ψ : GlmState rT → IProp GF} :
    iprop((∀ s, Φ s -∗ Ψ s) ∗ glmCreditBump' ρ ε Φ)
      ⊢ glmCreditBump' ρ ε Ψ := by
  iintro ⟨HΦΨ, HOT⟩
  iintro %ε' %Hlt
  imod HOT $$ %ε' %Hlt with HS
  imodintro
  iapply execStutter_mono_pred
  iframe HS
  iintro HΦ
  iapply HΦΨ $$ HΦ

abbrev glmPre' (Z : Cfg rT → ENNReal → IProp GF)
    (Φ : GlmState rT → IProp GF) : GlmState rT → IProp GF :=
  fun ⟨ρ, ε⟩ => iprop(
    glmCreditBump' ρ ε Φ ∨
    glmPrimStep' ρ.expr ρ.state ε Z ∨
    glmErasable' ρ.expr ρ.state ε Φ)

abbrev glm' (e : Exp rT) (σ : State rT) (ε : ENNReal)
    (Z : Cfg rT → ENNReal → IProp GF) : IProp GF :=
  bi_least_fixpoint (glmPre' Z) ((⟨e, σ⟩, ε) : GlmState rT)

instance glmPre'_mono {Z : Cfg rT → ENNReal → IProp GF} :
    BIMonoPred (glmPre' Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    obtain ⟨ρ, ε⟩ := s
    icases Hs with ⟨HOT | HPS | HSS⟩
    · ileft
      iapply glmCreditBump'_strong_mono
      iframe HOT
      iintro %s HΦ
      iapply Hwand $$ HΦ
    · iright; ileft; iexact HPS
    · iright; iright
      iapply glmErasable'_strong_mono
      iframe HSS
      iintro %s HΦ
      iapply Hwand $$ HΦ
  mono_pred_ne.ne {_ s s'} hd := by
    obtain rfl := eq_of_dist_discrete_leibniz hd; exact .of_eq rfl

theorem glm'_unfold {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z : Cfg rT → ENNReal → IProp GF} :
    glm' e σ ε Z =
      glmPre' Z
        (fun s => glm' s.1.expr s.1.state s.2 Z)
        ((⟨e, σ⟩, ε) : GlmState rT) :=
  least_fixpoint_unfold _

theorem glm'_strong_ind {Z : Cfg rT → ENNReal → IProp GF} {Ψ : GlmState rT → IProp GF}
    [NonExpansive Ψ] :
    iprop(□ (∀ s, glmPre' Z
              (fun s' => iprop(Ψ s' ∧ bi_least_fixpoint (glmPre' Z) s')) s
              -∗ Ψ s)) ⊢
      (∀ s, bi_least_fixpoint (glmPre' Z) s -∗ Ψ s) := by
  iintro #HM
  iapply least_fixpoint_ind $$ HM

theorem glm'_strong_mono
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} :
    iprop((∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε') ∗ glm' e σ ε Z₁) ⊢
      glm' e σ ε Z₂ := by
  iintro ⟨HZ, HG⟩
  let Ψ : GlmState rT → IProp GF := fun s => iprop(
    (∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε') -∗ bi_least_fixpoint (glmPre' Z₂) s)
  let : NonExpansive Ψ := nonExpansive_of_discrete_leibniz Ψ
  ihave HΨ : iprop(Ψ ((⟨e, σ⟩, ε) : GlmState rT)) $$ [HG]
  · iapply (least_fixpoint_iter (F := glmPre' Z₁))
    · iintro !> %s HF Hwand
      iapply least_fixpoint_unfold_mpr (glmPre' Z₂)
      obtain ⟨ρ, ε⟩ := s
      icases HF with ⟨HOT | HPS | HSS⟩
      · ileft
        iapply glmCreditBump'_strong_mono
        iframe HOT
        iintro %s HP
        iapply HP $$ Hwand
      · iright; ileft
        iapply glmPrimStep'_strong_mono
        iframe HPS
        iintro %ρ' %ε' HC
        iapply Hwand $$ HC
      · iright; iright
        iapply glmErasable'_strong_mono
        iframe HSS
        iintro %s HP
        iapply HP $$ Hwand
    · iexact HG
  iapply HΨ $$ HZ

theorem glm'_mono_grading
    {e : Exp rT} {σ : State rT} {ε ε' : ENNReal} {Z : Cfg rT → ENNReal → IProp GF}
    (hε : ε ≤ ε') :
    glm' e σ ε Z ⊢ glm' e σ ε' Z := by
  iintro HG
  ihave HG' := least_fixpoint_unfold_mp (glmPre' Z) $$ HG
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  icases HG' with ⟨HOT | HPS | HSS⟩
  · ileft
    iintro %ε'' %Hlt
    iapply HOT $$ %ε'' %(hε.trans_lt Hlt)
  · iright; ileft
    icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
    have Hexp' := Hexp.trans hε
    iexists R, ε₁, X₂, r
    iframe %Hred %HRmeas %Hbnd %Hexp' %Hpgl
    iexact HCont
  · iright; iright
    icases HSS with ⟨%μ, %R, %ε₁, %X₂, %r, %Heras, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
    have Hexp' := Hexp.trans hε
    iexists μ, R, ε₁, X₂, r
    iframe %Heras %HRmeas %Hbnd %Hexp' %Hpgl
    iexact HCont

theorem glm'_strong_mono_grading {e : Exp rT} {σ : State rT} {ε ε' : ENNReal}
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} (hε : ε ≤ ε') :
    iprop((∀ ρ ε'', Z₁ ρ ε'' -∗ Z₂ ρ ε'') ∗ glm' e σ ε Z₁) ⊢
      glm' e σ ε' Z₂ := by
  iintro ⟨HZ, HG⟩
  iapply glm'_mono_grading hε
  iapply glm'_strong_mono
  iframe

theorem glm'_mono_pred {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} :
    iprop((□ (∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε')) ∗ glm' e σ ε Z₁) ⊢
      glm' e σ ε Z₂ := by
  iintro ⟨#HZ, HG⟩
  iapply (least_fixpoint_strong_mono (glmPre' Z₁) (glmPre' Z₂)) $$ [] HG
  iintro !> %Φ %s HF
  obtain ⟨ρ, ε⟩ := s
  icases HF with ⟨HOT | HPS | HSS⟩
  · ileft; iexact HOT
  · iright; ileft
    iapply glmPrimStep'_strong_mono
    iframe HPS
    iintro %ρ' %ε' HC
    iapply HZ $$ HC
  · iright; iright; iexact HSS

theorem glm'_bind
    {K : Ectx rT} {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z : Cfg rT → ENNReal → IProp GF} :
    glm' e σ ε (fun ρ ε' => Z ⟨K.fill ρ.expr, ρ.state⟩ ε') ⊢
      glm' (K.fill e) σ ε Z := by
  iintro HG
  classical
  let Kinv : Exp rT → Option (Exp rT) := Function.partialInv K.fill
  have Kinv_left : ∀ e', Kinv (K.fill e') = some e' :=
    Function.partialInv_left (Ectx.fill_injective K)
  let Z' : Cfg rT → ENNReal → IProp GF :=
    fun ρ ε' => Z ⟨K.fill ρ.expr, ρ.state⟩ ε'
  let Φ : GlmState rT → IProp GF :=
    fun s => bi_least_fixpoint (glmPre' Z) ((⟨K.fill s.1.expr, s.1.state⟩, s.2) : GlmState rT)
  let : NonExpansive Φ := nonExpansive_of_discrete_leibniz Φ
  ihave HΦ : iprop(Φ ((⟨e, σ⟩, ε) : GlmState rT)) $$ [HG]
  · iapply (least_fixpoint_iter (F := glmPre' Z'))
    · iintro !> %s HF
      obtain ⟨ρ, ε'⟩ := s
      iapply least_fixpoint_unfold_mpr (glmPre' Z)
      icases HF with ⟨HOT | HPS | HSS⟩
      · ileft; iexact HOT
      · iright; ileft
        icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
        have Hsv : ¬ ρ.expr.isValue := val_stuck Hred
        set R' : Cfg rT → Prop := fun ρ' => ∃ ρ'', ρ' = K.fillCfg ρ'' ∧ R ρ'' with hR'def
        set X₂' : Cfg rT → ENNReal :=
          fun ρ' => (Kinv ρ'.expr).elim 0 (fun e' => X₂ ⟨e', ρ'.state⟩) with hX₂'def
        have hR'set : {ρ' | R' ρ'} = K.fillCfg '' {ρ'' | R ρ''} := by
          ext ρ'; simp only [hR'def, Set.mem_ofPred_eq, Set.mem_image]
          exact ⟨fun ⟨ρ'', heq, hR⟩ => ⟨ρ'', hR, heq.symm⟩,
            fun ⟨ρ'', hR, heq⟩ => ⟨ρ'', heq.symm, hR⟩⟩
        have hR'meas : MeasurableSet {ρ' | R' ρ'} :=
          hR'set ▸ Ectx.measurableSet_fillCfg_image K HRmeas
        have hX₂'fill : ∀ a : Cfg rT, X₂' (K.fillCfg a) = X₂ a := fun a => by
          simp only [hX₂'def, Ectx.fillCfg, Kinv_left, Option.elim]
        have hredK : Reducible (K.fill ρ.expr) ρ.state := Hred.fill K
        have hbnd' : ∀ ρ', X₂' ρ' ≤ r := by
          intro ρ'
          cases h : Kinv ρ'.expr with
          | none => simp [hX₂'def, h, Option.elim]
          | some e' => simp only [hX₂'def, h, Option.elim]; exact Hbnd ⟨e', ρ'.state⟩
        have hexp' :
            ε₁ + (∫⁻ a, X₂' a ∂ primStep ⟨K.fill ρ.expr, ρ.state⟩) ≤ ε' := by
          rw [primStep_fill Hsv]
          refine le_trans ?_ Hexp
          gcongr ε₁ + ?_
          refine (MeasureTheory.lintegral_map_le _ (Ectx.fillCfg.measurable K).aemeasurable).trans
            (Eq.le ?_)
          exact MeasureTheory.lintegral_congr_ae
            (Filter.Eventually.of_forall fun a => hX₂'fill a)
        have hpgl' : Pgl ε₁ R' (primStep ⟨K.fill ρ.expr, ρ.state⟩) := by
          show primStep ⟨K.fill ρ.expr, ρ.state⟩ {x | ¬ R' x} ≤ ε₁
          have hcompl : MeasurableSet {x : Cfg rT | ¬ R' x} := hR'meas.compl
          rw [primStep_fill Hsv,
            MeasureTheory.Measure.map_apply (by measurability) hcompl]
          refine (Eq.le ?_).trans Hpgl
          congr 1
          ext a
          simp only [hR'def, Set.mem_preimage, Set.mem_ofPred_eq, not_exists, not_and]
          refine ⟨fun h hR => h a rfl hR, fun hR ρ₃ hEq hR₃ => ?_⟩
          exact hR (Ectx.fillCfg_injective K hEq.symm ▸ hR₃)
        iexists R', ε₁, X₂', r
        iframe %hredK %hR'meas %hbnd' %hexp' %hpgl'
        iintro %ρ' ⟨%ρ'', %rfl, %HR⟩
        imod HCont $$ %ρ'' %HR with HS
        imodintro
        simp only [hX₂'def, Ectx.fillCfg, Kinv_left, Option.elim]
        iexact HS
      · iright; iright; iexact HSS
    · iexact HG
  iexact HΦ

/-! ## Introduction rules for `glm'` -/

theorem glm'_prim_step {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z : Cfg rT → ENNReal → IProp GF} :
    glmPrimStep' e σ ε Z ⊢ glm' e σ ε Z := by
  iintro HPS
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  iright; ileft
  iexact HPS

theorem glm'_erasable_step {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z : Cfg rT → ENNReal → IProp GF} :
    glmErasable' e σ ε (fun s => glm' s.1.expr s.1.state s.2 Z) ⊢
      glm' e σ ε Z := by
  iintro HES
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  iright; iright
  iexact HES

/-- Thin-air credit rule: a client may always assume a strictly larger error budget. -/
theorem glm'_credit_bump {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z : Cfg rT → ENNReal → IProp GF} :
    glmCreditBump' ⟨e, σ⟩ ε (fun s => glm' s.1.expr s.1.state s.2 Z) ⊢
      glm' e σ ε Z := by
  iintro HOT
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  ileft
  iexact HOT

end ErisWpGS

end TotalEris
end ProbLang
