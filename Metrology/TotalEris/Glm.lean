module

public import Metrology.Iris.ErrorCredits
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Erasable
public import Metrology.ProbLang.Erasure
public import Metrology.ProbLang.CtxStep
public import Metrology.ProbLang.Metatheory
public import Metrology.Iris.Fixpoint
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

/-!
# Graded lifting modality

The error-graded lifting modality `glm'`: erasable steps and credit bumps, then one prim step into
`Z`. (`LiveEris/Glm.lean` has the unrelated vector-credit `glm`.)
-/

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

namespace TotalEris

/-! ## Probability of good lifting -/

/-- The predicate `φ` fails with `μ`-probability at most `ε` (Eris `pgl`, probability of good
lifting). -/
def Pgl {α : Type _} [MeasurableSpace α] (ε : ENNReal) (φ : α → Prop)
    (μ : MeasureTheory.Measure α) : Prop := μ {x | ¬ φ x} ≤ ε

namespace Pgl

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : MeasureTheory.Measure α}

/-- Raising the failure bound `ε` preserves `Pgl`. -/
theorem mono_grading {ε ε' : ENNReal} {φ : α → Prop}
    (hε : ε ≤ ε') (h : Pgl ε φ μ) : Pgl ε' φ μ := h.trans hε

/-- Weakening the predicate preserves `Pgl`. -/
theorem mono_pred {ε : ENNReal} {φ ψ : α → Prop}
    (hφψ : ∀ a, φ a → ψ a) (h : Pgl ε φ μ) : Pgl ε ψ μ := by
  refine .trans (MeasureTheory.measure_mono ?_) h
  intro x hx hxφ; exact hx (hφψ x hxφ)

/-- A measure that gives the complement of `φ` zero mass satisfies `Pgl 0 φ`. -/
theorem zero_of_null {φ : α → Prop} (μ : MeasureTheory.Measure α)
    (Hnull : μ {x | ¬φ x} = 0) : Pgl 0 φ μ :=
  Hnull.le

/-- A measure supported on points satisfying `φ` satisfies `Pgl 0 φ`. -/
theorem zero_possible [MeasurableSingletonClass α]
    (h : IsAtomicSupport μ) : Pgl 0 (fun a => Possible a μ) μ := by
  show μ {x | ¬ Possible x μ} ≤ 0
  have hset : {x : α | ¬ Possible x μ} = {x | μ {x} = 0} := by
    ext x; simp [possible_iff_pos, pos_iff_ne_zero]
  rw [hset]; exact h.le

/-- A measure concentrated on `{x | φ x}` satisfies `Pgl 0 φ`. -/
theorem of_concentrated {φ : α → Prop}
    (h : Concentrated μ {x | φ x}) : Pgl 0 φ μ :=
  h.le

end Pgl

/-! ## Ghost state and the stutter -/

/-- Ghost state for the total Eris weakest precondition: state and error-credit interpretations. -/
class ErisWpGS (GF : BundledGFunctors) where
  hlc : HasLC
  invGS : InvGS_gen hlc GF
  stateInterp : State rT → IProp GF
  errInterp : ENNReal → IProp GF

attribute [reducible, instance] ErisWpGS.invGS

namespace ErisWpGS
variable {GF : BundledGFunctors}

/-- Either the budget `ε` already reaches `1` (vacuous), or `P ε` holds. -/
abbrev execStutter (P : ENNReal → IProp GF) (ε : ENNReal) : IProp GF :=
  iprop(⌜1 ≤ ε⌝ ∨ P ε)

/-- Stuttering at no cost is available for any `ε`. -/
theorem execStutter_free {P : ENNReal → IProp GF} {ε : ENNReal} :
    P ε ⊢ execStutter P ε :=
  or_intro_r

/-- Stuttering may spend one unit of error credit. -/
theorem execStutter_spend {P : ENNReal → IProp GF} {ε : ENNReal} (hε : 1 ≤ ε) :
    ⊢ execStutter P ε :=
  (pure_intro hε).trans or_intro_l

/-- `execStutter` is monotone in the credit budget. -/
theorem execStutter_mono {P Q : ENNReal → IProp GF} {ε ε' : ENNReal} (hε : ε ≤ ε') :
    ((P ε -∗ Q ε') ∗ execStutter P ε) ⊢ execStutter Q ε' := by
  iintro ⟨HM, HS⟩
  icases HS with ⟨%HVac | HP⟩
  · ileft; ipureintro; exact HVac.trans hε
  · iright; iapply HM $$ HP

/-- `execStutter` is monotone in the continuation predicate. -/
theorem execStutter_mono_pred {P Q : ENNReal → IProp GF} {ε : ENNReal} :
    ((P ε -∗ Q ε) ∗ execStutter P ε) ⊢ execStutter Q ε :=
  execStutter_mono le_rfl

variable [ErisWpGS (rT := rT) GF]
variable {e : Exp rT} {σ : State rT} {ε : ENNReal} {Z : Cfg rT → ENNReal → IProp GF}

/-! ## The three step kinds -/

/-- A configuration together with its remaining error budget. -/
abbrev GlmState (rT : Type _) [LawfulProbLangℝ rT] : Type _ := Cfg rT × ENNReal

instance : COFE (GlmState rT) := COFE.ofDiscrete _
instance : OFE.Discrete (GlmState rT) := ⟨id⟩

/-- Take a real program step, splitting the budget `ε` over the outcomes.
`R`: the outcomes kept, failing with probability `≤ ε₁` (`Pgl`); `X₂ ρ`: the budget passed to
outcome `ρ`, with `ε₁ + E[X₂] ≤ ε`; `r`: a uniform bound on `X₂`, mirroring Eris's `glm` (where it
makes the expectation finite); here expectations are `lintegral`s, so it is unused. -/
abbrev glmPrimStep' (e₁ : Exp rT) (σ₁ : State rT) (ε : ENNReal)
    (Z : Cfg rT → ENNReal → IProp GF) : IProp GF :=
  iprop(∃ (R : Cfg rT → Prop) (ε₁ : ENNReal) (X₂ : Cfg rT → ENNReal) (r : ENNReal),
    ⌜Reducible e₁ σ₁⌝ ∗
    ⌜MeasurableSet {ρ | R ρ}⌝ ∗
    ⌜∀ ρ, X₂ ρ ≤ r⌝ ∗
    ⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(primStep ⟨e₁, σ₁⟩)) ≤ ε⌝ ∗
    ⌜Pgl ε₁ R (primStep ⟨e₁, σ₁⟩)⌝ ∗
    (∀ ρ, ⌜R ρ⌝ -∗ |={∅}=> execStutter (Z ρ) (X₂ ρ)))

/-- Advance only the state by an expression-erasable measure `μ`, spending error per outcome.
`R`, `ε₁`, `X₂`, `r` are as in `glmPrimStep'`.
Total adequacy needs the witness `MeasurableSet {σ' | R σ'}` to split the `μ`-mass on `R`. -/
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

/-- `glmPrimStep'` is monotone in its continuation, under the wand. -/
theorem glmPrimStep'_strong_mono {e₁ : Exp rT} {σ₁ : State rT}
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} :
    iprop((∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε') ∗ glmPrimStep' e₁ σ₁ ε Z₁) ⊢ glmPrimStep' e₁ σ₁ ε Z₂ := by
  iintro ⟨HZ, HPrim⟩
  icases HPrim with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
  iexists R, ε₁, X₂, r
  iframe %Hred %HRmeas %Hbnd %Hexp %Hpgl
  iintro %ρ HR
  imod HCont $$ %ρ HR with HS
  imodintro
  iapply execStutter_mono_pred
  iframe HS
  iintro HZ₁
  iapply HZ $$ HZ₁

/-- `glmErasable'` is monotone in its continuation, under the wand. -/
theorem glmErasable'_strong_mono {e₁ : Exp rT} {σ₁ : State rT}
    {Φ Ψ : GlmState rT → IProp GF} :
    iprop((∀ s, Φ s -∗ Ψ s) ∗ glmErasable' e₁ σ₁ ε Φ) ⊢ glmErasable' e₁ σ₁ ε Ψ := by
  iintro ⟨HΦΨ, HEras⟩
  icases HEras with ⟨%μ, %R, %ε₁, %X₂, %r, %Heras, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
  iexists μ, R, ε₁, X₂, r
  iframe %Heras %HRmeas %Hbnd %Hexp %Hpgl
  iintro %σ' %HR
  imod HCont $$ %σ' %HR with HS
  imodintro
  iapply execStutter_mono_pred
  iframe HS
  iintro HΦ
  iapply HΦΨ $$ HΦ

/-- Assume any strictly larger error budget. -/
abbrev glmCreditBump' (ρ : Cfg rT) (ε : ENNReal)
    (Φ : GlmState rT → IProp GF) : IProp GF :=
  iprop(∀ ε', ⌜ε < ε'⌝ -∗ |={∅}=> execStutter (fun ε'' => Φ (ρ, ε'')) ε')

/-- `glmCreditBump'` is monotone in its continuation, under the wand. -/
theorem glmCreditBump'_strong_mono {ρ : Cfg rT}
    {Φ Ψ : GlmState rT → IProp GF} :
    iprop((∀ s, Φ s -∗ Ψ s) ∗ glmCreditBump' ρ ε Φ) ⊢ glmCreditBump' ρ ε Ψ := by
  iintro ⟨HΦΨ, HBump⟩
  iintro %ε' %Hlt
  imod HBump $$ %ε' %Hlt with HS
  imodintro
  iapply execStutter_mono_pred
  iframe HS
  iintro HΦ
  iapply HΦΨ $$ HΦ

/-! ## The modality `glm'` as a least fixpoint -/

/-- One unfolding of `glm'`: a credit bump or an erasable step, which recurse into `Φ`, or one
prim step, which ends in the continuation `Z`. -/
abbrev glmPre' (Z : Cfg rT → ENNReal → IProp GF)
    (Φ : GlmState rT → IProp GF) : GlmState rT → IProp GF :=
  fun ⟨ρ, ε⟩ => iprop(
    glmCreditBump' ρ ε Φ ∨
    glmPrimStep' ρ.expr ρ.state ε Z ∨
    glmErasable' ρ.expr ρ.state ε Φ)

/-- The graded lifting modality: least fixpoint of `glmPre'`. -/
abbrev glm' (e : Exp rT) (σ : State rT) (ε : ENNReal)
    (Z : Cfg rT → ENNReal → IProp GF) : IProp GF :=
  bi_least_fixpoint (glmPre' Z) ((⟨e, σ⟩, ε) : GlmState rT)

/-- `glmPre'` is monotone, so its least fixpoint exists. -/
instance glmPre'_mono {Z : Cfg rT → ENNReal → IProp GF} :
    BIMonoPred (glmPre' Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    obtain ⟨ρ, ε⟩ := s
    icases Hs with ⟨HBump | HPrim | HEras⟩
    · ileft
      iapply glmCreditBump'_strong_mono
      iframe HBump
      iintro %s HΦ
      iapply Hwand $$ HΦ
    · iright; ileft; iexact HPrim
    · iright; iright
      iapply glmErasable'_strong_mono
      iframe HEras
      iintro %s HΦ
      iapply Hwand $$ HΦ
  mono_pred_ne.ne {_ s s'} hd := by
    obtain rfl := OFE.Discrete.discrete hd; exact .of_eq rfl

/-- `glm'` unfolds once through `glmPre'`. -/
theorem glm'_unfold :
    glm' e σ ε Z = glmPre' Z (fun s => glm' s.1.expr s.1.state s.2 Z) ((⟨e, σ⟩, ε) : GlmState rT) :=
  least_fixpoint_unfold _

/-- Strong induction principle: `glm'` implies any `Ψ` closed under `glmPre'`. -/
theorem glm'_strong_ind {Ψ : GlmState rT → IProp GF}
    [NonExpansive Ψ] :
    iprop(□ (∀ s, glmPre' Z (fun s' => iprop(Ψ s' ∧ bi_least_fixpoint (glmPre' Z) s')) s -∗
              Ψ s)) ⊢
      (∀ s, bi_least_fixpoint (glmPre' Z) s -∗ Ψ s) := by
  iintro #HM
  iapply least_fixpoint_ind $$ HM

/-! ## Monotonicity -/

/-- `glm'` is monotone in its continuation `Z`, under the wand. -/
theorem glm'_strong_mono
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} :
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
      icases HF with ⟨HBump | HPrim | HEras⟩
      · ileft
        iapply glmCreditBump'_strong_mono
        iframe HBump
        iintro %s HP
        iapply HP $$ Hwand
      · iright; ileft
        iapply glmPrimStep'_strong_mono
        iframe HPrim
        iintro %ρ' %ε' HC
        iapply Hwand $$ HC
      · iright; iright
        iapply glmErasable'_strong_mono
        iframe HEras
        iintro %s HP
        iapply HP $$ Hwand
    · iexact HG
  iapply HΨ $$ HZ

/-- `glm'` is monotone in the credit budget. -/
theorem glm'_mono_grading
    {ε ε' : ENNReal}
    (hε : ε ≤ ε') :
    glm' e σ ε Z ⊢ glm' e σ ε' Z := by
  iintro HG
  ihave HG' := least_fixpoint_unfold_mp (glmPre' Z) $$ HG
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  icases HG' with ⟨HBump | HPrim | HEras⟩
  · ileft
    iintro %ε'' %Hlt
    iapply HBump $$ %ε'' %(hε.trans_lt Hlt)
  · iright; ileft
    icases HPrim with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
    replace Hexp := Hexp.trans hε
    iexists R, ε₁, X₂, r
    iframe %Hred %HRmeas %Hbnd %Hexp %Hpgl
    iexact HCont
  · iright; iright
    icases HEras with ⟨%μ, %R, %ε₁, %X₂, %r, %Heras, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
    replace Hexp := Hexp.trans hε
    iexists μ, R, ε₁, X₂, r
    iframe %Heras %HRmeas %Hbnd %Hexp %Hpgl
    iexact HCont

/-- `glm'` is monotone in the credit budget, under the wand. -/
theorem glm'_strong_mono_grading {ε ε' : ENNReal}
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} (hε : ε ≤ ε') :
    iprop((∀ ρ ε'', Z₁ ρ ε'' -∗ Z₂ ρ ε'') ∗ glm' e σ ε Z₁) ⊢
      glm' e σ ε' Z₂ := by
  iintro ⟨HZ, HG⟩
  iapply glm'_mono_grading hε
  iapply glm'_strong_mono
  iframe

/-- `glm'` is monotone in its continuation `Z`. -/
theorem glm'_mono_pred
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} :
    iprop((□ (∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε')) ∗ glm' e σ ε Z₁) ⊢
      glm' e σ ε Z₂ := by
  iintro ⟨#HZ, HG⟩
  iapply (least_fixpoint_strong_mono (glmPre' Z₁) (glmPre' Z₂)) $$ [] HG
  iintro !> %Φ %s HF
  obtain ⟨ρ, ε⟩ := s
  icases HF with ⟨HBump | HPrim | HEras⟩
  · ileft; iexact HBump
  · iright; ileft
    iapply glmPrimStep'_strong_mono
    iframe HPrim
    iintro %ρ' %ε' HC
    iapply HZ $$ HC
  · iright; iright; iexact HEras

/-! ## Bind -/

/-- Bind rule: run `e` under `glm'` with the continuation `Z` composed with the context `K`. -/
theorem glm'_bind
    {K : Ectx rT} :
    glm' e σ ε (fun ρ ε' => Z ⟨K.fill ρ.expr, ρ.state⟩ ε') ⊢
      glm' (K.fill e) σ ε Z := by
  iintro HG
  classical
  -- Induct on `glm' e` (least fixpoint); a prim step of `e` lifts to one of `K.fill e` via
  -- `primStep_fill`, pushing `R` and `X₂` forward along `K.fillCfg` (`X₂'` is `0` off its image).
  let Kinv : Exp rT → Option (Exp rT) := Function.partialInv K.fill
  have Kinv_left : ∀ e', Kinv (K.fill e') = some e' :=
    Function.partialInv_left (Ectx.fill_injective K)
  let Z' : Cfg rT → ENNReal → IProp GF := fun ρ ε' => Z ⟨K.fill ρ.expr, ρ.state⟩ ε'
  let Φ : GlmState rT → IProp GF :=
    fun s => bi_least_fixpoint (glmPre' Z) ((⟨K.fill s.1.expr, s.1.state⟩, s.2) : GlmState rT)
  let : NonExpansive Φ := nonExpansive_of_discrete_leibniz Φ
  ihave HΦ : iprop(Φ ((⟨e, σ⟩, ε) : GlmState rT)) $$ [HG]
  · iapply (least_fixpoint_iter (F := glmPre' Z'))
    · iintro !> %s HF
      obtain ⟨ρ, ε'⟩ := s
      iapply least_fixpoint_unfold_mpr (glmPre' Z)
      icases HF with ⟨HBump | HPrim | HEras⟩
      · ileft; iexact HBump
      · iright; ileft
        icases HPrim with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
        have Hsv : ¬ ρ.expr.isValue := val_stuck Hred
        set R' : Cfg rT → Prop := fun ρ' => ∃ ρ'', ρ' = K.fillCfg ρ'' ∧ R ρ'' with hR'def
        set X₂' : Cfg rT → ENNReal :=
          fun ρ' => (Kinv ρ'.expr).elim 0 (fun e' => X₂ ⟨e', ρ'.state⟩) with hX₂'def
        have hR'set : {ρ' | R' ρ'} = K.fillCfg '' {ρ'' | R ρ''} := by
          ext ρ'
          simp only [hR'def, Set.mem_ofPred_eq, Set.mem_image]
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
        have hexp' : ε₁ + (∫⁻ a, X₂' a ∂ primStep ⟨K.fill ρ.expr, ρ.state⟩) ≤ ε' := by
          rw [primStep_fill Hsv]
          refine le_trans ?_ Hexp
          gcongr ε₁ + ?_
          refine (MeasureTheory.lintegral_map_le _ (Ectx.fillCfg.measurable K).aemeasurable).trans
            (Eq.le ?_)
          exact MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun a => hX₂'fill a)
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
      · iright; iright; iexact HEras
    · iexact HG
  iexact HΦ

/-! ## Introduction rules for `glm'` -/

/-- A `glm'` goal follows from a primitive-step obligation. -/
theorem glm'_prim_step :
    glmPrimStep' e σ ε Z ⊢ glm' e σ ε Z := by
  iintro HPrim
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  iright
  ileft
  iexact HPrim

/-- A `glm'` goal follows from an erasable-step obligation. -/
theorem glm'_erasable_step :
    glmErasable' e σ ε (fun s => glm' s.1.expr s.1.state s.2 Z) ⊢
      glm' e σ ε Z := by
  iintro HES
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  iright
  iright
  iexact HES

/-- Thin-air credit rule: a client may always assume a strictly larger error budget. -/
theorem glm'_credit_bump :
    glmCreditBump' ⟨e, σ⟩ ε (fun s => glm' s.1.expr s.1.state s.2 Z) ⊢
      glm' e σ ε Z := by
  iintro HBump
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  ileft
  iexact HBump

end ErisWpGS

end TotalEris
end ProbLang
