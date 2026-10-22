module

public import Metrology.LiveEris.Credits
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.CtxStep
public import Metrology.ProbLang.Metatheory
public import Metrology.Iris.Fixpoint
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

@[expose] public section

noncomputable section

/-!
# Graded lifting modality over credit vectors

`glm` is the one-step lifting modality of LiveEris. It is TotalEris's `glm'` with the scalar error
budget replaced by a credit vector `ι → ℝ≥0∞`: every coordinate is averaged over the same outcome
distribution, failure mass is charged to every coordinate, and a branch is vacuous once every
coordinate reaches 1.
-/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang
namespace LiveEris

variable {rT : Type _} [LawfulProbLangℝ rT]

/-- `Pgl ε φ μ`: `φ` fails with probability at most `ε` under `μ`. -/
def Pgl {α : Type _} [MeasurableSpace α] (ε : ℝ≥0∞) (φ : α → Prop)
    (μ : MeasureTheory.Measure α) : Prop :=
  μ {x | ¬ φ x} ≤ ε

variable {ι : Type}

namespace CreditVec

/-- Every coordinate of a credit vector has reached 1: the branch may fail. -/
def Saturated (c : ι → ℝ≥0∞) : Prop := ∀ i, 1 ≤ c i

/-- `c'` is a strict bump of `c`: larger in every coordinate, strictly so where `c` is finite. -/
def Bump (c c' : ι → ℝ≥0∞) : Prop := c ≤ c' ∧ ∀ i, c i < ∞ → c i < c' i

/-- Failure mass `p`, charged to every coordinate. -/
def charge (p : ℝ≥0∞) : ι → ℝ≥0∞ := fun _ => p

/-- Coordinatewise expectation of a credit-vector-valued function. -/
def expect {α : Type _} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (X : α → ι → ℝ≥0∞) : ι → ℝ≥0∞ :=
  fun i => ∫⁻ a, X a i ∂μ

theorem Saturated.mono {c c' : ι → ℝ≥0∞} (h : c ≤ c') (hs : Saturated c) : Saturated c' :=
  fun i => (hs i).trans (h i)

theorem Bump.of_le {c c' c'' : ι → ℝ≥0∞} (h : c ≤ c') (hb : Bump c' c'') : Bump c c'' :=
  ⟨h.trans hb.1, fun i hi => by
    rcases (le_top : c' i ≤ ∞).lt_or_eq with h' | h'
    · exact (h i).trans_lt (hb.2 i h')
    · exact hi.trans_le (h' ▸ hb.1 i)⟩

end CreditVec

open CreditVec

class LiveWpGS (rT : outParam (Type _)) [LawfulProbLangℝ rT] (ι : outParam Type)
    (GF : BundledGFunctors) where
  hlc : HasLC
  invGS : InvGS_gen hlc GF
  stateInterp : State rT → IProp GF
  creditInterp : (ι → ℝ≥0∞) → IProp GF

attribute [reducible, instance] LiveWpGS.invGS

namespace LiveWpGS

variable {GF : BundledGFunctors}

/-- `P` at credit `c`, or nothing at all if `c` is saturated. -/
abbrev execStutter (P : (ι → ℝ≥0∞) → IProp GF) (c : ι → ℝ≥0∞) : IProp GF :=
  iprop(⌜Saturated c⌝ ∨ P c)

theorem execStutter_mono {P Q : (ι → ℝ≥0∞) → IProp GF} {c c' : ι → ℝ≥0∞} (hc : c ≤ c') :
    ((P c -∗ Q c') ∗ execStutter P c) ⊢ execStutter Q c' := by
  iintro ⟨HM, %HVac | HP⟩
  · ileft; ipureintro; exact HVac.mono hc
  · iright; iapply HM $$ HP

theorem execStutter_mono_pred {P Q : (ι → ℝ≥0∞) → IProp GF} {c : ι → ℝ≥0∞} :
    ((P c -∗ Q c) ∗ execStutter P c) ⊢ execStutter Q c :=
  execStutter_mono le_rfl

variable [LiveWpGS rT ι GF]

abbrev GlmState (rT : Type _) [LawfulProbLangℝ rT] (ι : Type) : Type _ := Cfg rT × (ι → ℝ≥0∞)

instance : COFE (GlmState rT ι) := COFE.ofDiscrete _
instance : OFE.Discrete (GlmState rT ι) := ⟨id⟩

/-- **Credit bump**: the client may assume any strict bump of its budget. -/
abbrev glmCreditBump (ρ : Cfg rT) (c : ι → ℝ≥0∞)
    (Φ : GlmState rT ι → IProp GF) : IProp GF :=
  iprop(∀ c', ⌜Bump c c'⌝ -∗ |={∅}=> execStutter (fun c'' => Φ (ρ, c'')) c')

theorem glmCreditBump_strong_mono {ρ : Cfg rT} {c : ι → ℝ≥0∞}
    {Φ Ψ : GlmState rT ι → IProp GF} :
    iprop((∀ s, Φ s -∗ Ψ s) ∗ glmCreditBump ρ c Φ) ⊢ glmCreditBump ρ c Ψ := by
  iintro ⟨HΦΨ, HOT⟩ %c' %Hlt
  imod HOT $$ %c' %Hlt with HS
  imodintro
  iapply execStutter_mono_pred
  iframe HS
  iintro HΦ
  iapply HΦΨ $$ HΦ

/-- **Primitive step**: take one step of `e₁`, charging the mass outside `R` and averaging the
continuation credits `X₂` against `c`. -/
abbrev glmPrimStep (e₁ : Exp rT) (σ₁ : State rT) (c : ι → ℝ≥0∞)
    (Z : Cfg rT → (ι → ℝ≥0∞) → IProp GF) : IProp GF :=
  iprop(∃ (R : Cfg rT → Prop) (ε₁ : ℝ≥0∞) (X₂ : Cfg rT → ι → ℝ≥0∞) (r : ι → ℝ≥0∞),
    ⌜Reducible e₁ σ₁⌝ ∗
    ⌜MeasurableSet {ρ | R ρ}⌝ ∗
    ⌜∀ ρ, X₂ ρ ≤ r⌝ ∗
    ⌜charge ε₁ + expect (primStep ⟨e₁, σ₁⟩) X₂ ≤ c⌝ ∗
    ⌜Pgl ε₁ R (primStep ⟨e₁, σ₁⟩)⌝ ∗
    (∀ ρ, ⌜R ρ⌝ -∗ |={∅}=> execStutter (Z ρ) (X₂ ρ)))

theorem glmPrimStep_strong_mono {e₁ : Exp rT} {σ₁ : State rT} {c : ι → ℝ≥0∞}
    {Z₁ Z₂ : Cfg rT → (ι → ℝ≥0∞) → IProp GF} :
    iprop((∀ ρ c', Z₁ ρ c' -∗ Z₂ ρ c') ∗ glmPrimStep e₁ σ₁ c Z₁) ⊢ glmPrimStep e₁ σ₁ c Z₂ := by
  iintro ⟨HZ, %R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
  iexists R, ε₁, X₂, r
  iframe %Hred %HRmeas %Hbnd %Hexp %Hpgl
  iintro %ρ HR
  imod HCont $$ %ρ HR with HS
  imodintro
  iapply execStutter_mono_pred
  iframe HS
  iintro HZ₁
  iapply HZ $$ HZ₁

abbrev glmPre (Z : Cfg rT → (ι → ℝ≥0∞) → IProp GF)
    (Φ : GlmState rT ι → IProp GF) : GlmState rT ι → IProp GF :=
  fun ⟨ρ, c⟩ => iprop(glmCreditBump ρ c Φ ∨ glmPrimStep ρ.expr ρ.state c Z)

/-- The graded lifting modality: credit bumps followed by one primitive step. -/
abbrev glm (e : Exp rT) (σ : State rT) (c : ι → ℝ≥0∞)
    (Z : Cfg rT → (ι → ℝ≥0∞) → IProp GF) : IProp GF :=
  bi_least_fixpoint (glmPre Z) ((⟨e, σ⟩, c) : GlmState rT ι)

instance glmPre_mono {Z : Cfg rT → (ι → ℝ≥0∞) → IProp GF} : BIMonoPred (glmPre Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    obtain ⟨ρ, c⟩ := s
    icases Hs with ⟨HOT | HPS⟩
    · ileft
      iapply glmCreditBump_strong_mono
      iframe HOT
      iintro %s HΦ
      iapply Hwand $$ HΦ
    · iright; iexact HPS
  mono_pred_ne.ne {_ s s'} hd := by
    obtain rfl := OFE.Discrete.discrete hd; exact .of_eq rfl

theorem glm_ne {n : Nat} {e : Exp rT} {σ : State rT} {c : ι → ℝ≥0∞}
    {Z₁ Z₂ : Cfg rT → (ι → ℝ≥0∞) → IProp GF} (HZ : ∀ ρ c', Z₁ ρ c' ≡{n}≡ Z₂ ρ c') :
    glm e σ c Z₁ ≡{n}≡ glm e σ c Z₂ := by
  refine least_fixpoint_ne_outer (fun _ s => ?_) (.of_eq rfl)
  refine or_ne.ne (.of_eq rfl) ?_
  refine exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => ?_
  refine sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
    sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) ?_
  exact forall_ne fun _ => wand_ne.ne (.of_eq rfl) <|
    BIFUpdate.ne.ne <| or_ne.ne (.of_eq rfl) (HZ _ _)

theorem glm_unfold {e : Exp rT} {σ : State rT} {c : ι → ℝ≥0∞}
    {Z : Cfg rT → (ι → ℝ≥0∞) → IProp GF} :
    glm e σ c Z = glmPre Z (fun s => glm s.1.expr s.1.state s.2 Z) ((⟨e, σ⟩, c) : GlmState rT ι) :=
  least_fixpoint_unfold _

theorem glm_strong_ind {Z : Cfg rT → (ι → ℝ≥0∞) → IProp GF} {Ψ : GlmState rT ι → IProp GF}
    [NonExpansive Ψ] :
    iprop(□ (∀ s, glmPre Z (fun s' => iprop(Ψ s' ∧ bi_least_fixpoint (glmPre Z) s')) s -∗ Ψ s)) ⊢
      (∀ s, bi_least_fixpoint (glmPre Z) s -∗ Ψ s) := by
  iintro #HM
  iapply least_fixpoint_ind $$ HM

theorem glm_strong_mono {e : Exp rT} {σ : State rT} {c : ι → ℝ≥0∞}
    {Z₁ Z₂ : Cfg rT → (ι → ℝ≥0∞) → IProp GF} :
    iprop((∀ ρ c', Z₁ ρ c' -∗ Z₂ ρ c') ∗ glm e σ c Z₁) ⊢ glm e σ c Z₂ := by
  iintro ⟨HZ, HG⟩
  let Ψ : GlmState rT ι → IProp GF := fun s => iprop(
    (∀ ρ c', Z₁ ρ c' -∗ Z₂ ρ c') -∗ bi_least_fixpoint (glmPre Z₂) s)
  let : NonExpansive Ψ := nonExpansive_of_discrete_leibniz Ψ
  iapply least_fixpoint_iter (F := glmPre Z₁) (Φ := Ψ) $$ [] %((⟨e, σ⟩, c) : GlmState rT ι) HG HZ
  iintro !> %s HF Hwand
  iapply least_fixpoint_unfold_mpr (glmPre Z₂)
  obtain ⟨ρ, c⟩ := s
  icases HF with ⟨HOT | HPS⟩
  · ileft
    iapply glmCreditBump_strong_mono
    iframe HOT
    iintro %s HP
    iapply HP $$ Hwand
  · iright
    iapply glmPrimStep_strong_mono
    iframe HPS
    iintro %ρ' %c' HC
    iapply Hwand $$ HC

theorem glm_mono_grading {e : Exp rT} {σ : State rT} {c c' : ι → ℝ≥0∞}
    {Z : Cfg rT → (ι → ℝ≥0∞) → IProp GF} (hc : c ≤ c') :
    glm e σ c Z ⊢ glm e σ c' Z := by
  iintro HG
  iapply least_fixpoint_unfold_mpr (glmPre Z)
  icases least_fixpoint_unfold_mp (glmPre Z) $$ HG with
    ⟨HOT | ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩⟩
  · ileft
    iintro %c'' %Hb
    iapply HOT $$ %c'' %(Bump.of_le hc Hb)
  · iright
    have Hexp' := Hexp.trans hc
    iexists R, ε₁, X₂, r
    iframe %Hred %HRmeas %Hbnd %Hexp' %Hpgl HCont

theorem glm_strong_mono_grading {e : Exp rT} {σ : State rT} {c c' : ι → ℝ≥0∞}
    {Z₁ Z₂ : Cfg rT → (ι → ℝ≥0∞) → IProp GF} (hc : c ≤ c') :
    iprop((∀ ρ c'', Z₁ ρ c'' -∗ Z₂ ρ c'') ∗ glm e σ c Z₁) ⊢ glm e σ c' Z₂ := by
  iintro ⟨HZ, HG⟩
  iapply glm_mono_grading hc
  iapply glm_strong_mono
  iframe

theorem glm_mono_pred {e : Exp rT} {σ : State rT} {c : ι → ℝ≥0∞}
    {Z₁ Z₂ : Cfg rT → (ι → ℝ≥0∞) → IProp GF} :
    iprop((□ (∀ ρ c', Z₁ ρ c' -∗ Z₂ ρ c')) ∗ glm e σ c Z₁) ⊢ glm e σ c Z₂ := by
  iintro ⟨#HZ, HG⟩
  iapply (least_fixpoint_strong_mono (glmPre Z₁) (glmPre Z₂)) $$ [] HG
  iintro !> %Φ %s HF
  obtain ⟨ρ, c⟩ := s
  icases HF with ⟨HOT | HPS⟩
  · ileft; iexact HOT
  · iright
    iapply glmPrimStep_strong_mono
    iframe HPS
    iintro %ρ' %c' HC
    iapply HZ $$ HC

theorem glm_bind {K : Ectx rT} {e : Exp rT} {σ : State rT} {c : ι → ℝ≥0∞}
    {Z : Cfg rT → (ι → ℝ≥0∞) → IProp GF} :
    glm e σ c (fun ρ c' => Z ⟨K.fill ρ.expr, ρ.state⟩ c') ⊢ glm (K.fill e) σ c Z := by
  iintro HG
  classical
  let Kinv : Exp rT → Option (Exp rT) := Function.partialInv K.fill
  have Kinv_left : ∀ e', Kinv (K.fill e') = some e' :=
    Function.partialInv_left (Ectx.fill_injective K)
  let Z' : Cfg rT → (ι → ℝ≥0∞) → IProp GF := fun ρ c' => Z ⟨K.fill ρ.expr, ρ.state⟩ c'
  let Φ : GlmState rT ι → IProp GF :=
    fun s => bi_least_fixpoint (glmPre Z) ((⟨K.fill s.1.expr, s.1.state⟩, s.2) : GlmState rT ι)
  let : NonExpansive Φ := nonExpansive_of_discrete_leibniz Φ
  ihave HΦ : iprop(Φ ((⟨e, σ⟩, c) : GlmState rT ι)) $$ [HG]
  · iapply (least_fixpoint_iter (F := glmPre Z'))
    · iintro !> %s HF
      obtain ⟨ρ, c'⟩ := s
      iapply least_fixpoint_unfold_mpr (glmPre Z)
      icases HF with ⟨HOT | HPS⟩
      · ileft; iexact HOT
      · iright
        icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
        have Hsv : ¬ ρ.expr.isValue := val_stuck Hred
        set R' : Cfg rT → Prop := fun ρ' => ∃ ρ'', ρ' = K.fillCfg ρ'' ∧ R ρ'' with hR'def
        set X₂' : Cfg rT → ι → ℝ≥0∞ :=
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
        have hexp' : charge ε₁ + expect (primStep ⟨K.fill ρ.expr, ρ.state⟩) X₂' ≤ c' := by
          refine le_trans (fun i => ?_) Hexp
          simp only [Pi.add_apply, expect]
          rw [primStep_fill Hsv]
          gcongr charge ε₁ i + ?_
          refine (MeasureTheory.lintegral_map_le _ (Ectx.fillCfg.measurable K).aemeasurable).trans
            (Eq.le ?_)
          exact MeasureTheory.lintegral_congr_ae
            (Filter.Eventually.of_forall fun a => congrFun (hX₂'fill a) i)
        have hpgl' : Pgl ε₁ R' (primStep ⟨K.fill ρ.expr, ρ.state⟩) := by
          show primStep ⟨K.fill ρ.expr, ρ.state⟩ {x | ¬ R' x} ≤ ε₁
          have hcompl : MeasurableSet {x : Cfg rT | ¬ R' x} := hR'meas.compl
          rw [primStep_fill Hsv, MeasureTheory.Measure.map_apply (by measurability) hcompl]
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
    · iexact HG
  iexact HΦ

theorem glm_prim_step {e : Exp rT} {σ : State rT} {c : ι → ℝ≥0∞}
    {Z : Cfg rT → (ι → ℝ≥0∞) → IProp GF} :
    glmPrimStep e σ c Z ⊢ glm e σ c Z := by
  iintro HPS
  iapply least_fixpoint_unfold_mpr (glmPre Z)
  iright
  iexact HPS

theorem glm_credit_bump {e : Exp rT} {σ : State rT} {c : ι → ℝ≥0∞}
    {Z : Cfg rT → (ι → ℝ≥0∞) → IProp GF} :
    glmCreditBump ⟨e, σ⟩ c (fun s => glm s.1.expr s.1.state s.2 Z) ⊢ glm e σ c Z := by
  iintro HOT
  iapply least_fixpoint_unfold_mpr (glmPre Z)
  ileft
  iexact HOT

end LiveWpGS

end LiveEris
end ProbLang
