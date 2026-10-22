module

public import Metrology.TotalEris.ErrorRules
public import Metrology.TotalEris.FupdPlainlyForall
public import Metrology.ProbLang.Erasure
import Metrology.Iris.LocalBI

@[expose] public section

/-!
# Total adequacy

Soundness of total-correctness Eris: `twp_tgl` (graded lift), `twp_mass_lim_exec`
(termination with probability `≥ 1 - ε`) and `twp_pgl_lim` (Pgl bound on `limExec`).
-/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors}
local bi IProp GF

theorem measurableEmbedding_ofVal :
    MeasurableEmbedding (Exp.ofVal : Val rT → Exp rT) := by
  refine ⟨fun a b h => Val.ext h, Exp.ofVal.measurable, fun s hs => ?_⟩
  obtain ⟨U, hU, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hrange : Set.range (Val.fst : Val rT → Exp rT) = {e : Exp rT | e.isValue} := by
    ext e
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, rfl⟩; exact Val.isValue v
    · intro h; exact ⟨Val.mk e h.some h.some.lc, rfl⟩
  show MeasurableSet (Val.fst '' (Val.fst ⁻¹' U))
  rw [Set.image_preimage_eq_inter_range, hrange]
  have hsplit : {e : Exp rT | e.isValue} = {e | e.isValueR} ∩ {e | Exp.lcb 0 e = true} := by
    ext e; simp [Exp.isValue_iff_isValueR, Set.mem_inter_iff]
  rw [hsplit]
  exact hU.inter (Exp.isValueR.measurable.setOf.inter Exp.lcb_zero.measurableSet)

theorem measurableSet_ofValSet {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v}) :
    MeasurableSet {e : Exp rT | ∃ v, e = Exp.ofVal v ∧ φ v} := by
  have heq : {e : Exp rT | ∃ v, e = Exp.ofVal v ∧ φ v} = Exp.ofVal '' {v | φ v} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    exact ⟨fun ⟨v, he, hv⟩ => ⟨v, hv, he.symm⟩, fun ⟨v, hv, he⟩ => ⟨v, he.symm, hv⟩⟩
  rw [heq]
  exact measurableEmbedding_ofVal.measurableSet_image' hφ

theorem measurableSet_TglCfgSet {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v}) :
    MeasurableSet {ρ : Cfg rT | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v} :=
  (measurableSet_ofValSet hφ).preimage Cfg.measurable_expr

/-- Graded total lift: `μ` puts mass at least `1 - ε` on values satisfying `φ`. -/
def Tgl (μ : MeasureTheory.Measure (Cfg rT)) (φ : Val rT → Prop) (ε : ENNReal) : Prop :=
  1 - ε ≤ μ {ρ : Cfg rT | ∃ v : Val rT, ρ.expr = Exp.ofVal v ∧ φ v}

theorem Pgl.of_tgl {μ : MeasureTheory.Measure (Cfg rT)} {φ : Val rT → Prop} {ε : ENNReal}
    (hS : MeasurableSet {ρ : Cfg rT | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v})
    (hμ : μ Set.univ ≤ 1) (h : Tgl μ φ ε) :
    Pgl ε (fun ρ => ∃ v, ρ.expr = Exp.ofVal v ∧ φ v) μ := by
  set S : Set (Cfg rT) := {ρ | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v}
  show μ Sᶜ ≤ ε
  have hS_ne_top : μ S ≠ (⊤ : ENNReal) := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((MeasureTheory.measure_mono (Set.subset_univ _)).trans hμ)
  refine (ENNReal.add_le_add_iff_left hS_ne_top).mp ?_
  rw [MeasureTheory.measure_add_measure_compl hS]
  exact hμ.trans (tsub_le_iff_right.mp h)

namespace Tgl

theorem termination_ineq {μ : MeasureTheory.Measure (Cfg rT)} {φ : Val rT → Prop}
    {ε : ENNReal} (h : Tgl μ φ ε) : 1 - ε ≤ μ Set.univ :=
  h.trans (MeasureTheory.measure_mono (Set.subset_univ _))

theorem mono_grading {μ : MeasureTheory.Measure (Cfg rT)} {φ : Val rT → Prop}
    {ε ε' : ENNReal} (hε : ε ≤ ε') (h : Tgl μ φ ε) : Tgl μ φ ε' :=
  (tsub_le_tsub_left hε 1).trans h

theorem of_ge_one {μ : MeasureTheory.Measure (Cfg rT)} {φ : Val rT → Prop}
    {ε : ENNReal} (hε : 1 ≤ ε) : Tgl μ φ ε := by
  show 1 - ε ≤ _
  rw [tsub_eq_zero_of_le hε]
  exact zero_le

theorem mono_pred {μ : MeasureTheory.Measure (Cfg rT)} {φ ψ : Val rT → Prop}
    {ε : ENNReal} (hφψ : ∀ v, φ v → ψ v) (h : Tgl μ φ ε) : Tgl μ ψ ε := by
  refine h.trans (MeasureTheory.measure_mono ?_)
  rintro x ⟨v, hxv, hφ⟩
  exact ⟨v, hxv, hφψ v hφ⟩

theorem congr_pred {μ : MeasureTheory.Measure (Cfg rT)} {φ ψ : Val rT → Prop}
    {ε : ENNReal} (h_iff : ∀ v, φ v ↔ ψ v) (h : Tgl μ φ ε) : Tgl μ ψ ε :=
  mono_pred (fun v => (h_iff v).mp) h

theorem of_dirac_val
    {v : Val rT} {σ : State rT} {φ : Val rT → Prop} (hφ : φ v) :
    Tgl (MeasureTheory.Measure.dirac (⟨Exp.ofVal v, σ⟩ : Cfg rT)) φ 0 := by
  show 1 - 0 ≤ _
  rw [tsub_zero]
  exact (MeasureTheory.Measure.dirac_apply_of_mem
    (show (⟨Exp.ofVal v, σ⟩ : Cfg rT) ∈
      {ρ : Cfg rT | ∃ v', ρ.expr = Exp.ofVal v' ∧ φ v'} from ⟨v, rfl, hφ⟩)).symm.le

theorem of_limExec_val
    {v : Val rT} {σ : State rT} {φ : Val rT → Prop} (hφ : φ v) :
    Tgl (limExec (⟨Exp.ofVal v, σ⟩ : Cfg rT)) φ 0 := by
  show Tgl (limExec (⟨v.1, σ⟩ : Cfg rT)) φ 0
  rw [limExec_of_isVal v.2]
  exact of_dirac_val hφ

theorem epsilon_limit {μ : MeasureTheory.Measure (Cfg rT)} {φ : Val rT → Prop}
    {ε' : ENNReal} (h : ∀ ε, ε' < ε → Tgl μ φ ε) : Tgl μ φ ε' := by
  set S : Set (Cfg rT) := {ρ | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v}
  show 1 - ε' ≤ μ S
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hμSc, hc1⟩ := exists_between hcon
  have hc_le_one : c ≤ 1 := hc1.le.trans tsub_le_self
  have hTglS : 1 - (1 - c) ≤ μ S := h (1 - c) (lt_tsub_comm.mp hc1)
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hc_le_one] at hTglS
  exact (hTglS.trans_lt hμSc).false

theorem pgl_limExec {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {φ : Val rT → Prop} (hφ : MeasurableSet {v : Val rT | φ v})
    (h : Tgl (limExec ⟨e, σ⟩) φ ε) :
    Pgl ε (fun ρ => ∃ v, ρ.expr = Exp.ofVal v ∧ φ v) (limExec ⟨e, σ⟩) :=
  Pgl.of_tgl (measurableSet_TglCfgSet hφ)
    (limExec_leq_mass (fun n => execN_univ_le_one n ⟨e, σ⟩)) h

theorem tgl_lift_prob
    {α : Type*} [MeasurableSpace α]
    {M : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure M]
    {ε ε₁ : ENNReal} {ε₂ : α → ENNReal}
    {R : α → Prop} {k : α → ENNReal}
    (hR : MeasurableSet {a | R a})
    (hk : Measurable k)
    (hpgl : Pgl ε₁ R M)
    (Hsum : ε₁ + (∫⁻ a, ε₂ a ∂M) ≤ ε)
    (Hcont : ∀ a, R a → 1 - ε₂ a ≤ k a) :
    1 - ε ≤ ∫⁻ a, k a ∂M := by
  have hMR : 1 - ε₁ ≤ M {a | R a} := by
    rw [tsub_le_iff_left]
    calc 1 = M {a | R a} + M {a | ¬ R a} := (MeasureTheory.prob_add_prob_compl hR).symm
      _ ≤ M {a | R a} + ε₁ := add_le_add le_rfl hpgl
      _ = ε₁ + M {a | R a} := add_comm _ _
  -- Split the integral using measurability of `k`; `ε₂` need not be measurable.
  have h_split : M {a | R a} ≤
      (∫⁻ a in {a | R a}, k a ∂M) + (∫⁻ a in {a | R a}, ε₂ a ∂M) := by
    have hone : M {a | R a} = ∫⁻ _ in {a | R a}, (1 : ENNReal) ∂M := by
      rw [MeasureTheory.setLIntegral_const, one_mul]
    rw [← MeasureTheory.lintegral_add_left hk, hone]
    refine MeasureTheory.lintegral_mono_ae ((MeasureTheory.ae_restrict_iff' hR).mpr
      (.of_forall fun a ha => ?_))
    exact tsub_le_iff_right.mp (Hcont a ha)
  have h_total : 1 - ε₁ ≤ (∫⁻ a, k a ∂M) + (∫⁻ a, ε₂ a ∂M) :=
    calc 1 - ε₁ ≤ M {a | R a} := hMR
      _ ≤ (∫⁻ a in {a | R a}, k a ∂M) + (∫⁻ a in {a | R a}, ε₂ a ∂M) := h_split
      _ ≤ (∫⁻ a, k a ∂M) + (∫⁻ a, ε₂ a ∂M) :=
        add_le_add (MeasureTheory.setLIntegral_le_lintegral _ k)
          (MeasureTheory.setLIntegral_le_lintegral _ ε₂)
  calc 1 - ε ≤ 1 - (ε₁ + ∫⁻ a, ε₂ a ∂M) := tsub_le_tsub_left Hsum 1
    _ = 1 - ε₁ - (∫⁻ a, ε₂ a ∂M) := by rw [tsub_tsub]
    _ ≤ ∫⁻ a, k a ∂M := tsub_le_iff_right.mpr h_total

theorem tgl_prim_step
    {e : Exp rT} {σ : State rT} {ε ε₁ : ENNReal} {ε₂ : Cfg rT → ENNReal}
    {R : Cfg rT → Prop} {P : Set (Cfg rT)}
    (hR : MeasurableSet {ρ | R ρ})
    (hP : MeasurableSet P)
    (Hred : Reducible e σ)
    (Hsum : ε₁ + (∫⁻ ρ, ε₂ ρ ∂primStep ⟨e, σ⟩) ≤ ε)
    (Hpgl : Pgl ε₁ R (primStep ⟨e, σ⟩))
    (Hcont : ∀ ρ, R ρ → 1 - ε₂ ρ ≤ (limExec ρ) P) :
    1 - ε ≤ ∫⁻ ρ, (limExec ρ) P ∂primStep ⟨e, σ⟩ :=
  have : MeasureTheory.IsProbabilityMeasure (primStep ⟨e, σ⟩) := prim_step_mass Hred
  tgl_lift_prob (M := primStep ⟨e, σ⟩) (k := fun ρ => (limExec ρ) P) hR
    ((MeasureTheory.Measure.measurable_coe hP).comp limExec.measurable)
    Hpgl Hsum Hcont

/-- Only uses that `ErasableExpr μ σ` makes `μ` a probability measure; the erasure
equation itself is used in `dbind_erasable`. -/
theorem tgl_erasable
    {e : Exp rT} {σ : State rT} {μ : MeasureTheory.Measure (State rT)}
    (heras : ErasableExpr μ σ)
    {ε ε₁ : ENNReal} {ε₂ : State rT → ENNReal}
    {R : State rT → Prop} {P : Set (Cfg rT)}
    (hR : MeasurableSet {σ' | R σ'})
    (hP : MeasurableSet P)
    (Hsum : ε₁ + (∫⁻ σ', ε₂ σ' ∂μ) ≤ ε)
    (Hpgl : Pgl ε₁ R μ)
    (Hcont : ∀ σ', R σ' → 1 - ε₂ σ' ≤ (limExec ⟨e, σ'⟩) P) :
    1 - ε ≤ ∫⁻ σ', (limExec ⟨e, σ'⟩) P ∂μ :=
  have : MeasureTheory.IsProbabilityMeasure μ := ⟨ErasableExpr.mass heras⟩
  tgl_lift_prob (M := μ) (k := fun σ' => (limExec ⟨e, σ'⟩) P) hR
    ((MeasureTheory.Measure.measurable_coe hP).comp
      (limExec.measurable.comp
        (by fun_prop : Measurable (fun σ' : State rT => (⟨e, σ'⟩ : Cfg rT)))))
    Hpgl Hsum Hcont

theorem dbind_prim_step
    {e : Exp rT} {σ : State rT} {ε ε₁ : ENNReal} {ε₂ : Cfg rT → ENNReal}
    {R : Cfg rT → Prop} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (hR : MeasurableSet {ρ | R ρ})
    (Hred : Reducible e σ)
    (Hsum : ε₁ + (∫⁻ ρ, ε₂ ρ ∂primStep ⟨e, σ⟩) ≤ ε)
    (Hpgl : Pgl ε₁ R (primStep ⟨e, σ⟩))
    (Hcont : ∀ ρ, R ρ → Tgl (limExec ρ) φ (ε₂ ρ)) :
    Tgl (limExec ⟨e, σ⟩) φ ε := by
  set S : Set (Cfg rT) := {ρ | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v}
  have hSmeas : MeasurableSet S := measurableSet_TglCfgSet hφ
  show 1 - ε ≤ (limExec ⟨e, σ⟩) S
  rw [limExec_not_final (val_stuck Hred),
    MeasureTheory.Measure.bind_apply hSmeas limExec.measurable.aemeasurable]
  exact tgl_prim_step hR hSmeas Hred Hsum Hpgl Hcont

theorem dbind_erasable
    {e : Exp rT} {σ : State rT} {μ : MeasureTheory.Measure (State rT)}
    (heras : ErasableExpr μ σ)
    {ε ε₁ : ENNReal} {ε₂ : State rT → ENNReal}
    {R : State rT → Prop} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (hR : MeasurableSet {σ' | R σ'})
    (Hsum : ε₁ + (∫⁻ σ', ε₂ σ' ∂μ) ≤ ε)
    (Hpgl : Pgl ε₁ R μ)
    (Hcont : ∀ σ', R σ' → Tgl (limExec ⟨e, σ'⟩) φ (ε₂ σ')) :
    Tgl (limExec ⟨e, σ⟩) φ ε := by
  set S : Set (Cfg rT) := {ρ | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v}
  set S' : Set (Exp rT) := {e | ∃ v, e = Exp.ofVal v ∧ φ v}
  have hSmeas : MeasurableSet S := measurableSet_TglCfgSet hφ
  have hkernel : Measurable (fun σ' : State rT => limExec (⟨e, σ'⟩ : Cfg rT)) := by
    measurability
  have h_eq : (μ.bind (fun σ' => limExec ⟨e, σ'⟩)) S = (limExec ⟨e, σ⟩) S := by
    have hmap : ∀ ν : MeasureTheory.Measure (Cfg rT), ν S = asExpr ν S' := fun ν => by
      unfold asExpr
      rw [MeasureTheory.Measure.map_apply Cfg.measurable_expr (measurableSet_ofValSet hφ)]
      rfl
    rw [hmap, hmap]
    congr 1
    exact ErasableExpr.lim_exec heras e
  show 1 - ε ≤ (limExec ⟨e, σ⟩) S
  calc 1 - ε ≤ ∫⁻ σ', (limExec ⟨e, σ'⟩) S ∂μ :=
        tgl_erasable heras hR hSmeas Hsum Hpgl Hcont
    _ = (μ.bind fun σ' => limExec ⟨e, σ'⟩) S :=
        (MeasureTheory.Measure.bind_apply hSmeas hkernel.aemeasurable).symm
    _ = (limExec ⟨e, σ⟩) S := h_eq

end Tgl

theorem Tgl_of_execStutter [ErisGS rT .hasNoLC GF] {μ : MeasureTheory.Measure (Cfg rT)}
    {φ : Val rT → Prop} {P : ENNReal → IProp GF} {ε : ENNReal}
    (hP : ∀ ε, P ε ⊢ |={∅}=> ⌜Tgl μ φ ε⌝) :
    execStutter P ε ⊢ |={∅}=> ⌜Tgl μ φ ε⌝ := by
  iintro (%Hvac | HZ)
  · imodintro; ipureintro; exact Tgl.of_ge_one Hvac
  · iapply (hP ε) $$ HZ

theorem glm_implies_tgl [ErisGS rT .hasNoLC GF]
    {φ : Val rT → Prop} {e : Exp rT} {σ : State rT} {ε : ENNReal}
    (hφ : MeasurableSet {v : Val rT | φ v}) :
    glm' (GF := GF) e σ ε
        (fun ρ ε₂ => iprop(|={∅}=> ⌜Tgl (limExec ρ) φ ε₂⌝))
      ⊢ iprop(|={∅}=> ⌜Tgl (limExec ⟨e, σ⟩) φ ε⌝) := by
  let Z : Cfg rT → ENNReal → IProp GF :=
    fun ρ ε₂ => iprop(|={∅}=> ⌜Tgl (limExec ρ) φ ε₂⌝)
  let Ψ : GlmState rT → IProp GF :=
    fun s => iprop(|={∅}=> ⌜Tgl (limExec s.1) φ s.2⌝)
  let : NonExpansive Ψ := nonExpansive_of_discrete_leibniz Ψ
  iintro HG
  ihave HInd : iprop(□ (∀ s, glmPre' Z
      (fun s' => iprop(Ψ s' ∧ bi_least_fixpoint (glmPre' Z) s')) s -∗ Ψ s)) $$ []
  · iintro !> %s HPre
    obtain ⟨⟨e', σ'⟩, ε'⟩ := s
    icases HPre with ⟨HOT | HPS⟩
    · ihave Hfa : iprop(∀ ε'', ⌜ε' < ε''⌝ -∗
          |={∅}=> ⌜Tgl (limExec ⟨e', σ'⟩) φ ε''⌝) $$ [HOT]
      · iintro %ε'' %hε
        imod HOT $$ %ε'' %hε with HS
        iapply Tgl_of_execStutter (fun _ => and_elim_l) $$ HS
      imod iProp_fupd_plainly_forall_pure_impl_no_lc $$ Hfa with %Hf
      imodintro
      ipureintro
      exact Tgl.epsilon_limit Hf
    · icases HPS with ⟨HPS | HSS⟩
      · -- The prim-step leaf is `Z ρ` itself; the other branches carry `Ψ ∧ glm`.
        icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %_, %Hsum, %Hpgl, HCont⟩
        ihave Hfa : iprop(∀ ρ, ⌜R ρ⌝ -∗
            |={∅}=> ⌜Tgl (limExec ρ) φ (X₂ ρ)⌝) $$ [HCont]
        · iintro %ρ %hR
          imod HCont $$ %ρ %hR with HS
          iapply Tgl_of_execStutter (P := Z ρ) (fun _ => .rfl) $$ HS
        imod iProp_fupd_plainly_forall_pure_impl_no_lc $$ Hfa with %Hf
        imodintro
        ipureintro
        exact Tgl.dbind_prim_step hφ HRmeas Hred Hsum Hpgl Hf
      · icases HSS with ⟨%μ, %R, %ε₁, %X₂, %r, %Heras, %HRmeas, %_, %Hsum, %Hpgl, HCont⟩
        ihave Hfa : iprop(∀ σ'', ⌜R σ''⌝ -∗
            |={∅}=> ⌜Tgl (limExec ⟨e', σ''⟩) φ (X₂ σ'')⌝) $$ [HCont]
        · iintro %σ'' %hR
          imod HCont $$ %σ'' %hR with HS
          iapply Tgl_of_execStutter (fun _ => and_elim_l) $$ HS
        imod iProp_fupd_plainly_forall_pure_impl_no_lc $$ Hfa with %Hf
        imodintro
        ipureintro
        exact Tgl.dbind_erasable Heras hφ HRmeas Hsum Hpgl Hf
  iapply glm'_strong_ind (Z := Z) (Ψ := Ψ) $$ HInd %(⟨⟨e, σ⟩, ε⟩ : GlmState rT) HG

theorem twp_step_fupd_tgl [ErisGS rT .hasNoLC GF]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v}) :
    iprop(stateInterp σ ∗ errInterp (rT := rT) ε ∗ tglWp ⊤ e (fun v => iprop(⌜φ v⌝)))
      ⊢ iprop(|={⊤,∅}=> ⌜Tgl (limExec ⟨e, σ⟩) φ ε⌝) := by
  iintro ⟨Hσ, Hε, HW⟩
  let Q : Exp rT → IProp GF := fun e' => iprop(
    ∀ σ' ε', stateInterp σ' ∗ errInterp (rT := rT) ε' -∗
      |={⊤,∅}=> ⌜Tgl (limExec ⟨e', σ'⟩) φ ε'⌝)
  let : NonExpansive Q := nonExpansive_of_discrete_leibniz Q
  ihave Hq : Q e $$ [HW]
  · iapply tglWp_ind (E := ⊤) (Q := Q) (Φ := fun v => iprop(⌜φ v⌝))
    · iintro !> %e' HPre %σ' %ε' ⟨Hσ', Hε'⟩
      cases htv : e'.toVal? with
      | some v =>
        obtain rfl : e' = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
        isimp only [tglWpPre_eq_value] at HPre
        imod HPre $$ %σ' %ε' [$Hσ' $Hε'] with ⟨_, _, %hφv⟩
        imod (BIFUpdate.subset (E1 := ⊤) (E2 := ∅) Std.LawfulSet.empty_subset) with _
        imodintro
        ipureintro
        exact Tgl.mono_grading zero_le (Tgl.of_limExec_val hφv)
      | none =>
        isimp only [tglWpPre_eq_step htv] at HPre
        imod HPre $$ %σ' %ε' [$Hσ' $Hε'] with HG
        ihave HG' : iprop(glm' e' σ' ε' (fun ρ ε₂ => iprop(|={∅}=> ⌜Tgl (limExec ρ) φ ε₂⌝))) $$ [HG]
        · iapply (glm'_strong_mono (Z₁ := fun ρ ε₂ => iprop(|={∅,⊤}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ Q ρ.expr))
            (Z₂ := fun ρ ε₂ => iprop(|={∅}=> ⌜Tgl (limExec ρ) φ ε₂⌝)))
          iframe HG
          iintro %ρ %ε₂ HL
          imod HL with ⟨Hσ'', Hε'', HQ⟩
          iapply HQ $$ %ρ.state %ε₂ [$Hσ'' $Hε'']
        iapply (glm_implies_tgl hφ) $$ HG'
    · iexact HW
  iapply Hq $$ %σ %ε [$Hσ $Hε]

theorem twp_tgl [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (Hwp : ∀ [ErisGS rT .hasNoLC GF], iprop(↯ε) ⊢
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    Tgl (limExec ⟨e, σ⟩) φ ε := by
  by_cases hε : 1 ≤ ε
  · exact Tgl.of_ge_one hε
  push Not at hε
  refine pure_soundness (PROP := bi%) ?_
  refine fupd_soundness .hasNoLC (GF := GF) (E1 := ⊤) (E2 := ∅) (n := 0)
    (fun Hinv => ?_)
  iintro _
  imod (app_ra_init (GF := GF) σ) with ⟨%IA, HappAuth⟩
  imod (ec_alloc (GF := GF) ε hε) with ⟨%γec, HecAuth, HecFrag⟩
  let IES : ErisGS rT .hasNoLC GF := {
    appGS := IA
    ecGS := { toECPreGS := inferInstance, γec := γec }
    invGS := Hinv }
  ihave Hwp' := Hwp $$ HecFrag
  iapply twp_step_fupd_tgl hφ
  iframe

theorem twp_tgl_value [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]
    {v : Val rT} {σ : State rT} {ε : ENNReal} {φ : Val rT → Prop}
    (hε : ε < 1)
    (Hwp : ∀ [ErisGS rT .hasNoLC GF], iprop(↯ε) ⊢
      tglWp ⊤ (Exp.ofVal v) (fun v => iprop(⌜φ v⌝))) :
    Tgl (limExec ⟨Exp.ofVal v, σ⟩) φ 0 := by
  refine Tgl.of_limExec_val ?_
  refine pure_soundness (PROP := bi%) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) (GF := GF) 0 0 (fun Hinv => ?_)
  iintro _
  imod (app_ra_init (GF := GF) σ) with ⟨%IA, HappAuth⟩
  imod (ec_alloc (GF := GF) ε hε) with ⟨%γec, HecAuth, HecFrag⟩
  let IES : ErisGS rT .hasNoLC GF := {
    appGS := IA
    ecGS := { toECPreGS := inferInstance, γec := γec }
    invGS := Hinv }
  ihave Hwp' := Hwp $$ HecFrag
  imod tglWp_value_inv_with_state (E := ⊤) (Φ := fun v => iprop(⌜φ v⌝))
    $$ [$Hwp' $HappAuth $HecAuth] with ⟨-, -, %hφ⟩
  simp only [Nat.repeat]
  imod (BIFUpdate.subset (E1 := ⊤) (E2 := ∅) Std.LawfulSet.empty_subset) with _
  imodintro
  ipureintro
  exact hφ

theorem twp_mass_lim_exec [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (Hwp : ∀ [ErisGS rT .hasNoLC GF], iprop(↯ε) ⊢
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    1 - ε ≤ (limExec ⟨e, σ⟩) Set.univ :=
  Tgl.termination_ineq (twp_tgl hφ Hwp)

theorem twp_pgl_lim [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (Hwp : ∀ [ErisGS rT .hasNoLC GF], iprop(↯ε) ⊢
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    Pgl ε (fun ρ => ∃ v, ρ.expr = Exp.ofVal v ∧ φ v) (limExec ⟨e, σ⟩) :=
  Tgl.pgl_limExec hφ (twp_tgl hφ Hwp)

theorem twp_tgl_limit [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (Hwp : ∀ ε', ε < ε' → ∀ [ErisGS rT .hasNoLC GF], iprop(↯ε') ⊢
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    Tgl (limExec ⟨e, σ⟩) φ ε :=
  Tgl.epsilon_limit (fun ε' hε' => twp_tgl hφ (Hwp ε' hε'))

theorem twp_mass_lim_exec_limit [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (Hwp : ∀ ε', ε < ε' → ∀ [ErisGS rT .hasNoLC GF], iprop(↯ε') ⊢
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    1 - ε ≤ (limExec ⟨e, σ⟩) Set.univ :=
  Tgl.termination_ineq (twp_tgl_limit hφ Hwp)

theorem twp_pgl_lim_limit [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (Hwp : ∀ ε', ε < ε' → ∀ [ErisGS rT .hasNoLC GF], iprop(↯ε') ⊢
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    Pgl ε (fun ρ => ∃ v, ρ.expr = Exp.ofVal v ∧ φ v) (limExec ⟨e, σ⟩) :=
  Tgl.pgl_limExec hφ (twp_tgl_limit hφ Hwp)

theorem twp_tgl_of_toVal [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {v : Val rT} {φ : Val rT → Prop}
    (hev : e.toVal? = some v) (hε : ε < 1)
    (Hwp : ∀ [ErisGS rT .hasNoLC GF], iprop(↯ε) ⊢
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    Tgl (limExec ⟨e, σ⟩) φ 0 := by
  obtain rfl : Exp.ofVal v = e := Exp.ofVal_of_toVal_some hev
  exact twp_tgl_value hε Hwp

end TotalEris
end ProbLang
