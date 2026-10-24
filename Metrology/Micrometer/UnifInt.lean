module

public import Metrology.Micrometer.Lifting
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.ProbLang.Metatheory
public import Metrology.Couplings.Bridges.AddCoupl

/-! # Uniform integer draws and their couplings

`unifInt z` is the uniform measure on `[0, z)`; the file couples two such draws and steps `rand`. -/

@[expose] public section

open Iris Iris.BI OFE GradedLifting
open MeasureTheory.Measure (ext_of_lintegral map_map dirac)
open scoped AppGS

namespace ProbLang
open MeasureTheory

open Cfg Exp Finset Ectx HeadReducible IsLawful AddCoupl
open ENNReal (inv_mul_le_inv_mul_add div_eq_inv_mul)
open _root_.Int (card_Ico toNat_le_toNat)

variable {rT : Type} {B : Type} {L : GradedLifting.{0} B} {z zL zR : Int}

/-! ## Coupled draws and their leftover cost -/

/-- The outcome of a coupled draw: the left draw is `n`, the right draw is `f n` under `K`. -/
abbrev CoupledDraw (z : Int) (f : Int → Int) (σ σ' : State rT) (K : Ectx rT) :
    Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
  ∃ n : Int, 0 ≤ n ∧ n < z ∧ c₁ = ⟨pl(#int n), σ⟩ ∧ c₂ = ⟨K.fill pl(#int (f n)), σ'⟩

open scoped Classical in
/-- The leftover cost of a coupled draw: `s (ε₂ n)` at the pair drawn from `n`, and `⊤` elsewhere,
keyed by the left draw along the bijection `f`. -/
noncomputable def Cfg.advLeftover [_root_.Top B] (s : ENNReal → B) (z : Int) (f : Int → Int)
    (σ σ' : State rT) (K : Ectx rT) (ε₂ : Int → ENNReal) : Cfg rT → Cfg rT → B :=
  fun ρ₁ ρ₂ => if h : CoupledDraw z f σ σ' K ρ₁ ρ₂ then s (ε₂ h.choose) else ⊤

/-- At the pair drawn from `n`, the leftover is `s (ε₂ n)`. -/
theorem Cfg.advLeftover_apply [_root_.Top B] (s : ENNReal → B) (f : Int → Int) (σ σ' : State rT)
    (K : Ectx rT) (ε₂ : Int → ENNReal) {n : Int} (h0 : 0 ≤ n) (hn : n < z) :
    advLeftover s z f σ σ' K ε₂ ⟨pl(#int n), σ⟩ ⟨K.fill pl(#int (f n)), σ'⟩ = s (ε₂ n) := by
  have hex : CoupledDraw z f σ σ' K ⟨pl(#int n), σ⟩ ⟨K.fill pl(#int (f n)), σ'⟩ :=
    ⟨n, h0, hn, rfl, rfl⟩
  obtain ⟨he, -⟩ := (mk.injEq ..).mp hex.choose_spec.2.2.1
  simp only [lit.injEq, BaseLit.int.injEq] at he
  simp only [advLeftover, hex, ↓reduceDIte, ← he]

variable [MeasurableSpace rT]

/-- The uniform measure on `[0, z)`. -/
noncomputable def unifInt (z : Int) (_hz : 0 < z) : Measure Int :=
  Measure.uniformOfFinset (Ico 0 z)

instance isProbabilityMeasure_unifInt {hz : 0 < z} : IsProbabilityMeasure (unifInt z hz) :=
  Measure.isProbabilityMeasure_uniformOfFinset (nonempty_Ico.mpr hz)

variable (hz : 0 < z) in
/-- `Cfg.uniform z σ` is `unifInt z` pushed to integer literals. -/
theorem Cfg.uniform_eq_map (σ : State rT) :
    uniform z σ = (unifInt z hz).map fun n => (⟨pl(#int n), σ⟩ : Cfg rT) :=
  uniform_eq_map_uniformOfFinset hz σ

/-! ## The uniform measure `unifInt` and its exact bijection coupling -/

section UniformInt

variable (hz : 0 < z)

/-- Integrals against `unifInt z` are averages over `[0, z)`. -/
theorem lintegral_unifInt (φ : Int → ENNReal) :
    ∫⁻ n, φ n ∂unifInt z hz = (z.toNat : ENNReal)⁻¹ * ∑ n ∈ Ico 0 z, φ n := by
  have hcard : (Ico (0 : Int) z).card = z.toNat := by rw [card_Ico]; omega
  rw [unifInt, lintegral_countable', tsum_eq_sum fun n hn => by
    rw [Measure.uniformOfFinset_apply_singleton_of_notMem hn, mul_zero], mul_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [Measure.uniformOfFinset_apply_singleton_of_mem hn, hcard, mul_comm]

/-- `unifInt z` gives each set the share of `[0, z)` it contains. -/
theorem unifInt_apply (S : Set Int) :
    unifInt z hz S = (z.toNat : ENNReal)⁻¹ * ∑ n ∈ Ico 0 z, S.indicator 1 n := by
  rw [← lintegral_unifInt, lintegral_indicator_one .of_discrete]

/-- `unifInt z` gives the singleton `{0}` mass `1/z`. -/
theorem unifInt_singleton_zero : unifInt z hz {0} = (z.toNat : ENNReal)⁻¹ := by
  rw [unifInt, Measure.uniformOfFinset_apply_singleton_of_mem (mem_Ico.2 ⟨le_rfl, hz⟩), card_Ico,
    sub_zero]

/-- `unifInt z` is carried by `[0, z)`. -/
theorem unifInt_compl_Ico : unifInt z hz (Set.Ico 0 z)ᶜ = 0 := by
  rw [unifInt, Measure.uniformOfFinset_apply_eq_zero_iff]
  simp [Set.disjoint_compl_right_iff_subset]

section
variable (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
  (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
include hdom hbij

/-- The uniform measure on `[0, z)` is invariant under a bijection of `[0, z)`. -/
theorem unifInt_map_bijOn :
    (unifInt z hz).map f = unifInt z hz := by
  refine ext_of_lintegral _ fun ψ hψ => ?_
  rw [lintegral_map hψ .of_discrete, lintegral_unifInt, lintegral_unifInt,
    sum_Ico_comp_of_bijOn hdom hbij]

variable (L) in
/-- Exact coupling of two uniform draws on `[0, z)` along a bijection `f`. -/
theorem unifInt_rel_bij [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful] [L.IsReflexive]
    [L.IsSupportLocal] :
    L.Rel 0 (fun n m ↦ 0 ≤ n ∧ n < z ∧ m = f n) (unifInt z hz) (unifInt z hz) := by
  -- reflexivity pushed along `f` relates `unifInt z` to `f_* unifInt z`, which is `unifInt z`
  have h := (rel_graph (L := L) (unifInt z hz) (f := f) .of_discrete).restrict
    measurableSet_Ico (unifInt_compl_Ico hz)
  rw [unifInt_map_bijOn hz f hdom hbij] at h
  exact h.mono le_rfl fun n m ⟨hm, h0, h1⟩ => ⟨h0, h1, hm.symm⟩

end

end UniformInt

/-- A lifting of two uniform integer draws pushes forward to the configurations they step to, under
an evaluation context `K` on the right. -/
theorem Cfg.uniform_rel_fill [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    {b : B} (HzL : 0 < zL) (HzR : 0 < zR) (σ σ' : State rT) (K : Ectx rT)
    {S : Int → Int → Prop} {S' : Cfg rT → Cfg rT → Prop}
    (h : L.Rel b S (unifInt zL HzL) (unifInt zR HzR))
    (hS : ∀ n m, S n m → S' ⟨pl(#int n), σ⟩ ⟨K.fill pl(#int m), σ'⟩) :
    L.Rel b S' (uniform zL σ) ((uniform zR σ').map K.fillCfg) := by
  rw [uniform_eq_map HzL, uniform_eq_map HzR, map_map (fillCfg.measurable K) .of_discrete]
  exact h.map hS .of_discrete .of_discrete

/-! ## Configuration couplings of `rand` draws along a bijection -/

section
variable (Hz : 0 < z)
include Hz

variable (σ σ' : State rT) (f : Int → Int)
  (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
  (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
include hdom hbij

/-- Exact coupling of `rand z ~ K[rand z]` along a bijection of `[0, z)`. -/
theorem Cfg.uniform_rel_bij_fill [Zero B] [Add B] [Preorder B]
    [OrderTop B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] (K : Ectx rT) :
    L.Rel 0 (CoupledDraw z f σ σ' K) (uniform z σ) ((uniform z σ').map K.fillCfg) :=
  uniform_rel_fill Hz Hz σ σ' K (unifInt_rel_bij L Hz f hdom hbij)
    fun n _ ⟨h0, h1, hm⟩ => ⟨n, h0, h1, rfl, hm ▸ rfl⟩

/-- Exact coupling of `rand z ~ K[rand z]` along a bijection of `[0, z)` (the `tv` instance of
`Cfg.uniform_rel_bij_fill`). -/
theorem Cfg.uniform_addCoupl_bij_fill (K : Ectx rT) :
    AddCoupl 0 {p | CoupledDraw z f σ σ' K p.1 p.2} (uniform z σ) ((uniform z σ').map K.fillCfg) :=
  (uniform_rel_bij_fill Hz σ σ' f hdom hbij K).addCoupl

/-- Exact coupling of `rand z ~ rand z` along a bijection of `[0, z)`. -/
theorem Cfg.uniform_addCoupl_bij :
    AddCoupl 0 {p : Cfg rT × Cfg rT | ∃ n, 0 ≤ n ∧ n < z ∧
        p.1 = ⟨pl(#int n), σ⟩ ∧ p.2 = ⟨pl(#int (f n)), σ'⟩}
      (uniform z σ) (uniform z σ') := by
  have h := uniform_addCoupl_bij_fill Hz σ σ' f hdom hbij []
  rwa [Ectx.fillCfg_empty, Measure.map_id] at h

end

/-! ## Uniform couplings along an injection (unequal bounds)

Coupling `unifInt zL ~ unifInt zR` along an injection costs the mass of the uncovered fraction of
the larger support (Rocq `ARcoupl_rand_rand_inj`, `ARcoupl_rand_rand_rev_inj`). -/

/-- Uniform coupling along an injection, smaller bound on the left:
`unifInt zL ~ unifInt zR` for `zL ≤ zR` along `f`, with error `(zR - zL)/zR`. -/
theorem unifInt_addCoupl_inj (HzL : 0 < zL) (Hle : zL ≤ zR) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂) :
    AddCoupl (((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal))
      {p : Int × Int | 0 ≤ p.1 ∧ p.1 < zL ∧ p.2 = f p.1}
      (unifInt zL HzL) (unifInt zR (HzL.trans_le Hle)) := by
  -- the left mass `∑ φ` is at most `S = ∑ ψ ∘ f`, which is at most `∑ ψ` and at most `zL`;
  -- rescaling from `1/zL` to `1/zR` costs at most `(zR - zL)/zR`.
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hpt
  show ∫⁻ c, φ c ∂(unifInt zL _) ≤ ∫⁻ c, ψ c ∂(unifInt zR _) + _
  rw [lintegral_unifInt, lintegral_unifInt]
  have hcast : (zR.toNat : ENNReal) = (zL.toNat : ENNReal) + ((zR - zL).toNat : ENNReal) := by
    norm_cast
    omega
  set S : ENNReal := ∑ n ∈ Ico (0 : Int) zL, ψ (f n)
  have h1 : ∑ n ∈ Ico (0 : Int) zL, φ n ≤ S :=
    sum_le_sum fun n hn => Hpt ⟨(mem_Ico.1 hn).1, (mem_Ico.1 hn).2, rfl⟩
  have h2 : S ≤ ∑ m ∈ Ico (0 : Int) zR, ψ m := sum_Ico_comp_le_of_injOn hdom hinj ψ
  have h3 : S ≤ (zL.toNat : ENNReal) := sum_Ico_le_toNat fun n => Hψb _
  calc (zL.toNat : ENNReal)⁻¹ * ∑ n ∈ Ico (0 : Int) zL, φ n
    _ ≤ (zL.toNat : ENNReal)⁻¹ * S := by gcongr
    _ ≤ (zR.toNat : ENNReal)⁻¹ * S + ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal) := by
      rw [hcast]
      exact inv_mul_le_inv_mul_add (by omega) h3
    _ ≤ (zR.toNat : ENNReal)⁻¹ * ∑ m ∈ Ico (0 : Int) zR, ψ m +
        ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal) := by gcongr

/-- Uniform coupling along an injection, smaller bound on the right:
`unifInt zL ~ unifInt zR` for `zR ≤ zL` along `f : [0, zR) ↪ [0, zL)`; the left draw is
`f m` when the right draw is `m`, with error `(zL - zR)/zL`. -/
theorem unifInt_addCoupl_rev_inj (HzR : 0 < zR) (Hle : zR ≤ zL) (f : Int → Int)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂) :
    AddCoupl (((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal))
      {p : Int × Int | 0 ≤ p.2 ∧ p.2 < zR ∧ p.1 = f p.2}
      (unifInt zL (HzR.trans_le Hle)) (unifInt zR HzR) := by
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hpt
  show ∫⁻ c, φ c ∂(unifInt zL _) ≤ ∫⁻ c, ψ c ∂(unifInt zR _) + _
  rw [lintegral_unifInt, lintegral_unifInt]
  set I := Ico (0 : Int) zR
  set J := Ico (0 : Int) zL
  have hinjOn : Set.InjOn f I := fun n hn m hm heq => by
    simp only [I, coe_Ico, Set.mem_Ico] at hn hm
    exact hinj n m hn.1 hn.2 hm.1 hm.2 heq
  have himg_sub : I.image f ⊆ J :=
    image_subset_iff.2 fun n hn => mem_Ico.2 (hdom n (mem_Ico.1 hn).1 (mem_Ico.1 hn).2)
  have himg_le : ∑ m ∈ I.image f, φ m ≤ ∑ m ∈ I, ψ m := by
    rw [sum_image hinjOn]
    exact sum_le_sum fun m hm => Hpt ⟨(mem_Ico.1 hm).1, (mem_Ico.1 hm).2, rfl⟩
  have hrest_le : ∑ n ∈ J \ I.image f, φ n ≤ ((zL - zR).toNat : ENNReal) :=
    calc ∑ n ∈ J \ I.image f, φ n
      _ ≤ ∑ _n ∈ J \ I.image f, 1 := sum_le_sum fun n _ => Hφb n
      _ = ((J \ I.image f).card : ENNReal) := by rw [sum_const, nsmul_eq_mul, mul_one]
      _ = ((zL - zR).toNat : ENNReal) := by
        rw [card_sdiff, inter_eq_left.mpr himg_sub, card_image_of_injOn hinjOn]
        simp only [I, J, card_Ico, sub_zero]
        norm_cast
        omega
  calc (zL.toNat : ENNReal)⁻¹ * ∑ n ∈ J, φ n
    _ ≤ (zL.toNat : ENNReal)⁻¹ * (∑ m ∈ I, ψ m + ((zL - zR).toNat : ENNReal)) := by
      gcongr
      rw [← sum_sdiff himg_sub, add_comm]
      exact add_le_add himg_le hrest_le
    _ = (zL.toNat : ENNReal)⁻¹ * ∑ m ∈ I, ψ m +
        ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal) := by
      rw [mul_add, div_eq_inv_mul]
    _ ≤ (zR.toNat : ENNReal)⁻¹ * ∑ m ∈ I, ψ m +
        ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal) := by
      gcongr
      exact_mod_cast toNat_le_toNat Hle

/-- The outcome of a reversed coupled draw: the right draw is `m` under `K`, the left draw is
`f m`. -/
abbrev CoupledDrawRev (z : Int) (f : Int → Int) (σ σ' : State rT) (K : Ectx rT) :
    Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
  ∃ m : Int, 0 ≤ m ∧ m < z ∧ c₁ = ⟨pl(#int (f m)), σ⟩ ∧ c₂ = ⟨K.fill pl(#int m), σ'⟩

/-- Coupling of `rand zL ~ K[rand zR]` along an injection, smaller bound on the left:
`unifInt_addCoupl_inj` pushed to configurations. -/
theorem Cfg.uniform_addCoupl_inj_fill (HzL : 0 < zL) (Hle : zL ≤ zR)
    (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂) :
    AddCoupl (((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal))
      {p | CoupledDraw zL f σ σ' K p.1 p.2}
      (uniform zL σ) ((uniform zR σ').map K.fillCfg) := by
  have h := (unifInt_addCoupl_inj HzL Hle f hdom hinj).codensity
  refine (uniform_rel_fill HzL (HzL.trans_le Hle) σ σ' K h ?_).addCoupl
  rintro n _ ⟨h0, h1, hm⟩
  exact ⟨n, h0, h1, rfl, hm ▸ rfl⟩

/-- Coupling of `rand zL ~ K[rand zR]` along an injection, smaller bound on the right:
`unifInt_addCoupl_rev_inj` pushed to configurations. -/
theorem Cfg.uniform_addCoupl_rev_inj_fill (HzR : 0 < zR)
    (Hle : zR ≤ zL) (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂) :
    AddCoupl (((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal))
      {p | CoupledDrawRev zR f σ σ' K p.1 p.2}
      (uniform zL σ) ((uniform zR σ').map K.fillCfg) := by
  have h := (unifInt_addCoupl_rev_inj HzR Hle f hdom hinj).codensity
  refine (uniform_rel_fill (HzR.trans_le Hle) HzR σ σ' K h ?_).addCoupl
  rintro _ m ⟨h0, h1, hm⟩
  exact ⟨m, h0, h1, hm ▸ rfl, rfl⟩

/-- Coupling of `rand zL ~ rand zR` along an injection, smaller bound on the left. -/
theorem Cfg.uniform_addCoupl_inj (HzL : 0 < zL) (Hle : zL ≤ zR)
    (σ σ' : State rT) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂) :
    AddCoupl (((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal))
      {p : Cfg rT × Cfg rT | ∃ n, 0 ≤ n ∧ n < zL ∧
        p.1 = ⟨pl(#int n), σ⟩ ∧ p.2 = ⟨pl(#int (f n)), σ'⟩}
      (uniform zL σ) (uniform zR σ') := by
  have h := uniform_addCoupl_inj_fill HzL Hle σ σ' f [] hdom hinj
  rwa [Ectx.fillCfg_empty, Measure.map_id] at h

/-- Coupling of `rand zL ~ rand zR` along an injection, smaller bound on the right. -/
theorem Cfg.uniform_addCoupl_rev_inj (HzR : 0 < zR) (Hle : zR ≤ zL)
    (σ σ' : State rT) (f : Int → Int) (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂) :
    AddCoupl (((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal))
      {p : Cfg rT × Cfg rT | ∃ m, 0 ≤ m ∧ m < zR ∧
        p.1 = ⟨pl(#int (f m)), σ⟩ ∧ p.2 = ⟨pl(#int m), σ'⟩}
      (uniform zL σ) (uniform zR σ') := by
  have h := uniform_addCoupl_rev_inj_fill HzR Hle σ σ' f [] hdom hinj
  rwa [Ectx.fillCfg_empty, Measure.map_id] at h

/-! ## Steps of `rand` -/

variable [LawfulProbLangℝ rT]

/-- If the head step of a locally closed `e` is `Cfg.uniform z σ`, so is its program step. -/
theorem primStep_eq_uniform_of_headStep {e : Exp rT} (h : headStep ⟨e, σ⟩ = uniform z σ)
    (hlc : e.IsLocallyClosed := by is_lc) : primStep ⟨e, σ⟩ = uniform z σ := by
  rw [primStep_eq_headStep (decompItem_none_of_lc_headReducible hlc (h ▸ uniform_ne_zero z σ)), h]

/-- `rand z` on the unit label steps to `Cfg.uniform z σ`. -/
theorem primStep_rand_unit (_Hz : 0 < z) (σ : State rT) :
    primStep ⟨pl(rand(#z, #())), σ⟩ = uniform z σ := by
  have h : headStep ⟨pl(rand(#z, #())), σ⟩ = uniform z σ := rfl
  exact primStep_eq_uniform_of_headStep h

/-- `primStep_rand_unit` together with discrete reducibility of `rand z`. -/
@[discrete]
theorem randUnit_uniform_step (Hz : 0 < z) (σ : State rT) :
    Discrete.Reducible pl(rand(#z, #())) σ ∧ primStep ⟨pl(rand(#z, #())), σ⟩ = uniform z σ :=
  ⟨.of_headStepSupport (.RandNoTapeS Hz le_rfl Hz) (by is_lc),
    primStep_rand_unit Hz σ⟩

variable {σ : State rT} {l : Loc} {M : Int}

/-- The head step of `rand z` on a tape label, by the tape's state. -/
theorem headStep_rand_lbl :
    headStep ⟨pl(rand(#z, #lbl l)), σ⟩ = match σ.tapes[l]? with
      | none => 0
      | some ⟨M, ns⟩ =>
        if M = z then
          match ns with
          | [] => uniform z σ
          | n :: ns => dirac ⟨.lit <| .int n,
            σ.update_tapes fun t => t.insert l ⟨M, ns⟩⟩
        else uniform z σ :=
  rfl

/-- `rand z` on a tape of another bound `M` steps to `Cfg.uniform z σ`. -/
theorem primStep_rand_lbl_wrong (HneM : z ≠ M) {fs : List { z' : Int // 0 ≤ z' ∧ z' < M }}
    (Hlk : σ.tapes[l]? = some ⟨M, fs⟩) :
    primStep ⟨pl(rand(#z, #lbl l)), σ⟩ = uniform z σ := by
  have h : headStep ⟨pl(rand(#z, #lbl l)), σ⟩ = uniform z σ := by
    rw [headStep_rand_lbl, Hlk]
    simp only [ite_eq_right (Ne.symm HneM)]
  exact primStep_eq_uniform_of_headStep h

/-- `rand z` on an empty tape of bound `z` steps to `Cfg.uniform z σ`. -/
theorem primStep_rand_lbl_empty (Hlk : σ.tapes[l]? = some ⟨z, []⟩) :
    primStep ⟨pl(rand(#z, #lbl l)), σ⟩ = uniform z σ := by
  have h : headStep ⟨pl(rand(#z, #lbl l)), σ⟩ = uniform z σ := by
    rw [headStep_rand_lbl, Hlk]
    simp only [↓reduceIte]
  exact primStep_eq_uniform_of_headStep h

/-- `primStep_rand_lbl_empty` with discrete reducibility. -/
@[discrete]
theorem randLbl_empty_uniform_step (Hz : 0 < z) (Hlk : σ.tapes[l]? = some ⟨z, []⟩) :
    Discrete.Reducible pl(rand(#z, #lbl l)) σ ∧ primStep ⟨pl(rand(#z, #lbl l)), σ⟩ = uniform z σ :=
  ⟨.of_headStepSupport (.RandTapeEmptyS Hz Hlk rfl le_rfl Hz rfl) (by is_lc),
    primStep_rand_lbl_empty Hlk⟩

/-- `primStep_rand_lbl_wrong` with discrete reducibility. -/
@[discrete]
theorem randLbl_wrong_uniform_step (Hz : 0 < z) (HneM : z ≠ M)
    {fs : List { z' : Int // 0 ≤ z' ∧ z' < M }} (Hlk : σ.tapes[l]? = some ⟨M, fs⟩) :
    Discrete.Reducible pl(rand(#z, #lbl l)) σ ∧ primStep ⟨pl(rand(#z, #lbl l)), σ⟩ = uniform z σ :=
  ⟨.of_headStepSupport (.RandTapeOtherS Hz Hlk HneM le_rfl Hz rfl) (by is_lc),
    primStep_rand_lbl_wrong HneM Hlk⟩

/-! ## Couplings of steps under an evaluation context -/

variable {e : Exp rT} {ε : ENNReal}

/-- A coupling with a step of `e` gives one with a step of `K[e]`. -/
theorem addCoupl_steps_ctx_bind_r {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {R : Set (α × Cfg rT)} {K : Ectx rT}
    (hv : ¬ e.isValue) (Hcpl : AddCoupl ε R μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε {p | ∃ e'', p.2.expr = K.fill e'' ∧ R (p.1, ⟨e'', p.2.state⟩)} μ
      (primStep ⟨K.fill e, σ⟩) := by
  rw [primStep_fill hv, ← Measure.map_id (μ := μ)]
  exact Hcpl.map id K.fillCfg measurable_id (fillCfg.measurable K) fun HR => ⟨_, rfl, HR⟩

/-- `addCoupl_steps_ctx_bind_r` for a relation on expressions only. -/
theorem addCoupl_steps_ctx_bind_r_no_state {μ : Measure (Cfg rT)}
    {R : Exp rT → Exp rT → Prop} {K : Ectx rT} (hv : ¬ e.isValue)
    (Hcpl : AddCoupl ε {p : Cfg rT × Cfg rT | R p.1.expr p.2.expr} μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε {p | ∃ e'', p.2.expr = K.fill e'' ∧ R p.1.expr e''} μ (primStep ⟨K.fill e, σ⟩) :=
  addCoupl_steps_ctx_bind_r hv Hcpl

/-! ## Outcome-dependent cost of a coupled draw -/

/-- Coupling `rand z ~ K[rand z]` along a bijection `f`, paying `s (ε₂ n)` at the left draw `n`
out of `s ε₁`. -/
theorem Cfg.uniform_lift_adv [AddCommMonoid B] [PartialOrder B]
    [CanonicallyOrderedAdd B] [OrderTop B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
    {s : ENNReal →+o B} [L.IsExpectationAdditive s] (Hz : 0 < z) (f : Int → Int) (ε₁ : ENNReal)
    (ε₂ : Int → ENNReal) (σ σ' : State rT) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (hamort : (∑ n ∈ Ico 0 z, ε₂ n) / z.toNat ≤ ε₁) :
    L (s ε₁) (advLeftover s z f σ σ' K ε₂) (primStep ⟨pl(rand(#z, #())), σ⟩)
      (primStep ⟨K.fill pl(rand(#z, #())), σ'⟩) := by
  -- Idea: `c m = ε₂ (f⁻¹ m)` is paid in expectation over the exact bijection coupling
  -- (`IsExpectationAdditive.add_right`); the average of `c` is the amortised bound `hamort`.
  set c : Int → ENNReal := fun m => ⨅ n, ⨅ (_ : (0 ≤ n ∧ n < z) ∧ f n = m), ε₂ n
  have hcf : ∀ n, 0 ≤ n → n < z → c (f n) = ε₂ n := fun n h0 h1 => by
    obtain ⟨_, -, huniq⟩ := hbij (f n) (hdom n h0 h1).1 (hdom n h0 h1).2
    refine _root_.le_antisymm (iInf₂_le n ⟨⟨h0, h1⟩, rfl⟩) (le_iInf₂ fun n' hn' => ?_)
    rw [(huniq n' hn').trans (huniq n ⟨⟨h0, h1⟩, rfl⟩).symm]
  have hint : 0 + s (∫⁻ m, c m ∂unifInt z Hz) ≤ s ε₁ := by
    rw [zero_add]
    refine OrderHomClass.mono s ?_
    rwa [lintegral_unifInt, ← sum_Ico_comp_of_bijOn hdom hbij c,
      sum_congr rfl fun n hn => hcf n (mem_Ico.1 hn).1 (mem_Ico.1 hn).2, ← div_eq_inv_mul]
  have h := IsExpectationAdditive.add_right (s := s) (c := c) .of_discrete
    (unifInt_rel_bij L Hz f hdom hbij)
  rw [primStep_rand_unit Hz, primStep_fill rand_not_isValue, primStep_rand_unit Hz,
    uniform_eq_map Hz σ, uniform_eq_map Hz σ',
    map_map (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
      (fillCfg.measurable K) .of_discrete]
  refine map .of_discrete .of_discrete (mono h hint fun n m => ?_)
  by_cases hnm : 0 ≤ n ∧ n < z ∧ m = f n
  · obtain ⟨h0, h1, rfl⟩ := hnm
    simp only [relCost_of (S := fun n m ↦ 0 ≤ n ∧ n < z ∧ m = f n) ⟨h0, h1, rfl⟩,
      zero_add, hcf n h0 h1]
    exact (advLeftover_apply s f σ σ' K ε₂ h0 h1).le
  · simp only [relCost_of_not (S := fun n m ↦ 0 ≤ n ∧ n < z ∧ m = f n) hnm]
    exact le_top.trans le_self_add

/-! ## The identity bijection and one-point avoidance -/

/-- `id` maps `[0, z)` into itself. -/
theorem id_dom_range : ∀ n, 0 ≤ n → n < z → 0 ≤ id n ∧ id n < z :=
  fun _ h0 hlt => ⟨h0, hlt⟩

/-- `id` is a bijection of `[0, z)`. -/
theorem id_bij_range : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ id n = m :=
  fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun _ ⟨_, heq⟩ => heq⟩

/-- Avoiding one value `bad` costs an average of at most `1/z`. -/
theorem avoid_one_amort (bad : Int) :
    (∑ n ∈ Ico 0 z, if n = bad then (1 : ENNReal) else 0) / z.toNat ≤ (z.toNat : ENNReal)⁻¹ := by
  rw [← one_div]
  gcongr
  rw [sum_ite_eq']
  split <;> simp

/-! ## Timeless tape and heap points-to predicates -/

section TimelessTapes

variable {GF : BundledGFunctors} {l : Loc} {t : Tape} {v : Val rT}

/-- Fragments of application tapes are timeless. -/
instance appTapesFrag_timeless [AppGS rT GF] :
    Timeless (l ↪ₐ t : IProp GF) := iOwn_timeless

variable [SpecGS rT GF]

/-- Fragments of spec tapes are timeless. -/
instance specTapesFrag_timeless :
    Timeless (l ↪ₛ t : IProp GF) := iOwn_timeless

/-- Fragments of the application heap are timeless. -/
instance appHeapFrag_timeless [AppGS rT GF] :
    Timeless (l ↦ v : IProp GF) := iOwn_timeless

/-- Fragments of the spec heap are timeless. -/
instance specHeapFrag_timeless : Timeless (l ↦ₛ v : IProp GF) := iOwn_timeless

variable {ns : List Int}

/-- Application natural-number tapes are timeless. -/
instance appNatTape_timeless [AppGS rT GF] :
    Timeless (appNatTape l z ns : IProp GF) := by
  unfold appNatTape
  infer_instance

/-- Spec natural-number tapes are timeless. -/
instance specNatTape_timeless :
    Timeless (specNatTape l z ns : IProp GF) := by
  unfold specNatTape
  infer_instance

end TimelessTapes

end ProbLang
