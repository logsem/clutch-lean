module

public import Metrology.Micrometer.Lifting
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.ProbLang.Metatheory
public import Metrology.Couplings.Bridges.AddCoupl

@[expose] public section

set_option linter.discrete false

/-! # Coupling Rules -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting
open scoped AppGS

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]
variable {B : Type} {L : GradedLifting.{0} B}

/-! ## `id` as a coupling bijection -/

theorem id_dom_range {z : Int} : ∀ n, 0 ≤ n → n < z → 0 ≤ id n ∧ id n < z :=
  fun _ h0 hlt => ⟨h0, hlt⟩

theorem avoid_one_amort {z : Int} (bad : Int) :
    (∑ n ∈ Finset.Ico 0 z, if n = bad then (1 : ENNReal) else 0) / z.toNat ≤
      (z.toNat : ENNReal)⁻¹ := by
  rw [← one_div]
  gcongr
  rw [Finset.sum_ite_eq']
  split <;> simp

theorem id_bij_range {z : Int} : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ id n = m :=
  fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun _ ⟨_, heq⟩ => heq⟩

/-! ## Timeless instances for tape predicates -/

section TimelessTapes

variable {GF : BundledGFunctors}

instance heapView_tape_frag_discreteE (l : Loc) (t : Tape) :
    OFE.DiscreteE (HeapView.Frag (H := LocHeap) l (.own 1) (toAgree t)) :=
  View.frag_discrete

instance appTapesFrag_timeless [MeasurableSingletonClass rT] [AppGS rT GF] (l : Loc) (t : Tape) :
    BI.Timeless (l ↪ₐ t : IProp GF) := iOwn_timeless

instance specTapesFrag_timeless [MeasurableSingletonClass rT] [SpecGS rT GF]
    (l : Loc) (t : Tape) : BI.Timeless (l ↪ₛ t : IProp GF) := iOwn_timeless

instance heapView_heap_frag_discreteE (l : Loc) (v : Val rT) :
    OFE.DiscreteE (HeapView.Frag (H := LocHeap) l (.own 1) (toAgree v)) :=
  View.frag_discrete

instance appHeapFrag_timeless [MeasurableSingletonClass rT] [AppGS rT GF]
    (l : Loc) (v : Val rT) : BI.Timeless (l ↦ v : IProp GF) := by
  unfold appHeapFrag
  exact iOwn_timeless

instance specHeapFrag_timeless [MeasurableSingletonClass rT] [SpecGS rT GF]
    (l : Loc) (v : Val rT) : BI.Timeless (l ↦ₛ v : IProp GF) := by
  unfold specHeapFrag
  exact iOwn_timeless

instance appNatTape_timeless [MeasurableSingletonClass rT] [AppGS rT GF]
    (l : Loc) (z : Int) (ns : List Int) : BI.Timeless (appNatTape l z ns : IProp GF) := by
  unfold appNatTape
  infer_instance

instance specNatTape_timeless [MeasurableSingletonClass rT] [SpecGS rT GF]
    (l : Loc) (z : Int) (ns : List Int) : BI.Timeless (specNatTape l z ns : IProp GF) := by
  unfold specNatTape
  infer_instance

end TimelessTapes

/-! ## Fold/unfold bridges for the user-level tape predicates -/

section NatTapeBridges

variable {GF : BundledGFunctors}

theorem appNatTape_fold [AppGS rT GF] {l : Loc} {z : Int} {ns : List Int}
    {fs : List { z' : Int // 0 ≤ z' ∧ z' < z }} (hfs : fs.map (fun x => x.val) = ns) :
    l ↪ₐ ⟨z, fs⟩ ⊢@{IProp GF} appNatTape l z ns := by
  iintro Hb
  iunfold appNatTape
  iexists fs
  iframe %hfs Hb

theorem specNatTape_fold [SpecGS rT GF] {l : Loc} {z : Int} {ns : List Int}
    {fs : List { z' : Int // 0 ≤ z' ∧ z' < z }} (hfs : fs.map (fun x => x.val) = ns) :
    l ↪ₛ ⟨z, fs⟩ ⊢@{IProp GF} specNatTape l z ns := by
  iintro Hb
  iunfold specNatTape
  iexists fs
  iframe %hfs Hb

end NatTapeBridges

/-! ## Core probability fact: uniform coupling under bijection -/

section UniformInt

open MeasureTheory

/-- The uniform measure on `[0, z)`. -/
noncomputable def unifInt (z : Int) (hz : 0 < z) : Measure Int :=
  (PMF.uniformOfFinset (Finset.Ico 0 z) (Finset.nonempty_Ico.mpr hz)).toMeasure

instance unifInt.isProbabilityMeasure {z : Int} {hz : 0 < z} :
    IsProbabilityMeasure (unifInt z hz) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- Integrals against `unifInt z` are averages over `[0, z)`. -/
theorem lintegral_unifInt {z : Int} (hz : 0 < z) (φ : Int → ENNReal) :
    ∫⁻ n, φ n ∂unifInt z hz = (z.toNat : ENNReal)⁻¹ * ∑ n ∈ Finset.Ico 0 z, φ n := by
  have hcard : (Finset.Ico (0 : Int) z).card = z.toNat := by rw [Int.card_Ico]; omega
  rw [unifInt, lintegral_countable', tsum_eq_sum fun n hn => by
      rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        PMF.uniformOfFinset_apply_of_notMem _ hn, mul_zero], Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.uniformOfFinset_apply_of_mem _ hn, hcard, mul_comm]

/-- `unifInt z` is carried by `[0, z)`. -/
theorem unifInt_compl_Ico {z : Int} (hz : 0 < z) : unifInt z hz (Set.Ico 0 z)ᶜ = 0 := by
  rw [unifInt, PMF.toMeasure_apply_eq_zero_iff _ measurableSet_Ico.compl]
  simp [Set.disjoint_compl_right_iff_subset]

/-- The uniform measure on `[0, z)` is invariant under a bijection of `[0, z)`. -/
theorem unifInt_map_bijOn {z : Int} (hz : 0 < z) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) :
    (unifInt z hz).map f = unifInt z hz := by
  refine Measure.ext_of_lintegral _ fun ψ hψ => ?_
  rw [lintegral_map hψ Measurable.of_discrete, lintegral_unifInt, lintegral_unifInt,
    Finset.sum_Ico_comp_of_bijOn hdom hbij]

variable (L) in
/-- Exact coupling of two uniform draws on `[0, z)` along a bijection `f`. -/
theorem unifInt_codensity_bij [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [L.IsReflexive] [L.IsSupportLocal] {z : Int} (hz : 0 < z) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) :
    L.Rel 0 (fun n m ↦ 0 ≤ n ∧ n < z ∧ m = f n) (unifInt z hz) (unifInt z hz) := by
  have h := (rel_graph (L := L) (unifInt z hz) (f := f) Measurable.of_discrete).restrict
    measurableSet_Ico (unifInt_compl_Ico hz)
  rw [unifInt_map_bijOn hz f hdom hbij] at h
  exact h.mono le_rfl fun n m ⟨hm, h0, h1⟩ => ⟨h0, h1, hm.symm⟩

/-- `Cfg.uniform z σ` is `unifInt z` pushed to integer literals. -/
theorem Cfg.uniform_eq_map {z : Int} (hz : 0 < z) (σ : State rT) :
    Cfg.uniform z σ = (unifInt z hz).map fun n => (⟨pl(#(.int n)), σ⟩ : Cfg rT) :=
  Cfg.uniform_eq_map_uniformOfFinset hz σ

/-- Pushes a coupling of two uniform integer draws to the configurations they step to, under an
evaluation context `K` on the right. -/
theorem Cfg.uniform_codensity_fill [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    {b : B} {zL zR : Int} (HzL : 0 < zL) (HzR : 0 < zR) (σ σ' : State rT) (K : Ectx rT)
    {S : Int → Int → Prop} {S' : Cfg rT → Cfg rT → Prop}
    (h : L.Rel b S (unifInt zL HzL) (unifInt zR HzR))
    (hS : ∀ n m, S n m → S' ⟨pl(#(.int n)), σ⟩ ⟨K.fill pl(#(.int m)), σ'⟩) :
    L.Rel b S' (Cfg.uniform zL σ) ((Cfg.uniform zR σ').map K.fillCfg) := by
  rw [Cfg.uniform_eq_map HzL, Cfg.uniform_eq_map HzR,
    Measure.map_map (Ectx.fillCfg.measurable K) Measurable.of_discrete]
  exact h.map hS Measurable.of_discrete Measurable.of_discrete

end UniformInt

/-- The outcome of a coupled draw: the left draw is `n`, the right draw is `f n` under `K`. -/
@[reducible] def CoupledDraw (z : Int) (f : Int → Int) (σ σ' : State rT) (K : Ectx rT) :
    Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
  ∃ n : Int, 0 ≤ n ∧ n < z ∧
    c₁ = ⟨pl(#(.int n)), σ⟩ ∧ c₂ = ⟨K.fill (pl(#(.int (f n)))), σ'⟩

/-- Exact coupling of `rand z ~ K[rand z]` along a bijection of `[0, z)`. -/
theorem Cfg.uniform_codensity_bij_fill [MeasurableSingletonClass rT] [Zero B] [Add B]
    [Preorder B] [OrderTop B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] {z : Int}
    (Hz : 0 < z) (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) :
    L.Rel 0 (CoupledDraw z f σ σ' K) (Cfg.uniform z σ) ((Cfg.uniform z σ').map K.fillCfg) :=
  Cfg.uniform_codensity_fill Hz Hz σ σ' K (unifInt_codensity_bij L Hz f hdom hbij)
    fun n _ ⟨h0, h1, hm⟩ => ⟨n, h0, h1, rfl, hm ▸ rfl⟩

/-- Exact coupling of `rand z ~ rand z` along a bijection of `[0, z)` (the `tv` instance of
`unifInt_codensity_bij`). -/
theorem Cfg.uniform_addCoupl_bij [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ σ' : State rT) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) :
    AddCoupl 0
      {p : Cfg rT × Cfg rT | ∃ n, 0 ≤ n ∧ n < z ∧
        p.1 = ⟨pl(#(.int n)), σ⟩ ∧ p.2 = ⟨pl(#(.int (f n))), σ'⟩}
      (Cfg.uniform z σ) (Cfg.uniform z σ') := by
  rw [Cfg.uniform_eq_map Hz, Cfg.uniform_eq_map Hz]
  refine Rel.addCoupl (S := fun (c₁ c₂ : Cfg rT) => ∃ n, 0 ≤ n ∧ n < z ∧
    c₁ = ⟨pl(#(.int n)), σ⟩ ∧ c₂ = ⟨pl(#(.int (f n))), σ'⟩)
    ((unifInt_codensity_bij GradedDivergence.tv.codensity Hz f hdom hbij).map ?_
      Measurable.of_discrete Measurable.of_discrete)
  rintro n _ ⟨h0, h1, hm⟩
  exact ⟨n, h0, h1, rfl, hm ▸ rfl⟩

/-- Exact coupling of `rand z ~ K[rand z]` along a bijection of `[0, z)` (the `tv` instance of
`Cfg.uniform_codensity_bij_fill`). -/
theorem Cfg.uniform_addCoupl_bij_fill [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) :
    AddCoupl 0 {p | CoupledDraw z f σ σ' K p.1 p.2}
      (Cfg.uniform z σ) ((Cfg.uniform z σ').map K.fillCfg) :=
  (Cfg.uniform_codensity_bij_fill Hz σ σ' f K hdom
    hbij).addCoupl

/-! ## Core probability fact: uniform couplings along an injection (unequal bounds)

Ports `ARcoupl_rand_rand_inj` / `ARcoupl_rand_rand_rev_inj` from
`clutch/theories/approxis/coupling_rules.v`: coupling `rand zL ~ rand zR` along an
injection costs the mass of the uncovered fraction of the *larger* support. -/

/-- Uniform coupling along an injection, smaller bound on the left:
`rand zL ~ rand zR` for `zL ≤ zR` along `f`, with error `(zR - zL)/zR`. -/
theorem unifInt_addCoupl_inj {zL zR : Int} (HzL : 0 < zL) (Hle : zL ≤ zR) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂) :
    AddCoupl (((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal))
      {p : Int × Int | 0 ≤ p.1 ∧ p.1 < zL ∧ p.2 = f p.1}
      (unifInt zL HzL) (unifInt zR (HzL.trans_le Hle)) := by
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hpt
  show ∫⁻ c, φ c ∂(unifInt zL _) ≤ ∫⁻ c, ψ c ∂(unifInt zR _) + _
  rw [lintegral_unifInt, lintegral_unifInt]
  have hcast : (zR.toNat : ENNReal) = (zL.toNat : ENNReal) + ((zR - zL).toNat : ENNReal) := by
    norm_cast
    omega
  set S : ENNReal := ∑ n ∈ Finset.Ico (0 : Int) zL, ψ (f n)
  have h1 : ∑ n ∈ Finset.Ico (0 : Int) zL, φ n ≤ S :=
    Finset.sum_le_sum fun n hn => Hpt ⟨(Finset.mem_Ico.1 hn).1, (Finset.mem_Ico.1 hn).2, rfl⟩
  have h2 : S ≤ ∑ m ∈ Finset.Ico (0 : Int) zR, ψ m :=
    Finset.sum_Ico_comp_le_of_injOn hdom hinj ψ
  have h3 : S ≤ (zL.toNat : ENNReal) := Finset.sum_Ico_le_toNat fun n => Hψb _
  calc (zL.toNat : ENNReal)⁻¹ * ∑ n ∈ Finset.Ico (0 : Int) zL, φ n
    _ ≤ (zL.toNat : ENNReal)⁻¹ * S := by gcongr
    _ ≤ (zR.toNat : ENNReal)⁻¹ * S + ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal) := by
        rw [hcast]
        exact ENNReal.inv_mul_le_inv_mul_add (by omega) h3
    _ ≤ (zR.toNat : ENNReal)⁻¹ * ∑ m ∈ Finset.Ico (0 : Int) zR, ψ m +
          ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal) := by gcongr

/-- Uniform coupling along an injection, smaller bound on the right:
`rand zL ~ rand zR` for `zR ≤ zL` along `f : [0, zR) ↪ [0, zL)`; the left draw is
`f m` when the right draw is `m`, with error `(zL - zR)/zL`. -/
theorem unifInt_addCoupl_rev_inj {zL zR : Int} (HzR : 0 < zR) (Hle : zR ≤ zL) (f : Int → Int)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂) :
    AddCoupl (((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal))
      {p : Int × Int | 0 ≤ p.2 ∧ p.2 < zR ∧ p.1 = f p.2}
      (unifInt zL (HzR.trans_le Hle)) (unifInt zR HzR) := by
  classical
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hpt
  show ∫⁻ c, φ c ∂(unifInt zL _) ≤ ∫⁻ c, ψ c ∂(unifInt zR _) + _
  rw [lintegral_unifInt, lintegral_unifInt]
  set I := Finset.Ico (0 : Int) zR
  set J := Finset.Ico (0 : Int) zL
  have hinjOn : Set.InjOn f I := fun n hn m hm heq => by
    simp only [I, Finset.coe_Ico, Set.mem_Ico] at hn hm
    exact hinj n m hn.1 hn.2 hm.1 hm.2 heq
  have himg_sub : I.image f ⊆ J :=
    Finset.image_subset_iff.2 fun n hn =>
      Finset.mem_Ico.2 (hdom n (Finset.mem_Ico.1 hn).1 (Finset.mem_Ico.1 hn).2)
  have himg_le : ∑ m ∈ I.image f, φ m ≤ ∑ m ∈ I, ψ m := by
    rw [Finset.sum_image hinjOn]
    exact Finset.sum_le_sum fun m hm => Hpt ⟨(Finset.mem_Ico.1 hm).1, (Finset.mem_Ico.1 hm).2, rfl⟩
  have hrest_le : ∑ n ∈ J \ I.image f, φ n ≤ ((zL - zR).toNat : ENNReal) :=
    calc ∑ n ∈ J \ I.image f, φ n
      _ ≤ ∑ _n ∈ J \ I.image f, 1 := Finset.sum_le_sum fun n _ => Hφb n
      _ = ((J \ I.image f).card : ENNReal) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ((zL - zR).toNat : ENNReal) := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr himg_sub,
            Finset.card_image_of_injOn hinjOn]
          simp only [I, J, Int.card_Ico, Int.sub_zero]
          norm_cast
          omega
  calc (zL.toNat : ENNReal)⁻¹ * ∑ n ∈ J, φ n
    _ ≤ (zL.toNat : ENNReal)⁻¹ * (∑ m ∈ I, ψ m + ((zL - zR).toNat : ENNReal)) := by
        gcongr
        rw [← Finset.sum_sdiff himg_sub, add_comm]
        exact add_le_add himg_le hrest_le
    _ = (zL.toNat : ENNReal)⁻¹ * ∑ m ∈ I, ψ m +
          ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal) := by
        rw [mul_add, ENNReal.div_eq_inv_mul]
    _ ≤ (zR.toNat : ENNReal)⁻¹ * ∑ m ∈ I, ψ m +
          ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal) := by
        gcongr
        exact_mod_cast Int.toNat_le_toNat Hle

/-- Uniform coupling along an injection, smaller bound on the left:
`rand zL ~ rand zR` for `zL ≤ zR` along `f`, with error `(zR - zL)/zR`. -/
theorem Cfg.uniform_addCoupl_inj [MeasurableSingletonClass rT] {zL zR : Int}
    (HzL : 0 < zL) (Hle : zL ≤ zR) (σ σ' : State rT) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂) :
    AddCoupl (((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal))
      {p : Cfg rT × Cfg rT | ∃ n, 0 ≤ n ∧ n < zL ∧
        p.1 = ⟨pl(#(.int n)), σ⟩ ∧ p.2 = ⟨pl(#(.int (f n))), σ'⟩}
      (Cfg.uniform zL σ) (Cfg.uniform zR σ') := by
  rw [Cfg.uniform_eq_map HzL, Cfg.uniform_eq_map (HzL.trans_le Hle)]
  refine AddCoupl.map _ _ Measurable.of_discrete Measurable.of_discrete ?_
    (unifInt_addCoupl_inj HzL Hle f hdom hinj)
  rintro n _ ⟨h0, h1, hm⟩
  exact ⟨n, h0, h1, rfl, hm ▸ rfl⟩

/-- Uniform coupling along an injection, smaller bound on the right:
`rand zL ~ rand zR` for `zR ≤ zL` along `f : [0, zR) ↪ [0, zL)`; the left draw is
`f m` when the right draw is `m`, with error `(zL - zR)/zL`. -/
theorem Cfg.uniform_addCoupl_rev_inj [MeasurableSingletonClass rT] {zL zR : Int}
    (HzR : 0 < zR) (Hle : zR ≤ zL) (σ σ' : State rT) (f : Int → Int)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂) :
    AddCoupl (((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal))
      {p : Cfg rT × Cfg rT | ∃ m, 0 ≤ m ∧ m < zR ∧
        p.1 = ⟨pl(#(.int (f m))), σ⟩ ∧ p.2 = ⟨pl(#(.int m)), σ'⟩}
      (Cfg.uniform zL σ) (Cfg.uniform zR σ') := by
  rw [Cfg.uniform_eq_map (HzR.trans_le Hle), Cfg.uniform_eq_map HzR]
  refine AddCoupl.map _ _ Measurable.of_discrete Measurable.of_discrete ?_
    (unifInt_addCoupl_rev_inj HzR Hle f hdom hinj)
  rintro _ m ⟨h0, h1, hm⟩
  exact ⟨m, h0, h1, hm ▸ rfl, rfl⟩

/-- Like `CoupledDraw`, but for the reversed injective coupling: the left draw is
`f m` for the right draw `m`. -/
@[reducible] def CoupledDrawRev (z : Int) (f : Int → Int) (σ σ' : State rT) (K : Ectx rT) :
    Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
  ∃ m : Int, 0 ≤ m ∧ m < z ∧
    c₁ = ⟨pl(#(.int (f m))), σ⟩ ∧ c₂ = ⟨K.fill (pl(#(.int m))), σ'⟩

/-- Coupling of `rand zL ~ K[rand zR]` along an injection, smaller bound on the left (the `tv`
instance of `Cfg.uniform_codensity_fill`). -/
theorem Cfg.uniform_addCoupl_inj_fill [MeasurableSingletonClass rT] {zL zR : Int}
    (HzL : 0 < zL) (Hle : zL ≤ zR) (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂) :
    AddCoupl (((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal))
      {p | CoupledDraw zL f σ σ' K p.1 p.2}
      (Cfg.uniform zL σ) ((Cfg.uniform zR σ').map K.fillCfg) := by
  have h := (unifInt_addCoupl_inj HzL Hle f hdom hinj).codensity
  refine (Cfg.uniform_codensity_fill HzL (HzL.trans_le Hle) σ σ' K h ?_).addCoupl
  rintro n _ ⟨h0, h1, hm⟩
  exact ⟨n, h0, h1, rfl, hm ▸ rfl⟩

/-- Coupling of `rand zL ~ K[rand zR]` along an injection, smaller bound on the right (the `tv`
instance of `Cfg.uniform_codensity_fill`). -/
theorem Cfg.uniform_addCoupl_rev_inj_fill [MeasurableSingletonClass rT] {zL zR : Int}
    (HzR : 0 < zR) (Hle : zR ≤ zL) (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂) :
    AddCoupl (((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal))
      {p | CoupledDrawRev zR f σ σ' K p.1 p.2}
      (Cfg.uniform zL σ) ((Cfg.uniform zR σ').map K.fillCfg) := by
  have h := (unifInt_addCoupl_rev_inj HzR Hle f hdom hinj).codensity
  refine (Cfg.uniform_codensity_fill (HzR.trans_le Hle) HzR σ σ' K h ?_).addCoupl
  rintro _ m ⟨h0, h1, hm⟩
  exact ⟨m, h0, h1, hm ▸ rfl, rfl⟩

theorem primStep_rand_unit [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z) (σ : State rT) :
    primStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩ = Cfg.uniform z σ := by
  have Hwitness : HeadStepSupport ⟨pl(rand(#(.int z), #(.unit))), σ⟩ ⟨pl(#(.int 0)), σ⟩ :=
    .RandNoTapeS Hz le_rfl Hz
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc)
    (HeadReducible.of_headStepSupport Hwitness))]
  rfl

theorem randUnit_uniform_step [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) :
    Discrete.Reducible pl(rand(#(.int z), #(.unit))) σ ∧
      primStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩ = Cfg.uniform z σ :=
  ⟨.of_headStepSupport (.RandNoTapeS Hz le_rfl Hz) (by is_lc),
    primStep_rand_unit Hz σ⟩

theorem primStep_rand_lbl_eq [MeasurableSingletonClass rT] {z : Int} {σ : State rT} {l : Loc}
    {ρ : Cfg rT} (Hwit : HeadStepSupport ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ ρ) :
    primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ =
      match σ.tapes[l]? with
      | none => 0
      | some ⟨M, ns⟩ =>
        if M = z then
          match ns with
          | [] => Cfg.uniform z σ
          | n :: ns => MeasureTheory.Measure.dirac ⟨.lit <| .int n,
              σ.update_tapes fun t => t.insert l ⟨M, ns⟩⟩
        else Cfg.uniform z σ := by
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc)
    (HeadReducible.of_headStepSupport Hwit))]
  rfl

theorem primStep_rand_lbl_wrong [MeasurableSingletonClass rT] {z M : Int} (Hz : 0 < z)
    (HneM : z ≠ M) (σ : State rT) (l : Loc) (fs : List { z' : Int // 0 ≤ z' ∧ z' < M })
    (Hlk : σ.tapes[l]? = some ⟨M, fs⟩) :
    primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ = Cfg.uniform z σ := by
  rw [primStep_rand_lbl_eq (.RandTapeOtherS Hz Hlk HneM le_rfl Hz rfl), Hlk]
  simp only [ite_eq_right (Ne.symm HneM)]

theorem primStep_rand_lbl_empty [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) (l : Loc) (Hlk : σ.tapes[l]? = some ⟨z, []⟩) :
    primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ = Cfg.uniform z σ := by
  rw [primStep_rand_lbl_eq (.RandTapeEmptyS Hz Hlk rfl le_rfl Hz rfl), Hlk]
  simp only [↓reduceIte]

private theorem randLbl_empty_uniform_step [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    {σ : State rT} {l : Loc} (Hlk : σ.tapes[l]? = some ⟨z, []⟩) :
    Discrete.Reducible pl(rand(#(.int z), #(.lbl l))) σ ∧
      primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ = Cfg.uniform z σ :=
  ⟨.of_headStepSupport (.RandTapeEmptyS Hz Hlk rfl le_rfl Hz rfl) (by is_lc),
    primStep_rand_lbl_empty Hz σ l Hlk⟩

private theorem randLbl_wrong_uniform_step [MeasurableSingletonClass rT] {z M : Int} (Hz : 0 < z)
    (HneM : z ≠ M) {σ : State rT} {l : Loc} {fs : List { z' : Int // 0 ≤ z' ∧ z' < M }}
    (Hlk : σ.tapes[l]? = some ⟨M, fs⟩) :
    Discrete.Reducible pl(rand(#(.int z), #(.lbl l))) σ ∧
      primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ = Cfg.uniform z σ :=
  ⟨.of_headStepSupport (.RandTapeOtherS Hz Hlk HneM le_rfl Hz rfl) (by is_lc),
    primStep_rand_lbl_wrong Hz HneM σ l fs Hlk⟩

/-! ## Coupling-context helpers -/

open MeasureTheory in
/-- A coupling with a step of `e` gives one with a step of `K[e]`. -/
theorem AddCoupl_steps_ctx_bind_r [MeasurableSingletonClass rT] {α} [MeasurableSpace α]
    {μ : Measure α} {e : Exp rT} {σ : State rT} {R : Set (α × Cfg rT)} {ε : ENNReal} {K : Ectx rT}
    (hv : ¬ e.isValue) (Hcpl : AddCoupl ε R μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε {p | ∃ e'', p.2.expr = K.fill e'' ∧ R (p.1, ⟨e'', p.2.state⟩)} μ
      (primStep ⟨K.fill e, σ⟩) := by
  rw [primStep_fill hv, ← Measure.map_id (μ := μ)]
  exact Hcpl.map id K.fillCfg measurable_id (Ectx.fillCfg.measurable K) fun HR => ⟨_, rfl, HR⟩

open MeasureTheory in
/-- `AddCoupl_steps_ctx_bind_r` for a relation on expressions only. -/
theorem AddCoupl_steps_ctx_bind_r_no_state [MeasurableSingletonClass rT]
    {μ : Measure (Cfg rT)} {e : Exp rT} {σ : State rT} {R : Exp rT → Exp rT → Prop} {ε : ENNReal}
    {K : Ectx rT} (hv : ¬ e.isValue)
    (Hcpl : AddCoupl ε {p : Cfg rT × Cfg rT | R p.1.expr p.2.expr} μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε {p | ∃ e'', p.2.expr = K.fill e'' ∧ R p.1.expr e''} μ (primStep ⟨K.fill e, σ⟩) :=
  AddCoupl_steps_ctx_bind_r hv Hcpl

/-- The leftover cost of a coupled draw: `s (ε₂ n)` at the pair drawn from `n`, and `⊤`
elsewhere. -/
noncomputable def Cfg.advLeftover [_root_.Top B] (s : ENNReal → B) (z : Int) (f : Int → Int)
    (σ σ' : State rT) (K : Ectx rT) (ε₂ : Int → ENNReal) : Cfg rT → Cfg rT → B :=
  fun ρ₁ ρ₂ => by
    classical
    exact if h : CoupledDraw z f σ σ' K ρ₁ ρ₂ then s (ε₂ h.choose) else ⊤

omit [LawfulProbLangℝ rT] in
theorem Cfg.advLeftover_apply [_root_.Top B] (s : ENNReal → B) {z : Int} (f : Int → Int)
    (σ σ' : State rT) (K : Ectx rT) (ε₂ : Int → ENNReal) {n : Int} (h0 : 0 ≤ n) (hn : n < z) :
    Cfg.advLeftover s z f σ σ' K ε₂ ⟨pl(#(.int n)), σ⟩ ⟨K.fill pl(#(.int (f n))), σ'⟩ =
      s (ε₂ n) := by
  classical
  have hex : CoupledDraw z f σ σ' K ⟨pl(#(.int n)), σ⟩ ⟨K.fill pl(#(.int (f n))), σ'⟩ :=
    ⟨n, h0, hn, rfl, rfl⟩
  obtain ⟨he, -⟩ := (Cfg.mk.injEq ..).mp hex.choose_spec.2.2.1
  simp only [Exp.lit.injEq, BaseLit.int.injEq] at he
  simp only [Cfg.advLeftover, hex, ↓reduceDIte, ← he]

/-- Coupling `rand z ~ K[rand z]` along a bijection `f`, paying `s (ε₂ n)` at the left draw `n`
out of `s ε₁`. -/
theorem Cfg.uniform_lift_adv [MeasurableSingletonClass rT] [AddCommMonoid B] [PartialOrder B]
    [CanonicallyOrderedAdd B] [OrderTop B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
    {s : ENNReal →+o B} [L.IsExpectationAdditive s] {z : Int} (Hz : 0 < z) (f : Int → Int)
    (ε₁ : ENNReal) (ε₂ : Int → ENNReal) (σ σ' : State rT) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (hamort : (∑ n ∈ Finset.Ico 0 z, ε₂ n) / z.toNat ≤ ε₁) :
    L (s ε₁) (Cfg.advLeftover s z f σ σ' K ε₂)
      (primStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩)
      (primStep ⟨K.fill pl(rand(#(.int z), #(.unit))), σ'⟩) := by
  classical
  -- Pay the right-sample cost `ε₂ (f⁻¹ m)` in expectation over the exact bijection coupling.
  set c : Int → ENNReal := fun m => ⨅ n, ⨅ (_ : (0 ≤ n ∧ n < z) ∧ f n = m), ε₂ n
  have hcf : ∀ n, 0 ≤ n → n < z → c (f n) = ε₂ n := fun n h0 h1 => by
    obtain ⟨_, -, huniq⟩ := hbij (f n) (hdom n h0 h1).1 (hdom n h0 h1).2
    refine _root_.le_antisymm (iInf₂_le n ⟨⟨h0, h1⟩, rfl⟩) (le_iInf₂ fun n' hn' => ?_)
    rw [(huniq n' hn').trans (huniq n ⟨⟨h0, h1⟩, rfl⟩).symm]
  have hint : 0 + s (∫⁻ m, c m ∂unifInt z Hz) ≤ s ε₁ := by
    rw [zero_add]
    refine OrderHomClass.mono s ?_
    rwa [lintegral_unifInt, ← Finset.sum_Ico_comp_of_bijOn hdom hbij c,
      Finset.sum_congr rfl fun n hn => hcf n (Finset.mem_Ico.1 hn).1 (Finset.mem_Ico.1 hn).2,
      ← ENNReal.div_eq_inv_mul]
  have h := IsExpectationAdditive.add_right (s := s) (c := c) Measurable.of_discrete
    (unifInt_codensity_bij L Hz f hdom hbij)
  rw [primStep_rand_unit Hz, primStep_fill Exp.rand_not_isValue, primStep_rand_unit Hz,
    Cfg.uniform_eq_map Hz σ, Cfg.uniform_eq_map Hz σ',
    MeasureTheory.Measure.map_map (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
      (Ectx.fillCfg.measurable K) Measurable.of_discrete]
  refine IsLawful.map Measurable.of_discrete Measurable.of_discrete
    (IsLawful.mono h hint fun n m => ?_)
  by_cases hnm : 0 ≤ n ∧ n < z ∧ m = f n
  · obtain ⟨h0, h1, rfl⟩ := hnm
    simp only [relCost_of (S := fun n m ↦ 0 ≤ n ∧ n < z ∧ m = f n) ⟨h0, h1, rfl⟩, zero_add,
      hcf n h0 h1]
    exact (Cfg.advLeftover_apply s f σ σ' K ε₂ h0 h1).le
  · simp only [relCost_of_not (S := fun n m ↦ 0 ≤ n ∧ n < z ∧ m = f n) hnm]
    exact le_top.trans le_self_add

section CouplingRules

variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSingletonClass rT] [MicrometerGS rT hlc GF]
  [BudgetGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]

private theorem randUnit_step_pure {z : Int} (Hz : 0 < z) (σ : State rT) {P A : IProp GF} :
    ⊢ P -∗ A -∗ ⌜Discrete.Reducible pl(rand(#(.int z), #(.unit))) σ ∧
      primStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩ = Cfg.uniform z σ⌝ := by
  iintro - -
  ipureintro
  exact randUnit_uniform_step Hz σ

private theorem appNatTape_empty_rand_step {z : Int} (Hz : 0 < z) (α : Loc) (σ : State rT) :
    ⊢@{IProp GF} appStateAuth σ -∗ appNatTape α z [] -∗
      ⌜Discrete.Reducible pl(rand(#(.int z), #(.lbl α))) σ ∧
        primStep ⟨pl(rand(#(.int z), #(.lbl α))), σ⟩ = Cfg.uniform z σ⌝ := by
  unfold appNatTape
  iintro Hσ ⟨%fs, %hmap, Hb⟩
  obtain rfl : fs = [] := List.map_eq_nil_iff.mp hmap
  ihave %hlk := app_state_lookup_tape $$ Hσ Hb
  ipureintro
  exact randLbl_empty_uniform_step Hz hlk

private theorem specNatTape_empty_rand_step {z : Int} (Hz : 0 < z) (α : Loc) (e : Exp rT)
    (σ : State rT) :
    ⊢@{IProp GF} Cfg.specAuth ⟨e, σ⟩ -∗ specNatTape α z [] -∗
      ⌜Discrete.Reducible pl(rand(#(.int z), #(.lbl α))) σ ∧
        primStep ⟨pl(rand(#(.int z), #(.lbl α))), σ⟩ = Cfg.uniform z σ⌝ := by
  unfold specNatTape
  iintro Hs ⟨%fs, %hmap, Hb⟩
  obtain rfl : fs = [] := List.map_eq_nil_iff.mp hmap
  ihave %hlk := spec_auth_lookup_tape $$ Hs Hb
  ipureintro
  exact randLbl_empty_uniform_step Hz hlk

theorem wp_couple_rand_core (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) {eL eR : Exp rT} (K : Ectx rT) (E : CoPset) (A : IProp GF) [BI.Timeless A]
    (HvL : eL.toVal? = none) (HvR : ¬ eR.isValue)
    (HstepL : ∀ σ, ⊢@{IProp GF} appStateAuth σ -∗ A -∗
      ⌜Discrete.Reducible eL σ ∧ primStep ⟨eL, σ⟩ = Cfg.uniform z σ⌝)
    (HstepR : ∀ e' σ', ⊢@{IProp GF} Cfg.specAuth ⟨e', σ'⟩ -∗ A -∗
      ⌜Discrete.Reducible eR σ' ∧ primStep ⟨eR, σ'⟩ = Cfg.uniform z σ'⌝)
    (Φ : Val rT → IProp GF) : iprop%
    ▷ A ∗ ⤇ K.fill eR ∗ (∀ n, A ∗ ⤇ K.fill pl(#(.int (f n))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E eL Φ := by
  iintro ⟨HA, Hj, Hcnt⟩
  iapply wp_lift_prim_steps_coupl HvL
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  imod HA
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  ihave %HL := HstepL σ₁ $$ Hσ HA
  ihave %HR := HstepR (K.fill eR) σ₁' $$ Hs HA
  have hb : 0 + b ≤ b := (zero_add b).le
  have hredL := HL.1.toReducible
  have hredR := HR.1.toReducible.fill K
  have hcpl : L.Rel 0 (CoupledDraw z f σ₁ σ₁' K)
      (primStep ⟨eL, σ₁⟩) (primStep ⟨K.fill eR, σ₁'⟩) := by
    rw [HL.2, primStep_fill HvR, HR.2]
    exact Cfg.uniform_codensity_bij_fill Hz σ₁ σ₁' f K hdom hbij
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iexists CoupledDraw z f σ₁ σ₁' K, 0, b
  iframe %hb %hredL %hredR %hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨n, hn0, hnz, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hb
  iapply wp_value_of_toVal rfl
  iapply Hcnt
  iframe HA Hj'
  ipureintro; exact ⟨hn0, hnz⟩

theorem wp_couple_rand_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.unit))) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz K E iprop(emp)
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => randUnit_step_pure Hz σ) (fun _ σ' => randUnit_step_pure Hz σ') Φ
  isplitr
  · iintro !>; iempintro
  iframe Hj
  iintro %n ⟨-, Hj', %hn⟩
  iapply Hcnt $$ %n %hn Hj'

omit [L.IsSupportLocal] in
theorem wp_couple_tapes_bij {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {z : Int} {α αₛ : Loc} {ns nsₛ : List Int} (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) : iprop%
    appNatTape α z ns ∗ specNatTape αₛ z nsₛ ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ appNatTape α z (ns ++ [n]) -∗ specNatTape αₛ z (nsₛ ++ [f n]) -∗
      wp L E e Φ) ⊢
    wp L E e Φ := by
  iintro ⟨Hα, Hαₛ, Hcnt⟩
  iunfold appNatTape at Hα
  iunfold specNatTape at Hαₛ
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  icases Hαₛ with ⟨%fsₛ, %Hfsₛ, Hαₛ⟩
  iapply wp_couple_erasables
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %hlk := app_state_lookup_tape $$ Hσ Hα
  ihave %hlk' := spec_auth_lookup_tape $$ Hs Hαₛ
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iexists (fun σ₂ σ₂' => ∃ n, 0 ≤ n ∧ n < z ∧
      σ₂ = σ₁.update_tapes (·.insert α ⟨z, fs ++ [tapeIdxOf Hz n]⟩) ∧
      σ₂' = σ₁'.update_tapes (·.insert αₛ ⟨z, fsₛ ++ [tapeIdxOf Hz (f n)]⟩)),
    tapePresample σ₁ α, tapePresample σ₁' αₛ
  have her := ErasableExpr.tapePresample hlk Hz
  have her' := ErasableExpr.tapePresample hlk' Hz
  have hcpl := tapePresample_codensity_bij (L := L) hlk hlk' Hz f hdom hbij
  iframe %her %her' %hcpl
  iintro %σ₂ %σ₂' %⟨n, hn0, hnz, rfl, rfl⟩
  imod app_state_update_tape $$ Hσ Hα with ⟨Hσ', Hα'⟩
  imod spec_auth_update_tape $$ Hs Hαₛ with ⟨Hs', Hαₛ'⟩
  imod Hclose
  imodintro
  simp only [micrometerWpGS_stateInterp_eq, micrometerWpGS_specInterp_eq,
    ExtTreeMap.insert_eq_PartialMap_insert]
  iframe Hσ' Hs' Hb
  have hd := hdom n hn0 hnz
  ihave HnatA := appNatTape_fold (ns := ns ++ [n])
    (by simp [← Hfs, tapeIdxOf_val Hz hn0 hnz]) $$ Hα'
  ihave HnatS := specNatTape_fold (ns := nsₛ ++ [f n])
    (by simp [← Hfsₛ, tapeIdxOf_val Hz hd.1 hd.2]) $$ Hαₛ'
  iapply Hcnt $$ %n %⟨hn0, hnz⟩ HnatA HnatS

theorem wp_couple_rand_lbl_rand_lbl_wrong (z M : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (HneM : z ≠ M) (K : Ectx rT) (E : CoPset) (α α' : Loc)
    (xs ys : List Int) (Φ : Val rT → IProp GF) : iprop%
    ▷ appNatTape α M xs ∗ ▷ specNatTape α' M ys ∗ ⤇ K.fill pl(rand(#(.int z), #(.lbl α'))) ∗
    (∀ n, appNatTape α M xs ∗ specNatTape α' M ys ∗ ⤇ K.fill pl(#(.int (f n))) ∗
      ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.lbl α))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz (eR := pl(rand(#(.int z), #(.lbl α')))) K E
    iprop(appNatTape α M xs ∗ specNatTape α' M ys)
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => by
      unfold appNatTape
      iintro Hσ ⟨⟨%fs, -, Hb⟩, -⟩
      ihave %hlk := app_state_lookup_tape $$ Hσ Hb
      ipureintro
      exact randLbl_wrong_uniform_step Hz HneM hlk)
    (fun _ σ' => by
      unfold specNatTape
      iintro Hs ⟨-, ⟨%fs', -, Hb'⟩⟩
      ihave %hlk := spec_auth_lookup_tape $$ Hs Hb'
      ipureintro
      exact randLbl_wrong_uniform_step Hz HneM hlk) Φ
  isplitl [Hα Hα']
  · iintro !>; iframe
  iframe Hj
  iintro %n ⟨⟨HA, HS⟩, Hj', %hn⟩
  iapply Hcnt
  iframe HA HS Hj' %hn

theorem wp_couple_rand_lbl_rand_lbl (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α α' : Loc) (Φ : Val rT → IProp GF) : iprop%
    ▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗ ⤇ K.fill pl(rand(#(.int z), #(.lbl α'))) ∗
    (∀ n, appNatTape α z [] ∗ specNatTape α' z [] ∗ ⤇ K.fill pl(#(.int (f n))) ∗
      ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.lbl α))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz (eR := pl(rand(#(.int z), #(.lbl α')))) K E
    iprop(appNatTape α z [] ∗ specNatTape α' z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => by iintro Hσ ⟨HA, -⟩; iapply (appNatTape_empty_rand_step Hz α σ) $$ Hσ HA)
    (fun e' σ' => by iintro Hs ⟨-, HS⟩; iapply (specNatTape_empty_rand_step Hz α' e' σ') $$ Hs HS)
    Φ
  isplitl [Hα Hα']
  · iintro !>; iframe
  iframe Hj
  iintro %n ⟨⟨HA, HS⟩, Hj', %hn⟩
  iapply Hcnt
  iframe HA HS Hj' %hn

/-! ## Mixed tape-rand couplings -/

theorem wp_couple_tape_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α : Loc) (Φ : Val rT → IProp GF) : iprop%
    ▷ appNatTape α z [] ∗ ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗
    (∀ n, appNatTape α z [] ∗ ⤇ K.fill pl(#(.int (f n))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.lbl α))) Φ :=
  wp_couple_rand_core z f hdom hbij Hz K E iprop(appNatTape α z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (appNatTape_empty_rand_step Hz α) (fun _ σ' => randUnit_step_pure Hz σ') Φ

theorem wp_couple_rand_tape (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α' : Loc) (Φ : Val rT → IProp GF) : iprop%
    ▷ specNatTape α' z [] ∗ ⤇ K.fill pl(rand(#(.int z), #(.lbl α'))) ∗
    (∀ n, specNatTape α' z [] ∗ ⤇ K.fill pl(#(.int (f n))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.unit))) Φ :=
  wp_couple_rand_core z f hdom hbij Hz K E iprop(specNatTape α' z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => randUnit_step_pure Hz σ) (specNatTape_empty_rand_step Hz α') Φ

end CouplingRules

/-! ## Rules that spend budget credits -/

section CreditRules

variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSingletonClass rT] [MicrometerGS rT hlc GF]
  [BudgetCreditGS B GF] [L.IsLawful] [L.IsTopAbsorbing]

/-- Couple `rand z ~ K[rand z]` along a bijection `f`, paying `s (ε₂ n)` to the continuation at
the left draw `n` out of `↯b (s ε₁)`, where `ε₁` bounds the average of `ε₂`. -/
theorem wp_couple_rand_rand_adv [L.IsReflexive] [L.IsSupportLocal]
    {s : ENNReal →+o B} [L.IsExpectationAdditive s] (z : Int) (f : Int → Int) (ε₁ : ENNReal)
    (ε₂ : Int → ENNReal)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (hamort : (∑ n ∈ Finset.Ico 0 z, ε₂ n) / z.toNat ≤ ε₁)
    (hc : IsAddLeftRegular (s ε₁)) (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗ ↯b (s ε₁) ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ⌜¬ L.Absorbing (s (ε₂ n))⌝ -∗ ↯b (s (ε₂ n)) -∗
      ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.unit))) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_lift_prim_steps_coupl_adv_absorbing Exp.rand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  have hredL := (randUnit_uniform_step Hz σ₁).1.toReducible
  have hredR := (randUnit_uniform_step Hz σ₁').1.toReducible.fill K
  imod BudgetCredit.supply_decrease hc $$ Hb Herr with ⟨%r, %hr, Hb⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  have hb : s ε₁ + r ≤ b := hr.ge
  imodintro
  have hlift := Cfg.uniform_lift_adv (L := L) (s := s) Hz f ε₁ ε₂ σ₁ σ₁' K hdom hbij hamort
  iexists Cfg.advLeftover s z f σ₁ σ₁' K ε₂, s ε₁, r
  iframe %hb %hredL %hredR %hlift
  iintro %e₂ %σ₂ %e₂' %σ₂' !>
  by_cases habs : L.Absorbing (Cfg.advLeftover s z f σ₁ σ₁' K ε₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + r)
  · imod Hclose
    imodintro
    ileft
    ipureintro
    exact habs
  by_cases hg : CoupledDraw z f σ₁ σ₁' K ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩
  · obtain ⟨n, hn0, hnz, h1, h2⟩ := hg
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h1
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h2
    rw [Cfg.advLeftover_apply s f _ _ K ε₂ hn0 hnz] at habs ⊢
    have hna : ¬ L.Absorbing (s (ε₂ n)) := fun h => habs (h.mono le_self_add)
    imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
    imod BudgetCredit.supply_increase $$ Hb with ⟨Hb, Hfrag⟩
    imod Hclose
    imodintro
    iright
    rw [add_comm (s (ε₂ n))]
    iframe Hσ Hs' Hb
    iapply wp_value_of_toVal rfl
    iapply Hcnt $$ %n %⟨hn0, hnz⟩ %hna Hfrag Hj'
  · exfalso
    refine habs ?_
    simp only [Cfg.advLeftover, hg, ↓reduceDIte]
    exact IsTopAbsorbing.absorbing_top.mono le_self_add

/-- Couple `rand z ~ K[rand z]` along the identity, avoiding the outcome `bad` for
`↯b (s (1 / z))` when `s 1` is absorbing. -/
theorem wp_couple_rand_rand_avoid [L.IsReflexive] [L.IsSupportLocal]
    {s : ENNReal →+o B} [L.IsExpectationAdditive s] (z bad : Int) (Hz : 0 < z)
    (habs : L.Absorbing (s 1))
    (hc : IsAddLeftRegular (s (z.toNat : ENNReal)⁻¹)) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗ ↯b (s (z.toNat : ENNReal)⁻¹) ∗
    (∀ n, ⌜(0 ≤ n ∧ n < z) ∧ n ≠ bad⌝ -∗ ⤇ K.fill pl(#(.int n)) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.unit))) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_couple_rand_rand_adv z id (z.toNat : ENNReal)⁻¹ (fun n => if n = bad then 1 else 0)
    id_dom_range id_bij_range Hz (avoid_one_amort bad) hc K E Φ
  iframe Hj Herr
  iintro %n %hn %hna - Hj'
  by_cases hb : n = bad
  · simp only [hb, ↓reduceIte] at hna
    exact (hna habs).elim
  · simp only [id_eq]
    iapply Hcnt $$ %n %⟨hn, hb⟩ Hj'

/-- Couple `rand zL ~ K[rand zR]` along `S`, given a lifting of the two uniform draws within the
cancelable budget `c`; spends `↯b c`. -/
private theorem wp_couple_rand_rand_lift (zL zR : Int) (HzL : 0 < zL) (HzR : 0 < zR)
    (S : Int → Int → Prop) (c : B) (hc : IsAddLeftRegular c)
    (Hcpl : L.Rel c S (unifInt zL HzL) (unifInt zR HzR)) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯b c ∗
    (∀ n m, ⌜S n m⌝ -∗ ⤇ K.fill pl(#(.int m)) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int zL), #(.unit))) Φ := by
  iintro ⟨Hj, Hc, Hcnt⟩
  iapply wp_lift_prim_steps_coupl Exp.rand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod BudgetCredit.supply_decrease hc $$ Hb Hc with ⟨%r, %hr, Hdec⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  let S' : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ n m, S n m ∧ c₁ = ⟨pl(#(.int n)), σ₁⟩ ∧ c₂ = ⟨K.fill pl(#(.int m)), σ₁'⟩
  iexists S', c, r
  have hsum : c + r ≤ b := hr.ge
  have hredL := (randUnit_uniform_step HzL σ₁).1.toReducible
  have hredR := ((randUnit_uniform_step HzR σ₁').1.toReducible).fill K
  have hcpl : L.Rel c S' (primStep ⟨pl(rand(#(.int zL), #(.unit))), σ₁⟩)
      (primStep ⟨K.fill pl(rand(#(.int zR), #(.unit))), σ₁'⟩) := by
    rw [primStep_rand_unit HzL, primStep_fill Exp.rand_not_isValue, primStep_rand_unit HzR]
    exact Cfg.uniform_codensity_fill HzL HzR σ₁ σ₁' K Hcpl fun n m h => ⟨n, m, h, rfl, rfl⟩
  iframe %hsum %hredL %hredR %hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨n, m, hS, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hdec
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %n %m %hS Hj'

/-- Coupling `rand zL ~ rand zR` along `f`, given a coupling `Hcpl` of the two uniform draws
that costs `binj`: the left draw is `n`, the right draw is `f n` (clutch's
`wp_couple_rand_rand_inj`, for any `L`). -/
theorem wp_couple_rand_rand_inj (zL zR : Int) (f : Int → Int)
    (b binj : B) (HzL : 0 < zL) (HzR : 0 < zR)
    (Hcpl : L.Rel binj (fun n m ↦ 0 ≤ n ∧ n < zL ∧ m = f n) (unifInt zL HzL) (unifInt zR HzR))
    (hb : binj ≤ b) (hc : IsAddLeftRegular binj) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯b b ∗
    (∀ n, ⌜0 ≤ n ∧ n < zL⌝ -∗ ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int zL), #(.unit))) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr := BudgetCredit.weaken hb $$ Herr
  iapply wp_couple_rand_rand_lift zL zR HzL HzR _ binj hc Hcpl K E Φ
  iframe Hj Herr
  iintro %n %m %⟨hn0, hnz, rfl⟩ Hj'
  iapply Hcnt $$ %n %⟨hn0, hnz⟩ Hj'

/-- Coupling `rand zL ~ rand zR` along `f`, given a coupling `Hcpl` of the two uniform draws
that costs `binj`: the left draw is `f m`, the right draw is `m` (clutch's
`wp_couple_rand_rand_rev_inj`, for any `L`). -/
theorem wp_couple_rand_rand_rev_inj (zL zR : Int) (f : Int → Int)
    (b binj : B) (HzL : 0 < zL) (HzR : 0 < zR)
    (Hcpl : L.Rel binj (fun n m ↦ 0 ≤ m ∧ m < zR ∧ n = f m) (unifInt zL HzL) (unifInt zR HzR))
    (hb : binj ≤ b) (hc : IsAddLeftRegular binj) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯b b ∗
    (∀ m, ⌜0 ≤ m ∧ m < zR⌝ -∗ ⤇ K.fill pl(#(.int m)) -∗ Φ (.int (f m))) ⊢
    wp L E pl(rand(#(.int zL), #(.unit))) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr := BudgetCredit.weaken hb $$ Herr
  iapply wp_couple_rand_rand_lift zL zR HzL HzR _ binj hc Hcpl K E Φ
  iframe Hj Herr
  iintro %n %m %⟨hm0, hmz, rfl⟩ Hj'
  iapply Hcnt $$ %m %⟨hm0, hmz⟩ Hj'

/-- Couple `rand N ~ K[rand N]` along `S`, given a lifting of the two uniform draws within the
cancelable budget `c`; spends `↯b c` (clutch-dp's `hoare_couple_laplace`, for any `L`). -/
theorem wp_couple_rand_rand_spend (N : Int) (HN : 0 < N) (S : Int → Int → Prop) (c : B)
    (hc : IsAddLeftRegular c) (Hcpl : L.Rel c S (unifInt N HN) (unifInt N HN))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int N), #(.unit))) ∗ ↯b c ∗
    (∀ r r', ⌜S r r'⌝ -∗ ⤇ K.fill pl(#(.int r')) -∗ Φ (.int r)) ⊢
    wp L E pl(rand(#(.int N), #(.unit))) Φ :=
  wp_couple_rand_rand_lift N N HN HN S c hc Hcpl K E Φ

end CreditRules

/-! ## Injective couplings at total variation -/

section CouplingRulesTV

variable {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSingletonClass rT]
  [MicrometerGS rT hlc GF] [BudgetCreditGS ENNReal GF]

private theorem isAddLeftRegular_natCast_div {a b : ℕ} (hb : b ≠ 0) :
    IsAddLeftRegular ((a : ENNReal) / b) :=
  (IsAddRegular.of_ne_top
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (Nat.cast_ne_zero.2 hb))).1

/-- Coupling `rand zL ~ rand zR` (`zL ≤ zR`) along an injection `f : [0,zL) ↪ [0,zR)`,
spending `(zR - zL)/zR` error credits: the left draw is `n`, the right draw is `f n`.
Ports `wp_couple_rand_rand_inj` from `clutch/theories/approxis/coupling_rules.v`. -/
theorem wp_couple_rand_rand_inj_tv (zL zR : Int) (f : Int → Int) (ε : ENNReal)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂)
    (HzL : 0 < zL) (Hle : zL ≤ zR)
    (hε : ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal) ≤ ε)
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯b ε ∗
    (∀ n, ⌜0 ≤ n ∧ n < zL⌝ -∗ ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp GradedDivergence.tv.codensity E pl(rand(#(.int zL), #(.unit))) Φ :=
  wp_couple_rand_rand_inj zL zR f ε _ HzL (HzL.trans_le Hle)
    (unifInt_addCoupl_inj HzL Hle f hdom hinj).codensity hε
    (isAddLeftRegular_natCast_div (by omega)) K E Φ

/-- Coupling `rand zL ~ rand zR` (`zR ≤ zL`) along an injection `f : [0,zR) ↪ [0,zL)`,
spending `(zL - zR)/zL` error credits: the left draw is `f m`, the right draw is `m`.
Ports `wp_couple_rand_rand_rev_inj` from `clutch/theories/approxis/coupling_rules.v`. -/
theorem wp_couple_rand_rand_rev_inj_tv (zL zR : Int) (f : Int → Int) (ε : ENNReal)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂)
    (HzR : 0 < zR) (Hle : zR ≤ zL)
    (hε : ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal) ≤ ε)
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯b ε ∗
    (∀ m, ⌜0 ≤ m ∧ m < zR⌝ -∗ ⤇ K.fill pl(#(.int m)) -∗ Φ (.int (f m))) ⊢
    wp GradedDivergence.tv.codensity E pl(rand(#(.int zL), #(.unit))) Φ :=
  wp_couple_rand_rand_rev_inj zL zR f ε _ (HzR.trans_le Hle) HzR
    (unifInt_addCoupl_rev_inj HzR Hle f hdom hinj).codensity hε
    (isAddLeftRegular_natCast_div (by omega)) K E Φ

end CouplingRulesTV

end ProbLang
