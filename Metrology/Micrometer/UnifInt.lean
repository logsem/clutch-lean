module

public import Metrology.Micrometer.Lifting
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.ProbLang.Metatheory
public import Metrology.Couplings.Bridges.AddCoupl

@[expose] public section

-- these rules use the @[discrete] lifting lemmas without being discrete themselves
set_option linter.discrete false

/-! Uniform integer draws, the steps of `rand`, their couplings, and timeless tape predicates. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting
open scoped AppGS

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]
variable {B : Type} {L : GradedLifting.{0} B}

/-! ## Uniform coupling under a bijection -/

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

/-- `unifInt z` gives each set the share of `[0, z)` it contains. -/
theorem unifInt_apply {z : Int} (hz : 0 < z) (S : Set Int) :
    unifInt z hz S = (z.toNat : ENNReal)⁻¹ * ∑ n ∈ Finset.Ico 0 z, S.indicator 1 n := by
  rw [← lintegral_unifInt, lintegral_indicator_one MeasurableSet.of_discrete]

/-- `unifInt N` gives the singleton `{0}` mass `1/N`. -/
theorem unifInt_singleton_zero {N : Int} (hN : 0 < N) :
    unifInt N hN {0} = (N.toNat : ENNReal)⁻¹ := by
  rw [unifInt, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.uniformOfFinset_apply_of_mem _ (Finset.mem_Ico.2 ⟨le_rfl, hN⟩), Int.card_Ico, sub_zero]

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
theorem unifInt_rel_bij [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
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
theorem Cfg.uniform_rel_fill [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    {b : B} {zL zR : Int} (HzL : 0 < zL) (HzR : 0 < zR) (σ σ' : State rT) (K : Ectx rT)
    {S : Int → Int → Prop} {S' : Cfg rT → Cfg rT → Prop}
    (h : L.Rel b S (unifInt zL HzL) (unifInt zR HzR))
    (hS : ∀ n m, S n m → S' ⟨pl(#(.int n)), σ⟩ ⟨K.fill pl(#(.int m)), σ'⟩) :
    L.Rel b S' (Cfg.uniform zL σ) ((Cfg.uniform zR σ').map K.fillCfg) := by
  rw [Cfg.uniform_eq_map HzL, Cfg.uniform_eq_map HzR,
    Measure.map_map (Ectx.fillCfg.measurable K) Measurable.of_discrete]
  exact h.map hS Measurable.of_discrete Measurable.of_discrete

end UniformInt

/-! ## Steps of `rand` -/

/-- `rand z` on the unit label steps to `Cfg.uniform z σ`. -/
theorem primStep_rand_unit [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z) (σ : State rT) :
    primStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩ = Cfg.uniform z σ := by
  have Hwitness : HeadStepSupport ⟨pl(rand(#(.int z), #(.unit))), σ⟩ ⟨pl(#(.int 0)), σ⟩ :=
    .RandNoTapeS Hz le_rfl Hz
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc)
    (HeadReducible.of_headStepSupport Hwitness))]
  rfl

/-- `rand z` on the unit label is discretely reducible and steps to `Cfg.uniform z σ`. -/
theorem randUnit_uniform_step [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) :
    Discrete.Reducible pl(rand(#(.int z), #(.unit))) σ ∧
      primStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩ = Cfg.uniform z σ :=
  ⟨.of_headStepSupport (.RandNoTapeS Hz le_rfl Hz) (by is_lc),
    primStep_rand_unit Hz σ⟩

/-- The step of `rand z` on a tape label, by the tape's state, given a head-step witness. -/
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

/-- `rand z` on a tape of another bound `M` steps to `Cfg.uniform z σ`. -/
theorem primStep_rand_lbl_wrong [MeasurableSingletonClass rT] {z M : Int} (Hz : 0 < z)
    (HneM : z ≠ M) (σ : State rT) (l : Loc) (fs : List { z' : Int // 0 ≤ z' ∧ z' < M })
    (Hlk : σ.tapes[l]? = some ⟨M, fs⟩) :
    primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ = Cfg.uniform z σ := by
  rw [primStep_rand_lbl_eq (.RandTapeOtherS Hz Hlk HneM le_rfl Hz rfl), Hlk]
  simp only [ite_eq_right (Ne.symm HneM)]

/-- `rand z` on an empty tape of bound `z` steps to `Cfg.uniform z σ`. -/
theorem primStep_rand_lbl_empty [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) (l : Loc) (Hlk : σ.tapes[l]? = some ⟨z, []⟩) :
    primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ = Cfg.uniform z σ := by
  rw [primStep_rand_lbl_eq (.RandTapeEmptyS Hz Hlk rfl le_rfl Hz rfl), Hlk]
  simp only [↓reduceIte]

/-- `primStep_rand_lbl_empty` with discrete reducibility. -/
theorem randLbl_empty_uniform_step [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    {σ : State rT} {l : Loc} (Hlk : σ.tapes[l]? = some ⟨z, []⟩) :
    Discrete.Reducible pl(rand(#(.int z), #(.lbl l))) σ ∧
      primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ = Cfg.uniform z σ :=
  ⟨.of_headStepSupport (.RandTapeEmptyS Hz Hlk rfl le_rfl Hz rfl) (by is_lc),
    primStep_rand_lbl_empty Hz σ l Hlk⟩

/-- `primStep_rand_lbl_wrong` with discrete reducibility. -/
theorem randLbl_wrong_uniform_step [MeasurableSingletonClass rT] {z M : Int} (Hz : 0 < z)
    (HneM : z ≠ M) {σ : State rT} {l : Loc} {fs : List { z' : Int // 0 ≤ z' ∧ z' < M }}
    (Hlk : σ.tapes[l]? = some ⟨M, fs⟩) :
    Discrete.Reducible pl(rand(#(.int z), #(.lbl l))) σ ∧
      primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ = Cfg.uniform z σ :=
  ⟨.of_headStepSupport (.RandTapeOtherS Hz Hlk HneM le_rfl Hz rfl) (by is_lc),
    primStep_rand_lbl_wrong Hz HneM σ l fs Hlk⟩

/-! ## Couplings of draws along a bijection -/

/-- The outcome of a coupled draw: the left draw is `n`, the right draw is `f n` under `K`. -/
@[reducible] def CoupledDraw (z : Int) (f : Int → Int) (σ σ' : State rT) (K : Ectx rT) :
    Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
  ∃ n : Int, 0 ≤ n ∧ n < z ∧
    c₁ = ⟨pl(#(.int n)), σ⟩ ∧ c₂ = ⟨K.fill pl(#(.int (f n))), σ'⟩

/-- Exact coupling of `rand z ~ K[rand z]` along a bijection of `[0, z)`. -/
theorem Cfg.uniform_rel_bij_fill [MeasurableSingletonClass rT] [Zero B] [Add B]
    [Preorder B] [OrderTop B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] {z : Int}
    (Hz : 0 < z) (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) :
    L.Rel 0 (CoupledDraw z f σ σ' K) (Cfg.uniform z σ) ((Cfg.uniform z σ').map K.fillCfg) :=
  Cfg.uniform_rel_fill Hz Hz σ σ' K (unifInt_rel_bij L Hz f hdom hbij)
    fun n _ ⟨h0, h1, hm⟩ => ⟨n, h0, h1, rfl, hm ▸ rfl⟩

/-- Exact coupling of `rand z ~ rand z` along a bijection of `[0, z)` (the `tv` instance of
`unifInt_rel_bij`). -/
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
    ((unifInt_rel_bij GradedDivergence.tv.codensity Hz f hdom hbij).map ?_
      Measurable.of_discrete Measurable.of_discrete)
  rintro n _ ⟨h0, h1, hm⟩
  exact ⟨n, h0, h1, rfl, hm ▸ rfl⟩

/-- Exact coupling of `rand z ~ K[rand z]` along a bijection of `[0, z)` (the `tv` instance of
`Cfg.uniform_rel_bij_fill`). -/
theorem Cfg.uniform_addCoupl_bij_fill [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) :
    AddCoupl 0 {p | CoupledDraw z f σ σ' K p.1 p.2}
      (Cfg.uniform z σ) ((Cfg.uniform z σ').map K.fillCfg) :=
  (Cfg.uniform_rel_bij_fill Hz σ σ' f K hdom hbij).addCoupl

/-! ## Uniform couplings along an injection (unequal bounds)

Coupling `rand zL ~ rand zR` along an injection costs the mass of the uncovered fraction of the
larger support (Rocq `ARcoupl_rand_rand_inj`, `ARcoupl_rand_rand_rev_inj`). -/

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
    c₁ = ⟨pl(#(.int (f m))), σ⟩ ∧ c₂ = ⟨K.fill pl(#(.int m)), σ'⟩

/-- Coupling of `rand zL ~ K[rand zR]` along an injection, smaller bound on the left (the `tv`
instance of `Cfg.uniform_rel_fill`). -/
theorem Cfg.uniform_addCoupl_inj_fill [MeasurableSingletonClass rT] {zL zR : Int}
    (HzL : 0 < zL) (Hle : zL ≤ zR) (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂) :
    AddCoupl (((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal))
      {p | CoupledDraw zL f σ σ' K p.1 p.2}
      (Cfg.uniform zL σ) ((Cfg.uniform zR σ').map K.fillCfg) := by
  have h := (unifInt_addCoupl_inj HzL Hle f hdom hinj).codensity
  refine (Cfg.uniform_rel_fill HzL (HzL.trans_le Hle) σ σ' K h ?_).addCoupl
  rintro n _ ⟨h0, h1, hm⟩
  exact ⟨n, h0, h1, rfl, hm ▸ rfl⟩

/-- Coupling of `rand zL ~ K[rand zR]` along an injection, smaller bound on the right (the `tv`
instance of `Cfg.uniform_rel_fill`). -/
theorem Cfg.uniform_addCoupl_rev_inj_fill [MeasurableSingletonClass rT] {zL zR : Int}
    (HzR : 0 < zR) (Hle : zR ≤ zL) (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂) :
    AddCoupl (((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal))
      {p | CoupledDrawRev zR f σ σ' K p.1 p.2}
      (Cfg.uniform zL σ) ((Cfg.uniform zR σ').map K.fillCfg) := by
  have h := (unifInt_addCoupl_rev_inj HzR Hle f hdom hinj).codensity
  refine (Cfg.uniform_rel_fill (HzR.trans_le Hle) HzR σ σ' K h ?_).addCoupl
  rintro _ m ⟨h0, h1, hm⟩
  exact ⟨m, h0, h1, hm ▸ rfl, rfl⟩

/-! ## Coupling under an evaluation context -/

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
elsewhere. Unlike `Cfg.drawCost`, which is keyed by both draws, this is keyed by the left draw
along the bijection `f`. -/
noncomputable def Cfg.advLeftover [_root_.Top B] (s : ENNReal → B) (z : Int) (f : Int → Int)
    (σ σ' : State rT) (K : Ectx rT) (ε₂ : Int → ENNReal) : Cfg rT → Cfg rT → B :=
  fun ρ₁ ρ₂ => by
    classical
    exact if h : CoupledDraw z f σ σ' K ρ₁ ρ₂ then s (ε₂ h.choose) else ⊤

omit [LawfulProbLangℝ rT] in
/-- At the pair drawn from `n`, the leftover is `s (ε₂ n)`. -/
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
    (unifInt_rel_bij L Hz f hdom hbij)
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

/-! ## `id` helpers for the coupling rules -/

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

end ProbLang
