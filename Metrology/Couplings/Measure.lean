module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Measure facts

General lemmas about binding, pushing forward and suprema of measures, the measurable space on
`Option X`, and small `ℝ≥0∞`, `EReal` and finite-sum bounds used throughout the development. -/

@[expose] public section

universe u

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory
open ENNReal (ofReal tsum_eq_iSup_sum finsetSum_iSup_of_monotone mul_iSup toReal_sum mul_ne_top
  ofReal_ne_top toReal_mul toReal_ofReal toReal_nonneg ofReal_sum_of_nonneg ofReal_mul
  ofReal_toReal)
open SimpleFunc (eapprox measurableSet_fiber)
open Set (univ)

namespace MeasureTheory.Measure

variable {X Y Z Φ : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace Φ]

/-! ## Product, bind and map -/

/-- The product of two measurable families of finite measures is measurable. -/
@[fun_prop]
theorem _root_.Measurable.measure_prod {f : Z → Measure X} {g : Z → Measure Y}
    (hf : Measurable f) (hg : Measurable g) [∀ z, IsFiniteMeasure (f z)]
    [∀ z, IsFiniteMeasure (g z)] : Measurable fun z ↦ (f z).prod (g z) := by
  have hf' : Measurable fun z ↦ (⟨f z, inferInstance⟩ : FiniteMeasure X) := hf.subtype_mk
  have hg' : Measurable fun z ↦ (⟨g z, inferInstance⟩ : FiniteMeasure Y) := hg.subtype_mk
  exact FiniteMeasure.measurable_fun_prod.comp (hf'.prodMk hg')

/-- Binding a pushed-forward measure is binding along the composite kernel. -/
theorem bind_map_eq {d : Φ → X} {h : X → Measure Y} (μ : Measure Φ)
    (hd : Measurable d := by fun_prop) (hh : Measurable h := by fun_prop) :
    (μ.map d).bind h = μ.bind (h ∘ d) := by
  rw [bind, bind, map_map hh hd]

/-- Binding is monotone in the measure. -/
theorem bind_mono_left {μ μ' : Measure X} (h : μ ≤ μ') {f : X → Measure Y}
    (hf : Measurable f := by fun_prop) : μ.bind f ≤ μ'.bind f := le_iff.2 fun s hs ↦ by
  rw [bind_apply hs hf.aemeasurable, bind_apply hs hf.aemeasurable]
  exact lintegral_mono' h le_rfl

/-- Precomposing a kernel with `g` is pushing the measure forward along `g`. -/
theorem _root_.ProbabilityTheory.Kernel.comap_comp_eq_comp_map {ν : Measure Y}
    {g : Y → Z} (κ : ProbabilityTheory.Kernel Z X) (hg : Measurable g) :
    κ.comap g hg ∘ₘ ν = κ ∘ₘ ν.map g := by
  ext A hA
  rw [bind_apply hA (ProbabilityTheory.Kernel.aemeasurable _),
    bind_apply hA (ProbabilityTheory.Kernel.aemeasurable _),
    lintegral_map (κ.measurable_coe hA) hg]
  rfl

/-- Binding is monotone in the kernel. -/
theorem bind_mono_right' (μ : Measure X) (f g : X → Measure Y) (Hf : Measurable f)
    (Hg : Measurable g) (h : ∀ a, f a ≤ g a) : μ.bind f ≤ μ.bind g := by
  refine le_intro fun S HS HNE => ?_
  rw [bind_apply HS Hf.aemeasurable, bind_apply HS Hg.aemeasurable]
  exact lintegral_mono fun a => h a S

/-- Binding commutes with pushforward when every space is discrete, so no measurability side
conditions. -/
theorem bind_map_comm_of_discrete [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Y]
    [DiscreteMeasurableSpace Z] (μ : Measure X) (k : X → Measure Y) (f : Y → Z) :
    (μ.bind k).map f = μ.bind fun a => (k a).map f := by
  ext S hS
  rw [map_apply .of_discrete hS, bind_apply .of_discrete Measurable.of_discrete.aemeasurable,
    bind_apply hS Measurable.of_discrete.aemeasurable]
  simp_rw [map_apply .of_discrete hS]

/-! ## Suprema of increasing sequences of measures -/

section Monotone

variable {μ : ℕ → Measure X} (hμ : Monotone μ)

include hμ

/-- The supremum of an increasing sequence of measures is computed setwise. -/
theorem iSup_apply_of_monotone {s : Set X} (hs : MeasurableSet s) : (⨆ n, μ n) s = ⨆ n, μ n s := by
  let ν : Measure X := ofMeasurable (fun s _ ↦ ⨆ n, μ n s) (by simp) fun f hf hd ↦ by
    simp_rw [measure_iUnion hd hf, tsum_eq_iSup_sum]
    rw [iSup_comm]
    exact iSup_congr fun _ ↦ (finsetSum_iSup_of_monotone fun k _ _ h ↦ hμ h (f k)).symm
  have hμν : ⨆ n, μ n ≤ ν := iSup_le fun n ↦ le_iff.2 fun t ht ↦ by
    rw [ofMeasurable_apply _ ht]
    exact le_iSup (μ · t) n
  refine le_antisymm ?_ (iSup_le fun n ↦ le_iff'.1 (le_iSup μ n) s)
  exact (le_iff'.1 hμν s).trans_eq (ofMeasurable_apply _ hs)

/-- Integrals against an increasing sequence of measures converge (monotone convergence). -/
theorem lintegral_iSup_of_monotone {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(⨆ n, μ n) = ⨆ n, ∫⁻ x, f x ∂μ n := by
  refine le_antisymm ?_ (iSup_le fun n ↦ lintegral_mono' (le_iSup μ n) le_rfl)
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  refine iSup_le fun k ↦ ?_
  have : (eapprox f k).lintegral (⨆ n, μ n) = ⨆ n, (eapprox f k).lintegral (μ n) := by
    simp only [SimpleFunc.lintegral, iSup_apply_of_monotone hμ (measurableSet_fiber _ _),
      mul_iSup]
    exact finsetSum_iSup_of_monotone fun _ _ _ h ↦ mul_le_mul_right (hμ h _) _
  exact this.trans_le (iSup_mono fun n ↦ lintegral_eapprox_le_lintegral hf k)

/-- Binding commutes with the supremum of an increasing sequence of measures. -/
theorem iSup_bind_of_monotone {f : X → Measure Y} (hf : Measurable f := by fun_prop) :
    (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  have hmono : Monotone fun n ↦ (μ n).bind f := fun _ _ h ↦ bind_mono_left (hμ h) hf
  ext s hs
  rw [iSup_apply_of_monotone hmono hs, bind_apply hs hf.aemeasurable,
    lintegral_iSup_of_monotone hμ (f := (f · s)) ((measurable_coe hs).comp hf)]
  simp_rw [bind_apply hs hf.aemeasurable]

/-- Pushing forward commutes with the supremum of an increasing sequence of measures. -/
theorem map_iSup_of_monotone {f : X → Y} (hf : Measurable f := by fun_prop) :
    (⨆ n, μ n).map f = ⨆ n, (μ n).map f := by
  simp_rw [← bind_dirac_eq_map _ hf]
  exact iSup_bind_of_monotone hμ

end Monotone

/-! ## Measures on a point -/

/-- A measure on a point is its mass times the Dirac mass. -/
theorem eq_smul_dirac_punit (μ : Measure PUnit.{u + 1}) : μ = μ univ • dirac PUnit.unit := by
  ext s hs
  rcases s.eq_empty_or_nonempty with rfl | hs'
  · simp
  · simp [Subsingleton.eq_univ_of_nonempty hs']

end MeasureTheory.Measure

/-! ## Measurable structure on `Option X` and `ULift` -/

section Option

variable {X : Type*} [MeasurableSpace X]

open Equiv (optionEquivSumPUnit)

/-- The measurable space on `Option X`, pulled back along its equivalence with `X ⊕ PUnit`. -/
instance Option.instMeasurableSpace : MeasurableSpace (Option X) :=
  .comap (optionEquivSumPUnit.{0, _} X) inferInstance

/-- The constructor `some` is measurable. -/
@[fun_prop]
theorem measurable_some : Measurable (some : X → Option X) := by
  refine measurable_comap_iff.2 ?_
  simpa [Function.comp_def, optionEquivSumPUnit] using measurable_inl

/-- `Option.elim` with a measurable branch for `some` is measurable. -/
@[fun_prop]
theorem measurable_option_elim {Z : Type*} [MeasurableSpace Z] {g : X → Z} (hg : Measurable g)
    (z : Z) : Measurable fun o : Option X ↦ o.elim z g := by
  have : (fun o : Option X ↦ o.elim z g) = Sum.elim g (fun _ ↦ z) ∘ optionEquivSumPUnit X := by
    funext o
    cases o <;> rfl
  rw [this]
  exact (hg.sumElim measurable_const).comp (comap_measurable _)

end Option

/-- The lift of a discrete measurable space is discrete. -/
instance discreteMeasurableSpace_uLift {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (ULift α) :=
  ⟨fun _ ↦ measurable_down (t := ULift.up ⁻¹' _) .of_discrete⟩

/-! ## Integrals over finite measures and finite spaces -/

namespace MeasureTheory

open Measure
open Finset (sum_congr coe_univ)

variable {Z : Type*} [MeasurableSpace Z]

/-- A function below `1` has finite integral against a finite measure. -/
theorem lintegral_ne_top_of_le_one (P : Measure Z) [IsFiniteMeasure P] {F : Z → ℝ≥0∞}
    (hF : ∀ z, F z ≤ 1) : ∫⁻ z, F z ∂P ≠ ⊤ :=
  ne_top_of_le_ne_top (measure_ne_top P univ) ((lintegral_mono hF).trans_eq lintegral_one)

/-- Integrating a function that factors through a finite partition sums over its cells. -/
theorem toReal_lintegral_ofReal_comp {n : ℕ} {π : Z → Fin n} (hπ : Measurable π) {w : Fin n → ℝ}
    (hw : ∀ j, 0 ≤ w j) (P : Measure Z) [IsFiniteMeasure P] :
    (∫⁻ z, ofReal (w (π z)) ∂P).toReal = ∑ j, w j * (P (π ⁻¹' {j})).toReal := by
  rw [← lintegral_map (f := fun j ↦ ofReal (w j)) (by fun_prop) hπ, lintegral_fintype,
    toReal_sum fun j _ ↦ mul_ne_top ofReal_ne_top (measure_ne_top _ _)]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [map_apply hπ (measurableSet_singleton j), toReal_mul, toReal_ofReal (hw j)]

/-- Total mass of a measure on a finite space as a sum of real point masses. -/
theorem sum_toReal_singleton [Fintype Z] [MeasurableSingletonClass Z] (ρ : Measure Z)
    [IsFiniteMeasure ρ] : ∑ i, (ρ {i}).toReal = (ρ univ).toReal := by
  rw [← toReal_sum fun _ _ ↦ measure_ne_top _ _, sum_measure_singleton, coe_univ]

/-- On a finite space the integral of `ofReal ∘ f` is the `ofReal` of the weighted sum. -/
theorem lintegral_ofReal_eq_sum [Fintype Z] [MeasurableSingletonClass Z] (P : Measure Z)
    [IsFiniteMeasure P] {f : Z → ℝ} (hf : 0 ≤ f) :
    ∫⁻ z, ofReal (f z) ∂P = ofReal (∑ z, (P {z}).toReal * f z) := by
  rw [lintegral_fintype, ofReal_sum_of_nonneg fun z _ ↦ mul_nonneg toReal_nonneg (hf z)]
  refine sum_congr rfl fun z _ ↦ ?_
  rw [ofReal_mul toReal_nonneg, ofReal_toReal (measure_ne_top _ _), mul_comm]

end MeasureTheory

/-! ## `ℝ≥0∞` bounds -/

namespace ENNReal

/-- Capping at `n` keeps a bound `a ≤ c b` with `1 ≤ c`. -/
theorem min_le_mul_min {a b c n : ℝ≥0∞} (h : a ≤ c * b) (hc : 1 ≤ c) : min a n ≤ c * min b n := by
  rcases le_total b n with hb | hb
  · rw [min_eq_left hb]
    exact (min_le_left _ _).trans h
  · rw [min_eq_right hb]
    exact (min_le_right _ _).trans (le_mul_of_one_le_left' hc)

/-- Enlarging the denominator of `a⁻¹ * S` to `a + d` loses at most `d / (a + d)` when `S ≤ a`. -/
theorem inv_mul_le_inv_mul_add {a d : ℕ} (ha : a ≠ 0) {S : ℝ≥0∞} (hS : S ≤ a) :
    (a : ℝ≥0∞)⁻¹ * S ≤ ((a : ℝ≥0∞) + d)⁻¹ * S + d / ((a : ℝ≥0∞) + d) := by
  have hinvS : (a : ℝ≥0∞)⁻¹ * S ≤ 1 := by
    calc (a : ℝ≥0∞)⁻¹ * S ≤ (a : ℝ≥0∞)⁻¹ * a := by gcongr
      _ = 1 := ENNReal.inv_mul_cancel (by positivity) (by finiteness)
  calc (a : ℝ≥0∞)⁻¹ * S = ((a + d : ℝ≥0∞)⁻¹ * (a + d)) * ((a : ℝ≥0∞)⁻¹ * S) := by
        rw [ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]
    _ = (a + d : ℝ≥0∞)⁻¹ * (a * ((a : ℝ≥0∞)⁻¹ * S) + d * ((a : ℝ≥0∞)⁻¹ * S)) := by
        rw [mul_assoc, add_mul]
    _ = (a + d : ℝ≥0∞)⁻¹ * (S + d * ((a : ℝ≥0∞)⁻¹ * S)) := by
        rw [← mul_assoc (a : ℝ≥0∞), ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]
    _ ≤ (a + d : ℝ≥0∞)⁻¹ * (S + d * 1) := by gcongr
    _ = ((a : ℝ≥0∞) + d)⁻¹ * S + d / ((a : ℝ≥0∞) + d) := by
        rw [mul_one, mul_add, ENNReal.div_eq_inv_mul]

/-- Finite budgets `ENNReal.ofReal x` cancel on the left. -/
theorem isAddLeftRegular_ofReal (x : ℝ) : IsAddLeftRegular (ofReal x) :=
  (IsAddRegular.of_ne_top ofReal_ne_top).1

/-- For `ε > 0` and `k > 1`, some power `kⁿ` lifts `ε` to at least `1`. -/
theorem exists_pow_mul_ge_one {ε : ℝ≥0∞} {k : ℝ≥0} (hε : 0 < ε) (hk : 1 < k) :
    ∃ n : ℕ, 1 ≤ ε * (k : ℝ≥0∞) ^ n := by
  obtain rfl | hε' := eq_or_ne ε ∞
  · exact ⟨0, by simp⟩
  · lift ε to ℝ≥0 using hε' with ε
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ε⁻¹ (by exact_mod_cast hk)
    have hlift : (1 : ℝ≥0) ≤ ε * k ^ n := by
      rw [mul_comm]
      refine (inv_le_iff_one_le_mul₀ ?_).mp hn.le
      exact_mod_cast hε
    exact ⟨n, by exact_mod_cast hlift⟩

end ENNReal

/-! ## `EReal` multiplication -/

namespace EReal

open Finset (forall_mem_insert sum_insert sum_nonneg)

/-- Multiplying by a constant distributes over a sum of nonnegative terms. -/
theorem mul_finset_sum_of_nonneg {ι : Type*} (s : Finset ι) (c : EReal) {x : ι → EReal}
    (hx : ∀ i ∈ s, 0 ≤ x i) : c * ∑ i ∈ s, x i = ∑ i ∈ s, c * x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [forall_mem_insert] at hx
    rw [sum_insert hj, sum_insert hj, left_distrib_of_nonneg hx.1 (sum_nonneg hx.2), ih hx.2]

/-- A positive real factor moves across `≤` as its inverse. -/
theorem le_coe_mul_iff {c : ℝ} (hc : 0 < c) {x y : EReal} :
    x ≤ c * y ↔ ((c⁻¹ : ℝ) : EReal) * x ≤ y := by
  have hc' : 0 < c⁻¹ := inv_pos.2 hc
  induction x <;> induction y <;>
    simp [coe_mul_top_of_pos hc, coe_mul_bot_of_pos hc, coe_mul_top_of_pos hc',
      coe_mul_bot_of_pos hc', ← coe_mul, inv_mul_le_iff₀ hc]

end EReal

/-! ## Sums over integer intervals -/

namespace Finset

/-- A sum composed with a map injective on `Ico 0 zL` and landing in `Ico 0 zR` is bounded by the
full codomain sum. -/
theorem sum_Ico_comp_le_of_injOn {zL zR : ℤ} {f : ℤ → ℤ}
    (hdom : ∀ n : ℤ, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂ : ℤ, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂)
    (g : ℤ → ℝ≥0∞) : ∑ n ∈ Ico 0 zL, g (f n) ≤ ∑ m ∈ Ico 0 zR, g m := by
  calc ∑ n ∈ Ico 0 zL, g (f n) = ∑ m ∈ (Ico 0 zL).image f, g m := (sum_image fun n hn m hm heq ↦ by
        simp only [coe_Ico, Set.mem_Ico] at hn hm
        exact hinj n m hn.1 hn.2 hm.1 hm.2 heq).symm
    _ ≤ ∑ m ∈ Ico 0 zR, g m := by
        refine sum_le_sum_of_subset fun m hm ↦ ?_
        obtain ⟨n, hn, rfl⟩ := mem_image.1 hm
        simp only [mem_Ico] at hn ⊢
        exact hdom n hn.1 hn.2

/-- A sum of `≤ 1` terms over `Ico 0 z` is at most `z.toNat`. -/
theorem sum_Ico_le_toNat {z : ℤ} {g : ℤ → ℝ≥0∞} (hg : ∀ n, g n ≤ 1) :
    ∑ n ∈ Ico 0 z, g n ≤ z.toNat := by
  calc ∑ n ∈ Ico 0 z, g n ≤ ∑ _n ∈ Ico 0 z, 1 := sum_le_sum fun n _ ↦ hg n
    _ = z.toNat := by rw [sum_const, Int.card_Ico, nsmul_eq_mul, mul_one, sub_zero]

end Finset
