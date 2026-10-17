module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod

/-! General facts about measures, and about the extended reals they take values in. -/

@[expose] public section

universe u

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {X X' X'' Y Z Φ Ψ : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace X'']
  [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace Φ] [MeasurableSpace Ψ]

/-- Pushing forward commutes with a commuting square. -/
theorem map_map_of_comm {ρ : Φ → X} {h : X → X''} {l : Φ → Ψ} {ρ' : Ψ → X''}
    (hc : ∀ φ, h (ρ φ) = ρ' (l φ)) (μ : Measure Φ) (hρ : Measurable ρ := by fun_prop)
    (hh : Measurable h := by fun_prop) (hl : Measurable l := by fun_prop)
    (hρ' : Measurable ρ' := by fun_prop) :
    (μ.map ρ).map h = (μ.map l).map ρ' := by
  rw [map_map hh hρ, map_map hρ' hl]
  exact congrArg (μ.map ·) (funext hc)

@[fun_prop]
theorem _root_.Measurable.measure_prod {f : Z → Measure X} {g : Z → Measure Y}
    (hf : Measurable f) (hg : Measurable g) [∀ z, IsFiniteMeasure (f z)]
    [∀ z, IsFiniteMeasure (g z)] : Measurable fun z ↦ (f z).prod (g z) := by
  have hf' : Measurable fun z ↦ (⟨f z, inferInstance⟩ : FiniteMeasure X) := hf.subtype_mk
  have hg' : Measurable fun z ↦ (⟨g z, inferInstance⟩ : FiniteMeasure Y) := hg.subtype_mk
  exact FiniteMeasure.measurable_fun_prod.comp (hf'.prodMk hg')

/-- Pushing forward a bind is binding the pushed-forward kernel. -/
theorem map_bind_eq {κ : Φ → Measure X} {k : X → Y} (μ : Measure Φ)
    (hκ : Measurable κ := by fun_prop) (hk : Measurable k := by fun_prop) :
    (μ.bind κ).map k = μ.bind fun φ ↦ (κ φ).map k := by
  rw [bind, bind, ← join_map_map hk, map_map (measurable_map k hk) hκ]
  rfl

/-- Binding a pushed-forward measure is binding along the composite kernel. -/
theorem bind_map_eq {d : Φ → X} {h : X → Measure Y} (μ : Measure Φ)
    (hd : Measurable d := by fun_prop) (hh : Measurable h := by fun_prop) :
    (μ.map d).bind h = μ.bind (h ∘ d) := by
  rw [bind, bind, map_map hh hd]

/-- Binding commutes with a commuting square of kernels. -/
theorem bind_map_of_comm {ρ : Φ → X} {h : X → Measure X'} {κ : Φ → Measure Ψ} {ρ' : Ψ → X'}
    (hc : ∀ φ, h (ρ φ) = (κ φ).map ρ') (μ : Measure Φ) (hρ : Measurable ρ := by fun_prop)
    (hh : Measurable h := by fun_prop) (hκ : Measurable κ := by fun_prop)
    (hρ' : Measurable ρ' := by fun_prop) :
    (μ.map ρ).bind h = (μ.bind κ).map ρ' := by
  rw [bind_map_eq μ hρ hh, map_bind_eq μ hκ hρ']
  exact congrArg μ.bind (funext hc)

/-- The supremum of an increasing sequence of measures is computed setwise. -/
theorem iSup_apply_of_monotone {μ : ℕ → Measure X} (hμ : Monotone μ) {s : Set X}
    (hs : MeasurableSet s) : (⨆ n, μ n) s = ⨆ n, μ n s := by
  let ν : Measure X := ofMeasurable (fun s _ ↦ ⨆ n, μ n s) (by simp) fun f hf hd ↦ by
    simp_rw [measure_iUnion hd hf, ENNReal.tsum_eq_iSup_sum]
    rw [iSup_comm]
    exact iSup_congr fun _ ↦ (ENNReal.finsetSum_iSup_of_monotone fun k _ _ h ↦ hμ h (f k)).symm
  have hμν : ⨆ n, μ n ≤ ν := iSup_le fun n ↦ le_iff.2 fun t ht ↦ by
    rw [ofMeasurable_apply _ ht]
    exact le_iSup (μ · t) n
  refine le_antisymm ?_ (iSup_le fun n ↦ le_iff'.1 (le_iSup μ n) s)
  exact (le_iff'.1 hμν s).trans_eq (ofMeasurable_apply _ hs)

/-- Integrals against an increasing sequence of measures converge (monotone convergence). -/
theorem lintegral_iSup_of_monotone {μ : ℕ → Measure X} (hμ : Monotone μ) {f : X → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x, f x ∂(⨆ n, μ n) = ⨆ n, ∫⁻ x, f x ∂μ n := by
  refine le_antisymm ?_ (iSup_le fun n ↦ lintegral_mono' (le_iSup μ n) le_rfl)
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  refine iSup_le fun k ↦ ?_
  have : (SimpleFunc.eapprox f k).lintegral (⨆ n, μ n) =
      ⨆ n, (SimpleFunc.eapprox f k).lintegral (μ n) := by
    simp only [SimpleFunc.lintegral, iSup_apply_of_monotone hμ (SimpleFunc.measurableSet_fiber _ _),
      ENNReal.mul_iSup]
    exact ENNReal.finsetSum_iSup_of_monotone fun _ _ _ h ↦ mul_le_mul_right (hμ h _) _
  exact this.trans_le (iSup_mono fun n ↦ lintegral_eapprox_le_lintegral hf k)

/-- Binding is monotone in the measure. -/
theorem bind_mono_left {μ μ' : Measure X} (h : μ ≤ μ') {f : X → Measure Y}
    (hf : Measurable f := by fun_prop) : μ.bind f ≤ μ'.bind f := le_iff.2 fun s hs ↦ by
  rw [bind_apply hs hf.aemeasurable, bind_apply hs hf.aemeasurable]
  exact lintegral_mono' h le_rfl

/-- Binding commutes with the supremum of an increasing sequence of measures. -/
theorem iSup_bind_of_monotone {μ : ℕ → Measure X} (hμ : Monotone μ) {f : X → Measure Y}
    (hf : Measurable f := by fun_prop) : (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  have hmono : Monotone fun n ↦ (μ n).bind f := fun _ _ h ↦ bind_mono_left (hμ h) hf
  ext s hs
  rw [iSup_apply_of_monotone hmono hs, bind_apply hs hf.aemeasurable,
    lintegral_iSup_of_monotone hμ (f := (f · s)) ((measurable_coe hs).comp hf)]
  simp_rw [bind_apply hs hf.aemeasurable]

/-- Pushing forward commutes with the supremum of an increasing sequence of measures. -/
theorem map_iSup_of_monotone {μ : ℕ → Measure X} (hμ : Monotone μ) {f : X → Y}
    (hf : Measurable f := by fun_prop) : (⨆ n, μ n).map f = ⨆ n, (μ n).map f := by
  simp_rw [← bind_dirac_eq_map _ hf]
  exact iSup_bind_of_monotone hμ

end MeasureTheory.Measure

/-- A set of `Option X` is measurable when its points under `some` are. -/
instance Option.instMeasurableSpace {X : Type*} [MeasurableSpace X] : MeasurableSpace (Option X) :=
  .comap (Equiv.optionEquivSumPUnit.{0, _} X) inferInstance

@[fun_prop]
theorem measurable_some {X : Type*} [MeasurableSpace X] : Measurable (some : X → Option X) := by
  refine measurable_comap_iff.2 ?_
  simpa [Function.comp_def, Equiv.optionEquivSumPUnit] using measurable_inl

/-- The lift of a discrete measurable space is discrete. -/
instance discreteMeasurableSpace_uLift {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (ULift α) :=
  ⟨fun _ ↦ measurable_down (t := ULift.up ⁻¹' _) .of_discrete⟩

namespace MeasureTheory

/-- A function below `1` has finite integral against a finite measure. -/
theorem lintegral_ne_top_of_le_one {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsFiniteMeasure P] {F : Z → ℝ≥0∞} (hF : ∀ z, F z ≤ 1) : ∫⁻ z, F z ∂P ≠ ⊤ :=
  ne_top_of_le_ne_top (measure_ne_top P Set.univ) ((lintegral_mono hF).trans_eq lintegral_one)

/-- A measure on a point is its mass times the Dirac mass. -/
theorem Measure.eq_smul_dirac_punit (μ : Measure PUnit.{u + 1}) :
    μ = μ Set.univ • Measure.dirac PUnit.unit := by
  ext s hs
  rcases s.eq_empty_or_nonempty with rfl | hs'
  · simp
  · simp [Subsingleton.eq_univ_of_nonempty hs']

/-- Integrating a function that factors through a finite partition sums over its cells. -/
theorem toReal_lintegral_ofReal_comp {Z : Type*} [MeasurableSpace Z] {n : ℕ} {π : Z → Fin n}
    (hπ : Measurable π) {w : Fin n → ℝ} (hw : ∀ j, 0 ≤ w j) (P : Measure Z) [IsFiniteMeasure P] :
    (∫⁻ z, ENNReal.ofReal (w (π z)) ∂P).toReal = ∑ j, w j * (P (π ⁻¹' {j})).toReal := by
  rw [← lintegral_map (f := fun j ↦ ENNReal.ofReal (w j)) (by fun_prop) hπ, lintegral_fintype,
    ENNReal.toReal_sum fun j _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Measure.map_apply hπ (measurableSet_singleton j), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hw j)]

end MeasureTheory

/-- Capping at `n` keeps a bound `a ≤ c b` with `1 ≤ c`. -/
theorem ENNReal.min_le_mul_min {a b c n : ℝ≥0∞} (h : a ≤ c * b) (hc : 1 ≤ c) :
    min a n ≤ c * min b n := by
  rcases le_total b n with hb | hb
  · rw [min_eq_left hb]
    exact (min_le_left _ _).trans h
  · rw [min_eq_right hb]
    exact (min_le_right _ _).trans (le_mul_of_one_le_left' hc)

/-- Enlarging the denominator of `a⁻¹ * S` to `a + d` loses at most `d / (a + d)` when `S ≤ a`. -/
theorem ENNReal.inv_mul_le_inv_mul_add {a d : ℕ} (ha : a ≠ 0) {S : ℝ≥0∞} (hS : S ≤ a) :
    (a : ℝ≥0∞)⁻¹ * S ≤ ((a : ℝ≥0∞) + d)⁻¹ * S + d / ((a : ℝ≥0∞) + d) := by
  have hinvS : (a : ℝ≥0∞)⁻¹ * S ≤ 1 := by
    calc (a : ℝ≥0∞)⁻¹ * S
      _ ≤ (a : ℝ≥0∞)⁻¹ * a := by gcongr
      _ = 1 := ENNReal.inv_mul_cancel (by positivity) (by finiteness)
  calc (a : ℝ≥0∞)⁻¹ * S
    _ = ((a + d : ℝ≥0∞)⁻¹ * (a + d)) * ((a : ℝ≥0∞)⁻¹ * S) := by
        rw [ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]
    _ = (a + d : ℝ≥0∞)⁻¹ * (a * ((a : ℝ≥0∞)⁻¹ * S) + d * ((a : ℝ≥0∞)⁻¹ * S)) := by
        rw [mul_assoc, add_mul]
    _ = (a + d : ℝ≥0∞)⁻¹ * (S + d * ((a : ℝ≥0∞)⁻¹ * S)) := by
        rw [← mul_assoc (a : ℝ≥0∞), ENNReal.mul_inv_cancel (by positivity) (by finiteness),
          one_mul]
    _ ≤ (a + d : ℝ≥0∞)⁻¹ * (S + d * 1) := by gcongr
    _ = ((a : ℝ≥0∞) + d)⁻¹ * S + d / ((a : ℝ≥0∞) + d) := by
        rw [mul_one, mul_add, ENNReal.div_eq_inv_mul]

theorem EReal.mul_finset_sum_of_nonneg {ι : Type*} (s : Finset ι) (c : EReal) {x : ι → EReal}
    (hx : ∀ i ∈ s, 0 ≤ x i) : c * ∑ i ∈ s, x i = ∑ i ∈ s, c * x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.forall_mem_insert] at hx
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      EReal.left_distrib_of_nonneg hx.1 (Finset.sum_nonneg hx.2), ih hx.2]

theorem EReal.le_coe_mul_iff {c : ℝ} (hc : 0 < c) {x y : EReal} :
    x ≤ c * y ↔ ((c⁻¹ : ℝ) : EReal) * x ≤ y := by
  have hc' : 0 < c⁻¹ := inv_pos.2 hc
  induction x <;> induction y <;>
    simp [EReal.coe_mul_top_of_pos hc, EReal.coe_mul_bot_of_pos hc, EReal.coe_mul_top_of_pos hc',
      EReal.coe_mul_bot_of_pos hc', ← EReal.coe_mul, inv_mul_le_iff₀ hc]

/-- A sum composed with a map injective on `Ico 0 zL` and landing in `Ico 0 zR` is
bounded by the full codomain sum. -/
theorem Finset.sum_Ico_comp_le_of_injOn {zL zR : ℤ} {f : ℤ → ℤ}
    (hdom : ∀ n : ℤ, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂ : ℤ, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂)
    (g : ℤ → ℝ≥0∞) : ∑ n ∈ Finset.Ico 0 zL, g (f n) ≤ ∑ m ∈ Finset.Ico 0 zR, g m := by
  calc ∑ n ∈ Finset.Ico 0 zL, g (f n)
    _ = ∑ m ∈ (Finset.Ico 0 zL).image f, g m :=
        (Finset.sum_image fun n hn m hm heq => by
          simp only [Finset.coe_Ico, Set.mem_Ico] at hn hm
          exact hinj n m hn.1 hn.2 hm.1 hm.2 heq).symm
    _ ≤ ∑ m ∈ Finset.Ico 0 zR, g m := by
        refine Finset.sum_le_sum_of_subset fun m hm => ?_
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
        simp only [Finset.mem_Ico] at hn ⊢
        exact hdom n hn.1 hn.2

/-- A sum of `≤ 1` terms over `Ico 0 z` is at most `z.toNat`. -/
theorem Finset.sum_Ico_le_toNat {z : ℤ} {g : ℤ → ℝ≥0∞} (hg : ∀ n, g n ≤ 1) :
    ∑ n ∈ Finset.Ico 0 z, g n ≤ z.toNat := by
  calc ∑ n ∈ Finset.Ico 0 z, g n
    _ ≤ ∑ _n ∈ Finset.Ico 0 z, 1 := Finset.sum_le_sum fun n _ => hg n
    _ = z.toNat := by
        rw [Finset.sum_const, Int.card_Ico, nsmul_eq_mul, mul_one, Int.sub_zero]
