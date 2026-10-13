module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Metrology.Couplings.DP.Discretize
public import Metrology.Couplings.DifferentialPrivacy

/-! Basic properties of `f`-divergences (Approximate Span Liftings, §4.2: Thms. 4.7–4.9). -/

@[expose] public section

open MeasureTheory Set Filter Topology GradedDivergence
open scoped ENNReal

universe u

namespace WeightFunction

variable {f : WeightFunction}

/-! ### The perspective of a convex weight -/

/-- A secant slope of a convex weight is at most its slope at infinity. -/
theorem le_slopeAtTop (hf : ConvexOn ℝ (Ici 0) f) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    (((f (x + h) - f x) / h : ℝ) : EReal) ≤ f.slopeAtTop := by
  set s := (f (x + h) - f x) / h
  have hlow (t : ℝ) (ht : x + h ≤ t) : f x + s * (t - x) ≤ f t := by
    have := hf.secant_mono (a := x) hx (by simp only [mem_Ici]; linarith)
      (by simp only [mem_Ici]; linarith) (by linarith) (by linarith) ht
    rw [add_sub_cancel_left] at this
    rw [← le_sub_iff_add_le', ← le_div_iff₀ (by linarith)]
    exact this
  by_contra! hlt
  obtain ⟨r, hr, hrs⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  rw [EReal.coe_lt_coe_iff] at hrs
  -- `f t / t ≥ s + (f x - s x) / t`, which exceeds `r` for large `t`
  have hev : ∀ᶠ t in atTop, (r : EReal) ≤ ((f t / t : ℝ) : EReal) := by
    have hlim : Tendsto (fun t : ℝ ↦ s + (f x - s * x) / t) atTop (𝓝 s) := by
      simpa using (tendsto_const_nhds (x := s)).add
        ((tendsto_const_nhds (x := f x - s * x)).div_atTop tendsto_id)
    filter_upwards [hlim.eventually (lt_mem_nhds hrs), eventually_ge_atTop (x + h),
      eventually_gt_atTop 0] with t h1 h2 h3
    rw [EReal.coe_le_coe_iff, le_div_iff₀ h3]
    have h1' := mul_lt_mul_of_pos_right h1 h3
    rw [add_mul, div_mul_cancel₀ _ h3.ne'] at h1'
    linarith [hlow t h2]
  exact absurd (Filter.le_limsup_of_frequently_le hev.frequently) (not_le.2 hr)

theorem slopeAtTop_ne_bot (hf : ConvexOn ℝ (Ici 0) f) : f.slopeAtTop ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_slopeAtTop hf le_rfl one_pos)

theorem persp_self {a : ℝ} (ha : 0 ≤ a) : f.persp a a = ((a * f 1 : ℝ) : EReal) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [persp]
  · simp [persp, ha.ne']

theorem persp_ne_bot (hf : ConvexOn ℝ (Ici 0) f) {a b : ℝ} (ha : 0 ≤ a) : f.persp a b ≠ ⊥ := by
  unfold persp
  split_ifs with hb ha0
  · simp
  · induction h : f.slopeAtTop with
    | bot => exact absurd h (slopeAtTop_ne_bot hf)
    | top => simp [EReal.coe_mul_top_of_pos (lt_of_le_of_ne ha (Ne.symm ha0))]
    | coe l => exact (EReal.coe_mul a l ▸ EReal.coe_ne_bot _)
  · exact EReal.coe_ne_bot _

/-- The perspective of a convex weight is subadditive. -/
theorem persp_add_le (hf : ConvexOn ℝ (Ici 0) f) {a a' b b' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (hb : 0 ≤ b) (hb' : 0 ≤ b') : f.persp (a + a') (b + b') ≤ f.persp a b + f.persp a' b' := by
  -- one-sided case: adding mass `a` against zero `b` costs at most `a f'(∞)`
  have side {a a' b' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hb' : 0 < b') :
      f.persp (a + a') b' ≤ f.persp a 0 + f.persp a' b' := by
    rcases ha.eq_or_lt with rfl | ha
    · simp [persp]
    simp only [persp, hb'.ne', ↓reduceIte, ha.ne']
    have key := le_slopeAtTop hf (div_nonneg ha' hb'.le) (div_pos ha hb')
    have hsplit : b' * f ((a + a') / b') = b' * f (a' / b') +
        a * ((f (a' / b' + a / b') - f (a' / b')) / (a / b')) := by
      rw [add_comm a a', add_div, add_comm (a' / b')]; field_simp; ring
    rw [hsplit, EReal.coe_add, add_comm, EReal.coe_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left key (EReal.coe_nonneg.2 ha.le)) le_rfl
  rcases hb.eq_or_lt with rfl | hb
  · rcases hb'.eq_or_lt with rfl | hb'
    · -- both denominators vanish: the perspective is linear in `a`
      rcases ha.eq_or_lt with rfl | ha
      · simp [persp]
      rcases ha'.eq_or_lt with rfl | ha'
      · simp [persp]
      simp only [persp, add_zero, ↓reduceIte, ha.ne', ha'.ne', (add_pos ha ha').ne']
      rw [EReal.coe_add, EReal.right_distrib_of_nonneg (EReal.coe_nonneg.2 ha.le)
        (EReal.coe_nonneg.2 ha'.le)]
    · rw [zero_add]
      exact side ha ha' hb'
  rcases hb'.eq_or_lt with rfl | hb'
  · rw [add_zero, add_comm a a', add_comm (f.persp a b)]
    exact side ha' ha hb
  -- both denominators positive: convexity with weights `b, b'`
  simp only [persp, hb.ne', hb'.ne', (add_pos hb hb').ne', ↓reduceIte]
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hw : b / (b + b') + b' / (b + b') = 1 := by field_simp
  have := hf.2 (mem_Ici.2 (div_nonneg ha hb.le)) (mem_Ici.2 (div_nonneg ha' hb'.le))
    (div_nonneg hb.le (add_pos hb hb').le) (div_nonneg hb'.le (add_pos hb hb').le) hw
  simp only [smul_eq_mul] at this
  have hpt : b / (b + b') * (a / b) + b' / (b + b') * (a' / b') = (a + a') / (b + b') := by
    field_simp
  rw [hpt] at this
  calc (b + b') * f ((a + a') / (b + b'))
      ≤ (b + b') * (b / (b + b') * f (a / b) + b' / (b + b') * f (a' / b')) :=
        mul_le_mul_of_nonneg_left this (add_pos hb hb').le
    _ = b * f (a / b) + b' * f (a' / b') := by field_simp

/-- The perspective of a convex weight is subadditive over finite sums. -/
theorem persp_sum_le (hf : ConvexOn ℝ (Ici 0) f) {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    f.persp (∑ i ∈ s, a i) (∑ i ∈ s, b i) ≤ ∑ i ∈ s, f.persp (a i) (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [persp]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    refine (persp_add_le hf (ha j (by simp)) (Finset.sum_nonneg fun i hi ↦ ha i (by simp [hi]))
      (hb j (by simp)) (Finset.sum_nonneg fun i hi ↦ hb i (by simp [hi]))).trans ?_
    exact add_le_add le_rfl (ih (fun i hi ↦ ha i (by simp [hi])) fun i hi ↦ hb i (by simp [hi]))

end WeightFunction

/-! ### Sums in the extended reals -/

theorem EReal.sum_ne_bot {ι : Type*} (s : Finset ι) {a : ι → EReal} (ha : ∀ i ∈ s, a i ≠ ⊥) :
    ∑ i ∈ s, a i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact EReal.add_ne_bot_iff.2 ⟨ha j (by simp), ih fun i hi ↦ ha i (by simp [hi])⟩

/-- Finite sums of converging extended reals converge, away from `⊥`. -/
theorem EReal.tendsto_finset_sum {ι α : Type*} {l : Filter α} (s : Finset ι)
    {g : ι → α → EReal} {a : ι → EReal} (hg : ∀ i ∈ s, Tendsto (g i) l (𝓝 (a i)))
    (ha : ∀ i ∈ s, a i ≠ ⊥) : Tendsto (fun n ↦ ∑ i ∈ s, g i n) l (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    have hs : ∑ i ∈ s, a i ≠ ⊥ := EReal.sum_ne_bot s fun i hi ↦ ha i (by simp [hi])
    exact (EReal.continuousAt_add (Or.inr hs) (Or.inl (ha j (by simp)))).tendsto.comp
      ((hg j (by simp)).prodMk_nhds (ih (fun i hi ↦ hg i (by simp [hi]))
        fun i hi ↦ ha i (by simp [hi])))

/-! ### Measure-level properties -/

variable {X : Type*} [MeasurableSpace X] {f : WeightFunction}

/-- On the diagonal, an `f`-divergence is the total mass times `f 1`. -/
theorem fDiv_self (μ : Measure X) [IsFiniteMeasure μ] :
    fDiv f μ μ = (((μ univ).toReal * f 1 : ℝ) : EReal) := by
  have hpart (n : ℕ) (k : X → Fin n) (hk : Measurable k) :
      ∑ i, f.persp (μ (k ⁻¹' {i})).toReal (μ (k ⁻¹' {i})).toReal =
        (((μ univ).toReal * f 1 : ℝ) : EReal) := by
    simp_rw [WeightFunction.persp_self ENNReal.toReal_nonneg, ← EReal.coe_finset_sum,
      ← Finset.sum_mul, ← ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _),
      sum_measure_preimage_singleton _ fun _ _ ↦ hk (measurableSet_singleton _),
      Finset.coe_univ, preimage_univ]
  refine le_antisymm (iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ (hpart n k hk).le) ?_
  exact le_iSup_of_le 1 <| le_iSup_of_le (fun _ ↦ 0) <| le_iSup_of_le measurable_const
    (hpart 1 _ measurable_const).ge

/-- On a finite space, a convex `f`-divergence is the sum over singletons. -/
theorem fDiv_eq_sum (hf : ConvexOn ℝ (Ici 0) f) {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ρ₁ ρ₂ : Measure I) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] :
    fDiv f ρ₁ ρ₂ = ∑ i, f.persp (ρ₁ {i}).toReal (ρ₂ {i}).toReal := by
  classical
  apply le_antisymm
  · refine iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun _ ↦ ?_
    have hfib (ρ : Measure I) [IsFiniteMeasure ρ] (j : Fin n) :
        (ρ (k ⁻¹' {j})).toReal = ∑ i ∈ Finset.univ.filter (k · = j), (ρ {i}).toReal := by
      rw [← ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _), sum_measure_singleton]
      congr 2
      ext; simp
    simp_rw [hfib]
    calc ∑ j, f.persp (∑ i ∈ Finset.univ.filter (k · = j), (ρ₁ {i}).toReal)
          (∑ i ∈ Finset.univ.filter (k · = j), (ρ₂ {i}).toReal)
        ≤ ∑ j, ∑ i ∈ Finset.univ.filter (k · = j), f.persp (ρ₁ {i}).toReal (ρ₂ {i}).toReal :=
          Finset.sum_le_sum fun j _ ↦ WeightFunction.persp_sum_le hf _
            (fun _ _ ↦ ENNReal.toReal_nonneg) fun _ _ ↦ ENNReal.toReal_nonneg
      _ = ∑ i, f.persp (ρ₁ {i}).toReal (ρ₂ {i}).toReal := Finset.sum_fiberwise _ _ _
  · let e := Fintype.equivFin I
    refine le_iSup_of_le _ <| le_iSup_of_le e <| le_iSup_of_le (measurable_of_countable _) ?_
    rw [← e.symm.sum_comp]
    refine le_of_eq (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [show ⇑e ⁻¹' {j} = {e.symm j} by ext; simp [Equiv.eq_symm_apply]]

/-- The perspective of a convex weight is continuous along sequences that keep the same
zero pattern. -/
theorem WeightFunction.tendsto_persp (hf : ConvexOn ℝ (Ici 0) f) {p q : ℕ → ℝ} {p₀ q₀ : ℝ}
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto q atTop (𝓝 q₀)) (hp0 : ∀ n, 0 ≤ p n)
    (hpz : ∀ n, p n = 0 ↔ p₀ = 0) (hqz : ∀ n, q n = 0 ↔ q₀ = 0) (hq0 : ∀ n, 0 ≤ q n) :
    Tendsto (fun n ↦ f.persp (p n) (q n)) atTop (𝓝 (f.persp p₀ q₀)) := by
  have hp₀ : 0 ≤ p₀ := ge_of_tendsto' hp hp0
  have hq₀ : 0 ≤ q₀ := ge_of_tendsto' hq hq0
  rcases hq₀.eq_or_lt with rfl | hq₀
  · have hqn (n : ℕ) : q n = 0 := (hqz n).2 rfl
    simp only [hqn]
    rcases hp₀.eq_or_lt with rfl | hp₀
    · simp only [(hpz _).2 rfl]
      exact tendsto_const_nhds
    simp only [persp, ↓reduceIte, hp₀.ne', fun n ↦ (not_congr (hpz n)).2 hp₀.ne']
    have hL := slopeAtTop_ne_bot hf
    have hp₀' : ((p₀ : EReal), f.slopeAtTop).1 ≠ 0 := by simpa using hp₀.ne'
    exact (EReal.continuousAt_mul (Or.inl hp₀') (Or.inl hp₀') (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).tendsto.comp
      ((EReal.tendsto_coe.2 hp).prodMk_nhds tendsto_const_nhds)
  have hev : ∀ᶠ n in atTop, 0 < q n := hq.eventually (lt_mem_nhds hq₀)
  have hlim : Tendsto (fun n ↦ q n * f (p n / q n)) atTop (𝓝 (q₀ * f (p₀ / q₀))) := by
    rcases hp₀.eq_or_lt with rfl | hp₀
    · have hpn (n : ℕ) : p n = 0 := (hpz n).2 rfl
      simpa [hpn] using hq.mul_const (f 0)
    refine hq.mul (((hf.continuousOn_interior).continuousAt ?_).tendsto.comp (hp.div hq hq₀.ne'))
    rw [interior_Ici]
    exact Ioi_mem_nhds (div_pos hp₀ hq₀)
  rw [show f.persp p₀ q₀ = ((q₀ * f (p₀ / q₀) : ℝ) : EReal) by simp [persp, hq₀.ne']]
  refine (EReal.tendsto_coe.2 hlim).congr' ?_
  filter_upwards [hev] with n hn
  simp [persp, hn.ne']

/-! ### `f`-divergence families as graded divergences -/

namespace fDivFamily

open Discretize

variable {ι : Type*} (F : ι → WeightFunction)

/-- An `f`-divergence is the supremum of its pushforwards to finite spaces. -/
theorem _root_.fDiv_eq_iSup_map (f : WeightFunction) {X : Type u} [MeasurableSpace X]
    (μ ν : Measure X) : fDiv f μ ν = ⨆ (n : ℕ) (k : X → ULift.{u} (Fin n)) (_ : Measurable k),
      fDiv f (μ.map k) (ν.map k) := by
  refine le_antisymm (iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_)
    (iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ fDiv_map_le f hk μ ν)
  have hk' : Measurable (ULift.up.{u} ∘ k) := measurable_up.comp hk
  refine le_iSup_of_le n <| le_iSup_of_le _ <| le_iSup_of_le hk' <| le_iSup_of_le n <|
    le_iSup_of_le ULift.down <| le_iSup_of_le measurable_down ?_
  simp only [Measure.map_apply hk' (measurable_down (measurableSet_singleton _))]
  exact le_rfl

/-- An `f`-divergence is the supremum of its pushforwards to finite spaces (Thm. 4.7). -/
instance isContinuous : (fDivFamily F : GradedDivergence.{u} ι).IsContinuous where
  eq_iSup α X _ μ ν _ _ := by
    simp_rw [fDivFamily, fDiv_eq_iSup_map (F α) μ, EReal.toENNReal_iSup]

/-- An `f`-divergence with `f 1 ≤ 0` at the unit grade is reflexive (§4.2). -/
theorem isReflexive [One ι] (h : F 1 1 ≤ 0) :
    (fDivFamily F : GradedDivergence.{u} ι).IsReflexive where
  self_le_zero μ _ := by
    refine EReal.toENNReal_le_iff_le_coe.2 ?_
    rw [EReal.coe_ennreal_zero, fDiv_self, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg h

/-- Families of convex `f`-divergences are approximable (Thm. 4.8, App. C.3). -/
theorem isApproximable (hF : ∀ α, ConvexOn ℝ (Ici 0) (F α)) :
    (fDivFamily F : GradedDivergence.{u} ι).IsApproximable where
  tendsto α X _ N f g _ _ μ₁ μ₂ _ _ hf hg := by
    rcases isEmpty_or_nonempty X with hX | hX
    · refine ⟨fun _ ↦ 0, fun _ ↦ isEmptyElim, fun _ j ↦ j.down.elim0,
        fun _ ↦ Subsingleton.measurable, fun _ ↦ Subsingleton.measurable, ?_⟩
      exact tendsto_const_nhds.congr fun n ↦ congrArg₂ (fun a b ↦ fDivFamily F α a b)
        (congrArg μ₁.bind (funext isEmptyElim)) (congrArg μ₂.bind (funext isEmptyElim))
    refine ⟨_, disc f g, rep f g, measurable_disc f g hf hg, measurable_rep f g, ?_⟩
    have hrd (n : ℕ) := (measurable_rep f g n).comp (measurable_disc f g hf hg n)
    have instComp {K : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (K x)]
        (n : ℕ) (x : X) : IsSubProbabilityMeasure ((K ∘ rep f g n ∘ disc f g n) x) :=
      inferInstanceAs (IsSubProbabilityMeasure (K _))
    have hb {K : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (K x)]
        (hK : Measurable K) (μ : Measure X) [IsSubProbabilityMeasure μ] :
        IsFiniteMeasure (μ.bind K) :=
      have := isSubProbabilityMeasure_bind (μ := μ) (f := K) inferInstance; inferInstance
    have hsum (n : ℕ) := @fDiv_eq_sum _ (hF α) _ _ _ _ (μ₁.bind (f ∘ rep f g n ∘ disc f g n))
      (μ₂.bind (g ∘ rep f g n ∘ disc f g n)) (hb (hf.comp (hrd n)) μ₁) (hb (hg.comp (hrd n)) μ₂)
    have hsum₀ := @fDiv_eq_sum _ (hF α) _ _ _ _ (μ₁.bind f) (μ₂.bind g) (hb hf μ₁) (hb hg μ₂)
    refine (EReal.continuous_toENNReal.tendsto _).comp ?_
    rw [funext hsum, hsum₀]
    refine EReal.tendsto_finset_sum _ (fun i _ ↦ ?_)
      fun i _ ↦ (F α).persp_ne_bot (hF α) ENNReal.toReal_nonneg
    have hlim {K : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (K x)]
        (hK : Measurable K) (μ : Measure X) [IsSubProbabilityMeasure μ]
        (hcell : ∀ n x i, cell n (K (rep f g n (disc f g n x)) {i}) = cell n (K x {i})) :
        Tendsto (fun n ↦ ((μ.bind (K ∘ rep f g n ∘ disc f g n)) {i}).toReal) atTop
          (𝓝 ((μ.bind K) {i}).toReal) :=
      have := hb hK μ
      (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_bind_disc hf hg hK hcell {i})
    have hzero {K : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (K x)]
        (hK : Measurable K) (μ : Measure X) [IsSubProbabilityMeasure μ]
        (hcell : ∀ n x i, cell n (K (rep f g n (disc f g n x)) {i}) = cell n (K x {i})) (n : ℕ) :
        ((μ.bind (K ∘ rep f g n ∘ disc f g n)) {i}).toReal = 0 ↔ ((μ.bind K) {i}).toReal = 0 := by
      have := hb hK μ
      have := hb (hK.comp (hrd n)) μ
      rw [ENNReal.toReal_eq_zero_iff, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _),
        or_iff_left (measure_ne_top _ _)]
      exact bind_disc_singleton_eq_zero_iff hf hg hK μ hcell n i
    exact (F α).tendsto_persp (hF α) (hlim hf μ₁ cell_fst) (hlim hg μ₂ cell_snd)
      (fun _ ↦ ENNReal.toReal_nonneg) (hzero hf μ₁ cell_fst) (hzero hg μ₂ cell_snd)
      fun _ ↦ ENNReal.toReal_nonneg

/-- A finite-composable family of convex `f`-divergences is composable (Thm. 4.9). -/
theorem isComposable_of_isFiniteComposable [Mul ι] (hF : ∀ α, ConvexOn ℝ (Ici 0) (F α))
    [(fDivFamily F : GradedDivergence.{u} ι).IsFiniteComposable] :
    (fDivFamily F : GradedDivergence.{u} ι).IsComposable :=
  have := isApproximable F hF
  IsComposable.of_finite _

end fDivFamily
