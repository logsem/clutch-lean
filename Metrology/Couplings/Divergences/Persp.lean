module

public import Mathlib.Analysis.Convex.Approximation
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! The perspective of a convex weight and Jensen's inequality for it (Approximate Span
Liftings, Def. 2.6). -/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-! ## Sums in the extended reals -/

namespace EReal

theorem coe_finset_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ((∑ i ∈ s, x i : ℝ) : EReal) = ∑ i ∈ s, (x i : EReal) :=
  map_sum (⟨⟨(↑), coe_zero⟩, coe_add⟩ : ℝ →+ EReal) x s

theorem sum_ne_bot {ι : Type*} (s : Finset ι) {a : ι → EReal} (ha : ∀ i ∈ s, a i ≠ ⊥) :
    ∑ i ∈ s, a i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.forall_mem_insert] at ha
    rw [Finset.sum_insert hj]
    exact add_ne_bot_iff.2 ⟨ha.1, ih ha.2⟩

theorem tendsto_finset_sum {ι α : Type*} {l : Filter α} (s : Finset ι) {g : ι → α → EReal}
    {a : ι → EReal} (hg : ∀ i ∈ s, Tendsto (g i) l (𝓝 (a i))) (ha : ∀ i ∈ s, a i ≠ ⊥) :
    Tendsto (fun n ↦ ∑ i ∈ s, g i n) l (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert j s hj ih =>
    rw [Finset.forall_mem_insert] at hg ha
    simp only [Finset.sum_insert hj]
    exact (continuousAt_add (Or.inr (sum_ne_bot s ha.2)) (Or.inl ha.1)).tendsto.comp
      (hg.1.prodMk_nhds (ih hg.2 ha.2))

theorem toENNReal_sum {ι : Type*} (s : Finset ι) {x : ι → EReal} (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, x i).toENNReal = ∑ i ∈ s, (x i).toENNReal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.forall_mem_insert] at hx
    rw [Finset.sum_insert hj, Finset.sum_insert hj, toENNReal_add hx.1 (Finset.sum_nonneg hx.2),
      ih hx.2]

end EReal

namespace ProbabilityTheory

/-! ## The slope at infinity and the perspective -/

variable {f g : ℝ → ℝ}

/-- The slope `limsup f t / t` of a weight at `+∞` (a limit for convex weights). -/
noncomputable def derivAtTop (f : ℝ → ℝ) : EReal :=
  limsup (fun t : ℝ ↦ ((f t / t : ℝ) : EReal)) atTop

/-- The perspective `b f (a / b)`, extended by `a f'(∞)` at `b = 0` (Def. 2.6). -/
noncomputable def persp (f : ℝ → ℝ) (a b : ℝ) : EReal :=
  if b = 0 then a * derivAtTop f else ((b * f (a / b) : ℝ) : EReal)

@[simp]
theorem persp_zero_right (f : ℝ → ℝ) (a : ℝ) : persp f a 0 = a * derivAtTop f := by
  simp [persp]

theorem persp_of_ne_zero {a b : ℝ} (hb : b ≠ 0) :
    persp f a b = ((b * f (a / b) : ℝ) : EReal) := by
  simp [persp, hb]

theorem persp_self {a : ℝ} (ha : 0 ≤ a) : persp f a a = ((a * f 1 : ℝ) : EReal) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  · rw [persp_of_ne_zero ha.ne', div_self ha.ne']

theorem le_derivAtTop_of_affine_le {c c' : ℝ} (h : ∀ t, 0 ≤ t → c * t + c' ≤ f t) :
    (c : EReal) ≤ derivAtTop f := by
  have hlim : Tendsto (fun t : ℝ ↦ ((c + c' / t : ℝ) : EReal)) atTop (𝓝 c) := by
    have := (tendsto_const_nhds (x := c)).add ((tendsto_const_nhds (x := c')).div_atTop tendsto_id)
    exact EReal.tendsto_coe.2 (by simpa using this)
  rw [← hlim.limsup_eq]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [EReal.coe_le_coe_iff, le_div_iff₀ ht, add_mul, div_mul_cancel₀ _ ht.ne']
  exact h t ht.le

theorem derivAtTop_nonneg (hf : ∀ t, 0 ≤ t → 0 ≤ f t) : 0 ≤ derivAtTop f := by
  simpa using le_derivAtTop_of_affine_le (c := 0) (by simpa using hf)

theorem derivAtTop_mono (h : ∀ t, 0 ≤ t → f t ≤ g t) : derivAtTop f ≤ derivAtTop g := by
  refine limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact EReal.coe_le_coe_iff.2 (div_le_div_of_nonneg_right (h t ht.le) ht.le)

/-- Every secant slope of a convex weight is at most its slope at `∞`. -/
theorem le_derivAtTop (hf : ConvexOn ℝ (Ici 0) f) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    (((f (x + h) - f x) / h : ℝ) : EReal) ≤ derivAtTop f := by
  set s := (f (x + h) - f x) / h
  have hlow (t : ℝ) (ht : x + h ≤ t) : f x + s * (t - x) ≤ f t := by
    have := hf.secant_mono hx (by simp only [mem_Ici]; linarith)
      (by simp only [mem_Ici]; linarith) (by linarith) (by linarith) ht
    rw [add_sub_cancel_left] at this
    rwa [← le_sub_iff_add_le', ← le_div_iff₀ (by linarith)]
  by_contra! hlt
  obtain ⟨r, hr, hrs⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  rw [EReal.coe_lt_coe_iff] at hrs
  -- `f t / t ≥ s + (f x - s x) / t`, which exceeds `r` for large `t`
  have hev : ∀ᶠ t in atTop, (r : EReal) ≤ ((f t / t : ℝ) : EReal) := by
    have hlim : Tendsto (fun t : ℝ ↦ s + (f x - s * x) / t) atTop (𝓝 s) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_const_nhds (x := f x - s * x)).div_atTop tendsto_id)
    filter_upwards [hlim.eventually (lt_mem_nhds hrs), eventually_ge_atTop (x + h),
      eventually_gt_atTop 0] with t h1 h2 h3
    rw [EReal.coe_le_coe_iff, le_div_iff₀ h3]
    replace h1 := mul_lt_mul_of_pos_right h1 h3
    rw [add_mul, div_mul_cancel₀ _ h3.ne'] at h1
    linarith [hlow t h2]
  exact absurd (le_limsup_of_frequently_le hev.frequently) (not_le.2 hr)

theorem derivAtTop_ne_bot (hf : ConvexOn ℝ (Ici 0) f) : derivAtTop f ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_derivAtTop hf le_rfl one_pos)

theorem derivAtTop_mul_ne_bot (hf : ConvexOn ℝ (Ici 0) f) {m : ℝ≥0∞} (hm : m ≠ ⊤) :
    derivAtTop f * m ≠ ⊥ := by
  rw [← EReal.coe_ennreal_toReal hm]
  induction h : derivAtTop f with
  | bot => exact absurd h (derivAtTop_ne_bot hf)
  | top =>
    rcases ENNReal.toReal_nonneg.eq_or_lt with h0 | h0
    · rw [← h0]
      simp
    · simp [EReal.top_mul_of_pos (EReal.coe_pos.2 h0)]
  | coe l => exact EReal.coe_mul l _ ▸ EReal.coe_ne_bot _

/-- An affine minorant of `f` bounds its perspective. -/
theorem affine_le_persp {c c' : ℝ} (h : ∀ t, 0 ≤ t → c * t + c' ≤ f t) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : ((c * a + c' * b : ℝ) : EReal) ≤ persp f a b := by
  rcases hb.eq_or_lt with rfl | hb
  · rw [persp_zero_right, mul_zero, add_zero, EReal.coe_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (le_derivAtTop_of_affine_le h) (EReal.coe_nonneg.2 ha)
  rw [persp_of_ne_zero hb.ne', EReal.coe_le_coe_iff]
  calc c * a + c' * b = b * (c * (a / b) + c') := by field_simp
    _ ≤ b * f (a / b) := mul_le_mul_of_nonneg_left (h _ (div_nonneg ha hb.le)) hb.le

theorem persp_nonneg (hf : ∀ t, 0 ≤ t → 0 ≤ f t) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ persp f a b := by
  simpa using affine_le_persp (c := 0) (c' := 0) (by simpa using hf) ha hb

theorem persp_mono (h : ∀ t, 0 ≤ t → f t ≤ g t) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    persp f a b ≤ persp g a b := by
  rcases hb.eq_or_lt with rfl | hb
  · simpa using mul_le_mul_of_nonneg_left (derivAtTop_mono h) (EReal.coe_nonneg.2 ha)
  rw [persp_of_ne_zero hb.ne', persp_of_ne_zero hb.ne', EReal.coe_le_coe_iff]
  exact mul_le_mul_of_nonneg_left (h _ (div_nonneg ha hb.le)) hb.le

theorem persp_ne_bot (hf : ConvexOn ℝ (Ici 0) f) {a b : ℝ} (ha : 0 ≤ a) : persp f a b ≠ ⊥ := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [persp_zero_right]
    rcases ha.eq_or_lt with rfl | ha
    · simp
    induction h : derivAtTop f with
    | bot => exact absurd h (derivAtTop_ne_bot hf)
    | top => simp [EReal.coe_mul_top_of_pos ha]
    | coe l => exact EReal.coe_mul a l ▸ EReal.coe_ne_bot _
  · rw [persp_of_ne_zero hb]
    exact EReal.coe_ne_bot _

/-- The perspective of a convex weight is subadditive. -/
theorem persp_add_le (hf : ConvexOn ℝ (Ici 0) f) {a a' b b' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (hb : 0 ≤ b) (hb' : 0 ≤ b') : persp f (a + a') (b + b') ≤ persp f a b + persp f a' b' := by
  -- one-sided case: adding mass `x` against zero costs at most `x f'(∞)`
  have side {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) :
      persp f (x + y) z ≤ persp f x 0 + persp f y z := by
    rcases hx.eq_or_lt with rfl | hx
    · simp
    rw [persp_zero_right, persp_of_ne_zero hz.ne', persp_of_ne_zero hz.ne']
    have key := le_derivAtTop hf (div_nonneg hy hz.le) (div_pos hx hz)
    have hsplit : z * f ((x + y) / z) = z * f (y / z) +
        x * ((f (y / z + x / z) - f (y / z)) / (x / z)) := by
      rw [add_comm x y, add_div, add_comm (y / z)]
      field_simp
      ring
    rw [hsplit, EReal.coe_add, add_comm, EReal.coe_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left key (EReal.coe_nonneg.2 hx.le)) le_rfl
  rcases hb.eq_or_lt with rfl | hb
  · rcases hb'.eq_or_lt with rfl | hb'
    · simp only [add_zero, persp_zero_right, EReal.coe_add]
      exact (EReal.right_distrib_of_nonneg (EReal.coe_nonneg.2 ha) (EReal.coe_nonneg.2 ha')).le
    · rw [zero_add]
      exact side ha ha' hb'
  rcases hb'.eq_or_lt with rfl | hb'
  · rw [add_zero, add_comm a a', add_comm (persp f a b)]
    exact side ha' ha hb
  -- both denominators positive: convexity with weights `b, b'`
  rw [persp_of_ne_zero hb.ne', persp_of_ne_zero hb'.ne',
    persp_of_ne_zero (add_pos hb hb').ne', ← EReal.coe_add, EReal.coe_le_coe_iff]
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

/-- Finite Jensen: the perspective of sums is at most the sum of perspectives. -/
theorem persp_sum_le (hf : ConvexOn ℝ (Ici 0) f) {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    persp f (∑ i ∈ s, a i) (∑ i ∈ s, b i) ≤ ∑ i ∈ s, persp f (a i) (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.forall_mem_insert] at ha hb
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    exact (persp_add_le hf ha.1 (Finset.sum_nonneg ha.2) hb.1 (Finset.sum_nonneg hb.2)).trans
      (add_le_add le_rfl (ih ha.2 hb.2))

/-- The perspective of a convex weight is continuous along sequences that keep the zero pattern
of the limit. -/
theorem tendsto_persp (hf : ConvexOn ℝ (Ici 0) f) {p q : ℕ → ℝ} {p₀ q₀ : ℝ}
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto q atTop (𝓝 q₀)) (hp0 : ∀ n, 0 ≤ p n)
    (hq0 : ∀ n, 0 ≤ q n) (hpz : ∀ n, p n = 0 ↔ p₀ = 0) (hqz : ∀ n, q n = 0 ↔ q₀ = 0) :
    Tendsto (fun n ↦ persp f (p n) (q n)) atTop (𝓝 (persp f p₀ q₀)) := by
  have hp₀ : 0 ≤ p₀ := ge_of_tendsto' hp hp0
  have hq₀ : 0 ≤ q₀ := ge_of_tendsto' hq hq0
  rcases hq₀.eq_or_lt with rfl | hq₀
  · simp only [fun n ↦ (hqz n).2 rfl, persp_zero_right]
    rcases hp₀.eq_or_lt with rfl | hp₀
    · simp [fun n ↦ (hpz n).2 rfl]
    have hp₀' : ((p₀ : EReal), derivAtTop f).1 ≠ 0 := by simpa using hp₀.ne'
    exact (EReal.continuousAt_mul (Or.inl hp₀') (Or.inl hp₀') (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).tendsto.comp
      ((EReal.tendsto_coe.2 hp).prodMk_nhds tendsto_const_nhds)
  have hev : ∀ᶠ n in atTop, 0 < q n := hq.eventually (lt_mem_nhds hq₀)
  have hlim : Tendsto (fun n ↦ q n * f (p n / q n)) atTop (𝓝 (q₀ * f (p₀ / q₀))) := by
    rcases hp₀.eq_or_lt with rfl | hp₀
    · simpa [fun n ↦ (hpz n).2 rfl] using hq.mul_const (f 0)
    refine hq.mul ((hf.continuousOn_interior.continuousAt ?_).tendsto.comp (hp.div hq hq₀.ne'))
    rw [interior_Ici]
    exact Ioi_mem_nhds (div_pos hp₀ hq₀)
  rw [persp_of_ne_zero hq₀.ne']
  refine (EReal.tendsto_coe.2 hlim).congr' ?_
  filter_upwards [hev] with n hn
  rw [persp_of_ne_zero hn.ne']

/-! ## Jensen's inequality -/

/-- Jensen's inequality for the perspective, against a weight with values in `[0, 1]`. -/
theorem persp_integral_le (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {G w : X → ℝ}
    (hG : ∀ x, 0 ≤ G x) (hGi : Integrable G ν) (hfG : Integrable (fun x ↦ f (G x)) ν)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    persp f (∫ x, w x * G x ∂ν) (∫ x, w x ∂ν) ≤ ((∫ x, w x * f (G x) ∂ν : ℝ) : EReal) := by
  have hwb : ∀ᵐ x ∂ν, ‖w x‖ ≤ 1 := .of_forall fun x ↦ (Real.norm_of_nonneg (hw0 x)).trans_le (hw1 x)
  have hwG : Integrable (fun x ↦ w x * G x) ν := hGi.bdd_mul hw.aestronglyMeasurable hwb
  have hwi : Integrable w ν := .of_bound hw.aestronglyMeasurable 1 hwb
  have hb0 : 0 ≤ ∫ x, w x ∂ν := integral_nonneg hw0
  rcases hb0.eq_or_lt with hb | hb
  · have h0 : w =ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg hw0 hwi).1 hb.symm
    rw [← hb, persp_zero_right, integral_eq_zero_of_ae (h0.mono fun x hx ↦ by simp [hx]),
      integral_eq_zero_of_ae (h0.mono fun x hx ↦ by simp [hx])]
    simp
  rw [persp_of_ne_zero hb.ne', EReal.coe_le_coe_iff]
  refine le_of_forall_lt_imp_le_of_dense fun y hy ↦ ?_
  obtain ⟨c, c', hle, heq⟩ := hf.exists_affine_le_of_lt_real
    (mem_Ici.2 (div_nonneg (integral_nonneg fun x ↦ mul_nonneg (hw0 x) (hG x)) hb.le))
    ((div_lt_iff₀' hb).2 hy) isClosed_Ici (hf.continuousOn_Ici hf_cont).lowerSemicontinuousOn
  calc y = c * ∫ x, w x * G x ∂ν + c' * ∫ x, w x ∂ν := by
        rw [← div_mul_cancel₀ y hb.ne', ← heq]
        field_simp
    _ = ∫ x, w x * (c * G x + c') ∂ν := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hwG.const_mul c)
          (hwi.const_mul c')]
        exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
    _ ≤ ∫ x, w x * f (G x) ∂ν :=
        integral_mono ((hwG.const_mul c).add (hwi.const_mul c') |>.congr
          (ae_of_all _ fun x ↦ by simp only [Pi.add_apply]; ring))
          (hfG.bdd_mul hw.aestronglyMeasurable hwb)
          fun x ↦ mul_le_mul_of_nonneg_left (hle _ (hG x)) (hw0 x)

end ProbabilityTheory
