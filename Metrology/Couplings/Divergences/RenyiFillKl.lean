module

public import Metrology.Couplings.Divergences.FillKl
public import Metrology.Couplings.Divergences.Power
public import Metrology.Couplings.Divergences.RenyiCodensity

/-! # From Rényi to filled KL

KL is at most every Rényi divergence of order `α > 1`. On sub-probability measures the Rényi
divergence is not normalized, so a lost left mass `1 - m` costs `α / (α - 1) · log (2 - m)` more in
filled KL (`renyiKlGap`); a left probability measure costs nothing. The bound holds for liftings of
every relation (`codensity_fill_kl_rel_of_renyi`), which gives the maps `renyiToFillKl`,
`zcdpToFillKl`, `powerToFillKl` and `renyiCurveToFillKl`.

The gap is needed: a point mass `1/2` against `2/5` is within Rényi-2 budget `0` but not within
filled KL `0`, since any filling of the left side has mass at least `1/2`. -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory InformationTheory GradedLifting Set
open scoped ENNReal NNReal

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {α : ℝ}

/-! ## The mass gap -/

/-- The extra filled-KL budget `α / (α - 1) · log (2 - m)` paid by a left measure of mass `m`. -/
noncomputable def renyiKlGap (α : ℝ) (m : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (α / (α - 1) * Real.log (2 - m.toReal))

@[simp]
theorem renyiKlGap_one : renyiKlGap α 1 = 0 := by
  norm_num [renyiKlGap]

@[simp]
theorem renyiKlGap_zero : renyiKlGap α 0 = ENNReal.ofReal (α / (α - 1) * Real.log 2) := by
  simp [renyiKlGap]

/-- The gap is largest for the zero measure, at `α / (α - 1) · log 2`. -/
theorem renyiKlGap_le (hα : 1 < α) {m : ℝ≥0∞} (hm : m ≤ 1) : renyiKlGap α m ≤ renyiKlGap α 0 := by
  have hm' : m.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hm)
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith)
    (by simp [ENNReal.toReal_nonneg])) (div_nonneg (by linarith) (by linarith)))

/-! ## The test bound -/

/-- Jensen's inequality for `exp` on a sub-probability measure, with the lost mass at value `0`:
the Donsker–Varadhan bound of the filled measure against itself. -/
theorem lintegral_ofReal_le_log {μ : Measure X} [IsSubProbabilityMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) {C : ℝ} (hC : ∀ x, f x ≤ C) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal
      (Real.log (∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ + (1 - μ univ)).toReal) := by
  have hd := klDualBound_of_le (m := μ.withBot) (P := μ.withBot) (Q := μ.withBot) le_rfl
  rw [klDiv_self] at hd
  have hg : Measurable fun o : Option X ↦ o.elim 0 f := measurable_option_elim hf 0
  have := hd hg (fun o ↦ by cases o <;> simp [h0]) ⟨max C 0, by
    rintro _ ⟨o, rfl⟩
    cases o
    exacts [le_max_right _ _, (hC _).trans (le_max_left _ _)]⟩
  simpa [lintegral_withBot μ hg.ennreal_ofReal, lintegral_withBot μ hg.exp.ennreal_ofReal]
    using this

/-- A Rényi coupling of `S` bounds tests ordered by a log moment on `S`: if `e^{f x} ≤ G y` on `S`,
then `∫ f dμ ≤ ρ + log Z + gap` for every `Z ≥ max 1 (∫ G dν)`. Test the coupling with `e^{t f}`
against `G^t` at `t = (α - 1) / α`, then apply Jensen's inequality. -/
theorem lintegral_le_of_rdpCoupl [hα : Fact (1 < α)] {μ : Measure X} {ν : Measure Y}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {ρ : ℝ≥0∞} {S : X → Y → Prop}
    (h : RdpCoupl α ρ S μ ν) {f : X → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) {C : ℝ}
    (hC : ∀ x, f x ≤ C) {G : Y → ℝ≥0∞} (hG : Measurable G)
    (hfG : ∀ x y, S x y → ENNReal.ofReal (Real.exp (f x)) ≤ G y) {Z : ℝ≥0∞}
    (hZ : ∫⁻ y, G y ∂ν ≤ Z) (hZ1 : 1 ≤ Z) (hZt : Z ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      ρ + ENNReal.ofReal (Real.log Z.toReal) + renyiKlGap α (μ univ) := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · simp
  have hα1 := hα.out
  obtain ⟨t, ht_def⟩ : ∃ t, t = (α - 1) / α := ⟨_, rfl⟩
  have ht : 0 < t := ht_def ▸ div_pos (by linarith) (by linarith)
  have hti : α / (α - 1) = t⁻¹ := by rw [ht_def, inv_div]
  have htt : t * (α / (α - 1)) = 1 := by rw [hti]; exact mul_inv_cancel₀ ht.ne'
  have htf : Measurable fun x ↦ t * f x := measurable_const.mul hf
  -- the Rényi coupling tested with `e^{t f}` against `G^t`
  have hE : ∫⁻ x, ENNReal.ofReal (Real.exp (t * f x)) ∂μ ≤
      ENNReal.ofReal (Real.exp (t * ρ.toReal)) * Z ^ t := by
    have := h (f := fun x ↦ ENNReal.ofReal (Real.exp (t * f x))) (g := fun y ↦ G y ^ t)
      htf.exp.ennreal_ofReal (hG.pow_const t) fun x y hS ↦ by
        rw [mul_comm t, Real.exp_mul, ← ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht.le]
        exact ENNReal.rpow_le_rpow (hfG x y hS) ht.le
    rw [← ht_def] at this
    simp_rw [← ENNReal.rpow_mul, htt, ENNReal.rpow_one] at this
    refine this.trans ?_
    rw [expBudget_of_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hρ), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal ht.le]
    gcongr
  -- Jensen at `t f`
  have hJ := lintegral_ofReal_le_log (μ := μ) htf (fun x ↦ mul_nonneg ht.le (h0 x))
    (C := t * C) fun x ↦ mul_le_mul_of_nonneg_left (hC x) ht.le
  simp_rw [ENNReal.ofReal_mul ht.le] at hJ
  rw [lintegral_const_mul _ hf.ennreal_ofReal] at hJ
  set A := ∫⁻ x, ENNReal.ofReal (f x) ∂μ
  set E := ∫⁻ x, ENNReal.ofReal (Real.exp (t * f x)) ∂μ
  have hA : A ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal C * μ univ) (by finiteness) ?_
    rw [← lintegral_const]
    exact lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hC x)
  have hEm : μ univ ≤ E := by
    calc μ univ = ∫⁻ _, 1 ∂μ := by simp
      _ ≤ E := lintegral_mono fun x ↦ by
        simpa using Real.one_le_exp (mul_nonneg ht.le (h0 x))
  have hEt : E ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg ht.le hZt)) hE
  have hm1 : μ univ ≤ 1 := IsSubProbabilityMeasure.measure_le_one _
  -- pass to reals
  set m := (μ univ).toReal
  set z := Z.toReal
  set r := ρ.toReal
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hm1' : m ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hm1)
  have hz1 : 1 ≤ z := by simpa using ENNReal.toReal_mono hZt hZ1
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hEm' : m ≤ E.toReal := ENNReal.toReal_mono hEt hEm
  have hE' : E.toReal ≤ Real.exp (t * r) * z ^ t := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ht.le hZt)) hE
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ← ENNReal.toReal_rpow] at this
  have hsum : (E + (1 - μ univ)).toReal = E.toReal + (1 - m) := by
    rw [ENNReal.toReal_add hEt (by finiteness), ENNReal.toReal_sub_of_le hm1 ENNReal.one_ne_top,
      ENNReal.toReal_one]
  rw [hsum, ← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_mul ht.le] at hJ
  have hL : 0 ≤ Real.log (E.toReal + (1 - m)) := Real.log_nonneg (by linarith)
  have hJ' : t * A.toReal ≤ Real.log (E.toReal + (1 - m)) := (ENNReal.ofReal_le_ofReal_iff hL).1 hJ
  -- `E + 1 - m ≤ M (2 - m)` with `M = e^{t r} z^t ≥ 1`
  set M := Real.exp (t * r) * z ^ t
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le (Real.one_le_exp (mul_nonneg ht.le hr0))
    (Real.one_le_rpow hz1 ht.le)
  have hlog : Real.log (E.toReal + (1 - m)) ≤ t * r + t * Real.log z + Real.log (2 - m) := by
    have h2m : 0 < 2 - m := by linarith
    calc Real.log (E.toReal + (1 - m)) ≤ Real.log (M * (2 - m)) :=
          Real.log_le_log (by linarith) (by nlinarith)
      _ = t * r + t * Real.log z + Real.log (2 - m) := by
          rw [Real.log_mul (by positivity) h2m.ne', Real.log_mul (Real.exp_pos _).ne'
            (by positivity), Real.log_exp, Real.log_rpow (by linarith)]
  have hlz : 0 ≤ Real.log z := Real.log_nonneg hz1
  have hl2 : 0 ≤ Real.log (2 - m) := Real.log_nonneg (by linarith)
  have ha : A.toReal ≤ r + Real.log z + t⁻¹ * Real.log (2 - m) := by
    refine le_of_mul_le_mul_left ?_ ht
    rw [mul_add, mul_add, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
    linarith
  calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
    _ ≤ ENNReal.ofReal (r + Real.log z + t⁻¹ * Real.log (2 - m)) := ENNReal.ofReal_le_ofReal ha
    _ = ρ + ENNReal.ofReal (Real.log z) + renyiKlGap α (μ univ) := by
        rw [ENNReal.ofReal_add (by positivity) (mul_nonneg (inv_nonneg.2 ht.le) hl2),
          ENNReal.ofReal_add hr0 hlz, ENNReal.ofReal_toReal hρ, renyiKlGap, hti]

/-! ## Rényi liftings are filled-KL liftings -/

/-- A Rényi lifting of a relation is a filled-KL lifting, at the extra budget of the left mass
gap: a filled-KL test is a log-moment test of the Rényi coupling. -/
theorem codensity_fill_kl_rel_of_renyi [hα : Fact (1 < α)] {μ : Measure X} {ν : Measure Y}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {ρ : ℝ≥0∞} {S : X → Y → Prop}
    (hS : (codensity (renyiDivergence α)).Rel ρ S μ ν) :
    (codensity (fill klDivergence)).Rel (ρ + renyiKlGap α (μ univ)) S μ ν := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · rw [show (⊤ : ℝ≥0∞) + renyiKlGap α (μ univ) = ⊤ from top_add _]
    exact codensity_top _ _ _
  have hR := (rdpCoupl_iff_codensity hρ).2 hS
  rw [codensity_rel_iff]
  intro I _ c _ k l _ _ hkl
  have : IsSubProbabilityMeasure (k ∘ₘ μ) := isSubProbabilityMeasure_bind μ _
  have : IsSubProbabilityMeasure (l ∘ₘ ν) := isSubProbabilityMeasure_bind ν _
  rw [fill_kl_iff]
  intro h hm h0 hb
  obtain ⟨C, hC⟩ := hb
  have hC' (o : Option I) : h o ≤ C := hC ⟨o, rfl⟩
  have hC0 : 0 ≤ C := (h0 none).trans (hC' none)
  have hhs : Measurable fun i ↦ ENNReal.ofReal (h (some i)) :=
    (hm.comp measurable_some).ennreal_ofReal
  -- `F x` is the left test mass at `x`, `G y` the exponential moment on the right at `y`
  set F : X → ℝ≥0∞ := fun x ↦ ∫⁻ i, ENNReal.ofReal (h (some i)) ∂(k x) with hF_def
  have hFm : Measurable F := hhs.lintegral_kernel
  have hFC (x : X) : F x ≤ ENNReal.ofReal C := calc
    F x ≤ ∫⁻ _, ENNReal.ofReal C ∂(k x) :=
        lintegral_mono fun i ↦ ENNReal.ofReal_le_ofReal (hC' _)
    _ = ENNReal.ofReal C * k x univ := lintegral_const _
    _ ≤ ENNReal.ofReal C := mul_le_of_le_one_right' (IsSubProbabilityMeasure.measure_le_one _)
  set G : Y → ℝ≥0∞ := fun y ↦ ∫⁻ o, ENNReal.ofReal (Real.exp (h o)) ∂(l y).withBot with hG_def
  have hGm : Measurable G := hm.exp.ennreal_ofReal.lintegral_kernel (κ := Kernel.withBot l)
  have hG1 (y : Y) : 1 ≤ G y := one_le_lintegral_exp h0
  have hGt (y : Y) : G y ≠ ⊤ := lintegral_exp_ne_top hC'
  -- the slack `c` comes off the left test
  set f : X → ℝ := fun x ↦ (F x - c).toReal with hf_def
  have hfm : Measurable f := (hFm.sub measurable_const).ennreal_toReal
  have hFt (x : X) : F x - c ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tsub_le_self.trans (hFC x))
  have hfC (x : X) : f x ≤ C := ENNReal.toReal_le_of_le_ofReal hC0 (tsub_le_self.trans (hFC x))
  have hF (x : X) : F x ≤ c + ENNReal.ofReal (f x) := by
    rw [hf_def, ENNReal.ofReal_toReal (hFt x), add_comm]
    exact le_tsub_add
  have hfG (x : X) (y : Y) (hxy : S x y) : ENNReal.ofReal (Real.exp (f x)) ≤ G y := by
    have hk := fill_kl_iff.1 (hkl x y hxy) hm h0 ⟨C, hC⟩
    rw [lintegral_map hm.ennreal_ofReal measurable_some] at hk
    have hGpos : 0 < (G y).toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (hG1 y)).ne' (hGt y)
    have hlog : f x ≤ Real.log (G y).toReal :=
      ENNReal.toReal_le_of_le_ofReal
        (Real.log_nonneg (by simpa using ENNReal.toReal_mono (hGt y) (hG1 y)))
        (tsub_le_iff_left.2 hk)
    rw [← ENNReal.ofReal_toReal (hGt y)]
    exact ENNReal.ofReal_le_ofReal ((Real.le_log_iff_exp_le hGpos).1 hlog)
  -- the right moment of the bind dominates the moments at each point
  have hZ : ∫⁻ y, G y ∂ν ≤ ∫⁻ o, ENNReal.ofReal (Real.exp (h o)) ∂(l ∘ₘ ν).withBot := by
    rw [Kernel.withBot_comp, Measure.lintegral_bind (Kernel.aemeasurable _)
      hm.exp.ennreal_ofReal.aemeasurable,
      lintegral_withBot _ hm.exp.ennreal_ofReal.lintegral_kernel]
    simp only [Kernel.liftBot_some, hG_def]
    exact le_self_add
  have hcore := lintegral_le_of_rdpCoupl hR hfm (fun _ ↦ ENNReal.toReal_nonneg) hfC hGm hfG hZ
    (one_le_lintegral_exp h0) (lintegral_exp_ne_top hC')
  calc ∫⁻ o, ENNReal.ofReal (h o) ∂(k ∘ₘ μ).map some
      = ∫⁻ x, F x ∂μ := by
        rw [lintegral_map hm.ennreal_ofReal measurable_some,
          Measure.lintegral_bind k.aemeasurable hhs.aemeasurable]
    _ ≤ ∫⁻ x, (c + ENNReal.ofReal (f x)) ∂μ := lintegral_mono hF
    _ = c * μ univ + ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ c + (ρ + ENNReal.ofReal (Real.log
          (∫⁻ o, ENNReal.ofReal (Real.exp (h o)) ∂(l ∘ₘ ν).withBot).toReal) +
          renyiKlGap α (μ univ)) :=
        add_le_add (mul_le_of_le_one_right' (IsSubProbabilityMeasure.measure_le_one _)) hcore
    _ = _ := by ring

/-- From a left probability measure, a Rényi lifting of a relation is a filled-KL lifting at the
same budget. -/
theorem codensity_fill_kl_rel_of_renyi_of_isProbabilityMeasure [Fact (1 < α)] {μ : Measure X}
    {ν : Measure Y} [IsProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {ρ : ℝ≥0∞}
    {S : X → Y → Prop} (hS : (codensity (renyiDivergence α)).Rel ρ S μ ν) :
    (codensity (fill klDivergence)).Rel ρ S μ ν := by
  simpa using codensity_fill_kl_rel_of_renyi hS

/-- A Rényi lifting of a relation is a filled-KL lifting at the extra budget
`α / (α - 1) · log 2`. -/
theorem codensity_fill_kl_rel_of_renyi_le [hα : Fact (1 < α)] {μ : Measure X} {ν : Measure Y}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {ρ : ℝ≥0∞} {S : X → Y → Prop}
    (hS : (codensity (renyiDivergence α)).Rel ρ S μ ν) :
    (codensity (fill klDivergence)).Rel (ρ + renyiKlGap α 0) S μ ν :=
  (codensity_fill_kl_rel_of_renyi hS).mono
    (by gcongr; exact renyiKlGap_le hα.out (IsSubProbabilityMeasure.measure_le_one _))
    fun _ _ h ↦ h

/-! ## Divergence-level bounds -/

/-- Filled KL is at most a Rényi divergence of order `α > 1`, plus the left mass gap. -/
theorem fill_kl_of_renyi [Fact (1 < α)] {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {ρ : ℝ≥0∞} (h : renyiDivergence α ρ μ ν) :
    fill klDivergence (ρ + renyiKlGap α (μ univ)) μ ν :=
  codensity_sound (codensity_fill_kl_rel_of_renyi (codensity_complete h))

/-- From a left probability measure, filled KL is at most a Rényi divergence of order `α > 1`. -/
theorem fill_kl_of_renyi_of_isProbabilityMeasure [Fact (1 < α)] {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {ρ : ℝ≥0∞}
    (h : renyiDivergence α ρ μ ν) : fill klDivergence ρ μ ν := by
  simpa using fill_kl_of_renyi h

/-- Between a probability measure and a sub-probability measure, KL is at most the Rényi
divergence of every order `α > 1`. -/
theorem klDiv_le_of_renyi [Fact (1 < α)] {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {ρ : ℝ≥0∞} (h : renyiDivergence α ρ μ ν) : klDiv μ ν ≤ ρ :=
  klDiv_le_of_fill (fill_kl_of_renyi_of_isProbabilityMeasure h)

/-! ## zCDP liftings are filled-KL liftings -/

/-- From a left probability measure, a zCDP lifting at `(ξ, ρ)` is a filled-KL lifting at
`ξ + ρ`: take the order to `1`. -/
theorem codensity_fill_kl_rel_of_zcdp_of_isProbabilityMeasure {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {ξ ρ : ℝ≥0∞} {S : X → Y → Prop}
    (h : zcdpLifting.Rel (ξ, ρ) S μ ν) : (codensity (fill klDivergence)).Rel (ξ + ρ) S μ ν := by
  refine GradedLifting.IsBudgetClosed.of_forall_gt (L := codensity (fill klDivergence))
    fun r hr ↦ ?_
  have hξρ : ξ + ρ ≠ ⊤ := (hr.trans_le le_top).ne
  obtain ⟨n, hn, hnr⟩ := ENNReal.exists_nnreal_pos_mul_lt (ENNReal.add_ne_top.1 hξρ).2
    (tsub_pos_of_lt hr).ne'
  have h1n : (1 : ℝ) < 1 + n := lt_add_of_pos_right _ (by exact_mod_cast hn)
  have : Fact (1 < (1 + n : ℝ)) := ⟨h1n⟩
  have hα := concentratedLifting_rel_iff.1 h ⟨1 + n, h1n⟩ h1n
  refine (codensity_fill_kl_rel_of_renyi_of_isProbabilityMeasure hα).mono ?_ fun _ _ h ↦ h
  show ξ + ENNReal.ofReal (1 + n) * ρ ≤ r
  rw [ENNReal.ofReal_add zero_le_one n.coe_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal,
    add_mul, one_mul, ← add_assoc]
  calc ξ + ρ + n * ρ ≤ ξ + ρ + (r - (ξ + ρ)) := by gcongr
    _ = r := add_tsub_cancel_of_le hr.le

end GradedDivergence

/-! ## Homomorphisms into filled KL -/

open GradedDivergence

namespace LiftingRelHom

variable {α : ℝ}

/-- Rényi liftings of relations are filled-KL liftings, at the extra budget
`α / (α - 1) · log 2` for lost left mass. -/
noncomputable def renyiToFillKl (α : ℝ) [Fact (1 < α)] :
    LiftingRelHom (codensity (renyiDivergence.{u} α)) (codensity (fill klDivergence.{u})) where
  map ρ := ρ + renyiKlGap α 0
  mono _ _ h := by simp only; gcongr
  map_rel := codensity_fill_kl_rel_of_renyi_le

@[simp]
theorem renyiToFillKl_map [Fact (1 < α)] (ρ : ℝ≥0∞) :
    (renyiToFillKl.{u} α).map ρ = ρ + renyiKlGap α 0 :=
  rfl

/-- zCDP liftings of relations are filled-KL liftings, at the best order. -/
noncomputable def zcdpToFillKl :
    LiftingRelHom zcdpLifting.{u} (codensity (fill klDivergence.{u})) where
  map b := ⨅ α ∈ Ioi (1 : ℝ), b.1 + ENNReal.ofReal α * b.2 + renyiKlGap α 0
  mono _ _ h := iInf₂_mono fun _ _ ↦ by grw [h.1, h.2]
  map_rel {_ _} _ _ b _ _ _ _ _ h := GradedLifting.IsBudgetClosed.of_forall_gt fun r hr ↦ by
    obtain ⟨α, hr⟩ := iInf_lt_iff.1 hr
    obtain ⟨hα, hr⟩ := iInf_lt_iff.1 hr
    have : Fact (1 < α) := ⟨hα⟩
    exact (codensity_fill_kl_rel_of_renyi_le
      (concentratedLifting_rel_iff.1 h ⟨α, hα⟩ hα)).mono hr.le fun _ _ h ↦ h

@[simp]
theorem zcdpToFillKl_map (b : ℝ≥0∞ × ℝ≥0∞) :
    zcdpToFillKl.{u}.map b = ⨅ α ∈ Ioi (1 : ℝ), b.1 + ENNReal.ofReal α * b.2 + renyiKlGap α 0 :=
  rfl

/-- Power liftings of relations (χ² at `α = 2`) are filled-KL liftings, through Rényi. -/
noncomputable def powerToFillKl (α : ℝ) [Fact (1 < α)] :
    LiftingRelHom (powerLifting.{u} α) (codensity (fill klDivergence.{u})) :=
  (renyiToFillKl α).comp ((LiftingHom.powerToRenyi α).toLiftingRelHom PowerBudget.toRenyi_top)

/-- Rényi-curve liftings of relations are filled-KL liftings, at each order. -/
noncomputable def renyiCurveToFillKl (α : Ioi (1 : ℝ)) :
    LiftingRelHom (codensity renyiCurve.{u}) (codensity (fill klDivergence.{u})) :=
  (renyiToFillKl α).comp ((LiftingHom.renyiCurveToRenyi α).toLiftingRelHom rfl)

end LiftingRelHom
