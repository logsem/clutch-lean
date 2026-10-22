module

public import Metrology.Couplings.Divergences.FillKl

/-!
# Filled Hellinger

`fill (hellingerDivergence α)` for `α ∈ (0, 1)` is equivalent to the Hölder test bound
`HellDualBound` on the `α`-affinity (`fill_hellinger_iff`), from which its divergence laws follow.
-/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory Set Filter Topology ENNReal

namespace ProbabilityTheory

variable {α : ℝ} {a b : ℝ≥0∞}

/-! ## Facts about powers in `ℝ≥0∞` -/

/-- The map `y ↦ y ^ (α - 1)` is antitone for `α < 1`. -/
theorem rpow_sub_one_le_rpow_sub_one (hα1 : α < 1) {x y : ℝ≥0∞} (h : x ≤ y) :
    y ^ (α - 1) ≤ x ^ (α - 1) := by
  rw [show α - 1 = -(1 - α) by ring, rpow_neg, rpow_neg]
  exact ENNReal.inv_le_inv.2 (rpow_le_rpow h (by linarith))

/-- The product `(x + ε) ^ α * x ^ (1 - α)` is at most `x + ε`. -/
theorem add_rpow_mul_rpow_le (hα0 : 0 < α) (hα1 : α < 1) (x ε : ℝ≥0∞) :
    (x + ε) ^ α * x ^ (1 - α) ≤ x + ε :=
  calc (x + ε) ^ α * x ^ (1 - α) ≤ (x + ε) ^ α * (x + ε) ^ (1 - α) := by
        gcongr
        exact le_self_add
    _ = x + ε := by
        rw [← rpow_add_of_nonneg _ _ hα0.le (by linarith), add_sub_cancel,
          rpow_one]

/-- The optimal filling's test integrates to the affinity. -/
theorem ofReal_mul_rpow_add_tsub_mul_rpow {p t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal p * ENNReal.ofReal (max p t) ^ (α - 1) +
      (ENNReal.ofReal (max p t) - ENNReal.ofReal p) * ENNReal.ofReal t ^ (α - 1) =
      ENNReal.ofReal (max p t) ^ α := by
  have key {x : ℝ≥0∞} (hx0 : x ≠ 0) (hxt : x ≠ ⊤) : x * x ^ (α - 1) = x ^ α :=
    calc x * x ^ (α - 1) = x ^ (1 : ℝ) * x ^ (α - 1) := by rw [rpow_one]
      _ = x ^ (1 + (α - 1)) := (rpow_add _ _ hx0 hxt).symm
      _ = x ^ α := by congr 1; ring
  rcases le_total t p with h | h
  · rw [max_eq_left h, tsub_self, zero_mul, add_zero]
    exact key (ofReal_pos.2 (ht.trans_le h)).ne' ofReal_ne_top
  · rw [max_eq_right h, ← add_mul, add_tsub_cancel_of_le (ofReal_le_ofReal h)]
    exact key (ofReal_pos.2 ht).ne' ofReal_ne_top

/-- A bound by `(X + ε) ^ α * Y` at every `ε > 0` is a bound by `X ^ α * Y`. -/
theorem le_rpow_mul_of_forall_add {X Y : ℝ≥0∞} (hX0 : X ≠ 0)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → a ≤ (X + ε) ^ α * Y) : a ≤ X ^ α * Y := by
  rcases eq_or_ne X ⊤ with rfl | hXt
  · simpa using h 1 one_pos
  have ht : Tendsto (fun ε : ℝ≥0∞ ↦ (X + ε) ^ α * Y) (𝓝[>] 0) (𝓝 (X ^ α * Y)) := by
    refine ENNReal.Tendsto.mul_const ?_ (.inl (rpow_pos (pos_iff_ne_zero.2 hX0) hXt).ne')
    have : Tendsto (fun ε : ℝ≥0∞ ↦ X + ε) (𝓝[>] 0) (𝓝 X) := by
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds
        ((continuous_const.add continuous_id).tendsto (0 : ℝ≥0∞)) :
        Tendsto (fun ε : ℝ≥0∞ ↦ X + ε) (𝓝[>] 0) (𝓝 (X + 0)))
    exact (continuous_rpow_const.tendsto X).comp this
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε ↦ h ε hε)

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-! ## The test bound -/

/-- The Hölder test bound `a` on the `α`-affinity of some probability measure above `m` against
`Q`. -/
def HellDualBound (α : ℝ) (a : ℝ≥0∞) (m Q : Measure Ω) : Prop :=
  ∀ ⦃g : Ω → ℝ≥0∞⦄ ⦃C : ℝ≥0∞⦄, Measurable g → (∀ ω, 0 < g ω) → (∀ ω, g ω ≤ C) → C ≠ 0 →
    C ≠ ⊤ → a ≤ (∫⁻ ω, g ω ∂m + (1 - m univ) * C) ^ α * (∫⁻ ω, g ω ^ (-(α / (1 - α))) ∂Q) ^ (1 - α)

/-- Test bounds weaken with the budget. -/
theorem HellDualBound.mono {m Q : Measure Ω} (h : HellDualBound α a m Q) (hb : b ≤ a) :
    HellDualBound α b m Q :=
  fun _ _ hg h0 hC hC0 hCt ↦ hb.trans (h hg h0 hC hC0 hCt)

/-- A probability measure `P` above `m` gives the Hölder test bound on its `α`-affinity. -/
theorem hellDualBound_of_le (hα0 : 0 < α) (hα1 : α < 1) {m P Q : Measure Ω}
    [IsProbabilityMeasure P] (hmP : m ≤ P) :
    HellDualBound α (∫⁻ ω, P.rnDeriv Q ω ^ α ∂Q) m Q := by
  intro g C hg hg0 hgC _ hC
  have : IsFiniteMeasure m := isFiniteMeasure_of_le P hmP
  have hs : 1 - α ≠ 0 := (sub_pos.2 hα1).ne'
  have hgt (ω : Ω) : g ω ≠ ⊤ := ne_top_of_le_ne_top hC (hgC ω)
  -- `(dP/dQ)^α = (g dP/dQ)^α (g^{-α/(1-α)})^{1-α}`
  have hpt (ω : Ω) : P.rnDeriv Q ω ^ α =
      (g ω * P.rnDeriv Q ω) ^ α * (g ω ^ (-(α / (1 - α)))) ^ (1 - α) := by
    rw [mul_rpow_of_nonneg _ _ hα0.le, ← rpow_mul,
      show -(α / (1 - α)) * (1 - α) = -α by field_simp, mul_right_comm,
      ← rpow_add _ _ (hg0 ω).ne' (hgt ω), add_neg_cancel, rpow_zero, one_mul]
  have hP : ∫⁻ ω, g ω * P.rnDeriv Q ω ∂Q ≤ ∫⁻ ω, g ω ∂m + (1 - m univ) * C := by
    calc ∫⁻ ω, g ω * P.rnDeriv Q ω ∂Q = ∫⁻ ω, g ω ∂(Q.withDensity (P.rnDeriv Q)) := by
          rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_rnDeriv _ _) hg]
          simp only [Pi.mul_apply, mul_comm]
      _ ≤ ∫⁻ ω, g ω ∂P := lintegral_mono' (withDensity_rnDeriv_le P Q) le_rfl
      _ = ∫⁻ ω, g ω ∂m + ∫⁻ ω, g ω ∂(P - m) := by
          rw [← lintegral_add_measure, add_comm, Measure.sub_add_cancel_of_le hmP]
      _ ≤ ∫⁻ ω, g ω ∂m + (1 - m univ) * C := by
          gcongr
          calc ∫⁻ ω, g ω ∂(P - m) ≤ ∫⁻ _, C ∂(P - m) := lintegral_mono hgC
            _ = (1 - m univ) * C := by
              rw [lintegral_const, Measure.sub_apply .univ hmP, measure_univ, mul_comm]
  calc ∫⁻ ω, P.rnDeriv Q ω ^ α ∂Q
      = ∫⁻ ω, (g ω * P.rnDeriv Q ω) ^ α * (g ω ^ (-(α / (1 - α)))) ^ (1 - α) ∂Q :=
        lintegral_congr hpt
    _ ≤ (∫⁻ ω, g ω * P.rnDeriv Q ω ∂Q) ^ α * (∫⁻ ω, g ω ^ (-(α / (1 - α))) ∂Q) ^ (1 - α) :=
        lintegral_mul_norm_pow_le (by fun_prop) (by fun_prop) hα0.le (by linarith) (by ring)
    _ ≤ _ := by gcongr

/-- The zero measure meets every bound up to `1` against a probability measure. -/
theorem hellDualBound_zero_left (hα0 : 0 < α) (hα1 : α < 1) (ha : a ≤ 1) (Q : Measure Ω)
    [IsProbabilityMeasure Q] : HellDualBound α a 0 Q := by
  refine (hellDualBound_of_le hα0 hα1 (P := Q) (Q := Q) (Measure.zero_le _)).mono (ha.trans_eq ?_)
  rw [lintegral_congr_ae ((rnDeriv_self Q).mono fun ω hω ↦ by rw [hω])]
  simp

/-- The first factor of a test is positive. -/
theorem lintegral_add_tsub_mul_ne_zero {m : Measure Ω} {g : Ω → ℝ≥0∞} {C : ℝ≥0∞}
    (hg : Measurable g) (hg0 : ∀ ω, 0 < g ω) (hC0 : C ≠ 0) :
    ∫⁻ ω, g ω ∂m + (1 - m univ) * C ≠ 0 := by
  intro hv
  obtain ⟨hgm, hmC⟩ := add_eq_zero.1 hv
  have hm1 : 1 ≤ m univ := tsub_eq_zero_iff_le.1 ((mul_eq_zero.1 hmC).resolve_right hC0)
  -- `g > 0` integrates to zero only against the zero measure
  have hm0 : m = 0 := by
    rw [lintegral_eq_zero_iff hg] at hgm
    exact ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 (hgm.mono fun x hx ↦ (hg0 x).ne' hx))
  simp [hm0] at hm1

/-! ## Test bounds compose -/

/-- Test bounds compose along kernels, multiplying the bounds. -/
theorem HellDualBound.comp (hα1 : α < 1) {m₁ Q₁ : Measure Ω}
    [IsSubProbabilityMeasure m₁] {K L : Kernel Ω Ω'} [IsSubMarkovKernel K]
    (h₁ : HellDualBound α a m₁ Q₁) (h₂ : ∀ ω, HellDualBound α b (K ω) (L ω)) :
    HellDualBound α (a * b) (K ∘ₘ m₁) (L ∘ₘ Q₁) := by
  intro g C hg hg0 hgC hC0 hC
  set β := α / (1 - α) with hβ
  have hs : 0 < 1 - α := sub_pos.2 hα1
  set v : Ω → ℝ≥0∞ := fun ω ↦ ∫⁻ x, g x ∂(K ω) + (1 - K ω univ) * C
  set u : Ω → ℝ≥0∞ := fun ω ↦ ∫⁻ x, g x ^ (-β) ∂(L ω)
  have hvm : Measurable v :=
    hg.lintegral_kernel.add (((K.measurable_coe .univ).const_sub 1).mul_const _)
  have hvC (ω : Ω) : v ω ≤ C := by
    have hk : K ω univ ≤ 1 := IsSubProbabilityMeasure.measure_le_one _
    calc v ω = ∫⁻ x, g x ∂(K ω) + (1 - K ω univ) * C := rfl
      _ ≤ ∫⁻ _, C ∂(K ω) + (1 - K ω univ) * C := by gcongr; exact hgC _
      _ = C := by rw [lintegral_const, mul_comm, ← add_mul, add_tsub_cancel_of_le hk, one_mul]
  have hvt (ω : Ω) : v ω ≠ ⊤ := ne_top_of_le_ne_top hC (hvC ω)
  have hv0 (ω : Ω) : 0 < v ω := pos_iff_ne_zero.2 (lintegral_add_tsub_mul_ne_zero hg hg0 hC0)
  -- the inner bounds, solved for `u`
  have hu (ω : Ω) : b ^ (1 - α)⁻¹ * v ω ^ (-β) ≤ u ω := by
    have hin : b ≤ v ω ^ α * u ω ^ (1 - α) := h₂ ω hg hg0 hgC hC0 hC
    have h1 : b * v ω ^ (-α) ≤ u ω ^ (1 - α) := by
      calc b * v ω ^ (-α) ≤ v ω ^ α * u ω ^ (1 - α) * v ω ^ (-α) := by gcongr
        _ = u ω ^ (1 - α) := by
          rw [mul_right_comm, ← rpow_add _ _ (hv0 ω).ne' (hvt ω), add_neg_cancel,
            rpow_zero, one_mul]
    calc b ^ (1 - α)⁻¹ * v ω ^ (-β) = (b * v ω ^ (-α)) ^ (1 - α)⁻¹ := by
          rw [mul_rpow_of_nonneg _ _ (inv_nonneg.2 hs.le), ← rpow_mul, hβ,
            neg_mul, div_eq_mul_inv]
      _ ≤ (u ω ^ (1 - α)) ^ (1 - α)⁻¹ := by gcongr
      _ = u ω := by rw [← rpow_mul, mul_inv_cancel₀ hs.ne', rpow_one]
  have hout := h₁ hvm hv0 hvC hC0 hC
  -- the first factors agree: the left kernel's lost mass is charged at `C`
  have hfirst : ∫⁻ ω, v ω ∂m₁ + (1 - m₁ univ) * C =
      ∫⁻ x, g x ∂(K ∘ₘ m₁) + (1 - (K ∘ₘ m₁) univ) * C := by
    have hKm : (K ∘ₘ m₁) univ = ∫⁻ ω, K ω univ ∂m₁ := Measure.bind_apply .univ K.aemeasurable
    have hKm1 : (K ∘ₘ m₁) univ ≤ m₁ univ := by
      rw [hKm]
      calc ∫⁻ ω, K ω univ ∂m₁ ≤ ∫⁻ _, 1 ∂m₁ :=
            lintegral_mono fun ω ↦ IsSubProbabilityMeasure.measure_le_one _
        _ = m₁ univ := by simp
    have hsub : ∫⁻ ω, (1 - K ω univ) ∂m₁ = m₁ univ - (K ∘ₘ m₁) univ := by
      rw [lintegral_sub (K.measurable_coe .univ) (hKm ▸ measure_ne_top _ _)
        (ae_of_all _ fun ω ↦ IsSubProbabilityMeasure.measure_le_one _), lintegral_one, hKm]
    simp only [v]
    rw [lintegral_add_left hg.lintegral_kernel, ← Measure.lintegral_bind K.aemeasurable
      hg.aemeasurable, lintegral_mul_const _ ((K.measurable_coe .univ).const_sub 1),
      hsub, add_assoc, ← add_mul, add_comm (m₁ univ - _),
      tsub_add_tsub_cancel (IsSubProbabilityMeasure.measure_le_one _) hKm1]
  -- the second factors: `∫ g^{-β} d(L ∘ Q₁) = ∫ u dQ₁ ≥ b^{1/(1-α)} ∫ v^{-β} dQ₁`
  have hsecond : b * (∫⁻ ω, v ω ^ (-β) ∂Q₁) ^ (1 - α) ≤
      (∫⁻ x, g x ^ (-β) ∂(L ∘ₘ Q₁)) ^ (1 - α) := by
    rw [Measure.lintegral_bind L.aemeasurable (hg.pow_const _).aemeasurable]
    calc b * (∫⁻ ω, v ω ^ (-β) ∂Q₁) ^ (1 - α)
        = (b ^ (1 - α)⁻¹ * ∫⁻ ω, v ω ^ (-β) ∂Q₁) ^ (1 - α) := by
          rw [mul_rpow_of_nonneg _ _ hs.le, ← rpow_mul, inv_mul_cancel₀ hs.ne',
            rpow_one]
      _ = (∫⁻ ω, b ^ (1 - α)⁻¹ * v ω ^ (-β) ∂Q₁) ^ (1 - α) := by
          rw [lintegral_const_mul _ (hvm.pow_const _)]
      _ ≤ (∫⁻ ω, u ω ∂Q₁) ^ (1 - α) := by gcongr with ω; exact hu ω
  calc a * b ≤ (∫⁻ ω, v ω ∂m₁ + (1 - m₁ univ) * C) ^ α *
        (∫⁻ ω, v ω ^ (-β) ∂Q₁) ^ (1 - α) * b := by gcongr
    _ = (∫⁻ ω, v ω ∂m₁ + (1 - m₁ univ) * C) ^ α * (b * (∫⁻ ω, v ω ^ (-β) ∂Q₁) ^ (1 - α)) := by ring
    _ ≤ _ := by rw [hfirst]; gcongr

/-! ## Test bounds give affinity bounds: the optimal filling -/

section Optimal

variable {m Q : Measure Ω}

/-- The test `max (dm/dQ) t ^ (α - 1)` on a set carrying `Q`, and `ε` on the rest, which carries
the singular part of `m`. -/
theorem le_of_hellDualBound_max (hα0 : 0 < α) (hα1 : α < 1) [IsProbabilityMeasure Q]
    [IsFiniteMeasure m] (h : HellDualBound α a m Q) {t : ℝ} (ht : 0 < t) {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hεt : ε ≤ ENNReal.ofReal t ^ (α - 1)) :
    a ≤ (ε * m.singularPart Q univ +
        ∫⁻ ω, m.rnDeriv Q ω * ENNReal.ofReal (max (m.rnDeriv Q ω).toReal t) ^ (α - 1) ∂Q +
        (1 - m univ) * ENNReal.ofReal t ^ (α - 1)) ^ α *
      (∫⁻ ω, ENNReal.ofReal (max (m.rnDeriv Q ω).toReal t) ^ α ∂Q) ^ (1 - α) := by
  classical
  set c : Ω → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal (max (m.rnDeriv Q ω).toReal t)
  have hcm : Measurable c :=
    ((measurable_rnDeriv m Q).ennreal_toReal.max measurable_const).ennreal_ofReal
  have hc0 (ω : Ω) : 0 < c ω := ofReal_pos.2 (ht.trans_le (le_max_right _ _))
  have hT (ω : Ω) : ENNReal.ofReal t ≤ c ω := ofReal_le_ofReal (le_max_right _ _)
  have hms := mutuallySingular_singularPart m Q
  set N := hms.nullSet
  have hN : MeasurableSet N := hms.measurableSet_nullSet
  set g : Ω → ℝ≥0∞ := N.piecewise (fun ω ↦ c ω ^ (α - 1)) fun _ ↦ ε
  have hgm : Measurable g := (hcm.pow_const _).piecewise hN measurable_const
  have hg0 (ω : Ω) : 0 < g ω := by
    by_cases hω : ω ∈ N
    · simpa [g, hω] using rpow_pos (hc0 ω) ofReal_ne_top
    · simpa [g, hω] using pos_iff_ne_zero.2 hε0
  have hgC (ω : Ω) : g ω ≤ ENNReal.ofReal t ^ (α - 1) := by
    by_cases hω : ω ∈ N
    · simpa [g, hω] using rpow_sub_one_le_rpow_sub_one hα1 (hT ω)
    · simpa [g, hω] using hεt
  have hC0 : ENNReal.ofReal t ^ (α - 1) ≠ 0 := (rpow_pos (ofReal_pos.2 ht) ofReal_ne_top).ne'
  have hCt : ENNReal.ofReal t ^ (α - 1) ≠ ⊤ :=
    rpow_ne_top_of_ne_zero (ofReal_pos.2 ht).ne' ofReal_ne_top
  have hQN : ∀ᵐ ω ∂Q, ω ∈ N := mem_ae_iff.2 hms.measure_compl_nullSet
  have hmsN : ∀ᵐ ω ∂m.singularPart Q, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hms.measure_nullSet
  have hgm' : ∫⁻ ω, g ω ∂m = ε * m.singularPart Q univ +
      ∫⁻ ω, m.rnDeriv Q ω * c ω ^ (α - 1) ∂Q := by
    conv_lhs => rw [haveLebesgueDecomposition_add m Q]
    rw [lintegral_add_measure,
      lintegral_congr_ae (g := fun _ ↦ ε) (hmsN.mono fun ω hω ↦ by simp [g, hω]),
      lintegral_const, mul_comm,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_rnDeriv _ _) hgm]
    congr 1
    exact lintegral_congr_ae (hQN.mono fun ω hω ↦ by simp [g, hω])
  have hgQ : ∫⁻ ω, g ω ^ (-(α / (1 - α))) ∂Q = ∫⁻ ω, c ω ^ α ∂Q := by
    refine lintegral_congr_ae (hQN.mono fun ω hω ↦ ?_)
    have hs : 1 - α ≠ 0 := (sub_pos.2 hα1).ne'
    simp only [g, Set.piecewise_eq_of_mem _ _ _ hω, ← rpow_mul]
    congr 1
    field_simp
    ring
  have := h hgm hg0 hgC hC0 hCt
  rwa [hgm', hgQ] at this

/-- A test bound for `m` is met by a probability measure above `m` of at least that affinity. -/
theorem exists_le_lintegral_rnDeriv_rpow_of_hellDualBound (hα0 : 0 < α) (hα1 : α < 1)
    [IsProbabilityMeasure Q] [IsFiniteMeasure m] (hm1 : m univ ≤ 1) (h : HellDualBound α a m Q) :
    ∃ P, IsProbabilityMeasure P ∧ m ≤ P ∧ a ≤ ∫⁻ ω, P.rnDeriv Q ω ^ α ∂Q := by
  set p : Ω → ℝ := fun ω ↦ (m.rnDeriv Q ω).toReal with hp
  have hpm : Measurable p := (measurable_rnDeriv m Q).ennreal_toReal
  have hp0 (ω : Ω) : 0 ≤ p ω := toReal_nonneg
  have hpint : Integrable p Q := integrable_toReal_rnDeriv
  set ms := m.singularPart Q
  have : IsFiniteMeasure ms := isFiniteMeasure_of_le m (singularPart_le m Q)
  have hms1 : ms univ ≤ 1 := (singularPart_le m Q univ).trans hm1
  have hrn : ∀ᵐ ω ∂Q, m.rnDeriv Q ω = ENNReal.ofReal (p ω) :=
    (rnDeriv_lt_top m Q).mono fun ω hω ↦ (ofReal_toReal hω.ne).symm
  have hdec : m univ = ms univ + ∫⁻ ω, m.rnDeriv Q ω ∂Q := by
    conv_lhs => rw [haveLebesgueDecomposition_add m Q]
    rw [Measure.add_apply, withDensity_apply _ .univ, Measure.restrict_univ]
  set F : ℝ → ℝ := fun t ↦ ∫ ω, max (p ω) t ∂Q + ms.real univ
  have hF0 : F 0 = m.real univ := by
    have : (fun ω ↦ max (p ω) 0) = p := funext fun ω ↦ max_eq_left (hp0 ω)
    simp only [F, this]
    rw [integral_toReal_rnDeriv']
    ring
  have hF1 : 1 ≤ F 1 := by
    have : (1 : ℝ) ≤ ∫ ω, max (p ω) 1 ∂Q := calc (1 : ℝ) = ∫ _, (1 : ℝ) ∂Q := by simp
        _ ≤ _ := integral_mono (integrable_const _) (hpint.sup (integrable_const 1))
            fun ω ↦ le_max_right _ _
    exact this.trans (le_add_of_nonneg_right measureReal_nonneg)
  have hreal1 : m.real univ ≤ 1 := by
    rw [measureReal_def]
    exact toReal_le_of_le_ofReal zero_le_one (by simpa using hm1)
  obtain ⟨t, ⟨ht0, -⟩, hFt⟩ : ∃ t ∈ Icc (0 : ℝ) 1, F t = 1 := intermediate_value_Icc zero_le_one
      ((lipschitzWith_integral_max hpint).continuous.add continuous_const).continuousOn
      ⟨hF0.trans_le hreal1, hF1⟩
  have hcint (s : ℝ) : Integrable (fun ω ↦ max (p ω) s) Q := hpint.sup (integrable_const s)
  rcases ht0.eq_or_lt with rfl | htpos
  · -- no lost mass: `m` itself, testing at every `s > 0` with `max (dm/dQ) s`
    have hmu : m univ = 1 := by
      rw [← ofReal_toReal (measure_ne_top m univ), ← measureReal_def, ← hF0, hFt,
        ofReal_one]
    refine ⟨m, ⟨hmu⟩, le_rfl, le_of_forall_pos_le_add fun δ hδ _ ↦ ?_⟩
    have hδ2 : (0 : ℝ) < δ / 2 := by positivity
    set s : ℝ := ((δ : ℝ) / 2) ^ α⁻¹
    have hs : 0 < s := Real.rpow_pos_of_pos hδ2 _
    have hsα : ENNReal.ofReal s ^ α = (δ : ℝ≥0∞) / 2 := by
      rw [ofReal_rpow_of_nonneg hs.le hα0.le, ← Real.rpow_mul hδ2.le,
        inv_mul_cancel₀ hα0.ne', Real.rpow_one, ofReal_div_of_pos two_pos]
      simp
    set ε : ℝ≥0∞ := min ((δ : ℝ≥0∞) / 2) (ENNReal.ofReal s ^ (α - 1))
    have hε0 : ε ≠ 0 := (lt_min (by simpa using hδ.ne')
      (rpow_pos (ofReal_pos.2 hs) ofReal_ne_top)).ne'
    have key := le_of_hellDualBound_max hα0 hα1 h hs hε0 (min_le_right _ _)
    rw [hmu, tsub_self, zero_mul, add_zero] at key
    set c : Ω → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal (max (p ω) s)
    set B := ∫⁻ ω, c ω ^ α ∂Q
    have h1 : ε * ms univ + ∫⁻ ω, m.rnDeriv Q ω * c ω ^ (α - 1) ∂Q ≤ B + ε := by
      rw [add_comm]
      gcongr
      · refine lintegral_mono_ae (hrn.mono fun ω hω ↦ ?_)
        rw [hω]
        calc ENNReal.ofReal (p ω) * c ω ^ (α - 1) ≤ ENNReal.ofReal (p ω) * c ω ^ (α - 1) +
              (c ω - ENNReal.ofReal (p ω)) * ENNReal.ofReal s ^ (α - 1) := le_self_add
          _ = c ω ^ α := ofReal_mul_rpow_add_tsub_mul_rpow hs
      · exact mul_le_of_le_one_right' hms1
    have h2 : a ≤ B + ε :=
      key.trans ((by gcongr : (ε * ms univ + ∫⁻ ω, m.rnDeriv Q ω * c ω ^ (α - 1) ∂Q) ^ α *
        B ^ (1 - α) ≤ (B + ε) ^ α * B ^ (1 - α)).trans (add_rpow_mul_rpow_le hα0 hα1 B ε))
    have h3 : B ≤ ∫⁻ ω, m.rnDeriv Q ω ^ α ∂Q + (δ : ℝ≥0∞) / 2 := by
      calc B ≤ ∫⁻ ω, (ENNReal.ofReal (p ω) ^ α + ENNReal.ofReal s ^ α) ∂Q := by
            refine lintegral_mono fun ω ↦ ?_
            calc c ω ^ α ≤ (ENNReal.ofReal (p ω) + ENNReal.ofReal s) ^ α := by
                  gcongr
                  rw [← ofReal_add (hp0 ω) hs.le]
                  exact ofReal_le_ofReal (max_le (le_add_of_nonneg_right hs.le)
                    (le_add_of_nonneg_left (hp0 ω)))
              _ ≤ _ := rpow_add_le_add_rpow _ _ hα0.le hα1.le
        _ = ∫⁻ ω, m.rnDeriv Q ω ^ α ∂Q + (δ : ℝ≥0∞) / 2 := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
              hsα]
            congr 1
            exact lintegral_congr_ae (hrn.mono fun ω hω ↦ by simp only [hω])
    calc a ≤ B + ε := h2
      _ ≤ ∫⁻ ω, m.rnDeriv Q ω ^ α ∂Q + (δ : ℝ≥0∞) / 2 + (δ : ℝ≥0∞) / 2 :=
          add_le_add h3 (min_le_left _ _)
      _ = _ := by rw [add_assoc, ENNReal.add_halves]
  · -- lost mass: fill with `m_s + max (dm/dQ) t • Q`, which has mass `1`
    set c : Ω → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal (max (p ω) t)
    have hcm : Measurable c := (hpm.max measurable_const).ennreal_ofReal
    have hcl : ∫⁻ ω, c ω ∂Q = ENNReal.ofReal (∫ ω, max (p ω) t ∂Q) :=
      (ofReal_integral_eq_lintegral_ofReal (hcint t)
        (ae_of_all _ fun ω ↦ (hp0 ω).trans (le_max_left _ _))).symm
    have : IsFiniteMeasure (Q.withDensity c) :=
      isFiniteMeasure_withDensity (by rw [hcl]; exact ofReal_ne_top)
    set P := ms + Q.withDensity c
    have hPu : P univ = 1 := by
      rw [Measure.add_apply, withDensity_apply _ .univ, Measure.restrict_univ, hcl,
        ← ofReal_toReal (measure_ne_top ms univ), ← measureReal_def,
        ← ofReal_add measureReal_nonneg
          (integral_nonneg fun ω ↦ (hp0 ω).trans (le_max_left _ _)), add_comm]
      exact (congrArg ENNReal.ofReal hFt).trans ofReal_one
    have hPrn : ∀ᵐ ω ∂Q, P.rnDeriv Q ω = c ω := by
      filter_upwards [rnDeriv_add ms (Q.withDensity c) Q,
        rnDeriv_singularPart m Q, rnDeriv_withDensity Q hcm] with ω h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3, Pi.zero_apply, zero_add]
    have hrnc : ∀ᵐ ω ∂Q, m.rnDeriv Q ω ≤ c ω :=
      hrn.mono fun ω hω ↦ hω ▸ ofReal_le_ofReal (le_max_left _ _)
    refine ⟨P, ⟨hPu⟩, ?_, ?_⟩
    · conv_lhs => rw [haveLebesgueDecomposition_add m Q]
      exact add_le_add le_rfl (withDensity_mono hrnc)
    rw [lintegral_congr_ae (hPrn.mono fun ω hω ↦ by rw [hω])]
    set B := ∫⁻ ω, c ω ^ α ∂Q
    -- the lost mass is `∫ (c - dm/dQ) dQ`, charged at `t^{α - 1}`, which completes the affinity
    have hrnfin : ∫⁻ ω, m.rnDeriv Q ω ∂Q ≠ ⊤ :=
      ne_top_of_le_ne_top (hcl ▸ ofReal_ne_top) (lintegral_mono_ae hrnc)
    have hlost : 1 - m univ = ∫⁻ ω, (c ω - m.rnDeriv Q ω) ∂Q := by
      rw [lintegral_sub' (measurable_rnDeriv m Q).aemeasurable hrnfin hrnc, ← hPu, hdec,
        Measure.add_apply, withDensity_apply _ .univ, Measure.restrict_univ, tsub_add_eq_tsub_tsub,
        ENNReal.add_sub_cancel_left (measure_ne_top _ _)]
    have hB : ∫⁻ ω, m.rnDeriv Q ω * c ω ^ (α - 1) ∂Q + (1 - m univ) * ENNReal.ofReal t ^ (α - 1) =
        B := by
      rw [hlost, ← lintegral_mul_const (f := fun ω ↦ c ω - m.rnDeriv Q ω) _
          (hcm.sub (measurable_rnDeriv m Q)),
        ← lintegral_add_left (f := fun ω ↦ m.rnDeriv Q ω * c ω ^ (α - 1))
          ((measurable_rnDeriv m Q).mul (hcm.pow_const _))]
      refine lintegral_congr_ae (hrn.mono fun ω hω ↦ ?_)
      simp only [hω]
      exact ofReal_mul_rpow_add_tsub_mul_rpow htpos
    refine le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    set ε : ℝ≥0∞ := min (δ : ℝ≥0∞) (ENNReal.ofReal t ^ (α - 1))
    have hε0 : ε ≠ 0 := (lt_min (by simpa using hδ)
      (rpow_pos (ofReal_pos.2 htpos) ofReal_ne_top)).ne'
    have key := le_of_hellDualBound_max hα0 hα1 h htpos hε0 (min_le_right _ _)
    rw [add_assoc, hB] at key
    have hfirst : ε * ms univ + B ≤ B + ε := by
      rw [add_comm]
      exact add_le_add le_rfl (mul_le_of_le_one_right' hms1)
    calc a ≤ (B + ε) ^ α * B ^ (1 - α) := key.trans (by gcongr)
      _ ≤ B + ε := add_rpow_mul_rpow_le hα0 hα1 B ε
      _ ≤ B + δ := add_le_add le_rfl (min_le_left _ _)

end Optimal

/-! ## Test bounds pass to suprema and close -/

/-- Test bounds pass to the supremum of an increasing sequence. -/
theorem HellDualBound.iSup (hα0 : 0 < α) {m : ℕ → Measure Ω} (hm : Monotone m) {Q : Measure Ω}
    [IsFiniteMeasure (⨆ n, m n)] (h : ∀ n, HellDualBound α a (m n) Q) :
    HellDualBound α a (⨆ n, m n) Q := by
  intro g C hg hg0 hgC hC0 hC
  refine le_rpow_mul_of_forall_add (lintegral_add_tsub_mul_ne_zero hg hg0 hC0) fun ε hε ↦ ?_
  have hsup : (⨆ n, m n) univ = ⨆ n, m n univ := iSup_apply_of_monotone hm .univ
  have hεC : 0 < ε / C := ENNReal.div_pos hε.ne' hC
  obtain ⟨n, hn⟩ : ∃ n, (⨆ n, m n) univ < m n univ + ε / C := by
    have hlt : (⨆ n, m n) univ < (⨆ n, m n) univ + ε / C :=
      lt_add_right (measure_ne_top _ _) hεC.ne'
    rw [hsup, iSup_add] at hlt
    rw [hsup]
    exact lt_iSup_iff.1 hlt
  refine (h n hg hg0 hgC hC0 hC).trans ?_
  have := hα0.le
  gcongr ?_ ^ α * _
  calc ∫⁻ ω, g ω ∂m n + (1 - m n univ) * C
      ≤ ∫⁻ ω, g ω ∂(⨆ n, m n) + ((1 - (⨆ n, m n) univ) + ε / C) * C := by
        gcongr
        · exact le_iSup m n
        · calc 1 - m n univ ≤ (1 - (⨆ n, m n) univ) + ((⨆ n, m n) univ - m n univ) :=
                tsub_le_tsub_add_tsub
            _ ≤ _ := by
                gcongr
                exact tsub_le_iff_left.2 hn.le
    _ ≤ ∫⁻ ω, g ω ∂(⨆ n, m n) + (1 - (⨆ n, m n) univ) * C + ε := by
        rw [add_mul, ENNReal.div_mul_cancel hC0 hC, add_assoc]

/-- Test bounds close from below. -/
theorem hellDualBound_of_forall_lt {m Q : Measure Ω} (h : ∀ b < a, HellDualBound α b m Q) :
    HellDualBound α a m Q :=
  fun _ _ hg h0 hC hC0 hCt ↦ le_of_forall_lt_imp_le_of_dense fun b hb ↦ h b hb hg h0 hC hC0 hCt

/-! ## The `α`-Hellinger divergence through the affinity -/

/-- The affinity `exp (-(1 - α) r)` of the Hellinger budget `r`, and `0` at `⊤`. -/
noncomputable def hellAff (α : ℝ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  if r = ⊤ then 0 else ENNReal.ofReal (Real.exp (-(1 - α) * r.toReal))

/-- The affinity of a finite budget is the exponential. -/
theorem hellAff_of_ne_top {r : ℝ≥0∞} (hr : r ≠ ⊤) :
    hellAff α r = ENNReal.ofReal (Real.exp (-(1 - α) * r.toReal)) := by
  simp [hellAff, hr]

/-- The affinity of a sum of budgets is the product of the affinities. -/
theorem hellAff_add (b c : ℝ≥0∞) : hellAff α (b + c) = hellAff α b * hellAff α c := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [hellAff]
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp [hellAff]
  simp only [hellAff, add_eq_top, hb, hc, or_self, ↓reduceIte,
    toReal_add hb hc, mul_add, Real.exp_add, ofReal_mul (Real.exp_pos _).le]

/-- The affinity is at most `1`. -/
theorem hellAff_le_one (hα1 : α ≤ 1) (r : ℝ≥0∞) : hellAff α r ≤ 1 := by
  unfold hellAff
  split_ifs
  · exact zero_le_one
  · exact ofReal_le_one.2 (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) toReal_nonneg))

/-- The affinity is right-continuous in the budget: `b < hellAff α r` holds at some larger
budget. -/
theorem exists_lt_hellAff {r : ℝ≥0∞} {b : ℝ≥0∞} (hb : b < hellAff α r) :
    ∃ r', r < r' ∧ b < hellAff α r' := by
  have hr : r ≠ ⊤ := fun h ↦ by simp [hellAff, h] at hb
  have hf : Tendsto (fun r' : ℝ≥0∞ ↦ ENNReal.ofReal (Real.exp (-(1 - α) * r'.toReal)))
      (𝓝 r) (𝓝 (hellAff α r)) := by
    rw [hellAff_of_ne_top hr]
    exact continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuous_exp.tendsto _).comp ((tendsto_toReal hr).const_mul (-(1 - α))))
  have hev : ∀ᶠ r' in 𝓝 r, b < hellAff α r' := by
    filter_upwards [hf.eventually (lt_mem_nhds hb), Iio_mem_nhds (lt_top_iff_ne_top.2 hr)]
      with r' h1 h2
    rwa [hellAff_of_ne_top (show r' < ⊤ from h2).ne]
  have : (𝓝[>] r).NeBot := nhdsGT_neBot_of_exists_gt ⟨⊤, lt_top_iff_ne_top.2 hr⟩
  have hev' : ∀ᶠ r' in 𝓝[>] r, b < hellAff α r' ∧ r < r' :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨r', h1, h2⟩ := hev'.exists
  exact ⟨r', h2, h1⟩

variable {X : Type*} [MeasurableSpace X]

/-- `(dP/dQ)^α` is integrable for `α ∈ (0, 1)`: it lies below `dP/dQ + 1`. -/
theorem integrable_toReal_rnDeriv_rpow (hα0 : 0 < α) (hα1 : α < 1) {P Q : Measure X}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (fun x ↦ (P.rnDeriv Q x).toReal ^ α) Q :=
  (integrable_toReal_rnDeriv.add (integrable_const 1)).mono'
    ((measurable_rnDeriv P Q).ennreal_toReal.pow_const α).aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      have hp0 : 0 ≤ (P.rnDeriv Q x).toReal := toReal_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp0 _), Pi.add_apply]
      rcases le_total (P.rnDeriv Q x).toReal 1 with h | h
      · linarith [Real.rpow_le_one hp0 h hα0.le]
      · have := Real.rpow_le_rpow_of_exponent_le h hα1.le
        rw [Real.rpow_one] at this
        linarith)

/-- Between probability measures, `α`-Hellinger is `(1 - ∫ (dP/dQ)^α dQ) / (1 - α)`. -/
theorem fDiv_hellFun_eq (hα0 : 0 < α) (hα1 : α < 1) {P Q : Measure X} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    fDiv (hellFun α) P Q = (((1 - ∫ x, (P.rnDeriv Q x).toReal ^ α ∂Q) / (1 - α) : ℝ) : EReal) := by
  set p : X → ℝ := fun x ↦ (P.rnDeriv Q x).toReal
  have hp0 (x : X) : 0 ≤ p x := toReal_nonneg
  have hpm : Measurable p := (measurable_rnDeriv P Q).ennreal_toReal
  have hpint : Integrable p Q := integrable_toReal_rnDeriv
  have hpα : Integrable (fun x ↦ p x ^ α) Q := integrable_toReal_rnDeriv_rpow hα0 hα1
  have hlin : Integrable (fun x ↦ α * p x + (1 - α)) Q :=
    (hpint.const_mul α).add (integrable_const _)
  have hint : Integrable (fun x ↦ hellFun α (p x)) Q := (hlin.sub hpα).div_const _
  rw [fDiv_of_integrable hint, derivAtTop_hellFun hα1]
  have hI : ∫ x, hellFun α (p x) ∂Q = (α * ∫ x, p x ∂Q + (1 - α) - ∫ x, p x ^ α ∂Q) / (1 - α) := by
    simp only [hellFun]
    rw [integral_div, integral_sub hlin hpα, integral_add (hpint.const_mul α) (integrable_const _),
      integral_const_mul]
    simp
  rw [hI, integral_toReal_rnDeriv',
    ← EReal.coe_ennreal_toReal (measure_ne_top (P.singularPart Q) univ), ← EReal.coe_mul,
    ← EReal.coe_add, EReal.coe_eq_coe_iff, ← measureReal_def, probReal_univ]
  have hs : 1 - α ≠ 0 := (sub_pos.2 hα1).ne'
  field_simp
  ring

end ProbabilityTheory

namespace GradedDivergence

variable {α : ℝ} {X : Type u} [MeasurableSpace X] {μ ν : Measure X} {r : ℝ≥0∞}

/-- Between probability measures an `α`-Hellinger bound `r` is the affinity bound
`∫ (dP/dQ)^α dQ ≥ e^{-(1-α) r}`. -/
theorem hellingerDivergence_iff_hellAff (hα0 : 0 < α) (hα1 : α < 1) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    hellingerDivergence α r μ ν ↔ hellAff α r ≤ ∫⁻ x, μ.rnDeriv ν x ^ α ∂ν := by
  rw [hellingerDivergence_iff, fDiv_hellFun_eq hα0 hα1]
  rcases eq_or_ne r ⊤ with rfl | hr
  · simp [hellAff]
  set A := ∫ x, (μ.rnDeriv ν x).toReal ^ α ∂ν
  have hA0 : 0 ≤ A := integral_nonneg fun x ↦ Real.rpow_nonneg toReal_nonneg _
  have hAl : ∫⁻ x, μ.rnDeriv ν x ^ α ∂ν = ENNReal.ofReal A := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_toReal_rnDeriv_rpow hα0 hα1)
      (ae_of_all _ fun x ↦ Real.rpow_nonneg toReal_nonneg _)]
    refine lintegral_congr_ae ((rnDeriv_lt_top μ ν).mono fun x hx ↦ ?_)
    change μ.rnDeriv ν x ^ α = ENNReal.ofReal ((μ.rnDeriv ν x).toReal ^ α)
    rw [← ofReal_rpow_of_nonneg toReal_nonneg hα0.le,
      ofReal_toReal hx.ne]
  have hs : 0 < 1 - α := sub_pos.2 hα1
  rw [hAl, bofThresh_of_ne_top _ hr, EReal.coe_le_coe_iff, hellAff_of_ne_top hr,
    ofReal_le_ofReal_iff hA0]
  simp only [bofReal, (by linarith : α - 1 ≠ 0), ↓reduceIte]
  rw [ show (α - 1) * r.toReal = -(1 - α) * r.toReal by ring,
    show ∀ e : ℝ, (e - 1) / (α - 1) = (1 - e) / (1 - α) from fun e ↦ by
      rw [← neg_sub, ← neg_sub 1 α, neg_div_neg_eq],
    div_le_div_iff_of_pos_right hs]
  constructor <;> intro h <;> linarith

variable [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]

/-- A filled `α`-Hellinger bound is the test bound of the relabelled left measure against the
filled right measure. -/
theorem fill_hellinger_iff (hα0 : 0 < α) (hα1 : α < 1) :
    fill (hellingerDivergence α) r μ ν ↔ HellDualBound α (hellAff α r) (μ.map some) ν.withBot := by
  refine ⟨fun ⟨μ', hle, _, hD⟩ ↦ ?_, fun h ↦ ?_⟩
  · have hD' := (hellingerDivergence_iff_hellAff hα0 hα1).1 hD
    exact (hellDualBound_of_le hα0 hα1 ((map_mono hle measurable_some).trans
      (map_some_le_withBot μ'))).mono hD'
  · obtain ⟨P, hP, hle, haff⟩ := exists_le_lintegral_rnDeriv_rpow_of_hellDualBound hα0 hα1
      (IsSubProbabilityMeasure.measure_le_one _) h
    refine ⟨Kernel.dropBot ∘ₘ P, Kernel.le_dropBot_comp hle, isSubProbabilityMeasure_bind _ _, ?_⟩
    change hellingerDivergence α r (Kernel.dropBot ∘ₘ P).withBot ν.withBot
    rw [Kernel.withBot_dropBot_comp]
    exact (hellingerDivergence_iff_hellAff hα0 hα1).2 haff

/-! ## The laws of filled Hellinger -/

section Laws

variable (α) [hα : Fact (α ∈ Ioo (0 : ℝ) 1)]

/-- Filled `α`-Hellinger composes (Rocq `FillDiv_composable`). -/
instance isComposable_fill_hellinger : (fill (hellingerDivergence.{u} α)).IsComposable where
  comp b c X Y _ _ μ₁ μ₂ _ _ κ η _ _ hμ hκ := by
    have hα0 := hα.out.1
    have hα1 := hα.out.2
    have : IsSubProbabilityMeasure (κ ∘ₘ μ₁) := isSubProbabilityMeasure_bind μ₁ _
    have : IsSubProbabilityMeasure (η ∘ₘ μ₂) := isSubProbabilityMeasure_bind μ₂ _
    rw [fill_hellinger_iff hα0 hα1] at hμ ⊢
    have hK : (κ ∘ₘ μ₁).map some = ((κ.map some) ∘ₖ Kernel.dropBot) ∘ₘ μ₁.map some := by
      rw [← Measure.comp_assoc, Kernel.dropBot_comp_map_some, Measure.map_comp _ _ measurable_some]
    rw [hK, Kernel.withBot_comp, hellAff_add]
    refine HellDualBound.comp hα1 hμ fun o ↦ ?_
    cases o with
    | none =>
      simpa [Kernel.comp_apply, Kernel.dropBot] using
        hellDualBound_zero_left hα0 hα1 (hellAff_le_one hα1.le c) (η.liftBot none)
    | some x =>
      have h := (fill_hellinger_iff hα0 hα1).1 (hκ x)
      simpa [Kernel.comp_apply, Kernel.dropBot, Kernel.map_apply _ measurable_some,
        Measure.dirac_bind (Kernel.measurable _)] using h

/-- Filled `α`-Hellinger passes to the supremum of an increasing sequence on the left (Rocq
`FillDiv_lim`). -/
instance isLeftContinuous_fill_hellinger :
    (fill (hellingerDivergence.{u} α)).IsLeftContinuous where
  iSup_left b X _ μ _ hμ ν _ h := by
    have : IsSubProbabilityMeasure (⨆ n, μ n) := ⟨by
      rw [iSup_apply_of_monotone hμ .univ]
      exact iSup_le fun n ↦ IsSubProbabilityMeasure.measure_le_one _⟩
    rw [fill_hellinger_iff hα.out.1 hα.out.2, map_iSup_of_monotone hμ measurable_some]
    have : IsFiniteMeasure (⨆ n, (μ n).map some) := by
      rw [← map_iSup_of_monotone hμ measurable_some]
      infer_instance
    exact HellDualBound.iSup hα.out.1 (fun _ _ hab ↦ Measure.map_mono (hμ hab) measurable_some)
      fun n ↦ (fill_hellinger_iff hα.out.1 hα.out.2).1 (h n)

/-- Filled `α`-Hellinger has closed budgets. -/
instance isBudgetClosed_fill_hellinger : (fill (hellingerDivergence.{u} α)).IsBudgetClosed where
  of_forall_gt {r} _ _ μ ν _ _ h := by
    rw [fill_hellinger_iff hα.out.1 hα.out.2]
    refine hellDualBound_of_forall_lt fun a ha ↦ ?_
    obtain ⟨r', hr', har'⟩ := exists_lt_hellAff ha
    exact ((fill_hellinger_iff hα.out.1 hα.out.2).1 (h r' hr')).mono har'.le

end Laws

end GradedDivergence
