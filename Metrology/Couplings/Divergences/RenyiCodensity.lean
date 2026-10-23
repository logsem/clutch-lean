module

public import Metrology.Couplings.Divergences.Concentrated

/-! # The Rényi codensity lifting

It is decided by tests into a point (`codensity_renyi_iff_unitTests`) and is the Hölder-dual Rényi
coupling (`rdpCoupl_iff_codensity`) (Rocq `renyi_kanto_canonical.v`, `renyi_codensity.v`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting Set Filter Topology
open scoped ENNReal
open Finset Kernel

namespace ProbabilityTheory

open Real

variable {α : ℝ} (hα : 1 < α)

include hα

/-! ## Support: the perspective of `t ↦ t ^ α`

Throughout, `β = α / (α - 1)` and `γ = (α - 1) / α = 1 / β`. -/

/-- The perspective of `t ↦ t ^ α` is positively homogeneous. -/
theorem persp_rpow_mul_left {s a b : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    persp (· ^ α) (s * a) (s * b) = s * persp (· ^ α) a b := by
  rw [persp_rpow_mul hα hs hs ha hb, persp_self, one_rpow, mul_one]

/-- The perspective of `t ↦ t ^ α` at `h` and `h ^ (α / (α - 1))` is `1`. -/
theorem persp_rpow_conj {h : ℝ} (hh : 0 < h) :
    persp (· ^ α) h (h ^ (α / (α - 1))) = 1 := by
  have hα1 : α - 1 ≠ 0 := sub_ne_zero.2 hα.ne'
  rw [persp_rpow_of_pos α (rpow_pos_of_pos hh _), ← EReal.coe_one, EReal.coe_eq_coe_iff]
  calc h ^ (α / (α - 1)) * (h / h ^ (α / (α - 1))) ^ α
      = h ^ (α / (α - 1)) * h ^ α / h ^ (α / (α - 1) * α) := by
        rw [div_rpow hh.le (rpow_nonneg hh.le _), ← rpow_mul hh.le, mul_div_assoc']
    _ = h ^ (α / (α - 1) + α - α / (α - 1) * α) := by rw [← rpow_add hh, ← rpow_sub hh]
    _ = h ^ (0 : ℝ) := by congr 1; field_simp; ring
    _ = 1 := rpow_zero h

/-- Weighting the cells by `h` on the left and `h ^ (α / (α - 1))` on the right does not
increase the sum of perspectives. -/
theorem persp_rpow_sum_le {ι : Type*} (s : Finset ι) {h p q : ι → ℝ}
    (hh : ∀ i, 0 ≤ h i) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    persp (· ^ α) (∑ i ∈ s, h i * p i) (∑ i ∈ s, h i ^ (α / (α - 1)) * q i) ≤
      ∑ i ∈ s, persp (· ^ α) (p i) (q i) := by
  have hβ : 0 < α / (α - 1) := div_pos (by linarith) (by linarith)
  refine (persp_sum_le (convexOn_rpow hα.le) s (fun i _ ↦ mul_nonneg (hh i) (hp i))
    fun i _ ↦ mul_nonneg (rpow_nonneg (hh i) _) (hq i)).trans
    (sum_le_sum fun i _ ↦ ?_)
  rcases (hh i).eq_or_lt with h0 | hpos
  · rw [← h0]
    rw [zero_rpow hβ.ne', zero_mul, zero_mul]
    rw [persp_rpow_zero_left (zero_lt_one.trans hα) le_rfl]
    exact persp_rpow_nonneg (hp i) (hq i)
  · rw [persp_rpow_mul hα (hh i) (rpow_nonneg (hh i) _) (hp i) (hq i),
      persp_rpow_conj hα hpos, one_mul]

/-- Away from the singular case `q = 0 < p`, the perspective of `t ↦ t ^ α` is `q (p / q) ^ α`. -/
theorem persp_rpow_of_ac {p q : ℝ} (hq : 0 ≤ q) (hpq : q = 0 → p = 0) :
    persp (· ^ α) p q = ((q * (p / q) ^ α : ℝ) : EReal) := by
  rcases hq.eq_or_lt with rfl | hq
  · simp [hpq rfl, persp_rpow_zero_left (zero_lt_one.trans hα) le_rfl]
  · exact persp_rpow_of_pos α hq

/-- Weighting `p` by `(p / q) ^ (α - 1)` gives the summand `q (p / q) ^ α`. -/
theorem rpow_div_sub_one_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : q = 0 → p = 0) : (p / q) ^ (α - 1) * p = q * (p / q) ^ α := by
  rcases hq.eq_or_lt with rfl | hq
  · simp [hpq rfl]
  calc (p / q) ^ (α - 1) * p = q * ((p / q) ^ (α - 1) * (p / q)) := by field_simp
    _ = q * (p / q) ^ α := by
        rw [← rpow_add_one' (div_nonneg hp hq.le) (by linarith), sub_add_cancel]

/-- Weighting `q` by `(p / q) ^ (α - 1)` at the conjugate exponent gives the summand
`q (p / q) ^ α`. -/
theorem rpow_div_sub_one_rpow_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ((p / q) ^ (α - 1)) ^ (α / (α - 1)) * q = q * (p / q) ^ α := by
  rw [← rpow_mul (div_nonneg hp hq), mul_div_cancel₀ _ (sub_ne_zero.2 hα.ne'), mul_comm]

/-- Scaling `S` by `t` on the left and `t ^ (α / (α - 1))` on the right leaves the perspective
of `t ↦ t ^ α` at `S`. -/
theorem persp_rpow_conj_mul_self {t S : ℝ} (ht : 0 < t) (hS : 0 ≤ S) :
    persp (· ^ α) (t * S) (t ^ (α / (α - 1)) * S) = S := by
  rw [persp_rpow_mul hα ht.le (rpow_nonneg ht.le _) hS hS, persp_rpow_conj hα ht, one_mul,
    persp_self, one_rpow, mul_one]

/-- Away from the singular case, the `[0, 1]`-valued weighting `h ∝ (p / q) ^ (α - 1)` turns the
perspective of the weighted sums into the sum of perspectives. -/
theorem exists_persp_rpow_eq_sum {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hpq : ∀ i, q i = 0 → p i = 0) :
    ∃ h : ι → ℝ, (∀ i, 0 ≤ h i ∧ h i ≤ 1) ∧
      persp (· ^ α) (∑ i, h i * p i) (∑ i, h i ^ (α / (α - 1)) * q i) =
        ∑ i, persp (· ^ α) (p i) (q i) := by
  set g : ι → ℝ := fun i ↦ (p i / q i) ^ (α - 1)
  have hg (i : ι) : 0 ≤ g i := rpow_nonneg (div_nonneg (hp i) (hq i)) _
  set T := 1 + ∑ i, g i
  have hT : 0 < T := add_pos_of_pos_of_nonneg one_pos (sum_nonneg fun i _ ↦ hg i)
  have hgT (i : ι) : g i ≤ T :=
    (single_le_sum (fun j _ ↦ hg j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
  set S := ∑ i, q i * (p i / q i) ^ α
  have hS : 0 ≤ S := sum_nonneg fun i _ ↦
    mul_nonneg (hq i) (rpow_nonneg (div_nonneg (hp i) (hq i)) _)
  have hgp (i : ι) : g i * p i = q i * (p i / q i) ^ α :=
    rpow_div_sub_one_mul hα (hp i) (hq i) (hpq i)
  have hgq (i : ι) : g i ^ (α / (α - 1)) * q i = q i * (p i / q i) ^ α :=
    rpow_div_sub_one_rpow_mul hα (hp i) (hq i)
  refine ⟨fun i ↦ g i / T, fun i ↦ ⟨div_nonneg (hg i) hT.le, (div_le_one hT).2 (hgT i)⟩, ?_⟩
  calc persp (· ^ α) (∑ i, g i / T * p i) (∑ i, (g i / T) ^ (α / (α - 1)) * q i)
      = persp (· ^ α) (T⁻¹ * S) (T⁻¹ ^ (α / (α - 1)) * S) := by
        congr 1
        · simp_rw [S, ← hgp, mul_sum, div_eq_inv_mul, mul_assoc]
        · simp_rw [S, ← hgq, mul_sum, div_eq_inv_mul,
            mul_rpow (inv_nonneg.2 hT.le) (hg _), mul_assoc]
    _ = S := persp_rpow_conj_mul_self hα (inv_pos.2 hT) hS
    _ = ∑ i, persp (· ^ α) (p i) (q i) := by
        simp_rw [persp_rpow_of_ac hα (hq _) (hpq _), S, EReal.coe_finset_sum]

/-- Some `[0, 1]`-valued weighting attains the sum of perspectives: `h ∝ (p / q) ^ (α - 1)`, or
a single cell where `q` vanishes below a positive `p`. -/
theorem exists_sum_persp_rpow_le {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    ∃ h : ι → ℝ, (∀ i, 0 ≤ h i ∧ h i ≤ 1) ∧ ∑ i, persp (· ^ α) (p i) (q i) ≤
      persp (· ^ α) (∑ i, h i * p i) (∑ i, h i ^ (α / (α - 1)) * q i) := by
  classical
  have hβ : 0 < α / (α - 1) := div_pos (by linarith) (by linarith)
  by_cases hsing : ∃ j, q j = 0 ∧ 0 < p j
  · obtain ⟨j, hqj, hpj⟩ := hsing
    refine ⟨fun i ↦ if i = j then 1 else 0, fun i ↦ by by_cases i = j <;> simp [*], ?_⟩
    simp [ite_mul, apply_ite (· ^ (α / (α - 1))), zero_rpow hβ.ne', hqj,
      persp_rpow_zero_right hα hpj]
  push Not at hsing
  obtain ⟨h, hh, heq⟩ := exists_persp_rpow_eq_sum hα hp hq fun i hi ↦ (hsing i hi).antisymm (hp i)
  exact ⟨h, hh, heq.ge⟩

end ProbabilityTheory

namespace GradedDivergence

open Real (exp exp_add exp_le_one_iff exp_neg exp_pos rpow_le_one rpow_nonneg)
open ENNReal hiding rpow_le_one

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {α : ℝ} {ρ : ℝ≥0∞}
  {R : X → Y → ℝ≥0∞} {μ : Measure X} {ν : Measure Y}

/-! ## Mass tests on a finite partition -/

/-- A test into a point that is constant on the cells of a finite partition has the perspective
of the cell masses as its divergence. -/
theorem fDiv_mass_comp_eq {I : Type*} [MeasurableSpace I] (hα : 1 < α) {n : ℕ} {π : I → Fin n}
    (hπ : Measurable π) {a b : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hF : Measurable fun i ↦ ENNReal.ofReal (a (π i)))
    (hG : Measurable fun i ↦ ENNReal.ofReal (b (π i)))
    (hF1 : ∀ i, ENNReal.ofReal (a (π i)) ≤ 1) (hG1 : ∀ i, ENNReal.ofReal (b (π i)) ≤ 1)
    (P Q : Measure I) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    fDiv (· ^ α) (mass.{u} hF ∘ₘ P) (mass.{u} hG ∘ₘ Q) =
      persp (· ^ α) (∑ j, a j * (P (π ⁻¹' {j})).toReal) (∑ j, b j * (Q (π ⁻¹' {j})).toReal) := by
  rw [mass_comp, mass_comp]
  rw [fDiv_smul_dirac (convexOn_rpow hα.le)
    (continuousWithinAt_rpow_zero (zero_lt_one.trans hα)) (lintegral_ne_top_of_le_one P hF1)
    (lintegral_ne_top_of_le_one Q hG1)]
  rw [toReal_lintegral_ofReal_comp hπ ha, toReal_lintegral_ofReal_comp hπ hb]

/-- Weighted masses on a finite partition give sub-Markov tests into a point whose divergence is `s`
times the perspective of the weighted cell masses. -/
theorem exists_mass_fDiv_eq {I : Type*} [MeasurableSpace I] (hα : 1 < α) {n : ℕ}
    {π : I → Fin n} (hπ : Measurable π) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {w : Fin n → ℝ}
    (hw : ∀ j, 0 ≤ w j ∧ w j ≤ 1) :
    ∃ (K L : Kernel I PUnit.{u + 1}), IsSubMarkovKernel K ∧ IsSubMarkovKernel L ∧
      ∀ (P Q : Measure I) [IsFiniteMeasure P] [IsFiniteMeasure Q],
        fDiv (· ^ α) (K ∘ₘ P) (L ∘ₘ Q) = s * persp (· ^ α) (∑ j, w j * (P (π ⁻¹' {j})).toReal)
          (∑ j, w j ^ (α / (α - 1)) * (Q (π ⁻¹' {j})).toReal) := by
  have hβ : 0 ≤ α / (α - 1) := div_nonneg (by linarith) (by linarith)
  have hF1 (i : I) : ENNReal.ofReal (s * w (π i)) ≤ 1 :=
    ofReal_le_one.2 ((mul_le_of_le_one_left (hw _).1 hs1).trans (hw _).2)
  have hG1 (i : I) : ENNReal.ofReal (s * w (π i) ^ (α / (α - 1))) ≤ 1 :=
    ofReal_le_one.2 ((mul_le_of_le_one_left (rpow_nonneg (hw _).1 _) hs1).trans
      (rpow_le_one (hw _).1 (hw _).2 hβ))
  have : Measurable w := .of_discrete
  have hF : Measurable fun i ↦ ENNReal.ofReal (s * w (π i)) := by fun_prop
  have hG : Measurable fun i ↦ ENNReal.ofReal (s * w (π i) ^ (α / (α - 1))) := by fun_prop
  refine ⟨mass.{u} hF, mass.{u} hG, isSubMarkovKernel_mass hF hF1,
    isSubMarkovKernel_mass hG hG1, fun P Q _ _ ↦ ?_⟩
  rw [fDiv_mass_comp_eq hα hπ (fun j ↦ mul_nonneg hs.le (hw j).1)
    (fun j ↦ mul_nonneg hs.le (rpow_nonneg (hw j).1 _)) hF hG hF1 hG1,
    ← persp_rpow_mul_left hα hs.le
      (sum_nonneg fun j _ ↦ mul_nonneg (hw j).1 toReal_nonneg)
      (sum_nonneg fun j _ ↦ mul_nonneg (rpow_nonneg (hw j).1 _) toReal_nonneg)]
  simp only [mul_sum, mul_assoc]

/-! ## The slack-Hölder bound and Rényi couplings -/

/-- The slack-Hölder bound: tests with `f x ≤ e^{(α - 1) R x y / α} g y` wherever `R x y < ⊤`
satisfy `E_μ[f] ≤ e^{(α - 1) ρ / α} ‖g‖_{α / (α - 1)}` in `ν` (Rocq `SH`). -/
def SlackHolder (α : ℝ) (ρ : ℝ≥0∞) (R : X → Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y) : Prop :=
  ∀ ⦃f : X → ℝ≥0∞⦄ ⦃g : Y → ℝ≥0∞⦄, Measurable f → Measurable g →
    (∀ x y, R x y < ⊤ → f x ≤ expBudget (ENNReal.ofReal ((α - 1) / α) * R x y) * g y) →
    ∫⁻ x, f x ∂μ ≤
      expBudget (ENNReal.ofReal ((α - 1) / α) * ρ) * (∫⁻ y, g y ^ (α / (α - 1)) ∂ν) ^ ((α - 1) / α)

/-- The Hölder-dual Rényi coupling of a relation: tests ordered on `S` satisfy
`E_μ[f] ≤ e^{(α - 1) ρ / α} ‖g‖_{α / (α - 1)}` in `ν` (Rocq `RDPcoupl`). -/
def RdpCoupl (α : ℝ) (ρ : ℝ≥0∞) (S : X → Y → Prop) (μ : Measure X) (ν : Measure Y) : Prop :=
  ∀ ⦃f : X → ℝ≥0∞⦄ ⦃g : Y → ℝ≥0∞⦄, Measurable f → Measurable g → (∀ x y, S x y → f x ≤ g y) →
    ∫⁻ x, f x ∂μ ≤
      expBudget (ENNReal.ofReal ((α - 1) / α) * ρ) * (∫⁻ y, g y ^ (α / (α - 1)) ∂ν) ^ ((α - 1) / α)

/-- The Rényi coupling of `S` is the slack-Hölder bound at the leftover of `S` (Rocq
`SH_boolean`). -/
theorem rdpCoupl_iff_slackHolder {S : X → Y → Prop} :
    RdpCoupl α ρ S μ ν ↔ SlackHolder α ρ (relCost S) μ ν := by
  have (f : X → ℝ≥0∞) (g : Y → ℝ≥0∞) (x : X) (y : Y) :
      ((relCost S x y : ℝ≥0∞) < ⊤ → f x ≤
        expBudget (ENNReal.ofReal ((α - 1) / α) * relCost S x y) * g y) ↔ (S x y → f x ≤ g y) := by
    by_cases hS : S x y <;> simp [hS]
  simp only [RdpCoupl, SlackHolder, this]

/-- Values in slack-Hölder relation at `r`, truncated at `M` and scaled by `t` into `[0, 1]`, give
point masses in Rényi relation at `r`. -/
theorem renyiDivergence_dirac_truncated (hα : 1 < α) {r a b t M : ℝ≥0∞} (hr : r ≠ ⊤)
    (hab : a ≤ expBudget (ENNReal.ofReal ((α - 1) / α) * r) * b) (ha : t * min a M ≤ 1)
    (hb : (t * min b M) ^ (α / (α - 1)) ≤ 1) :
    renyiDivergence α r ((t * min a M) • dirac PUnit.unit.{u + 1})
      ((t * min b M) ^ (α / (α - 1)) • dirac PUnit.unit) := by
  have hβγ : α / (α - 1) * ((α - 1) / α) = 1 := by
    have : α - 1 ≠ 0 := sub_ne_zero.2 hα.ne'
    have : α ≠ 0 := (zero_lt_one.trans hα).ne'
    field_simp
  rw [renyiDivergence_smul_dirac_iff hα hr (ne_top_of_le_ne_top one_ne_top ha)
    (ne_top_of_le_ne_top one_ne_top hb), ← rpow_mul, hβγ, rpow_one,
    mul_left_comm]
  gcongr
  exact min_le_mul_min hab (one_le_expBudget _)

/-! ## Tests into a point decide the codensity lifting -/

section

variable [hα : Fact (1 < α)]

/-- A Rényi codensity lifting passes its tests into a point at slack `0`. -/
theorem renyiDivergence_comp_of_codensity
    (h : (renyiDivergence α).codensity ρ R μ ν) {k : Kernel X PUnit.{u + 1}}
    {l : Kernel Y PUnit.{u + 1}} [IsSubMarkovKernel k] [IsSubMarkovKernel l]
    (hkl : ∀ x y, R x y < ⊤ → renyiDivergence α (R x y) (k x) (l y)) :
    renyiDivergence α ρ (k ∘ₘ μ) (l ∘ₘ ν) := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · exact renyiDivergence_top hα.out _ _
  simpa using h (c := 0) (by simpa using hρ.lt_top) fun x y ↦ by
    rcases (le_top : R x y ≤ ⊤).lt_or_eq with hR | hR
    · simpa using hkl x y hR
    · simpa [hR] using renyiDivergence_top hα.out (k x) (l y)

variable [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]

/-- Tests into a point at slack `0` decide the Rényi codensity lifting (Rocq `SH_iff_bind_unit`). -/
theorem codensity_renyi_of_unitTests
    (h : ∀ (k : Kernel X PUnit.{u + 1}) (l : Kernel Y PUnit.{u + 1}) [IsSubMarkovKernel k]
      [IsSubMarkovKernel l], (∀ x y, R x y < ⊤ → renyiDivergence α (R x y) (k x) (l y)) →
      renyiDivergence α ρ (k ∘ₘ μ) (l ∘ₘ ν)) :
    (renyiDivergence α).codensity ρ R μ ν := by
  intro I _ c hρc k l _ _ hkl
  obtain ⟨hρ, hc⟩ := add_lt_top.1 hρc
  have hα1 := hα.out
  have hf := convexOn_rpow hα1.le
  have hf_cont := continuousWithinAt_rpow_zero (zero_lt_one.trans hα1)
  -- `s` absorbs the slack `c`: scale both test masses by `s`
  set s := exp (-((α - 1) * c.toReal)) with hs_def
  have hs : 0 < s := exp_pos _
  have hs1 : s ≤ 1 := exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (by linarith) toReal_nonneg))
  rw [renyiDivergence_iff_of_ne_top hα1.le hρc.ne, fDiv_eq_iSup_partition hf hf_cont]
  refine iSup_le fun n ↦ iSup_le fun π ↦ iSup_le fun hπ ↦ ?_
  -- step 1: pick Hölder weights `w ∝ (p / q) ^ (α - 1)` so the partition sum is one point test
  obtain ⟨w, hw, hle⟩ := exists_sum_persp_rpow_le hα1
    (p := fun j ↦ ((k ∘ₘ μ) (π ⁻¹' {j})).toReal) (q := fun j ↦ ((l ∘ₘ ν) (π ⁻¹' {j})).toReal)
    (fun _ ↦ toReal_nonneg) fun _ ↦ toReal_nonneg
  refine hle.trans ?_
  -- the test into a point: masses `s w` on the left and `s w ^ (α / (α - 1))` on the right
  obtain ⟨K, L, _, _, hmass⟩ := exists_mass_fDiv_eq hα1 hπ hs hs1 hw
  -- the point test `K ∘ k`, `L ∘ l` passes at `R x y` because `s` cancels the `c` in `R x y + c`
  have key := h (K ∘ₖ k) (L ∘ₖ l) fun x y hR ↦ by
    rw [Kernel.comp_apply, Kernel.comp_apply, renyiDivergence_iff_of_ne_top hα1.le hR.ne, hmass]
    calc _ ≤ ((s : ℝ) : EReal) * fDiv (· ^ α) (k x) (l y) :=
          mul_le_mul_of_nonneg_left ((persp_rpow_sum_le hα1 _ (fun j ↦ (hw j).1)
            (fun _ ↦ toReal_nonneg) fun _ ↦ toReal_nonneg).trans
              (sum_persp_le_fDiv hf hf_cont hπ)) (EReal.coe_nonneg.2 hs.le)
      _ ≤ ((s : ℝ) : EReal) * ((exp ((α - 1) * (R x y + c).toReal) : ℝ) : EReal) :=
          mul_le_mul_of_nonneg_left ((renyiDivergence_iff_of_ne_top hα1.le
            (add_ne_top.2 ⟨hR.ne, hc.ne⟩)).1 (hkl x y)) (EReal.coe_nonneg.2 hs.le)
      _ = ((exp ((α - 1) * (R x y).toReal) : ℝ) : EReal) := by
          rw [← EReal.coe_mul, hs_def, ← exp_add, toReal_add hR.ne hc.ne]
          ring_nf
  rw [← Measure.comp_assoc, ← Measure.comp_assoc, renyiDivergence_iff_of_ne_top hα1.le hρ.ne,
    hmass] at key
  set A := persp (· ^ α) (∑ j, w j * ((k ∘ₘ μ) (π ⁻¹' {j})).toReal)
    (∑ j, w j ^ (α / (α - 1)) * ((l ∘ₘ ν) (π ⁻¹' {j})).toReal)
  -- step 2: `s * A ≤ e^{(α-1)ρ}`, so `A ≤ e^{(α-1)(ρ+c)}` since `s = e^{-(α-1)c}`
  calc A = ((s⁻¹ : ℝ) : EReal) * (s * A) := by
        rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hs.ne', EReal.coe_one, one_mul]
    _ ≤ ((s⁻¹ : ℝ) : EReal) * ((exp ((α - 1) * ρ.toReal) : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left key (EReal.coe_nonneg.2 (inv_nonneg.2 hs.le))
    _ = ((exp ((α - 1) * (ρ + c).toReal) : ℝ) : EReal) := by
        rw [← EReal.coe_mul, hs_def, ← exp_neg, ← exp_add, toReal_add hρ.ne hc.ne]
        ring_nf

/-- The Rényi codensity lifting is decided by tests into a point at slack `0` (Rocq
`SH_iff_bind_unit`, `kanto_bind`). -/
theorem codensity_renyi_iff_unitTests :
    (renyiDivergence α).codensity ρ R μ ν ↔
      ∀ (k : Kernel X PUnit.{u + 1}) (l : Kernel Y PUnit.{u + 1}) [IsSubMarkovKernel k]
        [IsSubMarkovKernel l], (∀ x y, R x y < ⊤ → renyiDivergence α (R x y) (k x) (l y)) →
        renyiDivergence α ρ (k ∘ₘ μ) (l ∘ₘ ν) :=
  ⟨fun h _ _ _ _ ↦ renyiDivergence_comp_of_codensity h, codensity_renyi_of_unitTests⟩

/-- A slack-Hölder bound gives the Rényi codensity lifting (Rocq `SH_to_bind_unit`). -/
theorem codensity_renyi_of_slackHolder (h : SlackHolder α ρ R μ ν) :
    (renyiDivergence α).codensity ρ R μ ν := by
  refine codensity_renyi_of_unitTests fun k l _ _ hkl ↦ ?_
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · exact renyiDivergence_top hα.out _ _
  have hα0 : 0 < α := zero_lt_one.trans hα.out
  have hα1 : 0 < α - 1 := sub_pos.2 hα.out
  have hγβ : (α - 1) / α * (α / (α - 1)) = 1 := by field_simp
  rw [eq_smul_dirac_punit (k ∘ₘ μ), eq_smul_dirac_punit (l ∘ₘ ν),
    renyiDivergence_smul_dirac_iff hα.out hρ (measure_ne_top _ _) (measure_ne_top _ _),
    bind_apply .univ k.measurable.aemeasurable, bind_apply .univ l.measurable.aemeasurable]
  have := h (k.measurable_coe .univ) ((l.measurable_coe .univ).pow_const ((α - 1) / α))
    fun x y hR ↦ by
      have := hkl x y hR
      rwa [eq_smul_dirac_punit (k x), eq_smul_dirac_punit (l y),
        renyiDivergence_smul_dirac_iff hα.out hR.ne (measure_ne_top _ _)
          (measure_ne_top _ _)] at this
  simpa only [← rpow_mul, hγβ, rpow_one] using this

/-- A Rényi codensity lifting bounds each truncation of a slack-Hölder test (Rocq
`bind_unit_to_SH_truncated`). -/
theorem slackHolder_truncated_of_codensity (hρ : ρ ≠ ⊤) (h : (renyiDivergence α).codensity ρ R μ ν)
    {f : X → ℝ≥0∞} {g : Y → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ x y, R x y < ⊤ → f x ≤ expBudget (ENNReal.ofReal ((α - 1) / α) * R x y) * g y)
    (N : ℕ) : ∫⁻ x, min (f x) (N + 1) ∂μ ≤ expBudget (ENNReal.ofReal ((α - 1) / α) * ρ) *
      (∫⁻ y, g y ^ (α / (α - 1)) ∂ν) ^ ((α - 1) / α) := by
  have hα0 : 0 < α := zero_lt_one.trans hα.out
  have hα1 : 0 < α - 1 := sub_pos.2 hα.out
  have hγ : 0 < (α - 1) / α := div_pos hα1 hα0
  have hβ : 0 < α / (α - 1) := div_pos hα0 hα1
  have hβγ : α / (α - 1) * ((α - 1) / α) = 1 := by field_simp
  set t : ℝ≥0∞ := ((N : ℝ≥0∞) + 1)⁻¹
  have ht0 : t ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
  have htop : t ≠ ⊤ := inv_ne_top.2 (by simp)
  have hcap (a : ℝ≥0∞) : t * min a (N + 1) ≤ 1 := by
    grw [min_le_right]
    exact (ENNReal.inv_mul_cancel (by simp) (by simp)).le
  have hcapβ (a : ℝ≥0∞) : (t * min a (N + 1)) ^ (α / (α - 1)) ≤ 1 :=
    ENNReal.rpow_le_one (hcap a) hβ.le
  have hF : Measurable fun x ↦ t * min (f x) (N + 1) := by fun_prop
  have hG : Measurable fun y ↦ (t * min (g y) (N + 1)) ^ (α / (α - 1)) := by fun_prop
  have := isSubMarkovKernel_mass.{u} hF fun x ↦ hcap (f x)
  have := isSubMarkovKernel_mass.{u} hG fun y ↦ hcapβ (g y)
  have key := renyiDivergence_comp_of_codensity h (k := mass.{u} hF)
    (l := mass.{u} hG) fun x y hR ↦
      renyiDivergence_dirac_truncated hα.out hR.ne (hfg x y hR) (hcap _) (hcapβ _)
  rw [mass_comp, mass_comp] at key
  rw [renyiDivergence_smul_dirac_iff hα.out hρ
    (lintegral_ne_top_of_le_one μ fun x ↦ hcap (f x))
    (lintegral_ne_top_of_le_one ν fun y ↦ hcapβ (g y))] at key
  set E := expBudget (ENNReal.ofReal ((α - 1) / α) * ρ)
  refine (ENNReal.mul_le_mul_iff_right ht0 htop).1 ?_
  calc t * ∫⁻ x, min (f x) (N + 1) ∂μ
      = ∫⁻ x, t * min (f x) (N + 1) ∂μ := (lintegral_const_mul _ (by fun_prop)).symm
    _ ≤ E * (∫⁻ y, (t * min (g y) (N + 1)) ^ (α / (α - 1)) ∂ν) ^ ((α - 1) / α) := key
    _ = t * (E * (∫⁻ y, min (g y) (N + 1) ^ (α / (α - 1)) ∂ν) ^ ((α - 1) / α)) := by
        simp_rw [mul_rpow_of_nonneg _ _ hβ.le]
        rw [lintegral_const_mul _ (by fun_prop), mul_rpow_of_nonneg _ _ hγ.le,
          ← rpow_mul, hβγ, rpow_one, mul_left_comm]
    _ ≤ t * (E * (∫⁻ y, g y ^ (α / (α - 1)) ∂ν) ^ ((α - 1) / α)) := by
        gcongr with y
        exact min_le_left _ _

/-- A Rényi codensity lifting at a finite budget is a slack-Hölder bound (Rocq
`bind_unit_to_SH`). -/
theorem slackHolder_of_codensity (hρ : ρ ≠ ⊤)
    (h : (renyiDivergence α).codensity ρ R μ ν) : SlackHolder α ρ R μ ν := by
  intro f g hf hg hfg
  have htrunc := slackHolder_truncated_of_codensity hρ h hf hg hfg
  have hsup (x : X) : ⨆ N : ℕ, min (f x) (N + 1) = f x := by
    rw [← inf_iSup_eq, ← iSup_add, iSup_natCast, _root_.top_add, inf_top_eq]
  calc ∫⁻ x, f x ∂μ
      = ∫⁻ x, ⨆ N : ℕ, min (f x) (N + 1) ∂μ := by simp_rw [hsup]
    _ = ⨆ N : ℕ, ∫⁻ x, min (f x) (N + 1) ∂μ :=
        lintegral_iSup (fun _ ↦ by fun_prop) fun _ _ _ _ ↦ by gcongr
    _ ≤ _ := iSup_le htrunc

/-- The Rényi codensity lifting at a finite budget is the slack-Hölder bound (Rocq
`SH_iff_bind_unit`). -/
theorem codensity_renyi_iff_slackHolder (hρ : ρ ≠ ⊤) :
    (renyiDivergence α).codensity ρ R μ ν ↔ SlackHolder α ρ R μ ν :=
  ⟨slackHolder_of_codensity hρ, codensity_renyi_of_slackHolder⟩

/-- Rényi couplings of a relation are exactly its Rényi codensity liftings (Rocq
`RDPcoupl_iff_codensity`). -/
theorem rdpCoupl_iff_codensity (hρ : ρ ≠ ⊤) {S : X → Y → Prop} :
    RdpCoupl α ρ S μ ν ↔ (codensity (renyiDivergence α)).Rel ρ S μ ν :=
  rdpCoupl_iff_slackHolder.trans (codensity_renyi_iff_slackHolder hρ).symm

/-! ## zCDP and tCDP liftings as Rényi couplings -/

/-- A zCDP relational lifting is a Hölder-dual Rényi coupling along `ξ + α ρ` at every order (Rocq
`gcf_zCDP_iff`). -/
theorem zcdpLifting_rel_iff_rdpCoupl {ξ ρ : ℝ≥0∞} (hξ : ξ ≠ ⊤) (hρ : ρ ≠ ⊤) {S : X → Y → Prop} :
    zcdpLifting.Rel (ξ, ρ) S μ ν ↔
      ∀ α : Ioi (1 : ℝ), RdpCoupl α (ξ + ENNReal.ofReal α * ρ) S μ ν := by
  refine concentratedLifting_rel_iff.trans (forall_congr' fun α ↦ ?_)
  have hne : ξ + ENNReal.ofReal α * ρ ≠ ⊤ := add_ne_top.2 ⟨hξ, mul_ne_top ofReal_ne_top hρ⟩
  exact ⟨fun h ↦ (rdpCoupl_iff_codensity hne).2 (h α.2), fun h _ ↦ (rdpCoupl_iff_codensity hne).1 h⟩

/-- A tCDP relational lifting is a Hölder-dual Rényi coupling along `α ρ` at every order below `ω`
(Rocq `gcf_tCDP_iff`). -/
theorem tcdpLifting_rel_iff_rdpCoupl {ω : ℝ} {ρ : ℝ≥0∞} (hρ : ρ ≠ ⊤) {S : X → Y → Prop} :
    (tcdpLifting ω).Rel ρ S μ ν ↔
      ∀ α : Ioi (1 : ℝ), (α : ℝ) < ω → RdpCoupl α (ENNReal.ofReal α * ρ) S μ ν := by
  refine tcdpLifting_rel_iff.trans (forall_congr' fun α ↦ forall_congr' fun _ ↦ ?_)
  exact (rdpCoupl_iff_codensity (mul_ne_top ofReal_ne_top hρ)).symm

end

end GradedDivergence
