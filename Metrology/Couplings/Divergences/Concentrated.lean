module

public import Metrology.Couplings.Divergences.Renyi

/-! Rényi curves and concentrated differential privacy as graded divergences (Approximate Span
Liftings, Eqs. 6 and 7, Thms. 4.12 and 4.13). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting Set
open scoped ENNReal

/-- Rényi orders are above one. -/
instance fact_one_lt_coe_ioi (α : Ioi (1 : ℝ)) : Fact (1 < (α : ℝ)) :=
  ⟨α.2⟩

namespace GradedDivergence

/-! ## Rényi curves -/

/-- Budgets indexed by the orders `α > 1`, so the budget order is a canonical partial order. -/
abbrev RenyiBudget :=
  Ioi (1 : ℝ) → ℝ≥0∞

/-- A Rényi bound at every order, each within its own budget (Rocq `RDPcoupl_curve`). -/
noncomputable def renyiCurve : GradedDivergence.{u} RenyiBudget :=
  fun ρ _ _ μ ν ↦ ∀ α : Ioi (1 : ℝ), renyiDivergence α (ρ α) μ ν

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

theorem renyiCurve_iff {ρ : RenyiBudget} {μ ν : Measure X} :
    renyiCurve ρ μ ν ↔ ∀ α : Ioi (1 : ℝ), renyiDivergence α (ρ α) μ ν :=
  Iff.rfl

instance isGraded_renyiCurve : renyiCurve.{u}.IsGraded where
  mono _ _ hb _ _ _ _ _ _ h α := IsGraded.mono (hb α) (h α)
  top μ ν _ _ α := IsGraded.top (D := renyiDivergence α) μ ν

instance isReflexive_renyiCurve : renyiCurve.{u}.IsReflexive where
  refl μ _ α := IsReflexive.refl (D := renyiDivergence α) μ

instance isComposable_renyiCurve : renyiCurve.{u}.IsComposable where
  comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hκ α := IsComposable.comp (h α) fun x ↦ hκ x α

instance isZeroLeft_renyiCurve : renyiCurve.{u}.IsZeroLeft where
  zero_left b _ _ ν _ α := IsZeroLeft.zero_left (b α) ν

/-- Rényi curves are left continuous (Rocq `GCFamLim_curve`). -/
instance isLeftContinuous_renyiCurve : renyiCurve.{u}.IsLeftContinuous where
  iSup_left b _ _ _ _ hμ ν _ h α := IsLeftContinuous.iSup_left (b α) hμ ν fun n ↦ h n α

/-- A bound at every larger curve is a bound at the curve: raise one order at a time. -/
instance isBudgetClosed_renyiCurve : renyiCurve.{u}.IsBudgetClosed where
  of_forall_gt {b} _ _ _ _ _ _ h α := by
    classical
    refine IsBudgetClosed.of_forall_gt fun t ht ↦ ?_
    simpa using h (Function.update b α t) (lt_update_self_iff.2 ht) α

/-- A codensity lifting of a Rényi curve is one at every order: tests at a single order are curve
tests with slack `⊤` at the other orders. -/
theorem codensity_renyiCurve_iff {ρ : RenyiBudget} {R : X → Y → RenyiBudget} {μ : Measure X}
    {ν : Measure Y} : renyiCurve.codensity ρ R μ ν ↔
      ∀ α : Ioi (1 : ℝ), (renyiDivergence α).codensity (ρ α) (fun x y ↦ R x y α) μ ν := by
  classical
  refine ⟨fun h α I _ c hc k l _ _ hkl ↦ ?_, fun h I _ c _ k l _ _ hkl α ↦ ?_⟩
  · have hlt : ρ + Function.update ⊤ α c < ⊤ := lt_top_iff_ne_top.2 fun htop ↦
      hc.ne (by simpa using congrFun htop α)
    have hkl' (x : X) (y : Y) (β : Ioi (1 : ℝ)) :
        renyiDivergence β ((R x y + Function.update (⊤ : RenyiBudget) α c) β) (k x) (l y) := by
      rcases eq_or_ne β α with rfl | hβ
      · simpa using hkl x y
      · simpa [hβ] using renyiDivergence_top β.2 (k x) (l y)
    simpa using h hlt hkl' α
  rcases eq_or_ne (ρ α + c α) ⊤ with htop | hlt
  · show renyiDivergence α (ρ α + c α) _ _
    rw [htop]
    exact renyiDivergence_top α.2 _ _
  · exact h α (lt_top_iff_ne_top.2 hlt) fun x y ↦ hkl x y α

/-- A curve with a finite order is not absorbing (Rocq `GCF_curve_top_exact`). -/
theorem not_absorbing_codensity_renyiCurve {ρ : RenyiBudget} (hρ : ∃ α, ρ α < ⊤) :
    ¬(codensity renyiCurve.{u}).Absorbing ρ := by
  classical
  obtain ⟨α, hα⟩ := hρ
  refine fun h ↦ not_absorbing_codensity_renyi α.2 hα fun R μ ν _ _ ↦ ?_
  simpa using codensity_renyiCurve_iff.1 (h (fun x y ↦ Function.update ⊤ α (R x y)) μ ν) α

/-! ## Concentrated divergences -/

section Line

variable (A : Set ℝ)

open Classical in
/-- The line `α ↦ ξ + α ρ` on the orders in `A`, `⊤` off `A` (Rocq `zcdp_line`, `tcdp_line`). -/
noncomputable def concentratedLine (b : ℝ≥0∞ × ℝ≥0∞) : RenyiBudget :=
  fun α ↦ if (α : ℝ) ∈ A then b.1 + ENNReal.ofReal α * b.2 else ⊤

/-- Lines add (Rocq `zcdp_line_add`, `tcdp_line_add`). -/
theorem concentratedLine_add (b c : ℝ≥0∞ × ℝ≥0∞) :
    concentratedLine A (b + c) = concentratedLine A b + concentratedLine A c := by
  ext α
  by_cases hα : (α : ℝ) ∈ A <;> simp [concentratedLine, hα, mul_add, add_add_add_comm]

theorem concentratedLine_mono : Monotone (concentratedLine A) := fun b c h α ↦ by
  by_cases hα : (α : ℝ) ∈ A
  · simpa [concentratedLine, hα] using add_le_add h.1 (mul_le_mul_right h.2 _)
  · simp [concentratedLine, hα]

theorem concentratedLine_snd_top (ξ : ℝ≥0∞) : concentratedLine A (ξ, ⊤) = ⊤ := by
  ext α
  have : ENNReal.ofReal α ≠ 0 := by simpa using zero_lt_one.trans α.2
  simp [concentratedLine, ENNReal.mul_top this]

theorem concentratedLine_top : concentratedLine A ⊤ = ⊤ :=
  concentratedLine_snd_top A ⊤

end Line

/-- Rényi bounds `ξ + α ρ` at the orders `α ∈ A` (Eqs. 6 and 7). -/
noncomputable def concentratedDivergence (A : Set ℝ) : GradedDivergence.{u} (ℝ≥0∞ × ℝ≥0∞) :=
  fun b ↦ renyiCurve (concentratedLine A b)

/-- `(ξ, ρ)`-zCDP: Rényi bounds `ξ + α ρ` at every order (Eq. 6). -/
noncomputable abbrev zcdpDivergence : GradedDivergence.{u} (ℝ≥0∞ × ℝ≥0∞) :=
  concentratedDivergence (Ioi 1)

/-- `(ρ, ω)`-tCDP: Rényi bounds `α ρ` at the orders `1 < α < ω` (Eq. 7). -/
noncomputable def tcdpDivergence (ω : ℝ) : GradedDivergence.{u} ℝ≥0∞ :=
  fun ρ ↦ concentratedDivergence (Ioo 1 ω) (0, ρ)

variable {A : Set ℝ} {b : ℝ≥0∞ × ℝ≥0∞} {ξ ρ : ℝ≥0∞} {ω : ℝ} {μ ν : Measure X}

theorem concentratedDivergence_of_forall
    (h : ∀ α : Ioi (1 : ℝ), (α : ℝ) ∈ A → renyiDivergence α (b.1 + ENNReal.ofReal α * b.2) μ ν) :
    concentratedDivergence A b μ ν := fun α ↦ by
  by_cases hα : (α : ℝ) ∈ A
  · simpa [concentratedLine, hα] using h α hα
  · simpa [concentratedLine, hα] using renyiDivergence_top α.2 μ ν

/-- Point masses with ordered masses are within budget zero. -/
theorem concentratedDivergence_zero_smul_dirac {a a' : ℝ≥0∞} (h : a ≤ a') (ha' : a' ≤ 1) :
    concentratedDivergence A 0 (a • dirac PUnit.unit.{u + 1}) (a' • dirac PUnit.unit) :=
  concentratedDivergence_of_forall fun α _ ↦ by
    simpa using renyiDivergence_zero_smul_dirac α.2 h ha'

theorem concentratedDivergence_iff (hA : A ⊆ Ioi 1) :
    concentratedDivergence A (ξ, ρ) μ ν ↔
      ∀ α ∈ A, renyiDivergence α (ξ + ENNReal.ofReal α * ρ) μ ν :=
  ⟨fun h α hα ↦ by simpa [concentratedLine, hα] using h ⟨α, hA hα⟩,
    fun h ↦ concentratedDivergence_of_forall fun α hα ↦ h α hα⟩

theorem zcdpDivergence_iff :
    zcdpDivergence (ξ, ρ) μ ν ↔ ∀ α, 1 < α → renyiDivergence α (ξ + ENNReal.ofReal α * ρ) μ ν :=
  concentratedDivergence_iff subset_rfl

theorem tcdpDivergence_iff :
    tcdpDivergence ω ρ μ ν ↔ ∀ α, 1 < α → α < ω → renyiDivergence α (ENNReal.ofReal α * ρ) μ ν :=
  (concentratedDivergence_iff Ioo_subset_Ioi_self).trans (by simp [and_imp])

/-! ## Instances -/

variable (A ω)

instance isGraded_concentrated : (concentratedDivergence.{u} A).IsGraded where
  mono _ _ hb _ _ _ _ _ _ h := IsGraded.mono (D := renyiCurve) (concentratedLine_mono A hb) h
  top μ ν _ _ := by
    change renyiCurve _ μ ν
    rw [concentratedLine_top]
    exact IsGraded.top μ ν

instance isReflexive_concentrated : (concentratedDivergence.{u} A).IsReflexive where
  refl μ _ := concentratedDivergence_of_forall fun _ _ ↦ by simpa using IsReflexive.refl μ

/-- Concentrated budgets add, since lines do (Thms. 4.12 and 4.13). -/
instance isComposable_concentrated : (concentratedDivergence.{u} A).IsComposable where
  comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hκ := by
    simpa only [concentratedDivergence, concentratedLine_add] using
      IsComposable.comp (D := renyiCurve) h hκ

instance isZeroLeft_concentrated : (concentratedDivergence.{u} A).IsZeroLeft where
  zero_left _ _ _ ν _ := IsZeroLeft.zero_left (D := renyiCurve) _ ν

instance isLeftContinuous_concentrated : (concentratedDivergence.{u} A).IsLeftContinuous where
  iSup_left _ _ _ _ _ hμ ν _ h := IsLeftContinuous.iSup_left (D := renyiCurve) _ hμ ν h

/-- A bound at every larger budget is one at the budget: raise the shift `ξ`. -/
instance isBudgetClosed_concentrated : (concentratedDivergence.{u} A).IsBudgetClosed where
  of_forall_gt {b} _ _ _ _ _ _ h := concentratedDivergence_of_forall fun α hα ↦
    IsBudgetClosed.of_forall_gt fun t ht ↦ by
      obtain ⟨ξ', hξ', rfl⟩ := exists_lt_add_of_lt_add ht
      simpa [concentratedLine, hα] using h (ξ', b.2) (Prod.mk_lt_mk_iff_left.2 hξ') α

instance isGraded_tcdp : (tcdpDivergence.{u} ω).IsGraded where
  mono _ _ hb _ _ _ _ _ _ h :=
    IsGraded.mono (D := concentratedDivergence _) (Prod.mk_le_mk.2 ⟨le_rfl, hb⟩) h
  top μ ν _ _ := by
    change renyiCurve _ μ ν
    rw [concentratedLine_snd_top]
    exact IsGraded.top μ ν

instance isReflexive_tcdp : (tcdpDivergence.{u} ω).IsReflexive where
  refl μ _ := IsReflexive.refl (D := concentratedDivergence _) μ

/-- tCDP budgets add (Thm. 4.13). -/
instance isComposable_tcdp : (tcdpDivergence.{u} ω).IsComposable where
  comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hκ := by
    simpa [tcdpDivergence] using IsComposable.comp (D := concentratedDivergence _) h hκ

instance isZeroLeft_tcdp : (tcdpDivergence.{u} ω).IsZeroLeft where
  zero_left _ _ _ ν _ := IsZeroLeft.zero_left (D := concentratedDivergence _) _ ν

instance isLeftContinuous_tcdp : (tcdpDivergence.{u} ω).IsLeftContinuous where
  iSup_left _ _ _ _ _ hμ ν _ h :=
    IsLeftContinuous.iSup_left (D := concentratedDivergence _) _ hμ ν h

/-- A bound at every larger budget is one at the budget: at order `α`, `ρ' = t / α`. -/
instance isBudgetClosed_tcdp : (tcdpDivergence.{u} ω).IsBudgetClosed where
  of_forall_gt {ρ} _ _ _ _ _ _ h := concentratedDivergence_of_forall fun α hα ↦
    IsBudgetClosed.of_forall_gt fun t ht ↦ by
      have h0 : ENNReal.ofReal α ≠ 0 := by simpa using zero_lt_one.trans α.2
      have hρ : ρ < t / ENNReal.ofReal α :=
        (ENNReal.lt_div_iff_mul_lt (.inl h0) (.inl ENNReal.ofReal_ne_top)).2
          (by simpa [mul_comm] using ht)
      simpa [concentratedLine, hα, ENNReal.mul_div_cancel h0 ENNReal.ofReal_ne_top] using
        h _ hρ α

variable {A}

/-! ## Concentrated codensity liftings -/

/-- A curve lifting along the lines is a concentrated lifting. -/
theorem codensity_concentrated_of_renyiCurve {R : X → Y → ℝ≥0∞ × ℝ≥0∞} {μ : Measure X}
    {ν : Measure Y}
    (h : renyiCurve.codensity (concentratedLine A b) (fun x y ↦ concentratedLine A (R x y)) μ ν) :
    (concentratedDivergence A).codensity b R μ ν := by
  intro I _ c _ k l _ _ hkl
  change renyiCurve _ _ _
  rw [concentratedLine_add]
  rcases eq_or_ne (concentratedLine A b + concentratedLine A c) ⊤ with htop | hlt
  · exact htop ▸ fun α ↦ renyiDivergence_top α.2 _ _
  · exact h (lt_top_iff_ne_top.2 hlt) fun x y ↦ concentratedLine_add A (R x y) c ▸ hkl x y

/-- Rényi liftings at every order of `A` give a concentrated lifting (Rocq `gcf_zCDP_iff`,
`gcf_tCDP_iff`, one direction). -/
theorem codensity_concentrated_of_forall {R : X → Y → ℝ≥0∞ × ℝ≥0∞} {μ : Measure X}
    {ν : Measure Y}
    (h : ∀ α ∈ A, (renyiDivergence α).codensity (b.1 + ENNReal.ofReal α * b.2)
      (fun x y ↦ (R x y).1 + ENNReal.ofReal α * (R x y).2) μ ν) :
    (concentratedDivergence A).codensity b R μ ν := by
  refine codensity_concentrated_of_renyiCurve (codensity_renyiCurve_iff.2 fun α ↦ ?_)
  by_cases hα : (α : ℝ) ∈ A
  · simpa [concentratedLine, hα] using h α hα
  · intro I _ c hc
    simp [concentratedLine, hα] at hc

theorem codensity_concentrated_rel_of_forall {S : X → Y → Prop} {μ : Measure X} {ν : Measure Y}
    (h : ∀ α ∈ A, (codensity (renyiDivergence α)).Rel (ξ + ENNReal.ofReal α * ρ) S μ ν) :
    (codensity (concentratedDivergence A)).Rel (ξ, ρ) S μ ν :=
  codensity_concentrated_of_forall fun α hα ↦ by
    have hR (x : X) (y : Y) : (relCost S x y : ℝ≥0∞ × ℝ≥0∞).1 +
        ENNReal.ofReal α * (relCost S x y : ℝ≥0∞ × ℝ≥0∞).2 = relCost S x y := by
      by_cases hS : S x y <;> simp [hS]
    simp only [hR]
    exact h α hα

end GradedDivergence
