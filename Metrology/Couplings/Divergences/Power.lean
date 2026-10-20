module

public import Metrology.Couplings.Divergences.Concentrated

/-! # Power and χ² divergences

Power budgets (`ℝ≥0∞` with `a + b + a b`), and power/χ² divergences and liftings as Rényi
regradings along `toRenyi`; main results `powerLifting_bind`, `chi2Lifting_bind` (Rocq `regrade.v`).
-/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting
open scoped ENNReal

/-- The Rényi order `2` is above one. -/
instance fact_one_lt_two_real : Fact (1 < (2 : ℝ)) :=
  ⟨one_lt_two⟩

namespace GradedDivergence

/-! ## Power budgets -/

/-- Budgets of power divergences: `ℝ≥0∞` with `a ⊕ b = a + b + a b`. Along `c ↦ log (1 + c)` this
is ordinary addition (`PowerBudget.log`), which is why power divergences are regraded Rényi. -/
def PowerBudget : Type :=
  ℝ≥0∞

namespace PowerBudget

/-- Power budgets are ordered as in `ℝ≥0∞`. -/
noncomputable instance instCompleteLinearOrder : CompleteLinearOrder PowerBudget :=
  inferInstanceAs (CompleteLinearOrder ℝ≥0∞)

/-- There are at least two power budgets. -/
instance instNontrivial : Nontrivial PowerBudget :=
  inferInstanceAs (Nontrivial ℝ≥0∞)

/-- A budget in `ℝ≥0∞` as a power budget. -/
noncomputable def ofENNReal : ℝ≥0∞ ≃o PowerBudget :=
  OrderIso.refl _

/-- A power budget as a budget in `ℝ≥0∞`. -/
noncomputable def toENNReal : PowerBudget ≃o ℝ≥0∞ :=
  OrderIso.refl _

@[simp]
theorem toENNReal_ofENNReal (c : ℝ≥0∞) : toENNReal (ofENNReal c) = c :=
  rfl

@[simp]
theorem ofENNReal_toENNReal (c : PowerBudget) : ofENNReal (toENNReal c) = c :=
  rfl

/-- The zero power budget is `0`. -/
noncomputable instance instZero : Zero PowerBudget :=
  ⟨ofENNReal 0⟩

/-- Power budgets compose as `a + b + a b` (Barthe–Olmedo's `γ = 1` law). -/
noncomputable instance instAdd : Add PowerBudget :=
  ⟨fun a b ↦ ofENNReal (toENNReal a + toENNReal b + toENNReal a * toENNReal b)⟩

@[simp]
theorem toENNReal_zero : toENNReal 0 = 0 :=
  rfl

@[simp]
theorem toENNReal_add (a b : PowerBudget) :
    toENNReal (a + b) = toENNReal a + toENNReal b + toENNReal a * toENNReal b :=
  rfl

@[simp]
theorem toENNReal_top : toENNReal ⊤ = ⊤ :=
  rfl

@[simp]
theorem ofENNReal_top : ofENNReal ⊤ = ⊤ :=
  rfl

/-- Power budgets form a monoid, isomorphic to `[1, ⊤]` under multiplication along `c ↦ 1 + c`. -/
noncomputable instance instAddCommMonoid : AddCommMonoid PowerBudget where
  add_assoc a b c := toENNReal.injective <| by simp only [toENNReal_add]; ring
  zero_add a := toENNReal.injective <| by simp
  add_zero a := toENNReal.injective <| by simp
  add_comm a b := toENNReal.injective <| by simp only [toENNReal_add]; ring
  nsmul := nsmulRec

/-- Composing power budgets is monotone. -/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid PowerBudget where
  add_le_add_left a b h c := toENNReal.le_iff_le.1 <| by
    have h := toENNReal.monotone h
    simp only [toENNReal_add]
    gcongr

/-- Every larger power budget is reached by adding `(b - a) / (1 + a)`. -/
instance instCanonicallyOrderedAdd : CanonicallyOrderedAdd PowerBudget where
  exists_add_of_le {a b} h := by
    refine ⟨ofENNReal ((toENNReal b - toENNReal a) / (1 + toENNReal a)), toENNReal.injective ?_⟩
    have h := toENNReal.monotone h
    rcases eq_or_ne (toENNReal a) ⊤ with ha | ha
    · simp_all
    rw [toENNReal_add, toENNReal_ofENNReal, add_assoc, ← one_add_mul,
      ENNReal.mul_div_cancel (by simp) (by simpa using ha), add_tsub_cancel_of_le h]
  le_add_self a b := toENNReal.le_iff_le.1 <| by
    simpa only [toENNReal_add, add_assoc, add_comm (toENNReal b)] using le_self_add
  le_self_add a b := toENNReal.le_iff_le.1 <| by
    simpa only [toENNReal_add, add_assoc] using le_self_add

/-! ## Composing a budget `k` times, and cancellation -/

/-- `k` composed budgets `c` multiply `1 + c` out `k` times. -/
theorem one_add_toENNReal_nsmul (k : ℕ) (c : PowerBudget) :
    1 + toENNReal (k • c) = (1 + toENNReal c) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, toENNReal_add, pow_succ, ← ih]; ring

/-- Finite power budgets cancel on the left. -/
theorem isAddLeftRegular_of_ne_top {c : PowerBudget} (hc : toENNReal c ≠ ⊤) :
    IsAddLeftRegular c := fun a b h ↦ by
  have key (x : PowerBudget) :
      toENNReal (c + x) = toENNReal c + (1 + toENNReal c) * toENNReal x := by
    rw [toENNReal_add]
    ring
  have h := congrArg toENNReal h
  rw [key, key] at h
  exact toENNReal.injective <| (ENNReal.mul_right_inj (by simp) (by simpa using hc)).1
    ((ENNReal.add_right_inj hc).1 h)

/-- A real power budget, `0` below `0`. -/
noncomputable def ofReal (c : ℝ) : PowerBudget :=
  ofENNReal (ENNReal.ofReal c)

@[simp]
theorem toENNReal_ofReal (c : ℝ) : toENNReal (ofReal c) = ENNReal.ofReal c :=
  rfl

/-- Real power budgets cancel on the left. -/
theorem isAddLeftRegular_ofReal (c : ℝ) : IsAddLeftRegular (ofReal c) :=
  isAddLeftRegular_of_ne_top (by simp)

/-- `k` composed budgets `c` are `(1 + c)^k - 1`. -/
theorem nsmul_ofReal {c : ℝ} (hc : 0 ≤ c) (k : ℕ) : k • ofReal c = ofReal ((1 + c) ^ k - 1) := by
  apply toENNReal.injective
  rw [toENNReal_ofReal, ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add zero_le_one hc, ENNReal.ofReal_one, ← toENNReal_ofReal c,
    ← one_add_toENNReal_nsmul, ENNReal.add_sub_cancel_left ENNReal.one_ne_top]

/-! ## Log coordinates -/

theorem log_one_add_nonneg (c : PowerBudget) : 0 ≤ ENNReal.log (1 + toENNReal c) :=
  ENNReal.zero_le_log_iff.2 le_self_add

/-- The additive budget `log (1 + c)`: power budgets compose as their logs add. -/
noncomputable def log : PowerBudget ≃+o ℝ≥0∞ where
  toFun c := (ENNReal.log (1 + toENNReal c)).toENNReal
  invFun ρ := ofENNReal (expBudget ρ - 1)
  left_inv c := by
    dsimp only
    rw [expBudget, EReal.coe_toENNReal (log_one_add_nonneg c), ENNReal.exp_log,
      ENNReal.add_sub_cancel_left ENNReal.one_ne_top, ofENNReal_toENNReal]
  right_inv ρ := by
    simp only [toENNReal_ofENNReal]
    rw [add_tsub_cancel_of_le (one_le_expBudget ρ), expBudget, EReal.log_exp, EReal.toENNReal_coe]
  map_add' a b := by
    rw [toENNReal_add, show 1 + (toENNReal a + toENNReal b + toENNReal a * toENNReal b) =
      (1 + toENNReal a) * (1 + toENNReal b) by ring, ENNReal.log_mul_add,
      EReal.toENNReal_add (log_one_add_nonneg a) (log_one_add_nonneg b)]
  map_le_map_iff' {a b} := by
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal (log_one_add_nonneg a),
      EReal.coe_toENNReal (log_one_add_nonneg b), ENNReal.log_le_log_iff,
      ENNReal.add_le_add_iff_left ENNReal.one_ne_top, toENNReal.le_iff_le]

theorem log_apply (c : PowerBudget) : log c = (ENNReal.log (1 + toENNReal c)).toENNReal :=
  rfl

/-- A real power budget `c ≥ 0` has log coordinate `log (1 + c)`. -/
theorem log_ofReal {c : ℝ} (hc : 0 ≤ c) : log (ofReal c) = ENNReal.ofReal (Real.log (1 + c)) := by
  rw [log_apply, toENNReal_ofReal, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hc,
    ENNReal.log_ofReal_of_pos (by positivity), EReal.real_coe_toENNReal]

theorem coe_log (c : PowerBudget) : (log c : EReal) = ENNReal.log (1 + toENNReal c) :=
  EReal.coe_toENNReal (log_one_add_nonneg c)

theorem expBudget_log (c : PowerBudget) : expBudget (log c) = 1 + toENNReal c := by
  rw [expBudget, coe_log, ENNReal.exp_log]

/-! ## Rényi coordinates -/

variable {α : ℝ} {c : PowerBudget}

/-- The Rényi budget `log (1 + c) / (α - 1)` of a power budget `c`, the inverse of
`ρ ↦ e^{(α - 1) ρ} - 1` (Rocq `power_phi`). -/
noncomputable def toRenyi (α : ℝ) (c : PowerBudget) : ℝ≥0∞ :=
  (ENNReal.ofReal (α - 1))⁻¹ * log c

theorem toRenyi_mono : Monotone (toRenyi α) := fun _ _ h ↦
  mul_right_mono (OrderHomClass.mono log h)

@[simp]
theorem toRenyi_zero : toRenyi α 0 = 0 := by
  simp [toRenyi]

@[simp]
theorem toRenyi_top : toRenyi α ⊤ = ⊤ := by
  simp [toRenyi, ENNReal.mul_top]

/-- Power budgets compose as Rényi budgets add (Rocq `power_phi_sum`). -/
theorem toRenyi_add (a b : PowerBudget) : toRenyi α (a + b) = toRenyi α a + toRenyi α b := by
  simp [toRenyi, mul_add]

theorem ofReal_mul_toRenyi (hα : 1 < α) (c : PowerBudget) :
    ENNReal.ofReal (α - 1) * toRenyi α c = log c := by
  rw [toRenyi, ← mul_assoc, ENNReal.mul_inv_cancel (by simpa using hα) ENNReal.ofReal_ne_top,
    one_mul]

theorem toRenyi_lt_top (hα : 1 < α) (hc : c < ⊤) : toRenyi α c < ⊤ :=
  ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by simpa using hα))
    (map_top log ▸ log.strictMono hc)

/-- At order `2` the Rényi budget is `log (1 + c)` itself. -/
theorem toRenyi_two (c : PowerBudget) : toRenyi 2 c = log c := by
  norm_num [toRenyi]

theorem toRenyi_surjective (hα : 1 < α) : Function.Surjective (toRenyi α) := fun ρ ↦ by
  refine ⟨log.symm (ENNReal.ofReal (α - 1) * ρ), ?_⟩
  rw [toRenyi, OrderAddMonoidIso.apply_symm_apply, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simpa using hα) ENNReal.ofReal_ne_top, one_mul]

/-- A Rényi budget above that of `c` is that of a larger power budget. -/
theorem exists_lt_toRenyi_eq (hα : 1 < α) {ρ : ℝ≥0∞} (h : toRenyi α c < ρ) :
    ∃ c', c < c' ∧ toRenyi α c' = ρ := by
  obtain ⟨c', rfl⟩ := toRenyi_surjective hα ρ
  exact ⟨c', lt_of_not_ge fun hc ↦ (toRenyi_mono hc).not_gt h, rfl⟩

/-- At `toRenyi α c` the Rényi moment threshold is `1 + c`. -/
theorem renyiThresh_toRenyi (hα : 1 < α) (c : PowerBudget) :
    renyiThresh α (toRenyi α c) = ((1 + toENNReal c : ℝ≥0∞) : EReal) := by
  rw [renyiThresh, ofReal_mul_toRenyi hα, expBudget_log]

end PowerBudget

open PowerBudget

/-! ## Power divergences -/

/-- The power divergence bound `e^{(α - 1) D_α(μ ‖ ν)} - 1 ≤ c`: the Rényi divergence read along
`c ↦ log (1 + c) / (α - 1)` (Rocq `GCF_power`). -/
noncomputable def powerDivergence (α : ℝ) : GradedDivergence.{u} PowerBudget :=
  (renyiDivergence α).comap (toRenyi α)

/-- The χ² divergence bound `∫ (dμ/dν)² dν - 1 ≤ c`, the power divergence of order `2` (Rocq
`GCF_chi2`). -/
noncomputable abbrev chi2Divergence : GradedDivergence.{u} PowerBudget :=
  powerDivergence 2

variable {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
  [MeasurableSpace Y'] {α : ℝ} {c : PowerBudget} {μ ν : Measure X}

/-- A power divergence bound is the Rényi bound at `log (1 + c) / (α - 1)`. -/
theorem powerDivergence_iff_renyi : powerDivergence α c μ ν ↔ renyiDivergence α (toRenyi α c) μ ν :=
  Iff.rfl

/-- A power divergence bound is the `α`-th moment bound `∫ (dμ/dν)^α dν ≤ 1 + c`. -/
theorem powerDivergence_iff (hα : 1 < α) :
    powerDivergence α c μ ν ↔ fDiv (· ^ α) μ ν ≤ ((1 + toENNReal c : ℝ≥0∞) : EReal) := by
  rw [powerDivergence_iff_renyi, renyiDivergence_iff, renyiThresh_toRenyi hα]

/-- A χ² bound `c` is the Rényi-2 bound `log (1 + c)` (Rocq `chi2_is_renyi2`). -/
theorem chi2Divergence_iff_renyi : chi2Divergence c μ ν ↔ renyiDivergence 2 (log c) μ ν := by
  rw [← toRenyi_two]
  rfl

/-- A χ² bound is the second-moment bound `∫ (dμ/dν)² dν ≤ 1 + c`. -/
theorem chi2Divergence_iff :
    chi2Divergence c μ ν ↔ fDiv (· ^ (2 : ℝ)) μ ν ≤ ((1 + toENNReal c : ℝ≥0∞) : EReal) :=
  powerDivergence_iff one_lt_two

/-- A real power divergence bound is the `α`-th moment bound `∫ (dμ/dν)^α dν ≤ 1 + c`. -/
theorem powerDivergence_ofReal_iff (hα : 1 < α) {c : ℝ} (hc : 0 ≤ c) :
    powerDivergence α (ofReal c) μ ν ↔ fDiv (· ^ α) μ ν ≤ ((1 + c : ℝ) : EReal) := by
  rw [powerDivergence_iff hα, toENNReal_ofReal, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one hc, EReal.coe_ennreal_ofReal, max_eq_left (by linarith)]

/-! ## Divergence instances -/

section Instances

variable (α) [hα : Fact (1 < α)]

/-- Power divergences are graded: `toRenyi` is monotone and keeps `⊤`. -/
instance isGraded_power : (powerDivergence.{u} α).IsGraded :=
  isGraded_comap_of_map_top toRenyi_mono toRenyi_top

/-- Power divergences are reflexive. -/
instance isReflexive_power : (powerDivergence.{u} α).IsReflexive :=
  isReflexive_comap zero_le

/-- Power budgets compose as `c₁ + c₂ + c₁ c₂`, since Rényi budgets add. -/
instance isComposable_power : (powerDivergence.{u} α).IsComposable :=
  isComposable_comap fun b c ↦ (toRenyi_add b c).ge

/-- The zero measure is within every power budget of every measure. -/
instance isZeroLeft_power : (powerDivergence.{u} α).IsZeroLeft :=
  GradedDivergence.isZeroLeft_comap

/-- Power divergences are left continuous (Rocq `GCFamLim_power`). -/
instance isLeftContinuous_power : (powerDivergence.{u} α).IsLeftContinuous :=
  GradedDivergence.isLeftContinuous_comap

/-- Power divergences are monotone in the right measure. -/
instance isRightMonotone_power : (powerDivergence.{u} α).IsRightMonotone :=
  GradedDivergence.isRightMonotone_comap

/-- Power divergences are antitone in the left measure. -/
instance isLeftAntitone_power : (powerDivergence.{u} α).IsLeftAntitone :=
  GradedDivergence.isLeftAntitone_comap

/-- Power divergences are budget closed, since every larger Rényi budget is a power budget. -/
instance isBudgetClosed_power : (powerDivergence.{u} α).IsBudgetClosed where
  of_forall_gt h := IsBudgetClosed.of_forall_gt (D := renyiDivergence α) fun _ hρ ↦ by
    obtain ⟨c', hc, rfl⟩ := exists_lt_toRenyi_eq hα.out hρ
    exact h c' hc

end Instances

/-! ## Power liftings -/

/-- The power lifting: the Rényi codensity lifting read along `c ↦ log (1 + c) / (α - 1)`
(Rocq `GCF_power`). -/
noncomputable def powerLifting (α : ℝ) : GradedLifting.{u} PowerBudget :=
  (codensity (renyiDivergence α)).comap (toRenyi α)

/-- The χ² lifting, the power lifting of order `2` (Rocq `GCF_chi2`). -/
noncomputable abbrev chi2Lifting : GradedLifting.{u} PowerBudget :=
  powerLifting 2

variable {R : X → Y → PowerBudget} {S : X → Y → Prop} {ν : Measure Y}

/-- A power lifting of a relation at `c` is a Rényi lifting at `toRenyi α c`. -/
theorem powerLifting_rel_iff :
    (powerLifting α).Rel c S μ ν ↔ (codensity (renyiDivergence α)).Rel (toRenyi α c) S μ ν :=
  comap_rel_iff toRenyi_zero toRenyi_top

/-- A χ² lifting at `c` is a Rényi-2 lifting at `log (1 + c)` (Rocq `chi2_is_renyi2`). -/
theorem chi2Lifting_rel_iff :
    chi2Lifting.Rel c S μ ν ↔ (codensity (renyiDivergence 2)).Rel (log c) S μ ν := by
  rw [← toRenyi_two]
  exact powerLifting_rel_iff

/-- The power lifting is the codensity lifting of the power divergence: `toRenyi α` is an
additive bijection, so the two families of tests agree. -/
theorem powerLifting_iff_codensity [hα : Fact (1 < α)] [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] :
    powerLifting α c R μ ν ↔ (powerDivergence α).codensity c R μ ν := by
  refine ⟨comap_codensity_le toRenyi_add, fun h I _ ρ hρ k l _ _ hkl ↦ ?_⟩
  -- each Rényi slack `ρ` is `toRenyi α c'`, so the Rényi test is a power test at a finite `c'`
  obtain ⟨c', rfl⟩ := toRenyi_surjective hα.out ρ
  simp only [← toRenyi_add] at hρ hkl ⊢
  refine h (lt_of_not_ge fun hc ↦ ?_) hkl
  simp [top_le_iff.1 hc] at hρ

/-! ## Lifting instances -/

section LiftingInstances

variable (α) [hα : Fact (1 < α)]

/-- Power liftings are lawful, since `toRenyi α` is additive. -/
instance isLawful_powerLifting : (powerLifting.{u} α).IsLawful :=
  isLawful_comap toRenyi_mono toRenyi_add fun _ ↦ toRenyi_lt_top hα.out

/-- Power liftings bind (Rocq `GBL_power`). -/
instance hasBind_powerLifting : (powerLifting.{u} α).HasBind :=
  hasBind_comap (L := codensity _) toRenyi_top

/-- Power liftings are reflexive (Rocq `GBL_power_head_diag`). -/
instance isReflexive_powerLifting : (powerLifting.{u} α).IsReflexive :=
  GradedLifting.isReflexive_comap toRenyi_zero toRenyi_top

/-- The zero measure on the left lifts against everything. -/
instance isZeroLeft_powerLifting : (powerLifting.{u} α).IsZeroLeft :=
  GradedLifting.isZeroLeft_comap

/-- Power liftings are left continuous. -/
instance isLeftContinuous_powerLifting : (powerLifting.{u} α).IsLeftContinuous :=
  GradedLifting.isLeftContinuous_comap

/-- Power liftings are support local (Rocq `power_head_supp`). -/
instance isSupportLocal_powerLifting : (powerLifting.{u} α).IsSupportLocal :=
  isSupportLocal_comap (L := codensity _) toRenyi_top

/-- Power liftings relate everything at `⊤`. -/
instance isTopAbsorbing_powerLifting : (powerLifting.{u} α).IsTopAbsorbing :=
  isTopAbsorbing_comap (L := codensity _) toRenyi_top

/-- A power lifting of equality gives the power divergence. -/
instance isSound_powerLifting : (powerLifting.{u} α).IsSound (powerDivergence α) where
  sound h := codensity_sound (D := renyiDivergence α) (powerLifting_rel_iff.1 h)

/-- The power divergence gives a power lifting of equality. -/
instance isComplete_powerLifting : (powerLifting.{u} α).IsComplete (powerDivergence α) where
  complete h := powerLifting_rel_iff.2 (codensity_complete h)

/-- Power liftings are budget closed, since every larger Rényi budget is a power budget. -/
instance isBudgetClosed_powerLifting : (powerLifting.{u} α).IsBudgetClosed where
  of_forall_gt h := GradedLifting.IsBudgetClosed.of_forall_gt (L := codensity _) fun _ hρ ↦ by
    obtain ⟨c', hc, rfl⟩ := exists_lt_toRenyi_eq hα.out hρ
    exact h c' hc

end LiftingInstances

/-! ## Bind laws -/

/-- Power liftings at `c₁` and `c₂` compose to `c₁ + c₂ + c₁ c₂`, Barthe and Olmedo's `γ = 1`
law (Rocq `power_lift_dbind`). -/
theorem powerLifting_bind [Fact (1 < α)] {c₁ c₂ : ℝ≥0∞} {S' : X' → Y' → Prop}
    (h : (powerLifting α).Rel (ofENNReal c₁) S μ ν) {f : X → Measure X'} {g : Y → Measure Y'}
    [∀ x, IsSubProbabilityMeasure (f x)] [∀ y, IsSubProbabilityMeasure (g y)]
    (hk : ∀ x y, S x y → (powerLifting α).Rel (ofENNReal c₂) S' (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    (powerLifting α).Rel (ofENNReal (c₁ + c₂ + c₁ * c₂)) S' (μ.bind f) (ν.bind g) := by
  rcases eq_or_ne c₂ ⊤ with rfl | hc
  · rw [show ofENNReal (c₁ + ⊤ + c₁ * ⊤) = ⊤ by simp]
    exact IsTopAbsorbing.top _ _ _
  exact HasBind.bind_rel_fun (c := ofENNReal c₂) (lt_top_iff_ne_top.2 hc) h hk hf hg

/-- χ² liftings at `c₁` and `c₂` compose to `c₁ + c₂ + c₁ c₂` (Barthe–Olmedo, Thm. 2; Rocq
`chi2_lift_dbind`). -/
theorem chi2Lifting_bind {c₁ c₂ : ℝ≥0∞} {S' : X' → Y' → Prop}
    (h : chi2Lifting.Rel (ofENNReal c₁) S μ ν) {f : X → Measure X'} {g : Y → Measure Y'}
    [∀ x, IsSubProbabilityMeasure (f x)] [∀ y, IsSubProbabilityMeasure (g y)]
    (hk : ∀ x y, S x y → chi2Lifting.Rel (ofENNReal c₂) S' (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    chi2Lifting.Rel (ofENNReal (c₁ + c₂ + c₁ * c₂)) S' (μ.bind f) (ν.bind g) :=
  powerLifting_bind h hk hf hg

end GradedDivergence

/-! ## Homomorphisms of power liftings -/

open GradedDivergence PowerBudget

namespace LiftingHom

/-- A power lifting is a Rényi lifting along `c ↦ log (1 + c) / (α - 1)`. -/
noncomputable def powerToRenyi (α : ℝ) :
    LiftingHom (powerLifting.{u} α) (codensity (renyiDivergence.{u} α)) :=
  comapHom toRenyi_mono

end LiftingHom
