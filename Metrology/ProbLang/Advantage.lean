module

public import Metrology.ProbLang.Exec
public import Metrology.Couplings.AdditiveCouplings

@[expose] public section

/-!
# Distinguishing advantage

`advantage X Y` is the worst-case total variation distance between the outputs of `X` and `Y`;
Clutch's point-mass `|Pr[X = v] − Pr[Y = v]|` vanishes on diffuse outputs, so we use TV instead.
-/

namespace ProbLang
open MeasureTheory

/-! ## Total variation distance -/

variable {α : Type _} [MeasurableSpace α] {μ ν : Measure α} {ε : ENNReal} {S : Set α}

/-- Total variation distance: the supremum, over measurable sets, of the mass difference. -/
noncomputable def tvDist (μ ν : Measure α) : ENNReal :=
  ⨆ S, ⨆ (_ : MeasurableSet S), (μ S - ν S) ⊔ (ν S - μ S)

/-- A bound on every measurable set's mass difference bounds `tvDist`. -/
theorem tvDist_le
    (h : ∀ S, MeasurableSet S → (μ S - ν S) ⊔ (ν S - μ S) ≤ ε) : tvDist μ ν ≤ ε :=
  iSup_le fun S ↦ iSup_le (h S)

/-- The mass difference of a measurable set is at most `tvDist`. -/
theorem le_tvDist (hS : MeasurableSet S) :
    (μ S - ν S) ⊔ (ν S - μ S) ≤ tvDist μ ν :=
  le_iSup₂_of_le S hS le_rfl

/-- `tvDist` is symmetric. -/
theorem tvDist_comm (μ ν : Measure α) : tvDist μ ν = tvDist ν μ :=
  iSup_congr fun _ ↦ iSup_congr fun _ ↦ sup_comm _ _

/-- A measure is at distance zero from itself. -/
@[simp] theorem tvDist_self (μ : Measure α) : tvDist μ μ = 0 := by
  simp [tvDist]

/-- Equal measures are at distance zero. -/
theorem tvDist_of_eq (h : μ = ν) : tvDist μ ν = 0 := by
  rw [h, tvDist_self]

/-- The mass of a measurable set under `μ` is at most its mass under `ν` plus `tvDist μ ν`. -/
theorem measure_le_add_tvDist (hS : MeasurableSet S) :
    μ S ≤ ν S + tvDist μ ν :=
  tsub_le_iff_left.mp (le_sup_left.trans (le_tvDist hS))

/-- `tvDist` satisfies the triangle inequality. -/
theorem tvDist_triangle (μ ν ρ : Measure α) :
    tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  refine tvDist_le fun S hS ↦ sup_le ?_ ?_
  · refine tsub_le_iff_right.mpr ?_
    calc μ S ≤ ν S + tvDist μ ν := measure_le_add_tvDist hS
      _ ≤ (ρ S + tvDist ν ρ) + tvDist μ ν := by gcongr; exact measure_le_add_tvDist hS
      _ = tvDist μ ν + tvDist ν ρ + ρ S := by ring
  · refine tsub_le_iff_right.mpr ?_
    calc ρ S ≤ ν S + tvDist ρ ν := measure_le_add_tvDist hS
      _ ≤ (μ S + tvDist ν μ) + tvDist ρ ν := by gcongr; exact measure_le_add_tvDist hS
      _ = tvDist μ ν + tvDist ν ρ + μ S := by
          rw [tvDist_comm ν μ, tvDist_comm ρ ν]; ring

/-! ## Bounds from additive couplings -/

/-- Equality couplings within `ε` in both directions bound the total variation distance by `ε`. -/
theorem tvDist_le_of_addCoupl_eq
    (h₁ : AddCoupl ε {p : α × α | p.1 = p.2} μ ν)
    (h₂ : AddCoupl ε {p : α × α | p.1 = p.2} ν μ) :
    tvDist μ ν ≤ ε :=
  tvDist_le fun _ hS ↦ sup_le (tsub_le_iff_left.mpr (h₁.eq_elim hS))
    (tsub_le_iff_left.mpr (h₂.eq_elim hS))

/-! ## Advantage of programs -/

variable {rT : Type _} [LawfulProbLangℝ rT]

/-- The largest total variation distance between the outputs of `X` and `Y` over initial states. -/
noncomputable def advantage (X Y : Exp rT) : ENNReal :=
  ⨆ σ : State rT, tvDist (limExecV ⟨X, σ⟩) (limExecV ⟨Y, σ⟩)

/-- A uniform bound on the output distance bounds `advantage`. -/
theorem advantage_le {X Y : Exp rT}
    (h : ∀ σ, tvDist (limExecV ⟨X, σ⟩) (limExecV ⟨Y, σ⟩) ≤ ε) :
    advantage X Y ≤ ε := iSup_le h

/-- The output distance at any initial state is at most `advantage`. -/
theorem le_advantage (X Y : Exp rT) (σ : State rT) :
    tvDist (limExecV ⟨X, σ⟩) (limExecV ⟨Y, σ⟩) ≤ advantage X Y :=
  le_iSup (fun σ : State rT ↦ tvDist (limExecV ⟨X, σ⟩) (limExecV ⟨Y, σ⟩)) σ

/-- `advantage` is symmetric. -/
theorem advantage_comm (X Y : Exp rT) : advantage X Y = advantage Y X :=
  iSup_congr fun _ ↦ tvDist_comm _ _

/-- A program has no advantage over itself. -/
@[simp] theorem advantage_self (X : Exp rT) : advantage X X = 0 := by
  simp [advantage]

/-- `advantage` satisfies the triangle inequality. -/
theorem advantage_triangle (X Y Z : Exp rT) :
    advantage X Z ≤ advantage X Y + advantage Y Z :=
  advantage_le fun σ ↦
    (tvDist_triangle _ (limExecV ⟨Y, σ⟩) _).trans
      (add_le_add (le_advantage X Y σ) (le_advantage Y Z σ))

/-- Programs with equal output distributions at every state have no advantage over each other. -/
theorem advantage_eq_zero_of_limExecV_eq {X Y : Exp rT}
    (h : ∀ σ : State rT, limExecV (⟨X, σ⟩ : Cfg rT) = limExecV ⟨Y, σ⟩) :
    advantage X Y = 0 := by
  simp [advantage, tvDist_of_eq (h _)]

end ProbLang
