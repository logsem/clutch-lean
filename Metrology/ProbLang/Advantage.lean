module

public import Metrology.ProbLang.Exec
public import Metrology.Couplings.AdditiveCouplings

@[expose] public section

/-!
# Distinguishing advantage

Clutch's point-mass advantage `|Pr[X = v] − Pr[Y = v]|` vanishes on diffuse outputs, so we
use total variation distance, which agrees with it on discrete languages.
-/

namespace ProbLang
open MeasureTheory

variable {α : Type _} [MeasurableSpace α]

/-- Total variation distance: the largest mass difference of a measurable set. -/
noncomputable def tvDist (μ ν : Measure α) : ENNReal :=
  ⨆ S, ⨆ (_ : MeasurableSet S), (μ S - ν S) ⊔ (ν S - μ S)

theorem tvDist_le {μ ν : Measure α} {ε : ENNReal}
    (h : ∀ S, MeasurableSet S → (μ S - ν S) ⊔ (ν S - μ S) ≤ ε) : tvDist μ ν ≤ ε :=
  iSup_le fun S => iSup_le (h S)

theorem le_tvDist {μ ν : Measure α} {S : Set α} (hS : MeasurableSet S) :
    (μ S - ν S) ⊔ (ν S - μ S) ≤ tvDist μ ν :=
  le_iSup₂_of_le S hS le_rfl

theorem tvDist_comm (μ ν : Measure α) : tvDist μ ν = tvDist ν μ :=
  iSup_congr fun _ => iSup_congr fun _ => sup_comm _ _

@[simp] theorem tvDist_self (μ : Measure α) : tvDist μ μ = 0 := by
  simp [tvDist]

theorem tvDist_of_eq {μ ν : Measure α} (h : μ = ν) : tvDist μ ν = 0 := by
  rw [h, tvDist_self]

theorem measure_le_add_tvDist {μ ν : Measure α} {S : Set α} (hS : MeasurableSet S) :
    μ S ≤ ν S + tvDist μ ν :=
  tsub_le_iff_left.mp (le_sup_left.trans (le_tvDist hS))

theorem tvDist_triangle (μ ν ρ : Measure α) :
    tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  refine tvDist_le fun S hS => sup_le ?_ ?_
  · refine tsub_le_iff_right.mpr ?_
    calc μ S ≤ ν S + tvDist μ ν := measure_le_add_tvDist hS
      _ ≤ (ρ S + tvDist ν ρ) + tvDist μ ν := by gcongr; exact measure_le_add_tvDist hS
      _ = tvDist μ ν + tvDist ν ρ + ρ S := by ring
  · refine tsub_le_iff_right.mpr ?_
    calc ρ S ≤ ν S + tvDist ρ ν := measure_le_add_tvDist hS
      _ ≤ (μ S + tvDist ν μ) + tvDist ρ ν := by gcongr; exact measure_le_add_tvDist hS
      _ = tvDist μ ν + tvDist ν ρ + μ S := by
          rw [tvDist_comm ν μ, tvDist_comm ρ ν]; ring

/-- Equality couplings within `ε` in both directions bound the total variation distance by `ε`. -/
theorem tvDist_le_of_addCoupl_eq {ε : ENNReal} {μ ν : Measure α}
    (h₁ : AddCoupl ε {p : α × α | p.1 = p.2} μ ν)
    (h₂ : AddCoupl ε {p : α × α | p.1 = p.2} ν μ) :
    tvDist μ ν ≤ ε :=
  tvDist_le fun _ hS =>
    sup_le (tsub_le_iff_left.mpr (AddCoupl.eq_elim h₁ hS))
      (tsub_le_iff_left.mpr (AddCoupl.eq_elim h₂ hS))

variable {rT : Type _} [LawfulProbLangℝ rT]

/-- The largest total variation distance between the outputs of `X` and `Y` over initial states. -/
noncomputable def advantage (X Y : Exp rT) : ENNReal :=
  ⨆ σ : State rT, tvDist (limExecV ⟨X, σ⟩) (limExecV ⟨Y, σ⟩)

theorem advantage_le {X Y : Exp rT} {ε : ENNReal}
    (h : ∀ σ, tvDist (limExecV ⟨X, σ⟩) (limExecV ⟨Y, σ⟩) ≤ ε) :
    advantage X Y ≤ ε := iSup_le h

theorem le_advantage (X Y : Exp rT) (σ : State rT) :
    tvDist (limExecV ⟨X, σ⟩) (limExecV ⟨Y, σ⟩) ≤ advantage X Y :=
  le_iSup (fun σ : State rT => tvDist (limExecV ⟨X, σ⟩) (limExecV ⟨Y, σ⟩)) σ

theorem advantage_comm (X Y : Exp rT) : advantage X Y = advantage Y X :=
  iSup_congr fun _ => tvDist_comm _ _

@[simp] theorem advantage_self (X : Exp rT) : advantage X X = 0 := by
  simp [advantage]

theorem advantage_triangle (X Y Z : Exp rT) :
    advantage X Z ≤ advantage X Y + advantage Y Z :=
  advantage_le fun σ =>
    (tvDist_triangle _ (limExecV ⟨Y, σ⟩) _).trans
      (add_le_add (le_advantage X Y σ) (le_advantage Y Z σ))

theorem advantage_eq_zero_of_limExecV_eq {X Y : Exp rT}
    (h : ∀ σ : State rT, limExecV (⟨X, σ⟩ : Cfg rT) = limExecV ⟨Y, σ⟩) :
    advantage X Y = 0 := by
  simp [advantage, fun σ => tvDist_of_eq (h σ)]

end ProbLang
