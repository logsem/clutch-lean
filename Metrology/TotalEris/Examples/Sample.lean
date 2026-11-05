module

public import Metrology.TotalEris
public import Metrology.ProbLang.Test.Sample
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-! # Named-family sampling in TotalEris -/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.ProofMode ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang.TotalErisSample

section Concrete

local instance : ProbLangDist ℝ := ProbLang.Test.Sample.coinProbLangDist
local instance : ProbLangFFI ℝ := ProbLangFFI.stuck
local instance : ProbLangObs ℝ := ProbLang.Test.Sample.zeroObs

variable {GF : BundledGFunctors} [ErisGS ℝ .hasNoLC GF]
local bi (IProp GF)

/-- The generic fresh-sample rule steps the concrete fair-coin family. -/
example (E : CoPset) :
    ⊢ tglWp E (pl(sample(2, #(), #())) : Exp ℝ) (fun _ => iprop(True)) := by
  iapply twp_sample rfl MeasurableSet.univ Concentrated.univ
  · rw [ProbLang.Test.Sample.dist_two]
    exact MeasureTheory.IsProbabilityMeasure.ne_zero _
  · iintro %w -
    itrivial

/-- The generic tape rule returns and consumes a concrete presampled coin. -/
example (E : CoPset) (l : Loc) :
    ⊢ appTapesFrag l (Tape.ofList 2 .unit [.bool true]) -∗
      tglWp E (.sample 2 (.ofVal .unit) pl(#lbl l))
        (fun w => iprop(⌜w = .bool true⌝)) := by
  iintro Hl
  iapply twp_sample_tape (m := 2) (ea := .ofVal .unit) (v := .unit)
    (w := .bool true) (t := Tape.ofList 2 .unit [.bool true]) (l := l)
    rfl ⟨rfl, rfl⟩ rfl
  isplitl [Hl]
  · iexact Hl
  · iintro -
    itrivial

open ProbLang.Test.Sample in
/-- With `↯(1/3)`, a draw from the `1/3`-coin family lands on `false`: the credit pays for the
`true` outcome. -/
example (E : CoPset) :
    ⊢ ↯(3⁻¹) -∗ tglWp E (.sample 4 (.ofVal .unit) pl(#()) : Exp ℝ)
      (fun w => iprop(⌜w = .bool false⌝)) := by
  iintro Herr
  let S : Set (Val ℝ) := {.bool true, .bool false}
  let ε₂ : Val ℝ → ℝ≥0∞ := Set.indicator {.bool true} 1
  have hS : MeasurableSet S := (Set.toFinite S).measurableSet
  have hconc : Concentrated (ProbLangDist.dist 4 (.unit : Val ℝ)) S := by
    simp [Concentrated, bern, S]
  have hd : ProbLangDist.dist 4 (.unit : Val ℝ) ≠ 0 := by
    have := bern_isProbabilityMeasure (ENNReal.inv_le_one.mpr (by norm_num : (1 : ℝ≥0∞) ≤ 3))
    rw [dist_four]
    exact MeasureTheory.IsProbabilityMeasure.ne_zero _
  have hε₂ : Measurable ε₂ := measurable_one.indicator (measurableSet_singleton _)
  have hInt : ∫⁻ w, ε₂ w ∂ProbLangDist.dist 4 (.unit : Val ℝ) ≤ 3⁻¹ := by
    simp [ε₂, bern, MeasureTheory.lintegral_add_measure]
  iapply twp_sample_exp rfl hS hconc hd hε₂ hInt $$ Herr
  iintro %w ⟨%hw, Hw⟩
  rcases hw with rfl | rfl
  · iexfalso
    iapply ErrorCredit.contradict (by simp [ε₂]) $$ Hw
  · itrivial

end Concrete

section Presample

open MeasureTheory (Measure IsProbabilityMeasure lintegral_map)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT] [ProbLangDist rT]
  [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
  {GF : BundledGFunctors} [ErisGS rT .hasNoLC GF]
local bi (IProp GF)

/-- Presampling a hole and then reading it returns the value stored by presampling. -/
example (E : CoPset) (l : Loc) (m : ℕ) (v : Val rT)
    (hd : ProbLangDist.dist m v ≠ 0) :
    ⊢ appTapesFrag l (Tape.empty m v) -∗
      tglWp E (.sample m (.ofVal v) pl(#lbl l))
        (fun _ => iprop(True)) := by
  iintro Hl
  have hv : (.sample m (.ofVal v) pl(#lbl l) : Exp rT).toVal? = none := rfl
  iapply twp_presample (e := .sample m (.ofVal v) pl(#lbl l))
    (α := l) (t := Tape.empty m v) (k := 0) (S := Set.univ)
    rfl MeasurableSet.univ Concentrated.univ hd hv
  iframe Hl
  iintro %w - Hl
  iapply twp_sample_tape (m := m) (ea := .ofVal v) (v := v) (w := w)
    (t := (Tape.empty m v).fillAt 0 w) (l := l) (Exp.toVal?_ofVal v) ⟨rfl, rfl⟩
  · simp [Tape.head?, Tape.fillAt, Tape.empty, Presamples.fillAt]
  · isplitl [Hl]
    · iexact Hl
    · iintro -
      itrivial

/-- With `↯(1/2)`, presampling a whole stream of fair `{0, 1}` draws pays for every stream not
starting with `0`, so reading the tape returns `0`. -/
example (E : CoPset) (l : Loc) :
    ⊢ ↯(2⁻¹) -∗ appTapesFrag l (Tape.empty unifIntName (.int 2)) -∗
      tglWp E (.rand (.ofVal (.int 2)) pl(#lbl l) : Exp rT) (fun w => iprop(⌜w = .int 0⌝)) := by
  iintro Herr Hl
  let t : Tape rT := Tape.empty unifIntName (.int 2)
  let ε₂ : Tape rT → ℝ≥0∞ := fun τ => if τ.head? = some (.int 0) then 0 else 1
  have hdist : t.dist = (Measure.uniformOfFinset (Finset.Ico 0 2)).map (fun z : Int => Val.int z) :=
    ProbLangDist.IsUniformInt.dist_pos 2 (by norm_num)
  have : IsProbabilityMeasure t.dist := by
    have := Measure.isProbabilityMeasure_uniformOfFinset
      (Finset.nonempty_Ico.mpr (by decide : (0 : Int) < 2))
    rw [hdist]
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 this
  have hε₂ : Measurable ε₂ :=
    .ite ((Tape.measurable_presamples_apply 0) (measurableSet_singleton _))
      measurable_const measurable_const
  have hInt : ∫⁻ ω, ε₂ (t.fillAll ω) ∂Measure.infinitePi (fun _ : ℕ => t.dist) ≤ 2⁻¹ := by
    have hg : Measurable fun w : Val rT => if some w = some (Val.int 0) then (0 : ℝ≥0∞) else 1 :=
      .ite (measurable_some (measurableSet_singleton _)) measurable_const measurable_const
    change ∫⁻ ω, (fun w : Val rT => if some w = some (Val.int 0) then (0 : ℝ≥0∞) else 1) (ω 0)
      ∂Measure.infinitePi (fun _ : ℕ => t.dist) ≤ 2⁻¹
    rw [← lintegral_map hg (measurable_pi_apply 0), Measure.infinitePi_map_eval, hdist,
      lintegral_map hg (by fun_prop), show Finset.Ico (0 : Int) 2 = {0, 1} by decide]
    simp [Measure.uniformOfFinset]
  iapply twp_presample_all_adv_comp hε₂ hInt rfl
  iframe Herr Hl
  iintro %ω Hω Hl
  by_cases h : ω 0 = .int 0
  · iapply twp_sample_tape (m := unifIntName) (v := .int 2) (w := ω 0) (t := t.fillAll ω)
      (l := l) (Exp.toVal?_ofVal _) ⟨rfl, rfl⟩ rfl
    iframe Hl
    iintro -
    ipureintro
    exact h
  · iexfalso
    iapply ErrorCredit.contradict (by simp [ε₂, t, Tape.head?, Tape.fillAll, Tape.empty, h]) $$ Hω

end Presample

end ProbLang.TotalErisSample
