module

public import Metrology.Iris.AppProgram
public import Metrology.ProbLang.Rv
public import Metrology.ProbLang.HeadStep
import Metrology.Iris.LocalBI

/-! # Random-variable points-to

`l ↦ᵣ c` and `l ↦ᵣₛ c` own the program or spec random variable at `l` and record that its
posterior is nonzero, so every test of it has a result. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.Cfg AgreeHeap PartialMap
  View
open RvCell (post)

variable {rT : Type _} [MeasurableSpace rT] [ProbLangDist rT] [ProbLangObs rT]
  {GF : BundledGFunctors} {σ : State rT} {e : Exp rT} {l : Loc} {c d : RvCell rT}
local bi (IProp GF)

/-- A random variable with a nonzero prior has a nonzero posterior before any observation. -/
theorem ProbLang.RvCell.post_fresh_ne_zero {n : ℕ} {v : Val rT} (hd : ProbLangDist.dist n v ≠ 0) :
    post ProbLangDist.dist (fresh n v) ≠ 0 := by
  have : MeasureTheory.IsProbabilityMeasure (ProbLangDist.dist n v) :=
    ⟨MeasureTheory.IsZeroOrProbabilityMeasure.measure_univ.resolve_left
      (hd <| MeasureTheory.Measure.measure_univ_eq_zero.mp ·)⟩
  rwa [post_fresh]

instance heapView_rv_frag_discreteE {c : RvCell rT} :
    DiscreteE (HeapView.Frag (H := LocHeap) l (.own 1) (toAgree c)) :=
  frag_discrete

/-! ## Program side -/

section App

variable [LawfulProbLangℝ rT] [AppGS rT GF]

/-- The program random variable at `l` is `c`, and its posterior is nonzero. -/
def appRv (l : Loc) (c : RvCell rT) : IProp GF :=
  iprop(appRvsFrag l c ∗ ⌜post ProbLangDist.dist c ≠ 0⌝)

@[inherit_doc] notation:51 l:51 " ↦ᵣ " c:51 => appRv l c

instance appRvsFrag_timeless : Timeless (appRvsFrag l c : IProp GF) := by
  unfold appRvsFrag
  exact iOwn_timeless

instance appRv_timeless : Timeless (l ↦ᵣ c : IProp GF) := by
  unfold appRv
  infer_instance

/-- An owned random variable has a nonzero posterior. -/
theorem appRv_post_ne_zero : l ↦ᵣ c ⊢ ⌜post ProbLangDist.dist c ≠ 0⌝ := by
  unfold appRv
  iintro ⟨-, %h⟩
  ipureintro
  exact h

/-- Owning `l ↦ᵣ c` against the authoritative state shows the random variable at `l` is `c`. -/
theorem app_state_lookup_rv : ⊢ appStateAuth σ -∗ l ↦ᵣ c -∗ ⌜σ.rvs[l]? = some c⌝ := by
  unfold appRv
  iintro Hσ ⟨Hl, -⟩
  iapply app_state_lookup_rvsFrag $$ Hσ Hl

/-- Replacing the random variable at `l` by one with a nonzero posterior updates the
authoritative state and the points-to. -/
theorem app_state_update_rv (hd : post ProbLangDist.dist d ≠ 0) :
    ⊢ appStateAuth σ -∗ l ↦ᵣ c ==∗
      appStateAuth (σ.updateRvs (fun h : LocHeap (RvCell rT) => insert h l d)) ∗ l ↦ᵣ d := by
  unfold appRv
  iintro Hσ ⟨Hl, -⟩
  imod app_state_update_rvsFrag $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  iframe Hσ Hl
  ipureintro
  exact hd

/-- Replacing the random variable at `l` by `d` updates the authoritative state, and gives the
points-to once `d` has a nonzero posterior. -/
theorem app_state_update_rv_wand :
    ⊢ appStateAuth σ -∗ l ↦ᵣ c ==∗
      appStateAuth (σ.updateRvs (fun h : LocHeap (RvCell rT) => insert h l d)) ∗
        (⌜post ProbLangDist.dist d ≠ 0⌝ -∗ l ↦ᵣ d) := by
  unfold appRv
  iintro Hσ ⟨Hl, -⟩
  imod app_state_update_rvsFrag $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  iframe Hσ
  iintro %hd
  iframe Hl
  ipureintro
  exact hd

/-- Allocating a random variable with a nonzero posterior yields `σ.rvs.fresh ↦ᵣ c`. -/
theorem app_state_rv_alloc (hc : post ProbLangDist.dist c ≠ 0) :
    ⊢ appStateAuth σ ==∗
      appStateAuth (σ.updateRvs (fun h : LocHeap (RvCell rT) => insert h σ.rvs.fresh c)) ∗
        σ.rvs.fresh ↦ᵣ c := by
  unfold appRv
  iintro Hσ
  imod app_state_rvsFrag_alloc c $$ Hσ with ⟨Hσ, Hl⟩
  imodintro
  iframe Hσ Hl
  ipureintro
  exact hc

end App

/-! ## Spec side -/

section Spec

variable [LawfulProbLangℝ rT] [SpecGS rT GF]

/-- The spec random variable at `l` is `c`, and its posterior is nonzero. -/
def specRv (l : Loc) (c : RvCell rT) : IProp GF :=
  iprop(specRvsFrag l c ∗ ⌜post ProbLangDist.dist c ≠ 0⌝)

@[inherit_doc] notation:50 l:50 " ↦ᵣₛ " c:50 => specRv l c

instance specRvsFrag_timeless : Timeless (specRvsFrag l c : IProp GF) := by
  unfold specRvsFrag
  exact iOwn_timeless

instance specRv_timeless : Timeless (l ↦ᵣₛ c : IProp GF) := by
  unfold specRv
  infer_instance

/-- An owned spec random variable has a nonzero posterior. -/
theorem specRv_post_ne_zero : l ↦ᵣₛ c ⊢ ⌜post ProbLangDist.dist c ≠ 0⌝ := by
  unfold specRv
  iintro ⟨-, %h⟩
  ipureintro
  exact h

/-- A spec random-variable points-to agrees with the authoritative random variables. -/
theorem spec_auth_lookup_rv : ⊢ specAuth ⟨e, σ⟩ -∗ l ↦ᵣₛ c -∗ ⌜σ.rvs[l]? = some c⌝ := by
  unfold specRv
  iintro Hs ⟨Hl, -⟩
  iapply spec_auth_lookup_rvsFrag $$ Hs Hl

/-- Replacing a spec random variable by one with a nonzero posterior updates the authoritative
cells and the points-to together. -/
theorem spec_auth_update_rv (hd : post ProbLangDist.dist d ≠ 0) :
    ⊢ specAuth ⟨e, σ⟩ -∗ l ↦ᵣₛ c ==∗
      specAuth ⟨e, σ.updateRvs (fun h : LocHeap (RvCell rT) => insert h l d)⟩ ∗ l ↦ᵣₛ d := by
  unfold specRv
  iintro Hs ⟨Hl, -⟩
  imod spec_auth_update_rvsFrag $$ Hs Hl with ⟨Hs, Hl⟩
  imodintro
  iframe Hs Hl
  ipureintro
  exact hd

/-- Replacing a spec random variable by `d` updates the authoritative cells, and gives the
points-to once `d` has a nonzero posterior. -/
theorem spec_auth_update_rv_wand :
    ⊢ specAuth ⟨e, σ⟩ -∗ l ↦ᵣₛ c ==∗
      specAuth ⟨e, σ.updateRvs (fun h : LocHeap (RvCell rT) => insert h l d)⟩ ∗
        (⌜post ProbLangDist.dist d ≠ 0⌝ -∗ l ↦ᵣₛ d) := by
  unfold specRv
  iintro Hs ⟨Hl, -⟩
  imod spec_auth_update_rvsFrag $$ Hs Hl with ⟨Hs, Hl⟩
  imodintro
  iframe Hs
  iintro %hd
  iframe Hl
  ipureintro
  exact hd

end Spec
