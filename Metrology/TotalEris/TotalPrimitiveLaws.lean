module

public import Metrology.Iris.Array
public import Metrology.TotalEris.ErisGS
import Metrology.ProbLang.Syntax.Notation
public import Metrology.TotalEris.TotalLifting

/-!
# Total-correctness primitive WP laws
-/

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS Possible HeadStepSupport
open Std.ExtTreeMap (insert_eq_PartialMap_insert)
open Exp (toVal?_ofVal toVal?_lit allocN_toVal?_eq_none)
open scoped AppGS

namespace ProbLang

variable {rT : Type _}

namespace TotalEris

section Lifting

variable {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] [ErisGS rT hlc GF]
variable {E : CoPset} {Φ : Val rT → IProp GF} {l : Loc} {z : Int}

/-! ## Heap operations -/

section DiscreteHeadSteps
variable [ProbLangDist.IsUniformInt rT]

/-- Total weakest precondition of `alloc` applied to `v` (Eris `wp_alloc`). -/
theorem twp_alloc {v : Val rT} :
    iprop(∀ l, appHeapFrag l v -∗ Φ (.loc l)) ⊢ tglWp E (.alloc (.ofVal v)) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible (.alloc (.ofVal v)) σ₁ :=
    (AllocS (toVal?_ofVal v) rfl rfl).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | AllocS hvd hl hσ =>
    rw [toVal?_ofVal] at hvd
    cases hvd
    subst hl hσ
    imod app_state_heap_alloc v $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.heap.fresh Hl

/-- Total weakest precondition of positive block allocation. -/
theorem twp_allocN {v : Val rT} {n : Int} (hn : 0 < n) : iprop%
    (∀ l, appArrayFrag l v n.toNat -∗ Φ (.loc l)) ⊢ tglWp E (.allocN pl(#n) v.1) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step allocN_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible (.allocN pl(#n) v.1) σ₁ :=
    (AllocNS (toVal?_ofVal v) hn rfl rfl).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | AllocNS hvd _ hl hσ =>
    rw [show v.fst.toVal? = some v from toVal?_ofVal v] at hvd
    cases hvd
    subst hl hσ
    imod app_state_heap_allocN v n.toNat $$ Hσ with ⟨Hσ', Hls⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.heap.fresh Hls

/-- Total weakest precondition of `!l` (Eris `wp_load`). -/
theorem twp_load {v : Val rT} :
    iprop(l ↦ v ∗ (l ↦ v -∗ Φ v)) ⊢ tglWp E pl(!#loc l) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  have hred : HeadReducible pl(!#loc l) σ₁ := (LoadS hlook rfl).ne_zero
  imodintro
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | LoadS hlook' hofv =>
    rw [hlook] at hlook'
    cases hlook'
    subst hofv
    imodintro
    isimp only [erisWpGS_stateInterp_eq, toVal?_ofVal]
    iframe Hσ
    iapply HΦ $$ Hl

/-- Total weakest precondition of `l ← v` (Eris `wp_store`). -/
theorem twp_store {v v' : Val rT} :
    iprop(l ↦ v' ∗ (l ↦ v -∗ Φ .unit)) ⊢ tglWp E (.store pl(#loc l) (.ofVal v)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  have hred : HeadReducible (.store pl(#loc l) (.ofVal v)) σ₁ :=
    (StoreS (toVal?_ofVal v) (by rw [hlook]; exact Option.isSome_some) rfl).ne_zero
  imodintro
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | StoreS hvd _ hσ =>
    rw [toVal?_ofVal] at hvd
    cases hvd
    subst hσ
    imod app_state_updateHeap $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ Hl'

end DiscreteHeadSteps

/-! ## Tape operations -/

/-- Total weakest precondition of allocating an empty family tape. -/
theorem twp_alloctape_family {m : ℕ} {v : Val rT} : iprop%
    (∀ l, appTapesFrag l (Tape.empty m v) -∗ Φ (.lbl l)) ⊢
      tglWp E (.tape m (.ofVal v)) Φ := by
  let next : State rT → Cfg rT := fun σ =>
    ⟨.lit (.lbl σ.tapes.fresh),
      σ.updateTapes (·.insert σ.tapes.fresh (Tape.empty m v))⟩
  iintro HΦ
  iapply twp_lift_atomic_head_step_concentrated solve_not_value
    (by simp [Exp.decompItem, Exp.toVal?_ofVal]) (fun σ => {next σ})
    (fun _ => measurableSet_singleton _)
    (fun σ => by
      rw [headStep_tape (toVal?_ofVal v)]
      simp [next, Concentrated])
    (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible (.tape m (.ofVal v)) σ₁ := by
    rw [HeadReducible, headStep_tape (toVal?_ofVal v)]
    simp
  iframe %hred
  iintro %e₂ %σ₂ %Hmem
  simp only [Set.mem_singleton_iff] at Hmem
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp Hmem
  imod app_state_tape_alloc (Tape.empty m v) $$ Hσ with ⟨Hσ', Hl⟩
  imodintro
  isimp only [erisWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_lit]
  iframe Hσ'
  iapply HΦ $$ %σ₁.tapes.fresh Hl

/-- Total weakest precondition of `tape(#z)` (Eris `wp_alloc_tape`). -/
theorem twp_alloctape :
    iprop(∀ l, appNatTape l z [] -∗ Φ (.lbl l)) ⊢ tglWp E pl(tape(#z)) Φ := by
  change iprop(∀ l, appNatTape l z [] -∗ Φ (.lbl l)) ⊢
    tglWp E (.tape unifIntName (.ofVal (Val.int z))) Φ
  iintro HΦ
  iapply twp_alloctape_family (m := unifIntName) (v := Val.int (rT := rT) z)
  iintro %l Hl
  iapply HΦ $$ %l
  iapply app_empty_to_natTape $$ Hl

/-! ## Random sampling -/

/-- A fresh family sample satisfies a postcondition on a measurable carrier of its law. -/
theorem twp_sample {m : ℕ} {ea : Exp rT} {v : Val rT} {S : Set (Val rT)}
    (hv : ea.toVal? = some v) (hS : MeasurableSet S)
    (hconc : Concentrated (ProbLangDist.dist m v) S)
    (hdist : ProbLangDist.dist m v ≠ 0) : iprop%
    (∀ w, ⌜w ∈ S⌝ -∗ Φ w) ⊢ tglWp E (.sample m ea pl(#())) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step_concentrated solve_not_value
    (by simp [Exp.decompItem, hv, Exp.toVal?_lit])
    (fun σ => Cfg.sampleSetOn S σ)
    (fun σ => Cfg.measurableSet_sampleSetOn hS σ)
    (fun σ => by
      rw [headStep_sample hv]
      exact Cfg.concentrated_sampleSetOn hS hconc σ)
    (by rw [← Exp.ofVal_of_toVal_some hv]; is_lc)
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro
    rw [HeadReducible, headStep_sample hv]
    exact fun hzero => hdist (Cfg.sample_eq_zero_iff.mp hzero)
  iintro %e₂ %σ₂ %Hmem
  change ∃ w ∈ S, (⟨e₂, σ₂⟩ : Cfg rT) = ⟨.ofVal w, σ₁⟩ at Hmem
  obtain ⟨w, hw, hcfg⟩ := Hmem
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp hcfg
  imodintro
  isimp only [erisWpGS_stateInterp_eq, toVal?_ofVal]
  iframe Hσ
  iapply HΦ $$ %w %hw

/-- A matching family tape returns and consumes its presampled head. -/
theorem twp_sample_tape {m : ℕ} {ea : Exp rT} {v w : Val rT} {t : Tape rT}
    (hv : ea.toVal? = some v) (hfamily : t.name = m ∧ t.arg = v)
    (hhead : t.head? = some w) : iprop%
    appTapesFrag l t ∗ (appTapesFrag l t.shift -∗ Φ w) ⊢
      tglWp E (.sample m ea pl(#lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply twp_lift_atomic_head_step_concentrated solve_not_value
    (by simp [Exp.decompItem, hv, Exp.toVal?_lit])
    (fun σ => Cfg.sampleTapeSet m v l σ)
    (fun σ => Cfg.measurableSet_sampleTapeSet m v l σ)
    (fun σ => Cfg.concentrated_headStep_sample_tape hv l σ)
    (by rw [← Exp.ofVal_of_toVal_some hv]; is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    rw [HeadReducible, headStep_sample_tape_some hv hlook hfamily hhead]
    simp
  iintro %e₂ %σ₂ %Hmem
  change ⟨e₂, σ₂⟩ ∈ Cfg.sampleTapeSet m v l σ₁ at Hmem
  simp only [Cfg.sampleTapeSet, hlook, hfamily, hhead] at Hmem
  cases Hmem
  imod app_state_update_tape $$ Hσ Hl with ⟨Hσ', Hl'⟩
  imodintro
  isimp only [erisWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_ofVal]
  iframe Hσ'
  iapply HΦ $$ Hl'

/-- A matching family-tape hole is consumed before a fresh draw from a measurable carrier. -/
theorem twp_sample_tape_empty {m : ℕ} {ea : Exp rT} {v : Val rT} {t : Tape rT}
    {S : Set (Val rT)} (hv : ea.toVal? = some v)
    (hfamily : t.name = m ∧ t.arg = v) (hhead : t.head? = none)
    (hS : MeasurableSet S) (hconc : Concentrated (ProbLangDist.dist m v) S)
    (hdist : ProbLangDist.dist m v ≠ 0) : iprop%
    appTapesFrag l t ∗ (∀ w, appTapesFrag l t.shift -∗ ⌜w ∈ S⌝ -∗ Φ w) ⊢
      tglWp E (.sample m ea pl(#lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply twp_lift_atomic_head_step_concentrated solve_not_value
    (by simp [Exp.decompItem, hv, Exp.toVal?_lit])
    (fun σ => Cfg.sampleTapeSetOn m v l S σ)
    (fun σ => Cfg.measurableSet_sampleTapeSetOn hS m v l σ)
    (fun σ => Cfg.concentrated_headStep_sampleTapeSetOn hS hconc hv l σ)
    (by rw [← Exp.ofVal_of_toVal_some hv]; is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    rw [HeadReducible, headStep_sample_tape_none hv hlook hfamily hhead]
    exact fun hzero => hdist (Cfg.sample_eq_zero_iff.mp hzero)
  iintro %e₂ %σ₂ %Hmem
  change ⟨e₂, σ₂⟩ ∈ Cfg.sampleTapeSetOn m v l S σ₁ at Hmem
  simp only [Cfg.sampleTapeSetOn, hlook, hfamily, hhead] at Hmem
  obtain ⟨w, hw, hcfg⟩ := Hmem
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp hcfg
  imod app_state_update_tape $$ Hσ Hl with ⟨Hσ', Hl'⟩
  imodintro
  isimp only [erisWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_ofVal]
  iframe Hσ'
  iapply HΦ $$ %w Hl' %hw

/-- A mismatching family tape is preserved during a fresh draw from a measurable carrier. -/
theorem twp_sample_tape_other {m : ℕ} {ea : Exp rT} {v : Val rT} {t : Tape rT}
    {S : Set (Val rT)} (hv : ea.toVal? = some v)
    (hfamily : ¬(t.name = m ∧ t.arg = v))
    (hS : MeasurableSet S) (hconc : Concentrated (ProbLangDist.dist m v) S)
    (hdist : ProbLangDist.dist m v ≠ 0) : iprop%
    appTapesFrag l t ∗ (∀ w, appTapesFrag l t -∗ ⌜w ∈ S⌝ -∗ Φ w) ⊢
      tglWp E (.sample m ea pl(#lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply twp_lift_atomic_head_step_concentrated solve_not_value
    (by simp [Exp.decompItem, hv, Exp.toVal?_lit])
    (fun σ => Cfg.sampleTapeSetOn m v l S σ)
    (fun σ => Cfg.measurableSet_sampleTapeSetOn hS m v l σ)
    (fun σ => Cfg.concentrated_headStep_sampleTapeSetOn hS hconc hv l σ)
    (by rw [← Exp.ofVal_of_toVal_some hv]; is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    rw [HeadReducible, headStep_sample_tape_other hv hlook hfamily]
    exact fun hzero => hdist (Cfg.sample_eq_zero_iff.mp hzero)
  iintro %e₂ %σ₂ %Hmem
  change ⟨e₂, σ₂⟩ ∈ Cfg.sampleTapeSetOn m v l S σ₁ at Hmem
  simp only [Cfg.sampleTapeSetOn, hlook, hfamily] at Hmem
  obtain ⟨w, hw, hcfg⟩ := Hmem
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp hcfg
  imodintro
  isimp only [erisWpGS_stateInterp_eq, toVal?_ofVal]
  iframe Hσ
  iapply HΦ $$ %w Hl %hw

variable {ns : List Int}

/-- Total weakest precondition of `rand(l) z` on a tape with head `n` (Eris `wp_rand_tape`). -/
theorem twp_rand_tape {n : Int} : iprop%
    appNatTape l z (n :: ns) ∗
      (appNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
      tglWp E pl(rand(#z, #lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  icases app_read_natTape_head $$ Hl with ⟨%x, %xs, Hback, %hxv, HHandback⟩
  iunfold appTapeList at Hback
  iapply twp_sample_tape (m := unifIntName) (l := l) (v := Val.int z) (w := Val.int x)
    (t := Tape.ofList unifIntName (Val.int z) ((x :: xs).map fun q ↦ Val.int q.val))
    rfl (by constructor <;> rfl) rfl
  iframe Hback
  iintro Hback'
  have hshift :
      (Tape.ofList unifIntName (Val.int (rT := rT) z)
        ((x :: xs).map fun q ↦ Val.int (rT := rT) q.val)).shift =
        Tape.ofList unifIntName (Val.int (rT := rT) z)
          (xs.map fun q ↦ Val.int (rT := rT) q.val) := rfl
  isimp only [hshift] at Hback'
  iunfold appTapeList at HHandback
  ihave HlNew := HHandback $$ Hback'
  subst hxv
  iapply HΦ $$ HlNew %(x.2)

section UniformInt
variable [ProbLangDist.IsUniformInt rT]

/-- Total weakest precondition of `rand z` without a tape (Eris `wp_rand`). -/
theorem twp_rand (Hz : 0 < z) :
    iprop(∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢ tglWp E pl(rand(#z, #())) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible pl(rand(#z, #())) σ₁ :=
    (rand_pos rfl Hz le_rfl Hz).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | UnifIntS hv hw =>
    rw [toVal?_lit] at hv
    cases hv
    rcases ProbLangDist.dist_unifInt_pos_inv hw with ⟨_, _, rfl, Hv0, Hvz⟩ | ⟨hnz, rfl⟩
    · imodintro
      isimp only [erisWpGS_stateInterp_eq, Exp.toVal?_ofVal]
      iframe Hσ
      iapply HΦ
      ipureintro
      exact ⟨Hv0, Hvz⟩
    · exact absurd Hz hnz
  | SampleS hn _ _ => exact (hn rfl).elim

/-- Total weakest precondition of `rand(l) z` on an empty tape (Eris `wp_rand_tape_empty`). -/
theorem twp_rand_tape_empty (Hz : 0 < z) : iprop%
    appNatTape l z [] ∗
      (∀ n, appNatTape l z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
      tglWp E pl(rand(#z, #lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  ihave HlBack := app_natTape_to_empty $$ Hl
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ HlBack
  imodintro
  isplitr
  · ipureintro
    exact (rand_tape_empty_pos rfl Hz hlook ⟨rfl, rfl⟩ rfl le_rfl Hz (by
      simpa using (State.updateTapes_no_change hlook).symm)).ne_zero
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | SampleTapeS _ hlook' _ hhead' _ =>
    rw [hlook] at hlook'
    cases hlook'
    cases hhead'
  | UnifIntTapeEmptyS hv hlook' _ _ hw hσ =>
    rw [toVal?_lit] at hv
    cases hv
    rcases ProbLangDist.dist_unifInt_pos_inv hw with ⟨_, _, rfl, hv0, hvz⟩ | ⟨hnz, rfl⟩
    · rw [hlook] at hlook'
      cases hlook'
      have hstate : σ₂ = σ₁ := hσ.trans (by
        simpa using State.updateTapes_no_change hlook)
      cases hstate
      imodintro
      isimp only [erisWpGS_stateInterp_eq, Exp.toVal?_ofVal]
      iframe Hσ
      ihave HlNat := app_empty_to_natTape $$ HlBack
      iapply HΦ $$ HlNat %⟨hv0, hvz⟩
    · exact absurd Hz hnz
  | UnifIntTapeOtherS hv hlook' hne hw =>
    rw [toVal?_lit] at hv
    cases hv
    rcases ProbLangDist.dist_unifInt_pos_inv hw with ⟨_, _, rfl, _, _⟩ | ⟨hnz, rfl⟩
    · rw [hlook] at hlook'
      cases hlook'
      exact hne ⟨rfl, rfl⟩ |>.elim
    · exact absurd Hz hnz
  | SampleTapeEmptyS hn _ _ _ _ _ _ | SampleTapeOtherS hn _ _ _ _ =>
    exact (hn rfl).elim

end UniformInt

end Lifting

end TotalEris
end ProbLang
