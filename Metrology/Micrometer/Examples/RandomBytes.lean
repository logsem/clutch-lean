module

public import Metrology.Micrometer.UnifInt
public import Metrology.Micrometer.WpTactics
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # The randombytes callback

The FFI arguments are `(ptr, (len, ()))`; the callback fills the consecutive byte cells and returns
unit. The bound of each fresh draw is 256, exclusive. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS

namespace ProbLang.RandomBytes

variable {rT : Type}

/-- Fill `len` consecutive cells with fresh byte draws, returning unit for nonpositive lengths. -/
@[pl_fold] def fill : Exp rT := pl%
  rec fill ptr len := if len <= #0 then #() else
    let byte := rand(#256, #());
    ptr ← byte;
    fill (ptr +ₗ #1) (len - #1)

/-- The FFI callback taking the nested tuple `(ptr, (len, ()))` and returning unit. -/
@[pl_fold] def randombytes : Exp rT := pl%
  fun args, &fill (fst(args)) (fst(snd(args)))

/-- The closed randombytes lambda supplied directly to an FFI environment. -/
def randombytesValue : Val rT := ⟨randombytes, .lam (by is_lc), by is_lc⟩

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- Decoding the FFI argument tuple produces the array-filling call. -/
theorem randombytes_steps (l : Loc) (n : Int) :
    PureSteps (rT := rT) (pl% &randombytes (#loc l, (#n, #()))) (pl% &fill #loc l #n) := by
  pure_step 4
  exact .refl _

/-- Nonpositive lengths return unit without sampling or accessing the heap. -/
theorem fill_nonpos_steps (l : Loc) {n : Int} (hn : n ≤ 0) :
    PureSteps (rT := rT) (pl% &fill #loc l #n) pl(#()) := by
  pure_steps
  simp only [decide_eq_true hn]
  pure_steps

/-- A fresh byte draw has the uniform law on exactly the integers from zero through 255. -/
theorem byte_draw (σ : State rT) :
    primStep ⟨pl(rand(#256, #())), σ⟩ =
      (unifInt 256 (by norm_num)).map (fun b => (⟨pl(#int b), σ⟩ : Cfg rT)) :=
  (primStep_rand_unit (z := 256) (by norm_num) σ).trans
    (Cfg.uniform_eq_map (z := 256) (by norm_num) σ)

/-- Every byte has probability one over 256 under the fresh byte-draw law. -/
theorem byte_draw_singleton {b : Int} (hb : 0 ≤ b ∧ b < 256) :
    unifInt 256 (by norm_num) {b} = (256 : ENNReal)⁻¹ := by
  rw [unifInt, MeasureTheory.Measure.uniformOfFinset_apply_singleton_of_mem
    (Finset.mem_Ico.mpr hb), Int.card_Ico]
  norm_num

variable {GF : BundledGFunctors}
local bi IProp GF

/-- Ownership of consecutive cells containing integers between zero and 255. -/
def byteArray [AppGS rT GF] (l : Loc) : Nat → IProp GF
  | 0 => emp
  | n + 1 => iprop(∃ b : Int, ⌜0 ≤ b ∧ b < 256⌝ ∗
      appHeapFrag l (.int b) ∗ byteArray (l + 1) n)

/- TODO: These rules use the base kernel; porting them to the FFI kernel remains a separate
obligation. -/
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [CanonicallyOrderedAdd B] [OrderTop B] {L : GradedLifting.{0} B}
  [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsReflexive]
  [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] {E : CoPset}

/-- Filling an owned initialized block produces ownership of the same number of byte cells. -/
theorem wp_fill (n : Nat) (l : Loc) (v : Val rT) (Φ : Val rT → IProp GF) : iprop%
    appArrayFrag l v n ∗ (byteArray l n -∗ Φ .unit) ⊢
      wp L E (pl% &fill #loc l #int n) Φ := by
  induction n generalizing l Φ with
  | zero =>
    iintro ⟨Hl, HΦ⟩
    wp_pures
    wp_value
    iapply HΦ
    simp only [byteArray]
    imodintro
    isimp only [appArrayFrag] at Hl
    iexact Hl
  | succ n ih =>
    simp only [appArrayFrag]
    iintro ⟨⟨Hl, Hls⟩, HΦ⟩
    wp_pures
    wp_bind (pl% rand(#256, #()))
    iapply wp_rand (by norm_num)
    iintro %b %hb
    wp_pures
    wp_bind (pl% #loc l ← #b)
    rw [show (pl(#loc l ← #b) : Exp rT) = .store pl(#loc l) (Exp.ofVal (.int b)) from rfl]
    iapply wp_store
    iframe Hl
    iintro Hl
    wp_pure 3
    rw [show ((n + 1 : Nat) : Int) - 1 = n by omega]
    wp_show (pl% &fill #loc (l + 1) #int n)
    iapply ih
    iframe Hls
    iintro Htail
    iapply HΦ
    simp only [byteArray]
    iexists b
    iframe Hl Htail
    ipureintro
    exact hb

/-- The tuple-argument callback fills the caller's owned array with byte-valued integers. -/
theorem wp_randombytes (n : Nat) (l : Loc) (v : Val rT) (Φ : Val rT → IProp GF) : iprop%
    appArrayFrag l v n ∗ (byteArray l n -∗ Φ .unit) ⊢
      wp L E (pl% &randombytes (#loc l, (#int n, #()))) Φ := by
  iintro H
  wp_steps randombytes_steps l n
  iapply wp_fill $$ H

end ProbLang.RandomBytes
