module

public import Metrology.Approxis.Lifting
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.ProbLang.Metatheory

@[expose] public section

set_option linter.discrete false

/-! # Coupling Rules -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang

variable {rT : Type _} [ProbLang.LawfulProbLangℝ rT]

/-! ## `id` as a coupling bijection -/

theorem id_dom_range {z : Int} : ∀ n, 0 ≤ n → n < z → 0 ≤ id n ∧ id n < z :=
  fun _ h0 hlt => ⟨h0, hlt⟩

theorem avoid_one_amort {z : Int} (bad : Int) :
    (∑ n ∈ Finset.Ico 0 z, if n = bad then (1 : ENNReal) else 0) / z.toNat ≤
      (z.toNat : ENNReal)⁻¹ := by
  rw [← one_div]
  gcongr
  rw [Finset.sum_ite_eq']
  split <;> simp

theorem id_bij_range {z : Int} : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ id n = m :=
  fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun _ ⟨_, heq⟩ => heq⟩

/-! ## Timeless instances for tape predicates -/

section TimelessTapes

variable {GF : BundledGFunctors}

instance heapView_tape_frag_discreteE (l : Loc) (t : Tape) :
    OFE.DiscreteE (HeapView.Frag (H := LocHeap) l (.own 1) (toAgree t)) :=
  View.frag_discrete

instance appTapesFrag_timeless [MeasurableSingletonClass rT] [AppGS rT GF] (l : Loc) (t : Tape) :
    BI.Timeless (l ↪ₐ t : IProp GF) := iOwn_timeless

instance specTapesFrag_timeless [MeasurableSingletonClass rT] [SpecGS rT GF]
    (l : Loc) (t : Tape) : BI.Timeless (l ↪ₛ t : IProp GF) := iOwn_timeless

instance heapView_heap_frag_discreteE (l : Loc) (v : Val rT) :
    OFE.DiscreteE (HeapView.Frag (H := LocHeap) l (.own 1) (toAgree v)) :=
  View.frag_discrete

instance appHeapFrag_timeless [MeasurableSingletonClass rT] [AppGS rT GF]
    (l : Loc) (v : Val rT) : BI.Timeless (l ↦ v : IProp GF) := by
  unfold appHeapFrag
  exact iOwn_timeless

instance specHeapFrag_timeless [MeasurableSingletonClass rT] [SpecGS rT GF]
    (l : Loc) (v : Val rT) : BI.Timeless (l ↦ₛ v : IProp GF) := by
  unfold specHeapFrag
  exact iOwn_timeless

instance appNatTape_timeless [MeasurableSingletonClass rT] [AppGS rT GF]
    (l : Loc) (z : Int) (ns : List Int) : BI.Timeless (appNatTape l z ns : IProp GF) := by
  unfold appNatTape
  infer_instance

instance specNatTape_timeless [MeasurableSingletonClass rT] [SpecGS rT GF]
    (l : Loc) (z : Int) (ns : List Int) : BI.Timeless (specNatTape l z ns : IProp GF) := by
  unfold specNatTape
  infer_instance

end TimelessTapes

/-! ## Fold/unfold bridges for the user-level tape predicates -/

section NatTapeBridges

variable {GF : BundledGFunctors}

theorem appNatTape_fold [AppGS rT GF] {l : Loc} {z : Int} {ns : List Int}
    {fs : List { z' : Int // 0 ≤ z' ∧ z' < z }} (hfs : fs.map (fun x => x.val) = ns) :
    l ↪ₐ ⟨z, fs⟩ ⊢@{IProp GF} appNatTape l z ns := by
  iintro Hb
  iunfold appNatTape
  iexists fs
  iframe %hfs Hb

theorem specNatTape_fold [SpecGS rT GF] {l : Loc} {z : Int} {ns : List Int}
    {fs : List { z' : Int // 0 ≤ z' ∧ z' < z }} (hfs : fs.map (fun x => x.val) = ns) :
    l ↪ₛ ⟨z, fs⟩ ⊢@{IProp GF} specNatTape l z ns := by
  iintro Hb
  iunfold specNatTape
  iexists fs
  iframe %hfs Hb

end NatTapeBridges

/-! ## Core probability fact: uniform coupling under bijection -/

open MeasureTheory in
private theorem addCoupl_map_right {α β β' : Type _} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace β'] {ε : ENNReal} {S : Set (α × β)} {R : Set (α × β')} {μ : Measure α}
    {ν : Measure β} {g : β → β'} (hg : Measurable g) (HR : ∀ a b, S (a, b) → R (a, g b))
    (H : AddCoupl ε S μ ν) : AddCoupl ε R μ (ν.map g) := by
  have := AddCoupl.map id g measurable_id hg (HR _ _) H
  rwa [Measure.map_id] at this

theorem Cfg.uniform_addCoupl_bij [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ σ' : State rT) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) :
    AddCoupl 0
      {p : Cfg rT × Cfg rT | ∃ n, 0 ≤ n ∧ n < z ∧
        p.1 = ⟨pl(#(.int n)), σ⟩ ∧ p.2 = ⟨pl(#(.int (f n))), σ'⟩}
      (Cfg.uniform z σ) (Cfg.uniform z σ') := by
  classical
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hle
  simp only [add_zero]
  show ∫⁻ c, φ c ∂(Cfg.uniform z σ) ≤ ∫⁻ c, ψ c ∂(Cfg.uniform z σ')
  rw [Cfg.lintegral_uniform' Hz σ Hφm, Cfg.lintegral_uniform' Hz σ' Hψm]
  refine mul_le_mul_right ?_ _
  rw [← Finset.sum_Ico_comp_of_bijOn hdom hbij fun m => ψ ⟨pl(#(.int m)), σ'⟩]
  refine Finset.sum_le_sum fun n hn => ?_
  simp only [Finset.mem_Ico] at hn
  exact Hle ⟨n, hn.1, hn.2, rfl, rfl⟩

@[reducible] def CoupledDraw (z : Int) (f : Int → Int) (σ σ' : State rT) (K : Ectx rT) :
    Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
  ∃ n : Int, 0 ≤ n ∧ n < z ∧
    c₁ = ⟨pl(#(.int n)), σ⟩ ∧ c₂ = ⟨K.fill (pl(#(.int (f n)))), σ'⟩

theorem Cfg.uniform_addCoupl_bij_fill [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) :
    AddCoupl 0 {p | CoupledDraw z f σ σ' K p.1 p.2}
      (Cfg.uniform z σ) ((Cfg.uniform z σ').map K.fillCfg) :=
  addCoupl_map_right (Ectx.fillCfg.measurable K)
    (by rintro _ _ ⟨n, h0, hz, heqL, rfl⟩; exact ⟨n, h0, hz, heqL, rfl⟩)
    (Cfg.uniform_addCoupl_bij Hz σ σ' f hdom hbij)

/-! ## Core probability fact: uniform couplings along an injection (unequal bounds)

Ports `ARcoupl_rand_rand_inj` / `ARcoupl_rand_rand_rev_inj` from
`clutch/theories/approxis/coupling_rules.v`: coupling `rand zL ~ rand zR` along an
injection costs the mass of the uncovered fraction of the *larger* support. -/

/-- A sum composed with a map injective on `Ico 0 zL` and landing in `Ico 0 zR` is
bounded by the full codomain sum. -/
theorem _root_.Finset.sum_Ico_comp_le_of_injOn {zL zR : Int} {f : Int → Int}
    (hdom : ∀ n : Int, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂ : Int, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂)
    (g : Int → ENNReal) :
    ∑ n ∈ Finset.Ico (0 : Int) zL, g (f n) ≤ ∑ m ∈ Finset.Ico (0 : Int) zR, g m := by
  have himg : ∑ m ∈ (Finset.Ico (0 : Int) zL).image f, g m =
      ∑ n ∈ Finset.Ico (0 : Int) zL, g (f n) :=
    Finset.sum_image fun n hn m hm heq => by
      simp only [Finset.coe_Ico, Set.mem_Ico] at hn hm
      exact hinj n m hn.1 hn.2 hm.1 hm.2 heq
  rw [← himg]
  refine Finset.sum_le_sum_of_subset fun m hm => ?_
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  simp only [Finset.mem_Ico] at hn ⊢
  exact hdom n hn.1 hn.2

/-- A sum of `≤ 1` terms over `Ico 0 z` is at most `z.toNat`. -/
theorem _root_.Finset.sum_Ico_le_toNat {z : Int} {g : Int → ENNReal}
    (hg : ∀ n, g n ≤ 1) :
    ∑ n ∈ Finset.Ico (0 : Int) z, g n ≤ (z.toNat : ENNReal) := by
  calc ∑ n ∈ Finset.Ico (0 : Int) z, g n
    _ ≤ ∑ _n ∈ Finset.Ico (0 : Int) z, 1 := Finset.sum_le_sum fun n _ => hg n
    _ = (z.toNat : ENNReal) := by
        rw [Finset.sum_const, Int.card_Ico, nsmul_eq_mul, mul_one, Int.sub_zero]

/-- Averaging cost of enlarging the denominator. -/
theorem _root_.ENNReal.inv_mul_le_inv_mul_add {a d : ℕ} (ha : a ≠ 0) {S : ENNReal}
    (hS : S ≤ (a : ENNReal)) :
    (a : ENNReal)⁻¹ * S ≤ ((a : ENNReal) + (d : ENNReal))⁻¹ * S +
      (d : ENNReal) / ((a : ENNReal) + (d : ENNReal)) := by
  have ha0 : (a : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have haT : (a : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.natCast_ne_top a
  have had0 : (a : ENNReal) + (d : ENNReal) ≠ 0 := by simp [ha0]
  have hadT : (a : ENNReal) + (d : ENNReal) ≠ (⊤ : ENNReal) :=
    ENNReal.add_ne_top.mpr ⟨haT, ENNReal.natCast_ne_top d⟩
  have hinvS : (a : ENNReal)⁻¹ * S ≤ 1 := by
    calc (a : ENNReal)⁻¹ * S
      _ ≤ (a : ENNReal)⁻¹ * (a : ENNReal) := by gcongr
      _ = 1 := ENNReal.inv_mul_cancel ha0 haT
  calc (a : ENNReal)⁻¹ * S
    _ = (((a : ENNReal) + d)⁻¹ * ((a : ENNReal) + d)) * ((a : ENNReal)⁻¹ * S) := by
        rw [ENNReal.inv_mul_cancel had0 hadT, one_mul]
    _ = ((a : ENNReal) + d)⁻¹ * ((a : ENNReal) * ((a : ENNReal)⁻¹ * S) +
          (d : ENNReal) * ((a : ENNReal)⁻¹ * S)) := by
        rw [mul_assoc, add_mul]
    _ = ((a : ENNReal) + d)⁻¹ * (S + (d : ENNReal) * ((a : ENNReal)⁻¹ * S)) := by
        rw [← mul_assoc (a : ENNReal), ENNReal.mul_inv_cancel ha0 haT, one_mul]
    _ ≤ ((a : ENNReal) + d)⁻¹ * (S + (d : ENNReal) * 1) := by gcongr
    _ = ((a : ENNReal) + d)⁻¹ * S + (d : ENNReal) / ((a : ENNReal) + d) := by
        rw [mul_one, mul_add, ENNReal.div_eq_inv_mul]

/-- Uniform coupling along an injection, smaller bound on the left:
`rand zL ~ rand zR` for `zL ≤ zR` along `f`, with error `(zR - zL)/zR`. -/
theorem Cfg.uniform_addCoupl_inj [MeasurableSingletonClass rT] {zL zR : Int}
    (HzL : 0 < zL) (Hle : zL ≤ zR) (σ σ' : State rT) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂) :
    AddCoupl (((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal))
      {p : Cfg rT × Cfg rT | ∃ n, 0 ≤ n ∧ n < zL ∧
        p.1 = ⟨pl(#(.int n)), σ⟩ ∧ p.2 = ⟨pl(#(.int (f n))), σ'⟩}
      (Cfg.uniform zL σ) (Cfg.uniform zR σ') := by
  classical
  have HzR : 0 < zR := HzL.trans_le Hle
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hpt
  show ∫⁻ c, φ c ∂(Cfg.uniform zL σ) ≤ ∫⁻ c, ψ c ∂(Cfg.uniform zR σ') + _
  rw [Cfg.lintegral_uniform' HzL σ Hφm, Cfg.lintegral_uniform' HzR σ' Hψm]
  have hcast : (zR.toNat : ENNReal) = (zL.toNat : ENNReal) + ((zR - zL).toNat : ENNReal) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  set S : ENNReal := ∑ n ∈ Finset.Ico (0 : Int) zL, ψ ⟨pl(#(.int (f n))), σ'⟩ with hS
  have h1 : ∑ n ∈ Finset.Ico (0 : Int) zL, φ ⟨pl(#(.int n)), σ⟩ ≤ S := by
    refine Finset.sum_le_sum fun n hn => ?_
    simp only [Finset.mem_Ico] at hn
    exact Hpt ⟨n, hn.1, hn.2, rfl, rfl⟩
  have h2 : S ≤ ∑ m ∈ Finset.Ico (0 : Int) zR, ψ ⟨pl(#(.int m)), σ'⟩ :=
    Finset.sum_Ico_comp_le_of_injOn hdom hinj fun m => ψ ⟨pl(#(.int m)), σ'⟩
  have h3 : S ≤ (zL.toNat : ENNReal) := Finset.sum_Ico_le_toNat fun n => Hψb _
  calc (zL.toNat : ENNReal)⁻¹ * ∑ n ∈ Finset.Ico (0 : Int) zL, φ ⟨pl(#(.int n)), σ⟩
    _ ≤ (zL.toNat : ENNReal)⁻¹ * S := by gcongr
    _ ≤ ((zL.toNat : ENNReal) + ((zR - zL).toNat : ENNReal))⁻¹ * S +
          ((zR - zL).toNat : ENNReal) / ((zL.toNat : ENNReal) + ((zR - zL).toNat : ENNReal)) :=
        ENNReal.inv_mul_le_inv_mul_add (by omega) h3
    _ = (zR.toNat : ENNReal)⁻¹ * S + ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal) := by
        rw [hcast]
    _ ≤ (zR.toNat : ENNReal)⁻¹ * ∑ m ∈ Finset.Ico (0 : Int) zR, ψ ⟨pl(#(.int m)), σ'⟩ +
          ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal) := by gcongr

/-- Uniform coupling along an injection, smaller bound on the right:
`rand zL ~ rand zR` for `zR ≤ zL` along `f : [0, zR) ↪ [0, zL)`; the left draw is
`f m` when the right draw is `m`, with error `(zL - zR)/zL`. -/
theorem Cfg.uniform_addCoupl_rev_inj [MeasurableSingletonClass rT] {zL zR : Int}
    (HzR : 0 < zR) (Hle : zR ≤ zL) (σ σ' : State rT) (f : Int → Int)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂) :
    AddCoupl (((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal))
      {p : Cfg rT × Cfg rT | ∃ m, 0 ≤ m ∧ m < zR ∧
        p.1 = ⟨pl(#(.int (f m))), σ⟩ ∧ p.2 = ⟨pl(#(.int m)), σ'⟩}
      (Cfg.uniform zL σ) (Cfg.uniform zR σ') := by
  classical
  have HzL : 0 < zL := HzR.trans_le Hle
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hpt
  show ∫⁻ c, φ c ∂(Cfg.uniform zL σ) ≤ ∫⁻ c, ψ c ∂(Cfg.uniform zR σ') + _
  rw [Cfg.lintegral_uniform' HzL σ Hφm, Cfg.lintegral_uniform' HzR σ' Hψm]
  have hinjOn : ∀ n ∈ Finset.Ico (0 : Int) zR, ∀ m ∈ Finset.Ico (0 : Int) zR,
      f n = f m → n = m := fun n hn m hm heq => by
    simp only [Finset.mem_Ico] at hn hm
    exact hinj n m hn.1 hn.2 hm.1 hm.2 heq
  have himg_sub : (Finset.Ico (0 : Int) zR).image f ⊆ Finset.Ico (0 : Int) zL := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    simp only [Finset.mem_Ico] at hn ⊢
    exact hdom n hn.1 hn.2
  have himg_card : ((Finset.Ico (0 : Int) zR).image f).card = zR.toNat := by
    rw [Finset.card_image_of_injOn hinjOn, Int.card_Ico, Int.sub_zero]
  have himg_le : ∑ m ∈ (Finset.Ico (0 : Int) zR).image f, φ ⟨pl(#(.int m)), σ⟩ ≤
      ∑ m ∈ Finset.Ico (0 : Int) zR, ψ ⟨pl(#(.int m)), σ'⟩ := by
    rw [Finset.sum_image hinjOn]
    refine Finset.sum_le_sum fun m hm => ?_
    simp only [Finset.mem_Ico] at hm
    exact Hpt ⟨m, hm.1, hm.2, rfl, rfl⟩
  have hrest_le : ∑ n ∈ Finset.Ico (0 : Int) zL \ (Finset.Ico (0 : Int) zR).image f,
      φ ⟨pl(#(.int n)), σ⟩ ≤ ((zL - zR).toNat : ENNReal) := by
    calc ∑ n ∈ Finset.Ico (0 : Int) zL \ (Finset.Ico (0 : Int) zR).image f,
        φ ⟨pl(#(.int n)), σ⟩
      _ ≤ ∑ _n ∈ Finset.Ico (0 : Int) zL \ (Finset.Ico (0 : Int) zR).image f, 1 :=
          Finset.sum_le_sum fun n _ => Hφb _
      _ = (((Finset.Ico (0 : Int) zL \ (Finset.Ico (0 : Int) zR).image f).card : ℕ) :
            ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (((zL - zR).toNat : ℕ) : ENNReal) := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr himg_sub, himg_card,
            Int.card_Ico, Int.sub_zero]
          congr 1
          omega
  have hsplit : ∑ n ∈ Finset.Ico (0 : Int) zL, φ ⟨pl(#(.int n)), σ⟩ ≤
      (∑ m ∈ Finset.Ico (0 : Int) zR, ψ ⟨pl(#(.int m)), σ'⟩) +
        ((zL - zR).toNat : ENNReal) := by
    rw [← Finset.sum_sdiff himg_sub, add_comm]
    exact add_le_add himg_le hrest_le
  calc (zL.toNat : ENNReal)⁻¹ * ∑ n ∈ Finset.Ico (0 : Int) zL, φ ⟨pl(#(.int n)), σ⟩
    _ ≤ (zL.toNat : ENNReal)⁻¹ * ((∑ m ∈ Finset.Ico (0 : Int) zR, ψ ⟨pl(#(.int m)), σ'⟩) +
          ((zL - zR).toNat : ENNReal)) := by gcongr
    _ = (zL.toNat : ENNReal)⁻¹ * ∑ m ∈ Finset.Ico (0 : Int) zR, ψ ⟨pl(#(.int m)), σ'⟩ +
          ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal) := by
        rw [mul_add, ENNReal.div_eq_inv_mul]
    _ ≤ (zR.toNat : ENNReal)⁻¹ * ∑ m ∈ Finset.Ico (0 : Int) zR, ψ ⟨pl(#(.int m)), σ'⟩ +
          ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal) := by
        gcongr
        exact_mod_cast Int.toNat_le_toNat Hle

/-- Like `CoupledDraw`, but for the reversed injective coupling: the left draw is
`f m` for the right draw `m`. -/
@[reducible] def CoupledDrawRev (z : Int) (f : Int → Int) (σ σ' : State rT) (K : Ectx rT) :
    Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
  ∃ m : Int, 0 ≤ m ∧ m < z ∧
    c₁ = ⟨pl(#(.int (f m))), σ⟩ ∧ c₂ = ⟨K.fill (pl(#(.int m))), σ'⟩

theorem Cfg.uniform_addCoupl_inj_fill [MeasurableSingletonClass rT] {zL zR : Int}
    (HzL : 0 < zL) (Hle : zL ≤ zR) (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂) :
    AddCoupl (((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal))
      {p | CoupledDraw zL f σ σ' K p.1 p.2}
      (Cfg.uniform zL σ) ((Cfg.uniform zR σ').map K.fillCfg) :=
  addCoupl_map_right (Ectx.fillCfg.measurable K)
    (by rintro _ _ ⟨n, h0, hz, heqL, rfl⟩; exact ⟨n, h0, hz, heqL, rfl⟩)
    (Cfg.uniform_addCoupl_inj HzL Hle σ σ' f hdom hinj)

theorem Cfg.uniform_addCoupl_rev_inj_fill [MeasurableSingletonClass rT] {zL zR : Int}
    (HzR : 0 < zR) (Hle : zR ≤ zL) (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂) :
    AddCoupl (((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal))
      {p | CoupledDrawRev zR f σ σ' K p.1 p.2}
      (Cfg.uniform zL σ) ((Cfg.uniform zR σ').map K.fillCfg) :=
  addCoupl_map_right (Ectx.fillCfg.measurable K)
    (by rintro _ _ ⟨m, h0, hz, heqL, rfl⟩; exact ⟨m, h0, hz, heqL, rfl⟩)
    (Cfg.uniform_addCoupl_rev_inj HzR Hle σ σ' f hdom hinj)

theorem primStep_rand_unit [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z) (σ : State rT) :
    primStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩ = Cfg.uniform z σ := by
  have Hwitness : HeadStepSupport ⟨pl(rand(#(.int z), #(.unit))), σ⟩ ⟨pl(#(.int 0)), σ⟩ :=
    .RandNoTapeS Hz (_root_.le_refl _) Hz
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc)
    (HeadReducible.of_headStepSupport Hwitness))]
  rfl

theorem randUnit_uniform_step [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) :
    Discrete.Reducible pl(rand(#(.int z), #(.unit))) σ ∧
      primStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩ = Cfg.uniform z σ :=
  ⟨.of_headStepSupport (.RandNoTapeS Hz (_root_.le_refl _) Hz) (by is_lc),
    primStep_rand_unit Hz σ⟩

theorem primStep_rand_lbl_eq [MeasurableSingletonClass rT] {z : Int} {σ : State rT} {l : Loc}
    {ρ : Cfg rT} (Hwit : HeadStepSupport ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ ρ) :
    primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ =
      match σ.tapes[l]? with
      | none => 0
      | some ⟨M, ns⟩ =>
        if M = z then
          match ns with
          | [] => Cfg.uniform z σ
          | n :: ns => MeasureTheory.Measure.dirac ⟨.lit <| .int n,
              σ.update_tapes fun t => t.insert l ⟨M, ns⟩⟩
        else Cfg.uniform z σ := by
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc)
    (HeadReducible.of_headStepSupport Hwit))]
  rfl

theorem primStep_rand_lbl_wrong [MeasurableSingletonClass rT] {z M : Int} (Hz : 0 < z)
    (HneM : z ≠ M) (σ : State rT) (l : Loc) (fs : List { z' : Int // 0 ≤ z' ∧ z' < M })
    (Hlk : σ.tapes[l]? = some ⟨M, fs⟩) :
    primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ = Cfg.uniform z σ := by
  rw [primStep_rand_lbl_eq (.RandTapeOtherS Hz Hlk HneM (_root_.le_refl _) Hz rfl), Hlk]
  simp only [ite_eq_right (Ne.symm HneM)]

theorem primStep_rand_lbl_empty [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) (l : Loc) (Hlk : σ.tapes[l]? = some ⟨z, []⟩) :
    primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ = Cfg.uniform z σ := by
  rw [primStep_rand_lbl_eq (.RandTapeEmptyS Hz Hlk rfl (_root_.le_refl _) Hz rfl), Hlk]
  simp only [↓reduceIte]

/-! ## Coupling-context helpers -/

open MeasureTheory in
theorem AddCoupl_steps_ctx_bind_r [MeasurableSingletonClass rT] {α} [MeasurableSpace α]
    {μ : Measure α} {e : Exp rT} {σ : State rT} {R : Set (α × Cfg rT)} {ε : ENNReal} {K : Ectx rT}
    (hv : ¬ e.isValue) (Hcpl : AddCoupl ε R μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε {p | ∃ e'', p.2.expr = K.fill e'' ∧ R (p.1, ⟨e'', p.2.state⟩)} μ
      (primStep ⟨K.fill e, σ⟩) := by
  rw [primStep_fill hv]
  exact addCoupl_map_right (Ectx.fillCfg.measurable K)
    (by rintro _ ⟨e', _⟩ HR; exact ⟨e', rfl, HR⟩) Hcpl

open MeasureTheory in
theorem AddCoupl_steps_ctx_bind_r_no_state [MeasurableSingletonClass rT]
    {μ : Measure (Cfg rT)} {e : Exp rT} {σ : State rT} {R : Exp rT → Exp rT → Prop} {ε : ENNReal}
    {K : Ectx rT} (hv : ¬ e.isValue)
    (Hcpl : AddCoupl ε {p : Cfg rT × Cfg rT | R p.1.expr p.2.expr} μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε {p | ∃ e'', p.2.expr = K.fill e'' ∧ R p.1.expr e''} μ (primStep ⟨K.fill e, σ⟩) := by
  rw [primStep_fill hv]
  exact addCoupl_map_right (Ectx.fillCfg.measurable K) (fun _ b HR => ⟨b.expr, rfl, HR⟩) Hcpl

section CouplingRules

variable {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSingletonClass rT] [ApproxisGS rT hlc GF]

private theorem randUnit_step_pure {z : Int} (Hz : 0 < z) (σ : State rT) {P A : IProp GF} :
    ⊢ P -∗ A -∗ ⌜Discrete.Reducible pl(rand(#(.int z), #(.unit))) σ ∧
      primStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩ = Cfg.uniform z σ⌝ := by
  iintro - -
  ipureintro
  exact randUnit_uniform_step Hz σ

private theorem appNatTape_empty_rand_step {z : Int} (Hz : 0 < z) (α : Loc) (σ : State rT) :
    ⊢@{IProp GF} appStateAuth σ -∗ appNatTape α z [] -∗
      ⌜Discrete.Reducible pl(rand(#(.int z), #(.lbl α))) σ ∧
        primStep ⟨pl(rand(#(.int z), #(.lbl α))), σ⟩ = Cfg.uniform z σ⌝ := by
  iintro Hσ HA
  iunfold appNatTape at HA
  icases HA with ⟨%fs, %hmap, Hb⟩
  obtain rfl : fs = [] := List.map_eq_nil_iff.mp hmap
  ihave %hlk := app_state_lookup_tape $$ Hσ Hb
  ipureintro
  exact ⟨.of_headStepSupport (.RandTapeEmptyS Hz hlk rfl (_root_.le_refl _) Hz rfl) (by is_lc),
    primStep_rand_lbl_empty Hz σ α hlk⟩

private theorem specNatTape_empty_rand_step {z : Int} (Hz : 0 < z) (α : Loc) (e : Exp rT)
    (σ : State rT) :
    ⊢@{IProp GF} Cfg.specAuth ⟨e, σ⟩ -∗ specNatTape α z [] -∗
      ⌜Discrete.Reducible pl(rand(#(.int z), #(.lbl α))) σ ∧
        primStep ⟨pl(rand(#(.int z), #(.lbl α))), σ⟩ = Cfg.uniform z σ⌝ := by
  iintro Hs HS
  iunfold specNatTape at HS
  icases HS with ⟨%fs, %hmap, Hb⟩
  obtain rfl : fs = [] := List.map_eq_nil_iff.mp hmap
  ihave %hlk := spec_auth_lookup_tape $$ Hs Hb
  ipureintro
  exact ⟨.of_headStepSupport (.RandTapeEmptyS Hz hlk rfl (_root_.le_refl _) Hz rfl) (by is_lc),
    primStep_rand_lbl_empty Hz σ α hlk⟩

theorem wp_couple_rand_core (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) {eL eR : Exp rT} (K : Ectx rT) (E : CoPset) (A : IProp GF) [BI.Timeless A]
    (HvL : eL.toVal? = none) (HvR : ¬ eR.isValue)
    (HstepL : ∀ σ, ⊢@{IProp GF} appStateAuth σ -∗ A -∗
      ⌜Discrete.Reducible eL σ ∧ primStep ⟨eL, σ⟩ = Cfg.uniform z σ⌝)
    (HstepR : ∀ e' σ', ⊢@{IProp GF} Cfg.specAuth ⟨e', σ'⟩ -∗ A -∗
      ⌜Discrete.Reducible eR σ' ∧ primStep ⟨eR, σ'⟩ = Cfg.uniform z σ'⌝)
    (Φ : Val rT → IProp GF) : iprop%
    ▷ A ∗ ⤇ K.fill eR ∗ (∀ n, A ∗ ⤇ K.fill pl(#(.int (f n))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp E eL Φ := by
  iintro ⟨HA, Hj, Hcnt⟩
  iapply wp_lift_prim_steps_coupl HvL
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  imod HA
  ihave %Heq := specAuth_specFrag_agree $$ Hs Hj
  subst Heq
  ihave %HL := HstepL σ₁ $$ Hσ HA
  ihave %HR := HstepR (K.fill eR) σ₁' $$ Hs HA
  have hεsum : 0 + ε ≤ ε := (zero_add ε).le
  have hredL := HL.1.toReducible
  have hredR := HR.1.toReducible.fill K
  have hcpl : AddCoupl 0 {p | CoupledDraw z f σ₁ σ₁' K p.1 p.2}
      (primStep ⟨eL, σ₁⟩) (primStep ⟨K.fill eR, σ₁'⟩) := by
    rw [HL.2, primStep_fill HvR, HR.2]
    exact Cfg.uniform_addCoupl_bij_fill Hz σ₁ σ₁' f K hdom hbij
  imod BIFUpdate.subset (E1 := E) Std.LawfulSet.empty_subset with Hclose
  imodintro
  iexists CoupledDraw z f σ₁ σ₁' K, 0, ε
  iframe %hεsum %hredL %hredR %hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨n, hn0, hnz, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update (e3 := K.fill pl(#(.int (f n)))) $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hε
  iapply wp_value_of_toVal (v := .int n) rfl
  iapply Hcnt
  iframe HA Hj'
  ipureintro; exact ⟨hn0, hnz⟩

theorem wp_couple_rand_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp E pl(rand(#(.int z), #(.unit))) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz (eL := pl(rand(#(.int z), #(.unit))))
    (eR := pl(rand(#(.int z), #(.unit)))) K E iprop(emp)
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => randUnit_step_pure Hz σ) (fun _ σ' => randUnit_step_pure Hz σ') Φ
  isplitr
  · iintro !>; iempintro
  iframe Hj
  iintro %n ⟨-, Hj', %hn⟩
  iapply Hcnt $$ %n %hn Hj'

theorem wp_couple_rand_rand_adv (z : Int) (f : Int → Int) (ε₁ : ENNReal) (ε₂ : Int → ENNReal)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (hamort : (∑ n ∈ Finset.Ico 0 z, ε₂ n) / z.toNat ≤ ε₁)
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗ ↯ ε₁ ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ↯ ε₂ n -∗ ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp E pl(rand(#(.int z), #(.unit))) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_lift_prim_steps_coupl_adv_err_le_1 Exp.rand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree $$ Hs Hj
  subst Heq
  set P : Cfg rT → Cfg rT → Int → Prop := fun ρ₁ ρ₂ n =>
    (0 ≤ n ∧ n < z) ∧ ρ₁ = ⟨pl(#(.int n)), σ₁⟩ ∧ ρ₂ = ⟨K.fill pl(#(.int (f n))), σ₁'⟩
  set X : Cfg rT → Cfg rT → ENNReal := fun ρ₁ ρ₂ => 1 ⊓ ⨅ n, ⨅ (_ : P ρ₁ ρ₂ n), ε₂ n
  have hXgraph : ∀ n, 0 ≤ n → n < z →
      X ⟨pl(#(.int n)), σ₁⟩ ⟨K.fill pl(#(.int (f n))), σ₁'⟩ = 1 ⊓ ε₂ n := by
    intro n h0 hn
    refine _root_.le_antisymm (inf_le_inf_left _ (iInf₂_le n ⟨⟨h0, hn⟩, rfl, rfl⟩))
      (le_inf inf_le_left (le_iInf₂ fun n' hn' => ?_))
    obtain ⟨-, h1, -⟩ := hn'
    obtain ⟨he, -⟩ := (Cfg.mk.injEq ..).mp h1
    simp only [Exp.lit.injEq, BaseLit.int.injEq] at he
    subst he
    exact inf_le_right
  have hXoff : ∀ ρ₁ ρ₂, (¬ ∃ n, P ρ₁ ρ₂ n) → X ρ₁ ρ₂ = 1 := fun ρ₁ ρ₂ h =>
    _root_.le_antisymm inf_le_left (le_inf le_rfl (le_iInf₂ fun n hn => absurd ⟨n, hn⟩ h))
  have Hkant : ExpCoupl ε₁ X (primStep ⟨pl(rand(#(.int z), #(.unit))), σ₁⟩)
      (primStep ⟨K.fill pl(rand(#(.int z), #(.unit))), σ₁'⟩) := by
    intro h₁ h₂ hm₁ hm₂ _ _ hle
    have hR : ∫⁻ b, h₂ b ∂(primStep ⟨K.fill pl(rand(#(.int z), #(.unit))), σ₁'⟩) =
        (z.toNat : ENNReal)⁻¹ * ∑ m ∈ Finset.Ico 0 z, h₂ ⟨K.fill pl(#(.int m)), σ₁'⟩ := by
      rw [primStep_fill Exp.rand_not_isValue, primStep_rand_unit Hz,
        MeasureTheory.lintegral_map hm₂
          (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
          (Ectx.fillCfg.measurable K),
        Cfg.lintegral_uniform' Hz σ₁'
          (φ := fun a : Cfg rT => h₂ ⟨K.fill a.expr, a.state⟩)
          (hm₂.comp (Ectx.fillCfg.measurable K))]
    rw [primStep_rand_unit Hz, Cfg.lintegral_uniform' Hz σ₁ hm₁, hR,
      ← Finset.sum_Ico_comp_of_bijOn hdom hbij fun m => h₂ ⟨K.fill pl(#(.int m)), σ₁'⟩]
    have hstep : ∑ n ∈ Finset.Ico 0 z, h₁ ⟨pl(#(.int n)), σ₁⟩ ≤
        (∑ n ∈ Finset.Ico 0 z, h₂ ⟨K.fill pl(#(.int (f n))), σ₁'⟩) +
          ∑ n ∈ Finset.Ico 0 z, ε₂ n := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n hn => ?_
      simp only [Finset.mem_Ico] at hn
      refine (hle _ ⟨K.fill pl(#(.int (f n))), σ₁'⟩).trans ?_
      gcongr
      rw [hXgraph n hn.1 hn.2]
      exact inf_le_right
    calc (z.toNat : ENNReal)⁻¹ * ∑ n ∈ Finset.Ico 0 z, h₁ ⟨pl(#(.int n)), σ₁⟩
      _ ≤ (z.toNat : ENNReal)⁻¹ * ((∑ n ∈ Finset.Ico 0 z, h₂ ⟨K.fill pl(#(.int (f n))), σ₁'⟩) +
          ∑ n ∈ Finset.Ico 0 z, ε₂ n) := by gcongr
      _ = (z.toNat : ENNReal)⁻¹ * (∑ n ∈ Finset.Ico 0 z, h₂ ⟨K.fill pl(#(.int (f n))), σ₁'⟩) +
          (z.toNat : ENNReal)⁻¹ * ∑ n ∈ Finset.Ico 0 z, ε₂ n := mul_add ..
      _ ≤ _ := by
        gcongr
        rwa [← ENNReal.div_eq_inv_mul]
  ihave %Hεle := ErrorCredit.supply_bound $$ Hε Herr
  imod ErrorCredit.supply_decrease $$ Hε Herr with Hdec
  imod BIFUpdate.subset (E1 := E) Std.LawfulSet.empty_subset with Hclose
  have hεsum : ε₁ + (ε - ε₁) ≤ ε := (add_tsub_cancel_of_le Hεle).le
  have hredL := (randUnit_uniform_step Hz σ₁).1.toReducible
  have hredR : Reducible (K.fill pl(rand(#(.int z), #(.unit)))) σ₁' :=
    (Discrete.Reducible.of_headStepSupport_fill K
    (.RandNoTapeS Hz (_root_.le_refl _) Hz) (by is_lc)).toReducible
  have hX : ∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1 := fun _ _ => inf_le_left
  imodintro
  iexists X, ε₁, ε - ε₁
  iframe %hεsum %hredL %hredR %hX %Hkant
  iintro %e₂ %σ₂ %e₂' %σ₂' !>
  by_cases hg : ∃ n, P ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ n
  · obtain ⟨n, ⟨hn0, hnz⟩, h1, h2⟩ := hg
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h1
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h2
    rw [hXgraph n hn0 hnz]
    by_cases hbig : 1 ≤ 1 ⊓ ε₂ n + (ε - ε₁)
    · imod Hclose
      imodintro
      ileft
      ipureintro
      exact hbig
    · rw [_root_.not_le] at hbig
      have hlt : ε₂ n < 1 := _root_.not_le.mp fun hge =>
        (_root_.lt_of_le_of_lt le_self_add hbig).ne (inf_eq_left.mpr hge)
      rw [inf_eq_right.mpr hlt.le] at hbig ⊢
      have hsum : ε - ε₁ + ε₂ n < 1 := (add_comm _ _).trans_lt hbig
      imod specProg_update (e3 := K.fill pl(#(.int (f n)))) $$ Hs Hj with ⟨Hs', Hj'⟩
      imod ErrorCredit.supply_increase hsum $$ Hdec with ⟨HdecA, Hfrag⟩
      imod Hclose
      imodintro
      iright
      iframe Hσ Hs'
      isplitl [HdecA]
      · iapply ErrorCredit.extAuth (add_comm _ _) $$ HdecA
      iapply wp_value_of_toVal rfl
      iapply Hcnt $$ %n %⟨hn0, hnz⟩ Hfrag Hj'
  · imod Hclose
    imodintro
    ileft
    ipureintro
    rw [hXoff _ _ hg]
    exact le_self_add

theorem wp_couple_rand_rand_avoid (z bad : Int) (Hz : 0 < z) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗ ↯ (z.toNat : ENNReal)⁻¹ ∗
    (∀ n, ⌜(0 ≤ n ∧ n < z) ∧ n ≠ bad⌝ -∗ ⤇ K.fill pl(#(.int n)) -∗ Φ (.int n)) ⊢
    wp E pl(rand(#(.int z), #(.unit))) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_couple_rand_rand_adv z id (z.toNat : ENNReal)⁻¹ (fun n => if n = bad then 1 else 0)
    id_dom_range id_bij_range Hz (avoid_one_amort bad) K E Φ
  iframe Hj Herr
  iintro %n %hn Hec Hj'
  by_cases hb : n = bad
  · rw [ite_eq_left hb]
    iexfalso
    iapply ErrorCredit.contradict (_root_.le_refl 1) $$ Hec
  · simp only [id_eq]
    iapply Hcnt $$ %n %⟨hn, hb⟩ Hj'

/-- Coupling `rand zL ~ rand zR` (`zL ≤ zR`) along an injection `f : [0,zL) ↪ [0,zR)`,
spending `(zR - zL)/zR` error credits: the left draw is `n`, the right draw is `f n`.
Ports `wp_couple_rand_rand_inj` from `clutch/theories/approxis/coupling_rules.v`. -/
theorem wp_couple_rand_rand_inj (zL zR : Int) (f : Int → Int) (ε : ENNReal)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂)
    (HzL : 0 < zL) (Hle : zL ≤ zR)
    (hε : ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal) ≤ ε)
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯ ε ∗
    (∀ n, ⌜0 ≤ n ∧ n < zL⌝ -∗ ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp E pl(rand(#(.int zL), #(.unit))) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr' := ErrorCredit.weaken hε $$ Herr
  iapply wp_lift_prim_steps_coupl Exp.rand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %εnow ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree $$ Hs Hj
  subst Heq
  ihave %Hεle := ErrorCredit.supply_bound $$ Hε Herr'
  imod ErrorCredit.supply_decrease $$ Hε Herr' with Hdec
  imod BIFUpdate.subset (E1 := E) Std.LawfulSet.empty_subset with Hclose
  imodintro
  iexists CoupledDraw zL f σ₁ σ₁' K,
    ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal),
    εnow - ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal)
  have hεsum := (add_tsub_cancel_of_le Hεle).le
  have hredL := (randUnit_uniform_step HzL σ₁).1.toReducible
  have hredR := ((randUnit_uniform_step (HzL.trans_le Hle) σ₁').1.toReducible).fill K
  have hcpl : AddCoupl (((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal))
      {p | CoupledDraw zL f σ₁ σ₁' K p.1 p.2}
      (primStep ⟨pl(rand(#(.int zL), #(.unit))), σ₁⟩)
      (primStep ⟨K.fill pl(rand(#(.int zR), #(.unit))), σ₁'⟩) := by
    rw [primStep_rand_unit HzL, primStep_fill Exp.rand_not_isValue,
      primStep_rand_unit (HzL.trans_le Hle)]
    exact Cfg.uniform_addCoupl_inj_fill HzL Hle σ₁ σ₁' f K hdom hinj
  iframe %hεsum %hredL %hredR %hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨n, hn0, hnz, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update (e3 := K.fill pl(#(.int (f n)))) $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hdec
  iapply wp_value_of_toVal (v := .int n) rfl
  iapply Hcnt $$ %n %⟨hn0, hnz⟩ Hj'

/-- Coupling `rand zL ~ rand zR` (`zR ≤ zL`) along an injection `f : [0,zR) ↪ [0,zL)`,
spending `(zL - zR)/zL` error credits: the left draw is `f m`, the right draw is `m`.
Ports `wp_couple_rand_rand_rev_inj` from `clutch/theories/approxis/coupling_rules.v`. -/
theorem wp_couple_rand_rand_rev_inj (zL zR : Int) (f : Int → Int) (ε : ENNReal)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂)
    (HzR : 0 < zR) (Hle : zR ≤ zL)
    (hε : ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal) ≤ ε)
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯ ε ∗
    (∀ m, ⌜0 ≤ m ∧ m < zR⌝ -∗ ⤇ K.fill pl(#(.int m)) -∗ Φ (.int (f m))) ⊢
    wp E pl(rand(#(.int zL), #(.unit))) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr' := ErrorCredit.weaken hε $$ Herr
  iapply wp_lift_prim_steps_coupl Exp.rand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %εnow ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree $$ Hs Hj
  subst Heq
  ihave %Hεle := ErrorCredit.supply_bound $$ Hε Herr'
  imod ErrorCredit.supply_decrease $$ Hε Herr' with Hdec
  imod BIFUpdate.subset (E1 := E) Std.LawfulSet.empty_subset with Hclose
  imodintro
  iexists CoupledDrawRev zR f σ₁ σ₁' K,
    ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal),
    εnow - ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal)
  have hεsum := (add_tsub_cancel_of_le Hεle).le
  have hredL := (randUnit_uniform_step (HzR.trans_le Hle) σ₁).1.toReducible
  have hredR := ((randUnit_uniform_step HzR σ₁').1.toReducible).fill K
  have hcpl : AddCoupl (((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal))
      {p | CoupledDrawRev zR f σ₁ σ₁' K p.1 p.2}
      (primStep ⟨pl(rand(#(.int zL), #(.unit))), σ₁⟩)
      (primStep ⟨K.fill pl(rand(#(.int zR), #(.unit))), σ₁'⟩) := by
    rw [primStep_rand_unit (HzR.trans_le Hle), primStep_fill Exp.rand_not_isValue,
      primStep_rand_unit HzR]
    exact Cfg.uniform_addCoupl_rev_inj_fill HzR Hle σ₁ σ₁' f K hdom hinj
  iframe %hεsum %hredL %hredR %hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨m, hm0, hmz, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update (e3 := K.fill pl(#(.int m))) $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hdec
  iapply wp_value_of_toVal (v := .int (f m)) rfl
  iapply Hcnt $$ %m %⟨hm0, hmz⟩ Hj'

theorem wp_couple_tapes_bij {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {z : Int} {α αₛ : Loc} {ns nsₛ : List Int} (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) : iprop%
    appNatTape α z ns ∗ specNatTape αₛ z nsₛ ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ appNatTape α z (ns ++ [n]) -∗ specNatTape αₛ z (nsₛ ++ [f n]) -∗
      wp E e Φ) ⊢
    wp E e Φ := by
  iintro ⟨Hα, Hαₛ, Hcnt⟩
  iunfold appNatTape at Hα
  iunfold specNatTape at Hαₛ
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  icases Hαₛ with ⟨%fsₛ, %Hfsₛ, Hαₛ⟩
  iapply wp_couple_erasables
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %hlk := app_state_lookup_tape $$ Hσ Hα
  ihave %hlk' := spec_auth_lookup_tape $$ Hs Hαₛ
  imod BIFUpdate.subset (E1 := E) Std.LawfulSet.empty_subset with Hclose
  imodintro
  iexists (fun σ₂ σ₂' => ∃ n, 0 ≤ n ∧ n < z ∧
      σ₂ = σ₁.update_tapes (·.insert α ⟨z, fs ++ [tapeIdxOf Hz n]⟩) ∧
      σ₂' = σ₁'.update_tapes (·.insert αₛ ⟨z, fsₛ ++ [tapeIdxOf Hz (f n)]⟩)),
    tapePresample σ₁ α, tapePresample σ₁' αₛ
  have her := ErasableExpr.tapePresample hlk Hz
  have her' := ErasableExpr.tapePresample hlk' Hz
  have hcpl := tapePresample_addCoupl_bij hlk hlk' Hz f hdom hbij
  iframe %her %her' %hcpl
  iintro %σ₂ %σ₂' %⟨n, hn0, hnz, rfl, rfl⟩
  imod app_state_update_tape (s := ⟨z, fs ++ [tapeIdxOf Hz n]⟩) $$ Hσ Hα with ⟨Hσ', Hα'⟩
  imod spec_auth_update_tape (s := ⟨z, fsₛ ++ [tapeIdxOf Hz (f n)]⟩) $$ Hs Hαₛ with ⟨Hs', Hαₛ'⟩
  imod Hclose
  imodintro
  simp only [approxisWpGS_stateInterp_eq, approxisWpGS_specInterp_eq,
    ExtTreeMap.insert_eq_PartialMap_insert]
  iframe Hσ' Hs' Hε
  have hd := hdom n hn0 hnz
  ihave HnatA := appNatTape_fold (l := α) (ns := ns ++ [n])
    (by simp [← Hfs, tapeIdxOf_val Hz hn0 hnz]) $$ Hα'
  ihave HnatS := specNatTape_fold (l := αₛ) (ns := nsₛ ++ [f n])
    (by simp [← Hfsₛ, tapeIdxOf_val Hz hd.1 hd.2]) $$ Hαₛ'
  iapply Hcnt $$ %n %⟨hn0, hnz⟩ HnatA HnatS

theorem wp_couple_rand_lbl_rand_lbl_wrong (z M : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (HneM : z ≠ M) (K : Ectx rT) (E : CoPset) (α α' : Loc)
    (xs ys : List Int) (Φ : Val rT → IProp GF) : iprop%
    ▷ appNatTape α M xs ∗ ▷ specNatTape α' M ys ∗ ⤇ K.fill pl(rand(#(.int z), #(.lbl α'))) ∗
    (∀ n, appNatTape α M xs ∗ specNatTape α' M ys ∗ ⤇ K.fill pl(#(.int (f n))) ∗
      ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp E pl(rand(#(.int z), #(.lbl α))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz (eL := pl(rand(#(.int z), #(.lbl α))))
    (eR := pl(rand(#(.int z), #(.lbl α')))) K E iprop(appNatTape α M xs ∗ specNatTape α' M ys)
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => by
      iintro Hσ ⟨HA, -⟩
      iunfold appNatTape at HA
      icases HA with ⟨%fs, -, Hb⟩
      ihave %hlk := app_state_lookup_tape $$ Hσ Hb
      ipureintro
      exact ⟨.of_headStepSupport (.RandTapeOtherS Hz hlk HneM (_root_.le_refl _) Hz rfl)
        (by is_lc), primStep_rand_lbl_wrong Hz HneM σ α fs hlk⟩)
    (fun _ σ' => by
      iintro Hs ⟨-, HS⟩
      iunfold specNatTape at HS
      icases HS with ⟨%fs', -, Hb'⟩
      ihave %hlk := spec_auth_lookup_tape $$ Hs Hb'
      ipureintro
      exact ⟨.of_headStepSupport (.RandTapeOtherS Hz hlk HneM (_root_.le_refl _) Hz rfl)
        (by is_lc), primStep_rand_lbl_wrong Hz HneM σ' α' fs' hlk⟩) Φ
  isplitl [Hα Hα']
  · iintro !>; iframe
  iframe Hj
  iintro %n ⟨⟨HA, HS⟩, Hj', %hn⟩
  iapply Hcnt
  iframe HA HS Hj' %hn

theorem wp_couple_rand_lbl_rand_lbl (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α α' : Loc) (Φ : Val rT → IProp GF) : iprop%
    ▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗ ⤇ K.fill pl(rand(#(.int z), #(.lbl α'))) ∗
    (∀ n, appNatTape α z [] ∗ specNatTape α' z [] ∗ ⤇ K.fill pl(#(.int (f n))) ∗
      ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp E pl(rand(#(.int z), #(.lbl α))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz (eL := pl(rand(#(.int z), #(.lbl α))))
    (eR := pl(rand(#(.int z), #(.lbl α')))) K E iprop(appNatTape α z [] ∗ specNatTape α' z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => by iintro Hσ ⟨HA, -⟩; iapply (appNatTape_empty_rand_step Hz α σ) $$ Hσ HA)
    (fun e' σ' => by iintro Hs ⟨-, HS⟩; iapply (specNatTape_empty_rand_step Hz α' e' σ') $$ Hs HS)
    Φ
  isplitl [Hα Hα']
  · iintro !>; iframe
  iframe Hj
  iintro %n ⟨⟨HA, HS⟩, Hj', %hn⟩
  iapply Hcnt
  iframe HA HS Hj' %hn

/-! ## Mixed tape-rand couplings -/

theorem wp_couple_tape_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α : Loc) (Φ : Val rT → IProp GF) : iprop%
    ▷ appNatTape α z [] ∗ ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗
    (∀ n, appNatTape α z [] ∗ ⤇ K.fill pl(#(.int (f n))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp E pl(rand(#(.int z), #(.lbl α))) Φ :=
  wp_couple_rand_core z f hdom hbij Hz K E iprop(appNatTape α z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (appNatTape_empty_rand_step Hz α) (fun _ σ' => randUnit_step_pure Hz σ') Φ

theorem wp_couple_rand_tape (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α' : Loc) (Φ : Val rT → IProp GF) : iprop%
    ▷ specNatTape α' z [] ∗ ⤇ K.fill pl(rand(#(.int z), #(.lbl α'))) ∗
    (∀ n, specNatTape α' z [] ∗ ⤇ K.fill pl(#(.int (f n))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp E pl(rand(#(.int z), #(.unit))) Φ :=
  wp_couple_rand_core z f hdom hbij Hz K E iprop(specNatTape α' z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => randUnit_step_pure Hz σ) (specNatTape_empty_rand_step Hz α') Φ

end CouplingRules

end ProbLang
