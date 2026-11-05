module

public import Metrology.ProbLang.HeadStep
public import Metrology.ProbLang.Reals
public import Metrology.Couplings.Laplace
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-! # The default distribution family

`defaultProbLangDist` supplies uniform integers, unit-uniform reals, Gaussian and Laplace laws at
names `0`–`3` (zero elsewhere); `IsGauss` and `IsLaplace` fix the reserved-family laws. -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped NNReal

namespace ProbLang

/-! ## Reading parameters from values -/

section Read

variable {rT : Type _}

/-- The integer of an integer value `#z`. -/
def Val.int? (v : Val rT) : Option ℤ :=
  (Exp.lit.π v.fst).bind BaseLit.int.π

/-- The two reals of a pair value `(#u, #s)`. -/
def Val.realPair? (v : Val rT) : Option (rT × rT) :=
  (Exp.pair.π v.fst).bind fun p => ((Exp.lit.π p.1).bind BaseLit.real.π).bind fun u =>
    ((Exp.lit.π p.2).bind BaseLit.real.π).bind fun s => some (u, s)

@[simp] theorem Val.int?_int (z : ℤ) : (Val.int (rT := rT) z).int? = some z :=
  rfl

@[simp] theorem Val.realPair?_pair_real (u s : rT) :
    ((Val.real u).pair (.real s)).realPair? = some (u, s) :=
  rfl

/-- A value read as the integer `z` is `#z`. -/
theorem Val.eq_int_of_int? {v : Val rT} {z : ℤ} (h : v.int? = some z) : v = .int z := by
  refine Val.ext ?_
  simp only [int?] at h
  generalize v.fst = e at h ⊢
  cases e <;> simp [Exp.lit.π] at h
  rename_i b
  cases b <;> simp [BaseLit.int.π] at h
  subst h
  rfl

/-- A value read as the reals `(u, s)` is `(#u, #s)`. -/
theorem Val.eq_pair_of_realPair? {v : Val rT} {u s : rT} (h : v.realPair? = some (u, s)) :
    v = (Val.real u).pair (.real s) := by
  refine Val.ext ?_
  simp only [realPair?] at h
  generalize v.fst = e at h ⊢
  cases e <;> simp [Exp.pair.π] at h
  rename_i e₁ e₂
  cases e₁ <;> cases e₂ <;> simp [Exp.lit.π] at h
  rename_i b₁ b₂
  cases b₁ <;> cases b₂ <;> simp [BaseLit.real.π] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

variable [MeasurableSpace rT]

/-- `Val.real` is measurable. -/
@[fun_prop]
theorem Val.real.measurable : Measurable (Val.real : rT → Val rT) := by
  rw [measurable_comap_iff]
  exact Exp.lit.measurable.comp BaseLit.real.measurable

/-- `Val.int?` is measurable. -/
theorem Val.int?.measurable : Measurable (int? (rT := rT)) :=
  Option.measurable_bind_param (Exp.lit.π.measurable.comp fst.measurable)
    (BaseLit.int.π.measurable.comp measurable_snd)

/-- `Val.realPair?` is measurable. -/
theorem Val.realPair?.measurable : Measurable (realPair? (rT := rT)) := by
  have hr : Measurable fun e : Exp rT => (Exp.lit.π e).bind BaseLit.real.π :=
    Option.measurable_bind_param Exp.lit.π.measurable
      (BaseLit.real.π.measurable.comp measurable_snd)
  have hs : Measurable fun q : (Exp rT × Exp rT) × rT =>
      ((Exp.lit.π q.1.2).bind BaseLit.real.π).bind fun s => some (q.2, s) :=
    Option.measurable_bind_param (hr.comp (measurable_snd.comp measurable_fst))
      (measurable_some.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact Option.measurable_bind_param (Exp.pair.π.measurable.comp fst.measurable)
    (Option.measurable_bind_param (hr.comp (measurable_fst.comp measurable_snd)) (hs.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

end Read

/-! ## The Gaussian and Laplace families -/

/-- The reserved Gaussian family draws `N(u, s²)` at `(#u, #s)`, so `s` is the standard deviation
(`s = 0` gives the point mass at `u`), and is zero elsewhere. -/
class ProbLangDist.IsGauss [ProbLangDist ℝ] : Prop where
  /-- A pair of reals `(u, s)` gives the Gaussian with mean `u` and variance `s²`. -/
  dist_pair (u s : ℝ) :
    ProbLangDist.dist gaussName ((Val.real u).pair (.real s)) =
      (gaussianReal u (s ^ 2).toNNReal).map Val.real
  /-- Other arguments give zero. -/
  dist_other (v : Val ℝ) (hv : ∀ u s : ℝ, v ≠ (Val.real u).pair (.real s)) :
    ProbLangDist.dist gaussName v = 0

/-- The reserved Laplace family draws `laplace a b` (density `exp (-|x - a| / b) / (2 b)`) at
`(#a, #b)` with `b > 0`, and is zero elsewhere. -/
class ProbLangDist.IsLaplace [ProbLangDist ℝ] : Prop where
  /-- A pair `(a, b)` with `b > 0` gives the Laplace law with location `a` and scale `b`. -/
  dist_pos (a : ℝ) (b : ℝ≥0) (hb : 0 < b) :
    ProbLangDist.dist laplaceName ((Val.real a).pair (.real b)) = (laplace a b).map Val.real
  /-- A nonpositive scale gives zero. -/
  dist_nonpos (a b : ℝ) (hb : b ≤ 0) :
    ProbLangDist.dist laplaceName ((Val.real a).pair (.real b)) = 0
  /-- Other arguments give zero. -/
  dist_other (v : Val ℝ) (hv : ∀ a b : ℝ, v ≠ (Val.real a).pair (.real b)) :
    ProbLangDist.dist laplaceName v = 0

/-! ## The default family -/

namespace DefaultDist

/-- The uniform-integer law at `N`: uniform on `[0, N)` for `N > 0`, else the value `-1`. -/
def unifIntLaw (N : ℤ) : Measure (Val ℝ) :=
  if 0 < N then (uniformOfFinset (Finset.Ico 0 N)).map (fun z : ℤ => Val.int z)
  else dirac (.int (-1))

/-- The Gaussian law at mean `p.1` and standard deviation `p.2`, as values. -/
def gaussLaw (p : ℝ × ℝ) : Measure (Val ℝ) :=
  (gaussianReal p.1 (p.2 ^ 2).toNNReal).map Val.real

/-- The Laplace law at location `p.1` and scale `p.2`, as values; zero for `p.2 ≤ 0`. -/
def laplaceLaw (p : ℝ × ℝ) : Measure (Val ℝ) :=
  if 0 < p.2 then (laplace p.1 p.2.toNNReal).map Val.real else 0

/-- `gaussLaw` is measurable. -/
theorem measurable_gaussLaw : Measurable gaussLaw := by
  have hg : Measurable fun p : ℝ × ℝ => gaussianReal p.1 (p.2 ^ 2).toNNReal :=
    measurable_gaussianReal.comp (measurable_fst.prodMk (measurable_snd.pow_const 2).real_toNNReal)
  exact (Measure.measurable_map _ Val.real.measurable).comp hg

/-- `laplaceLaw` is measurable. -/
theorem measurable_laplaceLaw : Measurable laplaceLaw := by
  have hl : Measurable fun p : ℝ × ℝ => laplace p.1 p.2.toNNReal := by
    fun_prop
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    ((Measure.measurable_map _ Val.real.measurable).comp hl) measurable_const

/-- The kernel giving `law` at the parameter `read` finds, and zero where there is none. -/
noncomputable def ofRead {β : Type} [MeasurableSpace β] {read : Val ℝ → Option β}
    (hr : Measurable read) {law : β → Measure (Val ℝ)} (hl : Measurable law) :
    Kernel (Val ℝ) (Val ℝ) where
  toFun v := (read v).elim 0 law
  measurable' := by
    convert Option.measurable_elim_param_zero hr (hl.comp measurable_snd) using 2 with v
    cases read v <;> rfl

/-- The default laws: names `0`–`3` are `rand`, `urand`, `gauss` and `laplace`. -/
noncomputable def kernel : ℕ → Kernel (Val ℝ) (Val ℝ)
  | 0 => ofRead Val.int?.measurable (measurable_of_countable unifIntLaw)
  | 1 => Kernel.const _ ((LawfulProbLangℝ.unifUnit (T := ℝ)).map Val.real)
  | 2 => ofRead Val.realPair?.measurable measurable_gaussLaw
  | 3 => ofRead Val.realPair?.measurable measurable_laplaceLaw
  | _ => 0

/-- `ofRead` is a probability measure or zero when each law is. -/
theorem isZeroOrProbabilityMeasure_ofRead {β : Type} [MeasurableSpace β]
    {read : Val ℝ → Option β} (hr : Measurable read) {law : β → Measure (Val ℝ)}
    (hl : Measurable law) (h : ∀ b, IsZeroOrProbabilityMeasure (law b)) (v : Val ℝ) :
    IsZeroOrProbabilityMeasure (ofRead hr hl v) := by
  change IsZeroOrProbabilityMeasure ((read v).elim 0 law)
  cases read v
  · exact (inferInstance : IsZeroOrProbabilityMeasure (0 : Measure (Val ℝ)))
  · exact h _

/-- `ofRead` is zero where `read` finds no parameter. -/
theorem ofRead_of_none {β : Type} [MeasurableSpace β] {read : Val ℝ → Option β}
    (hr : Measurable read) {law : β → Measure (Val ℝ)} (hl : Measurable law) {v : Val ℝ}
    (h : read v = none) : ofRead hr hl v = 0 := by
  change (read v).elim 0 law = 0
  rw [h]
  rfl

/-- Every default law is a probability measure or zero. -/
theorem isZeroOrProbabilityMeasure_kernel (n : ℕ) (v : Val ℝ) :
    IsZeroOrProbabilityMeasure (kernel n v) := by
  match n with
  | 0 =>
    refine isZeroOrProbabilityMeasure_ofRead Val.int?.measurable
      (measurable_of_countable unifIntLaw) (fun N ↦ ?_) v
    unfold unifIntLaw
    split_ifs with hN
    · have := isProbabilityMeasure_uniformOfFinset (Finset.nonempty_Ico.mpr hN)
      infer_instance
    · infer_instance
  | 1 =>
    have := LawfulProbLangℝ.unifUnit_isProbabilityMeasure (T := ℝ)
    change IsZeroOrProbabilityMeasure ((LawfulProbLangℝ.unifUnit (T := ℝ)).map Val.real)
    infer_instance
  | 2 =>
    refine isZeroOrProbabilityMeasure_ofRead Val.realPair?.measurable measurable_gaussLaw
      (fun p ↦ ?_) v
    change IsZeroOrProbabilityMeasure ((gaussianReal _ _).map Val.real)
    infer_instance
  | 3 =>
    refine isZeroOrProbabilityMeasure_ofRead Val.realPair?.measurable measurable_laplaceLaw
      (fun p ↦ ?_) v
    unfold laplaceLaw
    split_ifs with hp
    · have : Fact (0 < p.2.toNNReal) := ⟨Real.toNNReal_pos.mpr hp⟩
      infer_instance
    · infer_instance
  | _ + 4 =>
    change IsZeroOrProbabilityMeasure (0 : Measure (Val ℝ))
    infer_instance

end DefaultDist

open DefaultDist

/-- The default distribution family, at low priority so that local instances win. -/
noncomputable instance (priority := low) defaultProbLangDist : ProbLangDist ℝ where
  dist := kernel
  isZeroOrProbabilityMeasure_dist := isZeroOrProbabilityMeasure_kernel

/-- The default family draws uniform integers at name `0`. -/
instance : ProbLangDist.IsUniformInt ℝ where
  dist_pos N hN := by
    change unifIntLaw N = _
    simp [unifIntLaw, hN]
  dist_nonpos N hN := by
    change unifIntLaw N = _
    simp [unifIntLaw, hN.not_gt]
  dist_other v hv := by
    refine ofRead_of_none Val.int?.measurable (measurable_of_countable unifIntLaw)
      (Option.eq_none_iff_forall_ne_some.mpr fun z hz ↦ ?_)
    exact hv z (Val.eq_int_of_int? hz)

/-- The default family draws unit-uniform reals at name `1`. -/
instance : ProbLangDist.IsUniformReal ℝ where
  dist_eq _ := rfl

/-- The default family draws Gaussians at name `2`. -/
instance : ProbLangDist.IsGauss where
  dist_pair _ _ := rfl
  dist_other v hv := by
    refine ofRead_of_none Val.realPair?.measurable measurable_gaussLaw
      (Option.eq_none_iff_forall_ne_some.mpr fun p hp ↦ ?_)
    exact hv p.1 p.2 (Val.eq_pair_of_realPair? hp)

/-- The default family draws Laplace laws at name `3`. -/
instance : ProbLangDist.IsLaplace where
  dist_pos a b hb := by
    change laplaceLaw (a, b) = _
    simp [laplaceLaw, hb]
  dist_nonpos a b hb := by
    change laplaceLaw (a, b) = _
    simp [laplaceLaw, hb.not_gt]
  dist_other v hv := by
    refine ofRead_of_none Val.realPair?.measurable measurable_laplaceLaw
      (Option.eq_none_iff_forall_ne_some.mpr fun p hp ↦ ?_)
    exact hv p.1 p.2 (Val.eq_pair_of_realPair? hp)

end ProbLang
