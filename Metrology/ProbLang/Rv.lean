module

public import Metrology.ProbLang.CoreMeasures
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Random variables
`ProbLangObs`, the meanings of the observation names of `test`, and the law of a random variable
given what has been observed of it. -/

@[expose] public section

noncomputable section

open Classical MeasureTheory ProbabilityTheory Measure Set
open Kernel (measurable_kernel_prodMk_left coe_mk)

namespace ProbLang

variable {rT : Type _} [MeasurableSpace rT]

/-- Meanings of the observation names of `test`: an integer-valued measurable map per name, from
the argument and the value of the random variable. -/
class ProbLangObs (rT : Type _) [MeasurableSpace rT] where
  /-- The observation `test k` makes. -/
  obs : ℕ → Val rT × Val rT → Int
  /-- Each observation is measurable. -/
  measurable_obs (k : ℕ) : Measurable (obs k)

/-! ## Measure theory of conditioning on a countable observation -/

section Fiber

variable {Ω : Type _} [MeasurableSpace Ω]

/-- Integrating the conditionals on the fibers of an integer-valued map gives back the measure. -/
theorem bind_cond_fiber (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → Int} (hf : Measurable f) :
    (μ.map f).bind (fun y => μ[|f ⁻¹' {y}]) = μ := by
  ext A hA
  rw [bind_apply hA (Measurable.of_discrete.aemeasurable), lintegral_countable' ]
  simp_rw [map_apply hf (measurableSet_singleton _),
    cond_mul_eq_inter (hf (measurableSet_singleton _))]
  rw [← measure_iUnion (fun i j hij => ((disjoint_singleton.mpr hij).preimage f).mono
      inter_subset_left inter_subset_left)
    fun y => (hf (measurableSet_singleton _)).inter hA]
  congr 1
  ext x
  simp

/-- Almost every point lies in a fiber of positive measure. -/
theorem ae_fiber_ne_zero (μ : Measure Ω) (f : Ω → Int) :
    ∀ᵐ x ∂μ, μ (f ⁻¹' {f x}) ≠ 0 := by
  have hnull : μ (⋃ y ∈ {y : Int | μ (f ⁻¹' {y}) = 0}, f ⁻¹' {y}) = 0 :=
    (measure_biUnion_null_iff (to_countable _)).mpr fun y hy => hy
  refine measure_mono_null (fun x hx => ?_) hnull
  exact mem_biUnion (not_not.mp hx) rfl

/-- Conditioning the measures of a kernel on events that depend measurably on a parameter is
measurable in the parameter. -/
theorem measurable_cond_kernel {X Y : Type _} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel Y Ω) [IsFiniteKernel κ] {g : X → Y} (hg : Measurable g) (s : X → Set Ω)
    (hs : MeasurableSet {p : X × Ω | p.2 ∈ s p.1}) :
    Measurable (fun x => (κ (g x))[|s x]) := by
  have hsx : ∀ x, MeasurableSet (s x) := fun x => measurable_prodMk_left hs
  refine measurable_of_measurable_coe _ fun B hB => ?_
  simp_rw [cond_apply (hsx _)]
  have hsB : MeasurableSet {p : X × Ω | p.2 ∈ s p.1 ∩ B} := hs.inter (measurable_snd hB)
  have h1 := measurable_kernel_prodMk_left (κ := κ.comap g hg) hs
  have h2 := measurable_kernel_prodMk_left (κ := κ.comap g hg) hsB
  simp only [Kernel.comap_apply] at h1 h2
  exact h1.inv.mul h2

end Fiber

/-! ## Observations and the posterior of a random variable -/

namespace RvCell

variable [ProbLangObs rT]

/-- One step of `consistent`: keep the flag only if the value gives the observation's result. -/
def consistentStep (p : Bool × Val rT) (o : ℕ × Val rT × Int) : Bool × Val rT :=
  (p.1 && decide (ProbLangObs.obs o.1 (o.2.1, p.2) = o.2.2), p.2)

section Consistent

variable (l : List (ℕ × Val rT × Int)) (x : Val rT)

/-- Whether the value `x` gives every observation in `l` its recorded result. -/
def consistent : Bool :=
  (l.foldl consistentStep (true, x)).1

/-- `consistent` with an accumulated flag `b`. -/
private theorem foldl_consistentStep (b : Bool) :
    l.foldl consistentStep (b, x) = (b && consistent l x, x) := by
  induction l generalizing b with
  | nil => simp [consistent]
  | cons o l ih =>
    show l.foldl consistentStep (consistentStep (b, x) o) =
      (b && (l.foldl consistentStep (consistentStep (true, x) o)).1, x)
    simp only [consistentStep, ih, Bool.true_and, Bool.and_assoc]

/-- A value is consistent with a list of observations iff it gives each one its result. -/
theorem consistent_iff :
    consistent l x = true ↔ ∀ o ∈ l, ProbLangObs.obs o.1 (o.2.1, x) = o.2.2 := by
  induction l with
  | nil => simp [consistent]
  | cons o l ih =>
    show (l.foldl consistentStep (consistentStep (true, x) o)).1 = true ↔ _
    simp only [consistentStep, foldl_consistentStep, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq, ih, List.mem_cons, forall_eq_or_imp]

/-- Appending an observation adds one condition. -/
theorem consistent_append (o : ℕ × Val rT × Int) :
    consistent (l ++ [o]) x =
      (consistent l x && decide (ProbLangObs.obs o.1 (o.2.1, x) = o.2.2)) := by
  show ((l ++ [o]).foldl consistentStep (true, x)).1 = _
  rw [List.foldl_append, show l.foldl consistentStep (true, x) = (consistent l x, x) by
    rw [foldl_consistentStep, Bool.true_and]]
  rfl

end Consistent

/-- `consistentStep` is measurable. -/
theorem measurable_consistentStep :
    Measurable (fun q : (Bool × Val rT) × (ℕ × Val rT × Int) => consistentStep q.1 q.2) := by
  have hobs : Measurable (fun q : (Bool × Val rT) × (ℕ × Val rT × Int) =>
      ProbLangObs.obs q.2.1 (q.2.2.1, q.1.2)) := by
    have h : Measurable (fun p : ℕ × (Val rT × Val rT) => ProbLangObs.obs p.1 p.2) :=
      measurable_from_prod_countable_right fun k => ProbLangObs.measurable_obs k
    exact h.comp ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_fst)))
  have hg : Measurable (fun t : Bool × Int × Int => t.1 && decide (t.2.1 = t.2.2)) := .of_discrete
  exact (hg.comp ((measurable_fst.comp measurable_fst).prodMk (hobs.prodMk
    (measurable_snd.comp (measurable_snd.comp measurable_snd))))).prodMk
    (measurable_snd.comp measurable_fst)

/-- `consistent` is measurable in the observations and the value. -/
theorem measurable_consistent :
    Measurable (fun p : List (ℕ × Val rT × Int) × Val rT => consistent p.1 p.2) := by
  have h := List.measurable_foldl (f := consistentStep (rT := rT))
    (measurable_consistentStep.comp measurable_id)
  exact measurable_fst.comp (h.comp (measurable_fst.prodMk
    (measurable_const.prodMk measurable_snd)))

/-- The values consistent with the observations of a random variable. -/
def event (c : RvCell rT) : Set (Val rT) := {x | consistent c.obs x = true}

/-- The pairs of a random variable and a value consistent with its observations. -/
theorem measurableSet_event_graph : MeasurableSet {p : RvCell rT × Val rT | p.2 ∈ p.1.event} :=
  (measurable_consistent.comp (measurable_obs.prodMap measurable_id)) (measurableSet_singleton true)

/-- The event of a random variable is measurable. -/
theorem measurableSet_event (c : RvCell rT) : MeasurableSet c.event :=
  measurable_prodMk_left measurableSet_event_graph

/-- Observing intersects the event with a fiber of the observation. -/
theorem event_observe (c : RvCell rT) (k : ℕ) (a : Val rT) (y : Int) :
    (c.observe k a y).event = c.event ∩ (fun x => ProbLangObs.obs k (a, x)) ⁻¹' {y} := by
  ext x
  simp [event, observe, consistent_append]

variable (D : ℕ → Kernel (Val rT) (Val rT))

/-- The law of the value of a random variable whose prior names a kernel of `D`: its resolved value
if any, otherwise its prior conditioned on its observations. -/
def post (c : RvCell rT) : Measure (Val rT) :=
  match c.world with
  | some x => dirac x
  | none => (D c.prior c.arg)[|c.event]

/-- The random variable after a test: the observed value and the updated random variable. -/
def testCell (k : ℕ) (a : Val rT) (c : RvCell rT) : Measure (Int × RvCell rT) :=
  (post D c).map fun x => (ProbLangObs.obs k (a, x), c.observe k a (ProbLangObs.obs k (a, x)))

/-- Resolving a random variable: fix its value by a draw from its posterior (or leave it alone when
the posterior is zero). -/
def resolve (c : RvCell rT) : Measure (RvCell rT) :=
  if post D c = 0 then dirac c else (post D c).map c.resolveTo

variable {D}

/-- A resolved random variable has a Dirac posterior. -/
@[simp] theorem post_resolveTo (c : RvCell rT) (x : Val rT) : post D (c.resolveTo x) = dirac x :=
  rfl

/-- The posterior of an unresolved random variable. -/
theorem post_of_world_none {c : RvCell rT} (h : c.world = none) :
    post D c = (D c.prior c.arg)[|c.event] := by
  simp [post, h]

/-- A random variable with no observations has its prior as posterior. -/
theorem post_fresh (n : ℕ) (v : Val rT) [IsProbabilityMeasure (D n v)] :
    post D (fresh n v) = D n v := by
  have hev : (fresh n v).event = univ := by
    ext x
    simp [event, fresh, consistent]
  rw [post_of_world_none rfl, hev]
  show (D n v)[|univ] = _
  exact cond_univ _

/-- An observation's fiber is measurable. -/
theorem measurableSet_obs_fiber (k : ℕ) (a : Val rT) (y : Int) :
    MeasurableSet ((fun x => ProbLangObs.obs k (a, x)) ⁻¹' {y}) :=
  ((ProbLangObs.measurable_obs k).comp (measurable_const.prodMk measurable_id))
    (measurableSet_singleton y)

/-- An observation is measurable in the value. -/
theorem measurable_obs_apply (k : ℕ) (a : Val rT) :
    Measurable (fun x : Val rT => ProbLangObs.obs k (a, x)) :=
  (ProbLangObs.measurable_obs k).comp (measurable_const.prodMk measurable_id)

/-- A nonzero posterior is a probability measure. -/
theorem isProbabilityMeasure_post {c : RvCell rT} [IsZeroOrProbabilityMeasure (post D c)]
    (h : post D c ≠ 0) :
    IsProbabilityMeasure (post D c) :=
  ⟨IsZeroOrProbabilityMeasure.measure_univ.resolve_left (h <| measure_univ_eq_zero.mp ·)⟩

/-- A resolved random variable resolves to itself. -/
theorem resolve_of_world_some {c : RvCell rT} {x : Val rT} (h : c.world = some x) :
    resolve D c = dirac c := by
  obtain ⟨n, v, l, w⟩ := c
  obtain rfl : w = some x := h
  rw [resolve, ite_eq_right (by simp [post]),
    show post D ⟨n, v, l, some x⟩ = dirac x from rfl, map_dirac' (measurable_resolveTo _)]
  rfl

/-- The outcome of a test of `c` is measurable in the value. -/
theorem measurable_testOutcome (c : RvCell rT) (k : ℕ) (a : Val rT) :
    Measurable fun x => (ProbLangObs.obs k (a, x), c.observe k a (ProbLangObs.obs k (a, x))) :=
  (measurable_obs_apply k a).prodMk ((measurable_observe c k a).comp (measurable_obs_apply k a))

variable (D) in
/-- The posterior predictive of observation `k` at argument `a`: the law of a test's result. -/
def predictive (k : ℕ) (a : Val rT) (c : RvCell rT) : Measure Int :=
  (post D c).map fun x => ProbLangObs.obs k (a, x)

/-- The predictive mass of a result is the posterior mass of its fiber. -/
theorem predictive_singleton (k : ℕ) (a : Val rT) (c : RvCell rT) (y : Int) :
    predictive D k a c {y} = post D c ((fun x => ProbLangObs.obs k (a, x)) ⁻¹' {y}) :=
  Measure.map_apply (measurable_obs_apply k a) (measurableSet_singleton y)

/-- A test's result and updated random variable are the predictive result and its observation. -/
theorem testCell_eq_map_predictive (k : ℕ) (a : Val rT) (c : RvCell rT) :
    testCell D k a c = (predictive D k a c).map fun y => (y, c.observe k a y) := by
  rw [predictive, Measure.map_map Measurable.of_discrete (measurable_obs_apply k a)]
  rfl

/-- A nonzero posterior predicts some result with positive mass. -/
theorem exists_predictive_ne_zero {k : ℕ} {a : Val rT} {c : RvCell rT} (h : post D c ≠ 0) :
    ∃ y, predictive D k a c {y} ≠ 0 := by
  by_contra! hy
  refine h (measure_univ_eq_zero.mp ?_)
  have := measure_iUnion_null (μ := predictive D k a c) hy
  rwa [Set.iUnion_of_singleton, predictive,
    Measure.map_apply (measurable_obs_apply k a) MeasurableSet.univ, Set.preimage_univ] at this

/-- A resolved random variable predicts its observation surely. -/
@[simp] theorem predictive_resolveTo (k : ℕ) (a : Val rT) (c : RvCell rT) (x : Val rT) :
    predictive D k a (c.resolveTo x) = dirac (ProbLangObs.obs k (a, x)) := by
  rw [predictive, post_resolveTo, map_dirac' (measurable_obs_apply k a)]

/-- The results the predictive law gives no mass carry no mass together. -/
theorem predictive_null (k : ℕ) (a : Val rT) (c : RvCell rT) :
    predictive D k a c {y | predictive D k a c {y} = 0} = 0 := by
  rw [← Set.biUnion_of_singleton {y | predictive D k a c {y} = 0},
    measure_biUnion_null_iff (Set.to_countable _)]
  exact fun _ h => h

/-- A nonzero posterior gives some result's fiber positive mass. -/
theorem exists_post_fiber_ne_zero {k : ℕ} {a : Val rT} {c : RvCell rT} (h : post D c ≠ 0) :
    ∃ y, post D c ((fun x => ProbLangObs.obs k (a, x)) ⁻¹' {y}) ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_predictive_ne_zero (k := k) (a := a) h
  exact ⟨y, predictive_singleton k a c y ▸ hy⟩

section Kernels

variable [∀ n, IsFiniteKernel (D n)]

/-- The posterior after an observation is the posterior conditioned on the observation's fiber. -/
theorem post_observe {c : RvCell rT} (h : c.world = none) (k : ℕ) (a : Val rT) (y : Int) :
    post D (c.observe k a y) = (post D c)[|(fun x => ProbLangObs.obs k (a, x)) ⁻¹' {y}] := by
  rw [post_of_world_none h, post_of_world_none (by simpa using h), event_observe,
    cond_cond_eq_cond_inter (measurableSet_event c) (measurableSet_obs_fiber k a y)]
  rfl

/-- The posterior is measurable in the random variable. -/
theorem measurable_post : Measurable (post D) := by
  have hnone : Measurable (fun c : RvCell rT => (D c.prior c.arg)[|c.event]) := by
    have hn : ∀ n, Measurable (fun c : RvCell rT => (D n c.arg)[|c.event]) := fun n =>
      measurable_cond_kernel (D n) measurable_arg event measurableSet_event_graph
    have h : Measurable (fun p : ℕ × RvCell rT => (D p.1 p.2.arg)[|p.2.event]) :=
      measurable_from_prod_countable_right
        (f := fun p : ℕ × RvCell rT => (D p.1 p.2.arg)[|p.2.event]) hn
    have hpair : Measurable (fun c : RvCell rT => (c.prior, c)) :=
      measurable_prior.prodMk measurable_id
    simpa only [Function.comp_def] using h.comp hpair
  have hrw : post D = fun c => Option.casesOn (motive := fun _ => Measure (Val rT)) c.world
      ((D c.prior c.arg)[|c.event]) (fun x => dirac ((c, x) : RvCell rT × Val rT).2) := by
    funext c
    rcases c with ⟨n, v, l, _ | x⟩ <;> rfl
  rw [hrw]
  exact Option.measurable_elim_param measurable_world hnone (measurable_dirac.comp measurable_snd)

/-- The posterior is a probability measure or zero. -/
instance isZeroOrProbabilityMeasure_post (c : RvCell rT) :
    IsZeroOrProbabilityMeasure (post D c) := by
  unfold post
  rcases c.world with _ | x <;> infer_instance

/-- The posterior predictive is a probability measure or zero. -/
instance isZeroOrProbabilityMeasure_predictive (k : ℕ) (a : Val rT) (c : RvCell rT) :
    IsZeroOrProbabilityMeasure (predictive D k a c) := by
  unfold predictive
  infer_instance

/-- Observing a result of positive posterior mass keeps the posterior nonzero. -/
theorem post_observe_ne_zero {c : RvCell rT} {k : ℕ} {a : Val rT} {y : Int}
    (hy : post D c ((fun x => ProbLangObs.obs k (a, x)) ⁻¹' {y}) ≠ 0) :
    post D (c.observe k a y) ≠ 0 := by
  rcases hw : c.world with _ | x
  · rw [post_observe hw, Ne, ProbabilityTheory.cond_eq_zero, not_or]
    exact ⟨measure_ne_top _ _, hy⟩
  · rw [post, RvCell.world_observe, hw]
    exact dirac_ne_zero

/-- Observing a result of positive predictive mass keeps the posterior nonzero. -/
theorem post_observe_ne_zero_of_predictive {c : RvCell rT} {k : ℕ} {a : Val rT} {y : Int}
    (hy : predictive D k a c {y} ≠ 0) : post D (c.observe k a y) ≠ 0 :=
  post_observe_ne_zero (by rwa [← predictive_singleton])

/-- The posterior as a finite kernel. -/
instance isFiniteKernel_post :
    IsFiniteKernel (Kernel.mk (post D) measurable_post) :=
  ⟨1, ENNReal.one_lt_top, fun c => by rw [coe_mk]; exact prob_le_one⟩

/-- Resolving is a probability measure. -/
instance isProbabilityMeasure_resolve (c : RvCell rT) : IsProbabilityMeasure (resolve D c) := by
  unfold resolve
  split_ifs with h
  · infer_instance
  · have := isProbabilityMeasure_post h
    infer_instance

/-- Resolving is measurable in the random variable. -/
theorem measurable_resolve : Measurable (resolve D) := by
  have hset : MeasurableSet {c : RvCell rT | post D c = 0} := by
    have : {c : RvCell rT | post D c = 0} = (fun c => post D c univ) ⁻¹' {0} := by
      ext c
      simp
    rw [this]
    exact (measurable_coe MeasurableSet.univ).comp measurable_post
      (measurableSet_singleton 0)
  have hmap : Measurable (fun c : RvCell rT => (post D c).map c.resolveTo) :=
    measurable_map_uncurry measurable_resolveTo_uncurry measurable_post
  change Measurable fun c => if post D c = 0 then dirac c else (post D c).map c.resolveTo
  exact Measurable.ite hset measurable_dirac hmap

/-- Resolving as a finite kernel. -/
instance isFiniteKernel_resolve :
    IsFiniteKernel (Kernel.mk (resolve D) measurable_resolve) :=
  ⟨1, ENNReal.one_lt_top, fun c => by rw [coe_mk]; exact prob_le_one⟩

/-- A test is jointly measurable in the argument and the random variable. -/
theorem measurable_testCell_uncurry (k : ℕ) :
    Measurable (fun q : Val rT × RvCell rT => testCell D k q.1 q.2) := by
  have hobs : Measurable (fun p : (Val rT × RvCell rT) × Val rT =>
      ProbLangObs.obs k (p.1.1, p.2)) :=
    (ProbLangObs.measurable_obs k).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have : IsFiniteKernel (Kernel.mk (fun q : Val rT × RvCell rT => post D q.2)
      (measurable_post.comp measurable_snd)) :=
    ⟨1, ENNReal.one_lt_top, fun q => by rw [coe_mk]; exact prob_le_one⟩
  exact measurable_map_uncurry (h := fun p : (Val rT × RvCell rT) × Val rT =>
      (ProbLangObs.obs k (p.1.1, p.2), p.1.2.observe k p.1.1 (ProbLangObs.obs k (p.1.1, p.2))))
    (hobs.prodMk (measurable_observe_uncurry.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_const.prodMk ((measurable_fst.comp measurable_fst).prodMk hobs)))))
    (measurable_post.comp measurable_snd)

/-- A test as a measurable function of the random variable. -/
theorem measurable_testCell (k : ℕ) (a : Val rT) : Measurable (testCell D k a) :=
  (measurable_testCell_uncurry k).comp (measurable_const.prodMk measurable_id)

/-- A test is a probability measure or zero. -/
instance isZeroOrProbabilityMeasure_testCell (k : ℕ) (a : Val rT) (c : RvCell rT) :
    IsZeroOrProbabilityMeasure (testCell D k a c) := by
  unfold testCell
  infer_instance

/-- Resolving a random variable commutes with testing it (Bayes' rule for an integer
observation). -/
theorem resolve_bind_testCell (c : RvCell rT) (k : ℕ) (a : Val rT) :
    (resolve D c).bind (testCell D k a) =
      (testCell D k a c).bind fun p => (resolve D p.2).map (p.1, ·) := by
  set f : Val rT → Int := fun x => ProbLangObs.obs k (a, x) with hf_def
  have hf : Measurable f := measurable_obs_apply k a
  have hG : Measurable fun x => (f x, c.observe k a (f x)) := measurable_testOutcome c k a
  have : IsFiniteKernel (Kernel.mk (fun p : Int × RvCell rT => resolve D p.2)
      (measurable_resolve.comp measurable_snd)) :=
    ⟨1, ENNReal.one_lt_top, fun p => by rw [coe_mk]; exact prob_le_one⟩
  have hR : Measurable (fun p : Int × RvCell rT => (resolve D p.2).map (p.1, ·)) :=
    measurable_map_uncurry (h := fun q : (Int × RvCell rT) × RvCell rT => (q.1.1, q.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      (measurable_resolve.comp measurable_snd)
  rcases hw : c.world with _ | x0
  · by_cases hP : post D c = 0
    · -- a zero posterior: both sides are zero
      have ht : testCell D k a c = 0 := by simp [testCell, hP]
      rw [resolve, ite_eq_left hP, dirac_bind (measurable_testCell k a), ht]
      simp
    · -- the key case: the joint law of value and observation, two ways
      have := isProbabilityMeasure_post hP
      set P := post D c
      let H : Val rT → Int × RvCell rT := fun x => (f x, (c.resolveTo x).observe k a (f x))
      have hH : Measurable H :=
        hf.prodMk (measurable_observe_uncurry.comp ((measurable_resolveTo c).prodMk
          (measurable_const.prodMk (measurable_const.prodMk hf))))
      -- resolving first: the observation is read off the drawn value
      have hlhs : (resolve D c).bind (testCell D k a) = P.map H := by
        rw [resolve, ite_eq_right hP, Measure.bind_map (measurable_resolveTo c).aemeasurable
          (measurable_testCell k a).aemeasurable, ← bind_dirac_eq_map P hH]
        refine bind_congr_right (ae_of_all _ fun x => ?_)
        simp only [testCell, post_resolveTo]
        rw [map_dirac' (measurable_testOutcome _ k a)]
      -- testing first: almost every observation has a fiber of positive mass to resolve in
      have hae : (fun x => (resolve D (c.observe k a (f x))).map (f x, ·)) =ᵐ[P]
          fun x => (P[|f ⁻¹' {f x}]).map H := by
        filter_upwards [ae_fiber_ne_zero P f] with x hx
        have hpo : post D (c.observe k a (f x)) = P[|f ⁻¹' {f x}] := post_observe hw k a (f x)
        have hne : P[|f ⁻¹' {f x}] ≠ 0 := by simp [cond_eq_zero, hx, measure_ne_top]
        rw [resolve, hpo, ite_eq_right hne,
          map_map measurable_prodMk_left (measurable_resolveTo _)]
        refine map_congr ?_
        filter_upwards [ae_cond_mem (measurableSet_obs_fiber k a (f x))] with x' hx'
        have hfx : f x' = f x := hx'
        simp only [Function.comp, H, hfx, observe_resolveTo]
      rw [hlhs]
      unfold testCell
      rw [Measure.bind_map hG.aemeasurable hR.aemeasurable, bind_congr_right hae,
        ← Measure.bind_map (g := fun y => (P[|f ⁻¹' {y}]).map H) hf.aemeasurable
          Measurable.of_discrete.aemeasurable,
        ← Measure.map_bind Measurable.of_discrete.aemeasurable hH.aemeasurable,
        bind_cond_fiber P hf]
  · rw [resolve_of_world_some hw, dirac_bind (measurable_testCell k a)]
    have hpost : post D c = dirac x0 := by simp [post, hw]
    have ht : testCell D k a c = dirac (f x0, c.observe k a (f x0)) := by
      unfold testCell
      rw [hpost, map_dirac' hG]
    rw [ht, dirac_bind hR, resolve_of_world_some (x := x0) (by simp [hw]),
      map_dirac' measurable_prodMk_left]

end Kernels

end RvCell

end ProbLang
