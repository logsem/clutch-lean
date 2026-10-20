module

public import Metrology.ProbLang.Erasure.ErasableExpr

@[expose] public section

/-! Transfer of liftings of erasable state distributions to executions. -/

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure ProbLang.Measure

/-! ## Lifting wrappers -/

section Lifting

open GradedLifting

variable {B : Type*} {L : GradedLifting.{0} B}

/-- A bijection of `[0, N)` leaves `tapeIndexUniform N` invariant. -/
theorem tapeIndexUniform_map_bijOn {N : Int} (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    (tapeIndexUniform N).map (fun x => tapeIdxOf hN (f x.val)) = tapeIndexUniform N := by
  refine Measure.ext_of_lintegral _ fun ψ _ => ?_
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete, lintegral_tapeIndexUniform hN,
    lintegral_tapeIndexUniform hN,
    ← Finset.sum_Ico_comp_of_bijOn hdom hbij (fun m => ψ (tapeIdxOf hN m))]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [tapeIdxOf_val hN (Finset.mem_Ico.1 hn).1 (Finset.mem_Ico.1 hn).2]

/-- Uniform presample coupling on the index type, along a bijection of `[0, N)`. -/
theorem tapeIndexUniform_codensity_bij [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [L.IsReflexive] {N : Int} (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    L.Rel 0 (fun p q ↦ ∃ n : Int, 0 ≤ n ∧ n < N ∧ p = tapeIdxOf hN n ∧ q = tapeIdxOf hN (f n))
      (tapeIndexUniform N) (tapeIndexUniform N) := by
  have h := rel_graph (L := L) (tapeIndexUniform N) (f := fun x => tapeIdxOf hN (f x.val))
    Measurable.of_discrete
  rw [tapeIndexUniform_map_bijOn hN f hdom hbij] at h
  exact h.mono le_rfl fun p q hp =>
    ⟨p.val, p.2.1, p.2.2, Subtype.ext (tapeIdxOf_val hN p.2.1 p.2.2).symm, hp.symm⟩

/-- Uniform presample coupling on the index type, along a bijection of `[0, N)`
(the `tv` instance of `tapeIndexUniform_codensity_bij`). -/
theorem tapeIndexUniform_addCoupl_bij {N : Int} (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    AddCoupl 0
      {p : { z : Int // 0 ≤ z ∧ z < N } × { z : Int // 0 ≤ z ∧ z < N } |
        ∃ n : Int, 0 ≤ n ∧ n < N ∧ p.1 = tapeIdxOf hN n ∧ p.2 = tapeIdxOf hN (f n)}
      (tapeIndexUniform N) (tapeIndexUniform N) :=
  (tapeIndexUniform_codensity_bij hN f hdom hbij).addCoupl

theorem tapePresample_eq_map {σ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} (hσ : σ.tapes[α]? = some ⟨N, bs⟩) :
    tapePresample σ α =
      (tapeIndexUniform N).map (fun n => σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) := by
  simp only [tapePresample, hσ]
  rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]

/-- Two same-bound tapes presample in lockstep along a bijection `f` on `[0, N)`. -/
theorem tapePresample_codensity_bij [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [L.IsReflexive] {σ σ' : State rT} {α α' : Loc} {N : Int}
    {bs bs' : List { z : Int // 0 ≤ z ∧ z < N }}
    (hσ : σ.tapes[α]? = some ⟨N, bs⟩) (hσ' : σ'.tapes[α']? = some ⟨N, bs'⟩)
    (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    L.Rel 0
      (fun τ τ' ↦ ∃ n : Int, 0 ≤ n ∧ n < N ∧
        τ = σ.update_tapes (·.insert α ⟨N, bs ++ [tapeIdxOf hN n]⟩) ∧
        τ' = σ'.update_tapes (·.insert α' ⟨N, bs' ++ [tapeIdxOf hN (f n)]⟩))
      (tapePresample σ α) (tapePresample σ' α') := by
  rw [tapePresample_eq_map hσ, tapePresample_eq_map hσ']
  refine (tapeIndexUniform_codensity_bij hN f hdom hbij).map ?_ Measurable.of_discrete
    Measurable.of_discrete
  rintro _ _ ⟨n, h0, hn, rfl, rfl⟩
  exact ⟨n, h0, hn, rfl, rfl⟩

/-- Two same-bound tapes presample in lockstep along a bijection `f` on `[0, N)`
(the `tv` instance of `tapePresample_codensity_bij`). -/
theorem tapePresample_addCoupl_bij {σ σ' : State rT} {α α' : Loc} {N : Int}
    {bs bs' : List { z : Int // 0 ≤ z ∧ z < N }}
    (hσ : σ.tapes[α]? = some ⟨N, bs⟩) (hσ' : σ'.tapes[α']? = some ⟨N, bs'⟩)
    (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    AddCoupl 0
      {p : State rT × State rT | ∃ n : Int, 0 ≤ n ∧ n < N ∧
        p.1 = σ.update_tapes (·.insert α ⟨N, bs ++ [tapeIdxOf hN n]⟩) ∧
        p.2 = σ'.update_tapes (·.insert α' ⟨N, bs' ++ [tapeIdxOf hN (f n)]⟩)}
      (tapePresample σ α) (tapePresample σ' α') :=
  (tapePresample_codensity_bij hσ hσ' hN f hdom hbij).addCoupl

/-- Running to the limit from a measure of states first runs `m` steps. -/
theorem bind_limExec_eq_pexecN (μ : Measure (State rT)) (e : Exp rT) (m : Nat) :
    μ.bind (fun σ => limExec ⟨e, σ⟩) = (μ.bind fun σ => pexecN m ⟨e, σ⟩).bind limExec := by
  have hpk : Measurable fun σ : State rT => pexecN m (⟨e, σ⟩ : Cfg rT) :=
    pexecN_measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  rw [Measure.bind_bind hpk.aemeasurable limExec.measurable.aemeasurable]
  exact congrArg _ (funext fun σ => limExec_pexecN m ⟨e, σ⟩)

/-- Clutch `ARcoupl_erasure_erasable_exp_rhs`, projected: the continuation's budget depends
on the RHS sample. -/
theorem lift_erasure_erasable_exp_rhs [AddCommMonoid B] [PartialOrder B] [IsOrderedAddMonoid B]
    [CanonicallyOrderedAdd B] [OrderTop B] {s : ENNReal →+o B} [L.IsLawful] [L.HasBind]
    [L.IsExpectationAdditive s] [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁ μ₁' : Measure (State rT)} {R : State rT → Cfg rT → Prop}
    {Φexp : Exp rT → Exp rT → Prop}
    {b b₁ : B} {ε₂ : ENNReal} {E₂ : Cfg rT → ENNReal} {n m : Nat}
    (hE₂meas : Measurable E₂)
    (hCoupl : L.Rel b₁ R μ₁ (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)) ≤ ε₂)
    (hEpsSum : b₁ + s ε₂ ≤ b)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R σ₂ ρ' →
        L.Rel (s (E₂ ρ')) Φexp (asExpr (execN n ⟨e₁, σ₂⟩)) (limExecV ρ')) :
    L.Rel b Φexp (asExpr (execN n ⟨e₁, σ₁⟩)) (limExecV ⟨e₁', σ₁'⟩) := by
  have hek : Measurable (fun σ : State rT => execN n (⟨e₁, σ⟩ : Cfg rT)) :=
    (execN_measurable n).comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  have := hErase₁.isProbabilityMeasure
  have := hErase₁'.isProbabilityMeasure
  refine IsLawful.mono ?_ ((add_le_add le_rfl (OrderHomClass.mono s hBoundSum)).trans hEpsSum)
    le_rfl
  rw [← hErase₁ e₁ n, ← hErase₁'.lim_exec e₁', bind_limExec_eq_pexecN _ _ m]
  unfold asExpr
  rw [Measure.bind_map_comm _ _ _ Cfg.measurable_expr hek.aemeasurable,
      Measure.bind_map_comm _ _ _ Cfg.measurable_expr limExec.measurable.aemeasurable]
  exact IsExpectationAdditive.bind_adv hCoupl hCont
    ((Measure.measurable_map _ Cfg.measurable_expr).comp hek)
    ((Measure.measurable_map _ Cfg.measurable_expr).comp limExec.measurable) hE₂meas

/-- Clutch `ARcoupl_erasure_erasable_exp_rhs`, projected: the continuation's slack depends
on the RHS sample (the `tv` instance of `lift_erasure_erasable_exp_rhs`). -/
theorem AddCoupl_erasure_erasable_exp_rhs [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁ μ₁' : Measure (State rT)} {R : Set (State rT × Cfg rT)}
    {Φexp : Set (Exp rT × Exp rT)}
    {ε ε₁ ε₂ : ENNReal} {E₂ : Cfg rT → ENNReal} {n m : Nat}
    (hE₂meas : Measurable E₂)
    (hCoupl : AddCoupl ε₁ R μ₁
        (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)) ≤ ε₂)
    (hEpsSum : ε₁ + ε₂ ≤ ε)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R (σ₂, ρ') →
        AddCoupl (E₂ ρ') Φexp
          (asExpr (execN n ⟨e₁, σ₂⟩))
          (limExecV ρ')) :
    AddCoupl ε Φexp
      (asExpr (execN n ⟨e₁, σ₁⟩))
      (limExecV ⟨e₁', σ₁'⟩) := by
  have := hErase₁.isProbabilityMeasure
  exact (lift_erasure_erasable_exp_rhs (L := GradedDivergence.tv.codensity)
    (s := OrderAddMonoidHom.id _) hE₂meas hCoupl.codensity hBoundSum hEpsSum hErase₁ hErase₁'
    fun σ₂ ρ' hR => (hCont σ₂ ρ' hR).codensity).addCoupl

/-- Clutch `ARcoupl_erasure_erasable`, projected to expressions. -/
theorem AddCoupl_erasure_erasable [Countable rT] [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁ μ₂ : Measure (State rT)} {R : Set (State rT × State rT)}
    {Φexp : Set (Exp rT × Exp rT)}
    {ε ε₁ ε₂ : ENNReal} {n : Nat}
    (hSum : ε₁ + ε₂ ≤ ε)
    (hCoupl : AddCoupl ε₁ R μ₁ μ₂)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₂ : ErasableExpr μ₂ σ₁')
    (hCont : ∀ σ₂ σ₂', R (σ₂, σ₂') →
        AddCoupl ε₂ Φexp
          (asExpr (execN n ⟨e₁, σ₂⟩))
          (limExecV ⟨e₁', σ₂'⟩)) :
    AddCoupl ε Φexp
      (asExpr (execN n ⟨e₁, σ₁⟩))
      (limExecV ⟨e₁', σ₁'⟩) := by
  have := hErase₂.isProbabilityMeasure
  have hd := Measure.bind_dirac_eq_map μ₂ (f := (⟨e₁', ·⟩ : State rT → Cfg rT)) .of_discrete
  refine AddCoupl_erasure_erasable_exp_rhs (m := 0) (E₂ := fun _ => ε₂)
    (R := {p | ∃ σ', p.2 = ⟨e₁', σ'⟩ ∧ R (p.1, σ')}) measurable_const ?_ (by simp [hd]) hSum
    hErase₁ hErase₂ fun σ₂ ρ ⟨σ₂', (h : ρ = _), hR⟩ => h ▸ hCont σ₂ σ₂' hR
  simpa [hd] using hCoupl.map id _ measurable_id .of_discrete fun h => ⟨_, rfl, h⟩

/-- Clutch `ARcoupl_erasure_erasable_exp_lhs`, projected: the continuation's slack depends
on the LHS sample. -/
theorem AddCoupl_erasure_erasable_exp_lhs [Countable rT] [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁' : Measure (State rT)} {R : Set (Cfg rT × State rT)}
    {Φexp : Set (Exp rT × Exp rT)}
    {ε ε₁ ε₂ : ENNReal} {E₂ : Cfg rT → ENNReal} {n : Nat}
    (hE₂meas : Measurable E₂)
    (hCoupl : AddCoupl ε₁ R (primStep ⟨e₁, σ₁⟩) μ₁')
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(primStep ⟨e₁, σ₁⟩) ≤ ε₂)
    (hEpsSum : ε₁ + ε₂ ≤ ε)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ ρ σ₂', R (ρ, σ₂') →
        AddCoupl (E₂ ρ) Φexp
          (asExpr (execN n ρ))
          (limExecV ⟨e₁', σ₂'⟩)) :
    AddCoupl ε Φexp
      (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n)))
      (limExecV ⟨e₁', σ₁'⟩) := by
  have hmassk : ∀ ρ : Cfg rT, asExpr (execN n ρ) Set.univ ≤ 1 :=
    fun _ => IsSubProbabilityMeasure.measure_univ_le_one
  rw [← hErase₁'.lim_exec e₁']
  unfold asExpr
  rw [Measure.bind_map_comm_of_discrete, Measure.bind_map_comm_of_discrete]
  exact (AddCoupl.bind_adv_lhs Measurable.of_discrete Measurable.of_discrete hE₂meas hmassk
    hBoundSum hCoupl fun {ρ σ₂'} hR => hCont ρ σ₂' hR).mono_grading hEpsSum

/-- The value distributions of the `m`-step runs, as a kernel: the program's remaining run that a
bind law's side condition sees. -/
noncomputable def execVKernel (m : Nat) : ProbabilityTheory.Kernel (Cfg rT) (Exp rT) :=
  ⟨fun ρ => asExpr (execN m ρ),
    (Measure.measurable_map _ Cfg.measurable_expr).comp (execN_measurable m)⟩

instance execVKernel.isSubMarkovKernel (m : Nat) :
    ProbabilityTheory.IsSubMarkovKernel (execVKernel (rT := rT) m) :=
  ⟨fun ρ => asExpr.isSubProbabilityMeasure (execN m ρ)⟩

/-- The side condition of a step for the kernels adequacy binds with: the `m`-step run of `h x` on
the program side, for every `m` and measurable `h`, and the limit run of `f' y` on the spec side
(Rocq `side_for_exec`). -/
def _root_.GradedLifting.BindLaw.SideForExec [Preorder B] [Top B] (law : L.BindLaw) {X Y : Type}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) (R : X → Y → B)
    (f' : Y → Cfg rT) : Prop :=
  ∀ (m : Nat) (h : X → Cfg rT) (hh : Measurable h) (hf' : Measurable f'),
    law.side μ ν R ((execVKernel m).comap h hh) (limExecVKernel.comap f' hf')

/-- A side condition that holds for all kernels holds for the kernels adequacy binds with. -/
theorem _root_.GradedLifting.BindLaw.SideForExec.of_forall [Preorder B] [Top B] {law : L.BindLaw}
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {R : X → Y → B} {f' : Y → Cfg rT}
    (h : ∀ {X' Y' : Type} [MeasurableSpace X'] [MeasurableSpace Y']
      (k₁ : ProbabilityTheory.Kernel X X') (k₂ : ProbabilityTheory.Kernel Y Y'),
        law.side μ ν R k₁ k₂) :
    law.SideForExec μ ν R f' :=
  fun _ _ _ _ => h _ _

/-- `SideForExec` survives setting leftovers to `⊤` off a set. -/
theorem _root_.GradedLifting.BindLaw.SideForExec.supp [Preorder B] [Top B] {law : L.BindLaw}
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {R : X → Y → B} {f' : Y → Cfg rT} {A : Set X} [DecidablePred (· ∈ A)]
    (h : law.SideForExec μ ν R f') : law.SideForExec μ ν (A.piecewise R fun _ _ => ⊤) f' :=
  fun m h' hh hf' => law.side_supp (h m h' hh hf')

/-- Clutch `ARcoupl_erasure_erasable_exp_lhs_kanto`, projected, for a step of any bind law whose
program and spec distributions are images of the law's head measures (Rocq
`gcoupl_erasure_prog_bind_law`). -/
theorem lift_erasure_erasable_exp_lhs_kanto_law [Preorder B] [Top B] [Zero B]
    [MeasurableSingletonClass rT] (law : L.BindLaw)
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT} {μ₁' : Measure (State rT)} {Φexp : Exp rT → Exp rT → Prop}
    {b : B} {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ₀ : Measure X} {ν₀ : Measure Y}
    {f : X → Cfg rT} {f' : Y → Cfg rT} {R : X → Y → B} {n m : Nat}
    (hErase₁' : ErasableExpr μ₁' σ₁') (hf : Measurable f) (hprog : primStep ⟨e₁, σ₁⟩ = μ₀.map f)
    (hf' : Measurable f') (hspec : μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₀ ν₀ R b) (hside : law.SideForExec μ₀ ν₀ R f')
    (hCont : ∀ x y, R x y < ⊤ →
        L.Rel (R x y) Φexp (asExpr (execN n (f x))) (limExecV (f' y))) :
    L.Rel b Φexp
      (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n)))
      (limExecV ⟨e₁', σ₁'⟩) := by
  rw [← hErase₁'.lim_exec e₁', bind_limExec_eq_pexecN _ _ m]
  unfold asExpr
  rw [Measure.bind_map_comm _ _ _ Cfg.measurable_expr (execN_measurable n).aemeasurable,
      Measure.bind_map_comm _ _ _ Cfg.measurable_expr limExec.measurable.aemeasurable, hprog,
      hspec, Measure.bind_map
        (g := fun ρ => (execN n ρ).map (·.expr)) hf (execVKernel n).measurable,
      Measure.bind_map
        (g := fun ρ => (limExec ρ).map (·.expr)) hf' limExecVKernel.measurable]
  exact law.sound (f := (execVKernel n).comap f hf) (g := limExecVKernel.comap f' hf') hhead
    (hside n f hf hf') hCont

/-- Clutch `ARcoupl_erasure_erasable_exp_lhs_kanto`, projected: the leftover depends on both
samples. -/
theorem lift_erasure_erasable_exp_lhs_kanto [LT B] [Top B] [Zero B] [L.HasBind]
    [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁' : Measure (State rT)} {Φexp : Exp rT → Exp rT → Prop}
    {b : B} {R : Cfg rT → Cfg rT → B} {n m : Nat}
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hExp : L b R (primStep ⟨e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩)))
    (hCont : ∀ ρ ρ', R ρ ρ' < ⊤ →
        L.Rel (R ρ ρ') Φexp (asExpr (execN n ρ)) (limExecV ρ')) :
    L.Rel b Φexp
      (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n)))
      (limExecV ⟨e₁', σ₁'⟩) := by
  rw [← hErase₁'.lim_exec e₁', bind_limExec_eq_pexecN _ _ m]
  unfold asExpr
  rw [Measure.bind_map_comm _ _ _ Cfg.measurable_expr (execN_measurable n).aemeasurable,
      Measure.bind_map_comm _ _ _ Cfg.measurable_expr limExec.measurable.aemeasurable]
  exact HasBind.bind_fun hExp hCont
    ((Measure.measurable_map _ Cfg.measurable_expr).comp (execN_measurable n))
    limExecV.measurable

/-- Clutch-dp `spec_coupl` erasure, projected, for a step of any bind law whose spec distribution
is an image of the law's spec-side head measure (Rocq `gcoupl_erasure_bind_law`). -/
theorem lift_erasure_erasable_law [Preorder B] [Top B] [Zero B] [MeasurableSingletonClass rT]
    (law : L.BindLaw) {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT} {μ₁ μ₁' : Measure (State rT)}
    {Φexp : Exp rT → Exp rT → Prop} {b : B} {Y : Type} [MeasurableSpace Y] {ν₀ : Measure Y}
    {f' : Y → Cfg rT} {R : State rT → Y → B} {n m : Nat}
    (hf' : Measurable f') (hspec : μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₁ ν₀ R b) (hside : law.SideForExec μ₁ ν₀ R f')
    (hErase₁ : ErasableExpr μ₁ σ₁) (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ y, R σ₂ y < ⊤ →
      L.Rel (R σ₂ y) Φexp (asExpr (execN n ⟨e₁, σ₂⟩)) (limExecV (f' y))) :
    L.Rel b Φexp (asExpr (execN n ⟨e₁, σ₁⟩)) (limExecV ⟨e₁', σ₁'⟩) := by
  have hh : Measurable (fun σ : State rT => (⟨e₁, σ⟩ : Cfg rT)) :=
    Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩
  have hek : Measurable (fun σ : State rT => execN n (⟨e₁, σ⟩ : Cfg rT)) :=
    (execN_measurable n).comp hh
  rw [← hErase₁ e₁ n, ← hErase₁'.lim_exec e₁', bind_limExec_eq_pexecN _ _ m]
  unfold asExpr
  rw [Measure.bind_map_comm _ _ _ Cfg.measurable_expr hek.aemeasurable,
      Measure.bind_map_comm _ _ _ Cfg.measurable_expr limExec.measurable.aemeasurable, hspec,
      Measure.bind_map
        (g := fun ρ => (limExec ρ).map (·.expr)) hf' limExecVKernel.measurable]
  exact law.sound (f := (execVKernel n).comap _ hh) (g := limExecVKernel.comap f' hf') hhead
    (hside n _ hh hf') hCont

/-- Clutch-dp `spec_coupl` erasure, projected: erasable distributions on both sides, coupled by a
lifting whose per-pair leftover is the continuation's budget. -/
theorem lift_erasure_erasable [LT B] [Top B] [Zero B] [L.HasBind] [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT} {μ₁ μ₁' : Measure (State rT)}
    {Φexp : Exp rT → Exp rT → Prop} {b : B} {R : State rT → Cfg rT → B} {n m : Nat}
    (hCoupl : L b R μ₁ (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hErase₁ : ErasableExpr μ₁ σ₁) (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R σ₂ ρ' < ⊤ →
      L.Rel (R σ₂ ρ') Φexp (asExpr (execN n ⟨e₁, σ₂⟩)) (limExecV ρ')) :
    L.Rel b Φexp (asExpr (execN n ⟨e₁, σ₁⟩)) (limExecV ⟨e₁', σ₁'⟩) := by
  have hek : Measurable (fun σ : State rT => execN n (⟨e₁, σ⟩ : Cfg rT)) :=
    (execN_measurable n).comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  rw [← hErase₁ e₁ n, ← hErase₁'.lim_exec e₁', bind_limExec_eq_pexecN _ _ m]
  unfold asExpr
  rw [Measure.bind_map_comm _ _ _ Cfg.measurable_expr hek.aemeasurable,
      Measure.bind_map_comm _ _ _ Cfg.measurable_expr limExec.measurable.aemeasurable]
  exact HasBind.bind_fun hCoupl hCont ((Measure.measurable_map _ Cfg.measurable_expr).comp hek)
    limExecV.measurable

/-- Clutch `ARcoupl_erasure_erasable_exp_lhs_kanto`, projected: the slack depends on both
samples (the `tv` instance of `lift_erasure_erasable_exp_lhs_kanto`). -/
theorem AddCoupl_erasure_erasable_exp_lhs_kanto [MeasurableSingletonClass rT]
    {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
    {μ₁' : Measure (State rT)} {Φexp : Set (Exp rT × Exp rT)}
    {ε : ENNReal} {E₂ : Cfg rT → Cfg rT → ENNReal}
    {n m : Nat}
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hExp : ExpCoupl ε E₂ (primStep ⟨e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩)))
    (hCont : ∀ ρ ρ',
        AddCoupl (E₂ ρ ρ') Φexp
          (asExpr (execN n ρ))
          (limExecV ρ')) :
    AddCoupl ε Φexp
      (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n)))
      (limExecV ⟨e₁', σ₁'⟩) :=
  (lift_erasure_erasable_exp_lhs_kanto hErase₁'
    (expCoupl_iff_codensity_tv.1 hExp) fun ρ ρ' _ => (hCont ρ ρ').codensity).addCoupl

end Lifting

end ProbLang
