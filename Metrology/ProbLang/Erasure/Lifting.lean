module

public import Metrology.ProbLang.Erasure.ErasableExpr
public import Metrology.Couplings.Bridges.AddCoupl

@[expose] public section

/-! # Erasure as a lifting rule

Lifting rules for programs run from an erasable state distribution (`ErasableExpr`). -/

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT]

open MeasureTheory MeasureTheory.Measure
open ProbabilityTheory
open Measurable (of_discrete)

section Lifting

open GradedLifting

variable {B : Type*} {L : GradedLifting.{0} B} {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
  {μ₁ μ₁' : Measure (State rT)} {n m : Nat}

/-! ## Presample couplings -/

/-- Uniform presample coupling on the index type, along a bijection of `[0, N)`. -/
theorem tapeIndexUniform_rel_bij [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [L.IsReflexive] {N : Int} (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    L.Rel 0 (fun p q => ∃ n : Int, 0 ≤ n ∧ n < N ∧ p = tapeIdxOf hN n ∧ q = tapeIdxOf hN (f n))
      (tapeIndexUniform N) (tapeIndexUniform N) := by
  have h := rel_graph (L := L) (tapeIndexUniform N) (f := fun x => tapeIdxOf hN (f x.val))
    of_discrete
  rw [tapeIndexUniform_map_bijOn hN f hdom hbij] at h
  exact h.mono le_rfl fun p q hp =>
    ⟨p.val, p.2.1, p.2.2, Subtype.ext (tapeIdxOf_val hN p.2.1 p.2.2).symm, hp.symm⟩

/-- The `tv` instance of `tapeIndexUniform_rel_bij`. -/
theorem tapeIndexUniform_addCoupl_bij {N : Int} (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    AddCoupl 0 {p : { z : Int // 0 ≤ z ∧ z < N } × { z : Int // 0 ≤ z ∧ z < N } |
        ∃ n : Int, 0 ≤ n ∧ n < N ∧ p.1 = tapeIdxOf hN n ∧ p.2 = tapeIdxOf hN (f n)}
      (tapeIndexUniform N) (tapeIndexUniform N) :=
  (tapeIndexUniform_rel_bij hN f hdom hbij).addCoupl

/-- Two same-bound tapes presample in lockstep along a bijection `f` on `[0, N)`. -/
theorem tapePresample_rel_bij [Zero B] [Add B] [Preorder B] [OrderTop B] [L.IsLawful]
    [L.IsReflexive] {σ σ' : State rT} {α α' : Loc} {N : Int}
    {bs bs' : List { z : Int // 0 ≤ z ∧ z < N }}
    (hσ : σ.tapes[α]? = some ⟨N, bs⟩) (hσ' : σ'.tapes[α']? = some ⟨N, bs'⟩)
    (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    L.Rel 0 (fun τ τ' => ∃ n : Int, 0 ≤ n ∧ n < N ∧
        τ = σ.update_tapes (·.insert α ⟨N, bs ++ [tapeIdxOf hN n]⟩) ∧
        τ' = σ'.update_tapes (·.insert α' ⟨N, bs' ++ [tapeIdxOf hN (f n)]⟩))
      (tapePresample σ α) (tapePresample σ' α') := by
  rw [tapePresample_eq_map hσ, tapePresample_eq_map hσ']
  refine (tapeIndexUniform_rel_bij hN f hdom hbij).map ?_ of_discrete
    of_discrete
  rintro _ _ ⟨n, h0, hn, rfl, rfl⟩
  exact ⟨n, h0, hn, rfl, rfl⟩

/-- The `tv` instance of `tapePresample_rel_bij`. -/
theorem tapePresample_addCoupl_bij {σ σ' : State rT} {α α' : Loc} {N : Int}
    {bs bs' : List { z : Int // 0 ≤ z ∧ z < N }}
    (hσ : σ.tapes[α]? = some ⟨N, bs⟩) (hσ' : σ'.tapes[α']? = some ⟨N, bs'⟩)
    (hN : 0 < N) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < N → 0 ≤ f n ∧ f n < N)
    (hbij : ∀ m : Int, 0 ≤ m → m < N → ∃! n : Int, (0 ≤ n ∧ n < N) ∧ f n = m) :
    AddCoupl 0 {p : State rT × State rT | ∃ n : Int, 0 ≤ n ∧ n < N ∧
        p.1 = σ.update_tapes (·.insert α ⟨N, bs ++ [tapeIdxOf hN n]⟩) ∧
        p.2 = σ'.update_tapes (·.insert α' ⟨N, bs' ++ [tapeIdxOf hN (f n)]⟩)}
      (tapePresample σ α) (tapePresample σ' α') :=
  (tapePresample_rel_bij hσ hσ' hN f hdom hbij).addCoupl
variable [LawfulProbLangℝ rT]

/-! ## Erasure rules for a graded lifting -/

/-- The program side of an erasure rule: running from `σ` is running from a state drawn from an
erasable `μ`. -/
theorem asExpr_execN_eq_bind_of_erasable {μ : Measure (State rT)} {σ : State rT}
    (h : ErasableExpr μ σ) (e : Exp rT) (n : Nat) :
    asExpr (execN n ⟨e, σ⟩) = μ.bind fun σ' => asExpr (execN n ⟨e, σ'⟩) := by
  rw [← h e n]
  exact asExpr_bind _ _
    ((execN_measurable n).comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩))

/-- The spec side of an erasure rule: the limit from `σ` is the limit after drawing a state from an
erasable `μ` and running `m` steps. -/
theorem limExecV_eq_bind_of_erasable {μ : Measure (State rT)} {σ : State rT}
    (h : ErasableExpr μ σ) (e : Exp rT) (m : Nat) :
    limExecV ⟨e, σ⟩ = (μ.bind fun σ' => pexecN m ⟨e, σ'⟩).bind limExecV := by
  rw [← h.lim_exec e, bind_limExec_eq_pexecN _ _ m, asExpr_bind _ _ limExec.measurable]
  rfl

section Rules

variable {Φexp : Exp rT → Exp rT → Prop} {b : B}

/-- Erasure rule for a lifting whose continuation grade depends on the spec sample (Clutch
`ARcoupl_erasure_erasable_exp_rhs`). -/
theorem lift_erasure_erasable_exp_rhs [AddCommMonoid B] [PartialOrder B] [IsOrderedAddMonoid B]
    [CanonicallyOrderedAdd B] [OrderTop B] {s : ENNReal →+o B} [L.IsLawful] [L.HasBind]
    [L.IsExpectationAdditive s] {R : State rT → Cfg rT → Prop} {b₁ : B} {ε₂ : ENNReal}
    {E₂ : Cfg rT → ENNReal}
    (hE₂meas : Measurable E₂)
    (hCoupl : L.Rel b₁ R μ₁ (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)) ≤ ε₂)
    (hEpsSum : b₁ + s ε₂ ≤ b)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R σ₂ ρ' → L.Rel (s (E₂ ρ')) Φexp (asExpr (execN n ⟨e₁, σ₂⟩)) (limExecV ρ')) :
    L.Rel b Φexp (asExpr (execN n ⟨e₁, σ₁⟩)) (limExecV ⟨e₁', σ₁'⟩) := by
  have hek : Measurable (fun σ : State rT => execN n (⟨e₁, σ⟩ : Cfg rT)) :=
    (execN_measurable n).comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  have := hErase₁.isProbabilityMeasure
  have := hErase₁'.isProbabilityMeasure
  refine IsLawful.mono ?_ ((add_le_add le_rfl (OrderHomClass.mono s hBoundSum)).trans hEpsSum)
    le_rfl
  rw [asExpr_execN_eq_bind_of_erasable hErase₁ e₁ n, limExecV_eq_bind_of_erasable hErase₁' e₁' m]
  exact IsExpectationAdditive.bind_adv hCoupl hCont (asExpr.measurable.comp hek)
    limExecV.measurable hE₂meas

/-- Erasure rule for a lifting of erasable state distributions on both sides, with the per-pair
leftover as the continuation's grade (Clutch-dp `spec_coupl` erasure). -/
theorem lift_erasure_erasable [LT B] [Top B] [Zero B] [L.HasBind] {R : State rT → Cfg rT → B}
    (hCoupl : L b R μ₁ (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hErase₁ : ErasableExpr μ₁ σ₁) (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R σ₂ ρ' < ⊤ →
      L.Rel (R σ₂ ρ') Φexp (asExpr (execN n ⟨e₁, σ₂⟩)) (limExecV ρ')) :
    L.Rel b Φexp (asExpr (execN n ⟨e₁, σ₁⟩)) (limExecV ⟨e₁', σ₁'⟩) := by
  have hek : Measurable (fun σ : State rT => execN n (⟨e₁, σ⟩ : Cfg rT)) :=
    (execN_measurable n).comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  rw [asExpr_execN_eq_bind_of_erasable hErase₁ e₁ n, limExecV_eq_bind_of_erasable hErase₁' e₁' m]
  exact HasBind.bind_fun hCoupl hCont (asExpr.measurable.comp hek) limExecV.measurable

/-- Erasure rule for a lifting of the program's prim step and the `m`-step spec run, with the
continuation grade depending on both samples (Clutch `ARcoupl_erasure_erasable_exp_lhs_kanto`). -/
theorem lift_erasure_erasable_exp_lhs_kanto [LT B] [Top B] [Zero B] [L.HasBind]
    {R : Cfg rT → Cfg rT → B}
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hExp : L b R (primStep ⟨e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩)))
    (hCont : ∀ ρ ρ', R ρ ρ' < ⊤ → L.Rel (R ρ ρ') Φexp (asExpr (execN n ρ)) (limExecV ρ')) :
    L.Rel b Φexp (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n))) (limExecV ⟨e₁', σ₁'⟩) := by
  rw [asExpr_bind _ _ (execN_measurable n), limExecV_eq_bind_of_erasable hErase₁' e₁' m]
  exact HasBind.bind_fun hExp hCont (asExpr.measurable.comp (execN_measurable n))
    limExecV.measurable

/-! ## Erasure rules for a bind law -/

/-- The value distributions of the `m`-step runs, as a kernel. -/
noncomputable def execVKernel (m : Nat) : Kernel (Cfg rT) (Exp rT) :=
  ⟨fun ρ => asExpr (execN m ρ),
    (measurable_map _ Cfg.measurable_expr).comp (execN_measurable m)⟩

instance execVKernel.isSubMarkovKernel (m : Nat) :
    IsSubMarkovKernel (execVKernel (rT := rT) m) :=
  ⟨fun ρ => asExpr.isSubProbabilityMeasure (execN m ρ)⟩

section Law

variable [Preorder B] [Top B] {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

/-- The side condition of a bind law at the kernels the erasure rules bind with (Rocq
`side_for_exec`). -/
def _root_.GradedLifting.BindLaw.SideForExec (law : L.BindLaw) (μ : Measure X) (ν : Measure Y)
    (R : X → Y → B) (f' : Y → Cfg rT) : Prop :=
  ∀ (m : Nat) (h : X → Cfg rT) (hh : Measurable h) (hf' : Measurable f'),
    law.side μ ν R ((execVKernel m).comap h hh) (limExecVKernel.comap f' hf')

/-- A side condition that holds for all kernels holds for the kernels adequacy binds with. -/
theorem _root_.GradedLifting.BindLaw.SideForExec.of_forall {law : L.BindLaw} {μ : Measure X}
    {ν : Measure Y} {R : X → Y → B} {f' : Y → Cfg rT}
    (h : ∀ {X' Y' : Type} [MeasurableSpace X'] [MeasurableSpace Y']
      (k₁ : Kernel X X') (k₂ : Kernel Y Y'),
        law.side μ ν R k₁ k₂) :
    law.SideForExec μ ν R f' :=
  fun _ _ _ _ => h _ _

/-- `SideForExec` survives setting leftovers to `⊤` off a set. -/
theorem _root_.GradedLifting.BindLaw.SideForExec.supp {law : L.BindLaw} {μ : Measure X}
    {ν : Measure Y} {R : X → Y → B} {f' : Y → Cfg rT} {A : Set X} [DecidablePred (· ∈ A)]
    (h : law.SideForExec μ ν R f') : law.SideForExec μ ν (A.piecewise R fun _ _ => ⊤) f' :=
  fun m h' hh hf' => law.side_supp (h m h' hh hf')

/-- Erasure rule for a bind law between the program's prim step and the `m`-step spec run, both
given as pushforwards (Rocq `gcoupl_erasure_prog_bind_law`). -/
theorem lift_erasure_erasable_exp_lhs_kanto_law [Zero B] (law : L.BindLaw) {μ₀ : Measure X}
    {ν₀ : Measure Y} {f : X → Cfg rT} {f' : Y → Cfg rT} {R : X → Y → B}
    (hErase₁' : ErasableExpr μ₁' σ₁') (hf : Measurable f) (hprog : primStep ⟨e₁, σ₁⟩ = μ₀.map f)
    (hf' : Measurable f') (hspec : μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₀ ν₀ R b) (hside : law.SideForExec μ₀ ν₀ R f')
    (hCont : ∀ x y, R x y < ⊤ → L.Rel (R x y) Φexp (asExpr (execN n (f x))) (limExecV (f' y))) :
    L.Rel b Φexp (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n))) (limExecV ⟨e₁', σ₁'⟩) := by
  rw [asExpr_bind _ _ (execN_measurable n), limExecV_eq_bind_of_erasable hErase₁' e₁' m, hprog,
    hspec, bind_map (g := fun ρ => asExpr (execN n ρ)) hf.aemeasurable
      (execVKernel n).measurable.aemeasurable,
    bind_map (g := limExecV) hf'.aemeasurable limExecV.measurable.aemeasurable]
  exact law.sound (f := (execVKernel n).comap f hf) (g := limExecVKernel.comap f' hf') hhead
    (hside n f hf hf') hCont

/-- Erasure rule for a bind law between an erasable state distribution and the `m`-step spec run
(Rocq `gcoupl_erasure_bind_law`). -/
theorem lift_erasure_erasable_law [Zero B] (law : L.BindLaw) {ν₀ : Measure Y} {f' : Y → Cfg rT}
    {R : State rT → Y → B}
    (hf' : Measurable f') (hspec : μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₁ ν₀ R b) (hside : law.SideForExec μ₁ ν₀ R f')
    (hErase₁ : ErasableExpr μ₁ σ₁) (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ y, R σ₂ y < ⊤ →
      L.Rel (R σ₂ y) Φexp (asExpr (execN n ⟨e₁, σ₂⟩)) (limExecV (f' y))) :
    L.Rel b Φexp (asExpr (execN n ⟨e₁, σ₁⟩)) (limExecV ⟨e₁', σ₁'⟩) := by
  have hh : Measurable (fun σ : State rT => (⟨e₁, σ⟩ : Cfg rT)) :=
    Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩
  rw [asExpr_execN_eq_bind_of_erasable hErase₁ e₁ n, limExecV_eq_bind_of_erasable hErase₁' e₁' m,
    hspec, bind_map (g := limExecV) hf'.aemeasurable limExecV.measurable.aemeasurable]
  exact law.sound (f := (execVKernel n).comap _ hh) (g := limExecVKernel.comap f' hf') hhead
    (hside n _ hh hf') hCont

end Law

end Rules

/-! ## `tv` corollaries -/

section Tv

variable {Φexp : Set (Exp rT × Exp rT)} {ε ε₁ ε₂ : ENNReal}

/-- The `tv` instance of `lift_erasure_erasable_exp_rhs` (Clutch
`ARcoupl_erasure_erasable_exp_rhs`). -/
theorem addCoupl_erasable_exp_rhs
    {R : Set (State rT × Cfg rT)} {E₂ : Cfg rT → ENNReal}
    (hE₂meas : Measurable E₂)
    (hCoupl : AddCoupl ε₁ R μ₁ (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)) ≤ ε₂)
    (hEpsSum : ε₁ + ε₂ ≤ ε)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R (σ₂, ρ') → AddCoupl (E₂ ρ') Φexp (asExpr (execN n ⟨e₁, σ₂⟩))
          (limExecV ρ')) :
    AddCoupl ε Φexp (asExpr (execN n ⟨e₁, σ₁⟩)) (limExecV ⟨e₁', σ₁'⟩) := by
  have := hErase₁.isProbabilityMeasure
  exact (lift_erasure_erasable_exp_rhs
    (s := OrderAddMonoidHom.id _) hE₂meas hCoupl.codensity hBoundSum hEpsSum hErase₁ hErase₁'
    fun σ₂ ρ' hR => (hCont σ₂ ρ' hR).codensity).addCoupl

/-- Erasure rule for a `tv` coupling of erasable states with constant continuation slack (Clutch
`ARcoupl_erasure_erasable`). -/
theorem addCoupl_erasable [Countable rT]
    {μ₂ : Measure (State rT)} {R : Set (State rT × State rT)}
    (hSum : ε₁ + ε₂ ≤ ε)
    (hCoupl : AddCoupl ε₁ R μ₁ μ₂)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₂ : ErasableExpr μ₂ σ₁')
    (hCont : ∀ σ₂ σ₂', R (σ₂, σ₂') → AddCoupl ε₂ Φexp (asExpr (execN n ⟨e₁, σ₂⟩))
          (limExecV ⟨e₁', σ₂'⟩)) :
    AddCoupl ε Φexp (asExpr (execN n ⟨e₁, σ₁⟩)) (limExecV ⟨e₁', σ₁'⟩) := by
  have := hErase₂.isProbabilityMeasure
  have hd := bind_dirac_eq_map μ₂ (f := (⟨e₁', ·⟩ : State rT → Cfg rT)) .of_discrete
  refine addCoupl_erasable_exp_rhs (m := 0) (E₂ := fun _ => ε₂)
    (R := {p | ∃ σ', p.2 = ⟨e₁', σ'⟩ ∧ R (p.1, σ')}) measurable_const ?_ (by simp [hd]) hSum
    hErase₁ hErase₂ fun σ₂ ρ ⟨σ₂', (h : ρ = _), hR⟩ => h ▸ hCont σ₂ σ₂' hR
  simpa [hd] using hCoupl.map id _ measurable_id .of_discrete fun h => ⟨_, rfl, h⟩

/-- Erasure rule for a `tv` coupling of the program's prim step and an erasable spec state (Clutch
`ARcoupl_erasure_erasable_exp_lhs`). -/
theorem addCoupl_erasable_exp_lhs [Countable rT]
    {R : Set (Cfg rT × State rT)} {E₂ : Cfg rT → ENNReal}
    (hE₂meas : Measurable E₂)
    (hCoupl : AddCoupl ε₁ R (primStep ⟨e₁, σ₁⟩) μ₁')
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(primStep ⟨e₁, σ₁⟩) ≤ ε₂)
    (hEpsSum : ε₁ + ε₂ ≤ ε)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ ρ σ₂', R (ρ, σ₂') → AddCoupl (E₂ ρ) Φexp (asExpr (execN n ρ))
          (limExecV ⟨e₁', σ₂'⟩)) :
    AddCoupl ε Φexp (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n))) (limExecV ⟨e₁', σ₁'⟩) := by
  have hmassk : ∀ ρ : Cfg rT, asExpr (execN n ρ) Set.univ ≤ 1 :=
    fun _ => IsSubProbabilityMeasure.measure_univ_le_one
  rw [← hErase₁'.lim_exec e₁']
  unfold asExpr
  rw [bind_map_comm_of_discrete, bind_map_comm_of_discrete]
  exact (AddCoupl.bind_adv_lhs of_discrete of_discrete hE₂meas hmassk
    hBoundSum hCoupl fun {ρ σ₂'} hR => hCont ρ σ₂' hR).mono_grading hEpsSum

/-- The `tv` instance of `lift_erasure_erasable_exp_lhs_kanto` (Clutch
`ARcoupl_erasure_erasable_exp_lhs_kanto`). -/
theorem addCoupl_erasable_exp_lhs_kanto
    {E₂ : Cfg rT → Cfg rT → ENNReal}
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hExp : ExpCoupl ε E₂ (primStep ⟨e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩)))
    (hCont : ∀ ρ ρ',
        AddCoupl (E₂ ρ ρ') Φexp (asExpr (execN n ρ)) (limExecV ρ')) :
    AddCoupl ε Φexp (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n))) (limExecV ⟨e₁', σ₁'⟩) :=
  (lift_erasure_erasable_exp_lhs_kanto hErase₁'
    (expCoupl_iff_codensity_tv.1 hExp) fun ρ ρ' _ => (hCont ρ ρ').codensity).addCoupl

end Tv

end Lifting

end ProbLang
