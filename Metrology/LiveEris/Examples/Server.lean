module

public import Metrology.LiveEris.Examples.StopOrSpin
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-!
# Servers

Two servers that run forever, each flipping a coin per round and handling a request on heads.
`serve` counts requests in a heap cell, with progress "the counter went up by one". `flagServer`
raises a flag and lowers it again, with progress "the flag is up": entering a set of states, which
is what liveness adequacy needs.
-/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.LiveEris ProbLang.LiveEris.LiveWpGS
open scoped ENNReal AppGS

namespace ProbLang.LiveEris.Examples

@[pl_fold]
def serve {rT : Type _} (ℓ : Loc) : Exp rT := pl%
  rec serve u :=
    if rand(#2, #.unit) = #0 then (#(.loc ℓ) ← (!#(.loc ℓ) + #(.int 1)); serve u) else serve u

/-- The counter at `ℓ` went up by one. -/
def CtrUp {rT : Type _} (ℓ : Loc) (σ σ' : State rT) : Prop :=
  ∃ n : ℤ, σ.heap[ℓ]? = some (.int n) ∧ σ'.heap[ℓ]? = some (.int (n + 1))

@[pl_fold]
def serveFlag {rT : Type _} : Exp rT := pl%
  rec serve f :=
    if rand(#2, #.unit) = #0 then (f ← #true; f ← #false; serve f) else serve f

pl_closed serveFlag

def flagServer {rT : Type _} : Exp rT := pl% let f := alloc(#false); &serveFlag f

/-- Some heap cell holds `true`: the flag is up. -/
def FlagUp {rT : Type _} (σ : State rT) : Prop := ∃ l : Loc, σ.heap[l]? = some (.bool true)

variable {rT : Type _} {hlc : HasLC} {GF : BundledGFunctors} [LawfulProbLangℝ rT]
  [LiveGS rT hlc GF]

omit [LawfulProbLangℝ rT] in
theorem ctrUp_store (ℓ : Loc) (n : ℤ) (σ : State rT) (h : σ.heap[ℓ]? = some (.int n)) :
    CtrUp ℓ σ (σ.update_heap (·.insert ℓ (.int (n + 1)))) :=
  ⟨n, h, by simp [State.update_heap]⟩

omit [LawfulProbLangℝ rT] in
theorem flagUp_store (l : Loc) (σ : State rT) :
    FlagUp (σ.update_heap (·.insert l (.bool true))) :=
  ⟨l, by simp [State.update_heap]⟩

noncomputable abbrev ServeStmt (ℓ : Loc) : IProp GF :=
  iprop(∀ (n : ℤ) (Ψ : Val rT → IProp GF),
    ℓ ↦ (.int n : Val rT) -∗ lwp (CtrUp ℓ) ⊤ (Exp.app (serve ℓ) pl(#(.unit))) Ψ)

theorem lwp_serve_depth (ℓ : Loc) (k : ℕ) :
    ⊢@{IProp GF} □ ▷ ServeStmt (rT := rT) ℓ -∗ ∀ (n : ℤ) (Ψ : Val rT → IProp GF),
      ℓ ↦ (.int n : Val rT) -∗ ↯((2⁻¹ : ℝ≥0∞) ^ k) -∗
        lwp (CtrUp ℓ) ⊤ (Exp.app (serve ℓ) pl(#(.unit))) Ψ := by
  induction k with
  | zero =>
    iintro - %_ %_ - He
    iexfalso
    iapply Credit.err_contradict (by simp) $$ He
  | succ k IHk =>
    iintro #IH %n %Ψ Hl He
    live_pure
    live_pure
    live_bind (pl(rand(#2, #.unit)) : Exp rT)
    iapply (lwp_rand_err (F := fun m => if m = 0 then 0 else (2⁻¹ : ℝ≥0∞) ^ k) (by norm_num)
      (avg_two (by rw [zero_add, two_mul_half_pow]))) $$ He
    iintro %m ⟨%Hm, He⟩
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · live_pure
      live_pure
      live_bind (pl(!#(.loc ℓ)) : Exp rT)
      iapply lwp_load
      iframe Hl
      iintro Hl
      live_pure
      live_bind (Exp.store pl(#(.loc ℓ)) (Exp.ofVal (Val.int (n + 1))) : Exp rT)
      iapply (lwp_store_progress (v' := Val.int n) (ctrUp_store ℓ n))
      iframe Hl
      inext
      iintro Hl
      live_pure
      live_bind (Exp.app (serve (rT := rT) ℓ) pl(#(.unit)))
      iapply IH $$ %(n + 1) %_ Hl
    · live_pure
      live_pure
      live_bind (Exp.app (serve (rT := rT) ℓ) pl(#(.unit)))
      iapply IHk $$ IH %n %_ Hl
      iapply Credit.frag_ext (by simp) rfl $$ He

/-- The counter server makes progress: its spec needs no credits. -/
theorem lwp_serve (ℓ : Loc) (n : ℤ) (Ψ : Val rT → IProp GF) :
    iprop(ℓ ↦ (.int n : Val rT)) ⊢@{IProp GF}
      lwp (CtrUp ℓ) ⊤ (Exp.app (serve ℓ) pl(#(.unit))) Ψ := by
  have H : ⊢@{IProp GF} ServeStmt (rT := rT) ℓ := by
    iapply loeb_wand_intuitionistically
    iintro !> #IH %n' %Ψ' Hl
    iapply lwp_of_err_liminf_zero liminf_half_pow (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w)
    iintro %k Hk
    iapply lwp_serve_depth ℓ k $$ IH %n' %Ψ' Hl Hk
  iintro Hl
  iapply H $$ %n %Ψ Hl

noncomputable abbrev FlagStmt : IProp GF :=
  iprop(∀ (l : Loc) (Ψ : Val rT → IProp GF),
    l ↦ (.bool false : Val rT) -∗
      lwp (fun _ σ' => FlagUp σ') ⊤ (Exp.app serveFlag pl(#(.loc l))) Ψ)

theorem lwp_serveFlag_depth (k : ℕ) :
    ⊢@{IProp GF} □ ▷ FlagStmt (rT := rT) -∗ ∀ (l : Loc) (Ψ : Val rT → IProp GF),
      l ↦ (.bool false : Val rT) -∗ ↯((2⁻¹ : ℝ≥0∞) ^ k) -∗
        lwp (fun _ σ' => FlagUp σ') ⊤ (Exp.app serveFlag pl(#(.loc l))) Ψ := by
  induction k with
  | zero =>
    iintro - %_ %_ - He
    iexfalso
    iapply Credit.err_contradict (by simp) $$ He
  | succ k IHk =>
    iintro #IH %l %Ψ Hl He
    live_pure
    live_pure
    live_bind (pl(rand(#2, #.unit)) : Exp rT)
    iapply (lwp_rand_err (F := fun m => if m = 0 then 0 else (2⁻¹ : ℝ≥0∞) ^ k) (by norm_num)
      (avg_two (by rw [zero_add, two_mul_half_pow]))) $$ He
    iintro %m ⟨%Hm, He⟩
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · live_pure
      live_pure
      live_bind (Exp.store pl(#(.loc l)) (Exp.ofVal (.bool true)) : Exp rT)
      iapply (lwp_store_progress (v' := .bool false) (fun σ _ => flagUp_store l σ))
      iframe Hl
      inext
      iintro Hl
      live_pure
      live_bind (Exp.store pl(#(.loc l)) (Exp.ofVal (.bool false)) : Exp rT)
      iapply lwp_store
      iframe Hl
      iintro Hl
      live_pure
      live_bind (Exp.app (serveFlag (rT := rT)) pl(#(.loc l)))
      iapply IH $$ %l %_ Hl
    · live_pure
      live_pure
      live_bind (Exp.app (serveFlag (rT := rT)) pl(#(.loc l)))
      iapply IHk $$ IH %l %_ Hl
      iapply Credit.frag_ext (by simp) rfl $$ He

theorem lwp_serveFlag : ⊢@{IProp GF} FlagStmt (rT := rT) := by
  iapply loeb_wand_intuitionistically
  iintro !> #IH %l %Ψ Hl
  iapply lwp_of_err_liminf_zero liminf_half_pow (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w)
  iintro %k Hk
  iapply lwp_serveFlag_depth k $$ IH %l %Ψ Hl Hk

theorem lwp_flagServer (Ψ : Val rT → IProp GF) :
    ⊢@{IProp GF} lwp (fun _ σ' => FlagUp σ') ⊤ flagServer Ψ := by
  live_bind (Exp.alloc (Exp.ofVal (.bool false)) : Exp rT)
  iapply lwp_alloc
  iintro %l Hl
  live_pure
  live_bind (Exp.app (serveFlag (rT := rT)) pl(#(.loc l)))
  iapply lwp_serveFlag $$ %l %_ Hl

theorem measurableSet_flagUp : MeasurableSet {σ : State rT | FlagUp σ} := by
  have hv : MeasurableSet {o : Option (Val rT) | o = some (.bool true)} := by
    have h : MeasurableSet {w : Val rT | w = .bool true} := by
      have h := (MeasurableSet.singleton (Exp.ofVal (Val.bool true : Val rT))).preimage
        Exp.ofVal.measurable
      convert h using 1
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => h ▸ rfl, fun h => Val.ext h⟩
    convert MeasurableSet.image_some h using 1
    ext o
    simp
  have heq : {σ : State rT | FlagUp σ} =
      ⋃ l : Loc, (fun σ : State rT => σ.heap[l]?) ⁻¹' {o | o = some (.bool true)} := by
    ext σ; simp [FlagUp]
  rw [heq]
  exact MeasurableSet.iUnion fun l =>
    ((LocHeap.measurable_getElem? l).comp State.measurable_heap) hv

/-- With probability 1, the flag server makes at least `m` steps into flag-up states, for every
`m`. -/
theorem flagServer_live (σ : State ℝ) (m : ℕ) :
    1 ≤ progressBound FlagUp (fun _ => False) m ⟨flagServer, σ⟩ := by
  simpa using lwp_adequacy_liveness (GF := liveGF) (Q := fun _ σ' => FlagUp σ') (ε := 0)
    (δ := 0) (P := FlagUp) measurableSet_flagUp (by simp) (fun _ _ h => h) (by simp)
    (fun [LiveGS ℝ .hasNoLC liveGF] => by iintro -; iapply lwp_flagServer) m

end ProbLang.LiveEris.Examples
