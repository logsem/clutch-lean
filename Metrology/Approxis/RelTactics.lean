module

public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.Model
public import Metrology.Approxis.AppRelRules

@[expose] public section

/-! # Relational tactics -/

namespace ProbLang
open Iris Iris.BI Iris.ProofMode

/-! ### Pure-step tactics -/

macro "rel_pure_l" : tactic =>
  `(tactic| (iapply (refines_pure_l (K := []) (Hφ := by trivial)); inext))
macro "rel_pure_r" : tactic => `(tactic| iapply (refines_pure_r (K := []) (Hφ := by trivial)))
macro "rel_pures_l" : tactic => `(tactic| (try repeat rel_pure_l))
macro "rel_pures_r" : tactic => `(tactic| (try repeat rel_pure_r))

/-! ### Binding / structural -/

macro "rel_apply " L:term : tactic => `(tactic| iapply ($L : _))
macro "rel_arrow_val" : tactic => `(tactic| iapply refines_arrow_val)
macro "rel_vals" : tactic => `(tactic| iapply refines_ret)

/-! ### Heap operations -/

macro "rel_alloc_l" : tactic => `(tactic| iapply (refines_alloc_l (K := [])))
macro "rel_alloc_r" : tactic => `(tactic| iapply (refines_alloc_r (K := [])))
macro "rel_load_l" : tactic => `(tactic| iapply (refines_load_l (K := [])))
macro "rel_load_r" : tactic => `(tactic| iapply (refines_load_r (K := [])))
macro "rel_store_l" : tactic => `(tactic| iapply (refines_store_l (K := [])))
macro "rel_store_r" : tactic => `(tactic| iapply (refines_store_r (K := [])))

/-! ### Tape operations -/

macro "rel_alloctape_l" : tactic => `(tactic| iapply (refines_alloctape_l (K := [])))
macro "rel_alloctape_r" : tactic => `(tactic| iapply (refines_alloctape_r (K := [])))

/-! ### Rand operations -/

macro "rel_randU_l " Hz:term : tactic => `(tactic| iapply (refines_randU_l (K := []) $Hz))
macro "rel_randU_r " Hz:term : tactic => `(tactic| iapply (refines_randU_r (K := []) $Hz))
macro "rel_randT_l" : tactic => `(tactic| iapply (refines_randT_l (K := [])))
macro "rel_randT_r" : tactic => `(tactic| iapply (refines_randT_r (K := [])))

end ProbLang
