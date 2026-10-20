module

import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.Compatibility
public import Metrology.ProbLang.Syntax.LocallyClosed

/-! # Compatibility lemmas for state and sampling

Closed `refines` compatibility rules for `alloc`, `load`, `store`, `tape` and `rand`, used by the
fundamental theorem. -/

@[expose] public section

-- these rules use the @[discrete] lifting lemmas without being discrete themselves
set_option linter.discrete false

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting
open scoped AppGS

namespace ProbLang

section Compatibility
variable {rT : Type} [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B]
  [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [IR : MicrometerRGS rT hlc GF] [BudgetCreditGS B GF]
  [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]
  [L.HasBind]

/-! ### Allocation -/

/-- Compatibility of `alloc`: both sides allocate and the new cells are tied by the invariant of
`lrel_ref A`. -/
theorem refines_alloc {e e' : Exp rT} {A : lrel rT GF} : iprop%
    refines L ⊤ e e' A ⊢ refines L ⊤ (.alloc e) (.alloc e') (lrel_ref A) := by
  show _ ⊢ refines L ⊤ (Ectx.fill [EctxItem.alloc] e) (Ectx.fill [EctxItem.alloc] e') (lrel_ref A)
  iintro IH
  iapply refines_bind [EctxItem.alloc] [EctxItem.alloc] $$ IH
  iintro %v %v' #HA
  rw [Ectx.fill_alloc, Ectx.fill_alloc, Ectx.eq_fill_nil (Exp.alloc v.1),
    Ectx.eq_fill_nil (Exp.alloc v'.1)]
  iapply refines_alloc_r
  iintro %l' Hl'
  iapply refines_alloc_l
  iintro %l Hl
  imod Iris.inv_alloc (P := iprop(∃ w1 w2, appHeapFrag l w1 ∗ specHeapFrag l' w2 ∗ A w1 w2))
    $$ [Hl Hl' HA] with #HInv
  · iintro !>
    iexists v, v'
    iframe Hl Hl' HA
  iapply refines_ret (e1 := Ectx.fill [] pl(#(.loc l))) (e2 := Ectx.fill [] pl(#(.loc l')))
    (v1 := .loc l) (v2 := .loc l') rfl rfl
  imodintro
  iunfold lrel_ref
  iexists l, l'
  iframe HInv
  itrivial

/-- Compatibility of tape allocation: both sides allocate an empty tape, tied by an invariant. -/
theorem refines_alloctape {e e' : Exp rT} : iprop%
    refines L ⊤ e e' lrel_int ⊢@{IProp GF} refines L ⊤ (.tape e) (.tape e') lrel_tape := by
  show _ ⊢@{IProp GF}
    refines L ⊤ (Ectx.fill [EctxItem.tape] e) (Ectx.fill [EctxItem.tape] e') lrel_tape
  iintro IH
  iapply refines_bind [EctxItem.tape] [EctxItem.tape] $$ IH
  iintro %v %v' Hint
  iunfold lrel_int at Hint
  icases Hint with ⟨%n, %hv, %hv'⟩
  rw [Ectx.fill_tape, Ectx.fill_tape, hv, hv',
    Ectx.eq_fill_nil (pl(tape(#(.int n))) : Exp rT)]
  iapply refines_alloctape_r
  iintro %l' Hl'
  iapply refines_alloctape_l
  iintro %l Hl
  imod Iris.inv_alloc (P := iprop(appTapesFrag l ⟨n, []⟩ ∗ specTapesFrag l' ⟨n, []⟩))
    $$ [Hl Hl'] with #HInv
  · ihave Hl'e := spec_natTape_to_empty $$ Hl'
    rw [← show Tape.empty n = ⟨n, []⟩ from rfl]
    iintro !>
    iframe Hl Hl'e
  iapply refines_ret (e1 := Ectx.fill [] pl(#(.lbl l))) (e2 := Ectx.fill [] pl(#(.lbl l')))
    (v1 := .lbl l) (v2 := .lbl l') rfl rfl
  imodintro
  iunfold lrel_tape
  iexists l, l', n
  iframe HInv
  itrivial

/-! ### Loads and stores -/

/-- Compatibility of `load`: opens the `lrel_ref A` invariant around the atomic left load. -/
theorem refines_load {e e' : Exp rT} {A : lrel rT GF} : iprop%
    refines L ⊤ e e' (lrel_ref A) ⊢ refines L ⊤ (.load e) (.load e') A := by
  show _ ⊢ refines L ⊤ (Ectx.fill [EctxItem.load] e) (Ectx.fill [EctxItem.load] e') A
  iintro IH
  iapply refines_bind [EctxItem.load] [EctxItem.load] $$ IH
  iintro %v %v' HRef
  iunfold lrel_ref at HRef
  icases HRef with ⟨%l, %l', %heq, %heq', #Hinv⟩
  rw [Ectx.fill_load, Ectx.fill_load, heq, heq', Ectx.eq_fill_nil (pl(!#(.loc l)) : Exp rT)]
  iapply refines_atomic_l (OpenInv.of_atomic (Atomic.load' l))
  iintro %K' Hr
  iinv Hinv with ⟨%w1, %w2, >Hw1, >Hw2, #HwAL⟩ Hclose
  imodintro
  ihave HStep := step_load K' $$ [$Hr $Hw2]
  iapply specUpdate_wp
  iapply specUpdate_bind Std.LawfulSet.subset_refl
  iframe HStep
  iintro ⟨HKRes, Hw2'⟩
  iapply specUpdate_ret
  have HE : (∅ : CoPset) ⊆ ⊤ \ ↑(logN.@ (l, l')) := Std.LawfulSet.empty_subset
  -- `A w1 w2` from the invariant is still under ▷; spend the load's step to remove it.
  iapply wp_step_fupd HE Exp.load_toVal?_eq_none
  isplitl [HwAL]
  · iapply step_fupd_intro HE $$ HwAL
  iapply wp_load
  iframe Hw1
  iintro Hw1' #HwA
  imod Hclose $$ [Hw1' Hw2' HwA] with -
  · iintro !>
    iexists w1, w2
    iframe Hw1' Hw2' HwA
  imodintro
  iexists Exp.ofVal w2
  iframe HKRes
  iapply refines_ret (e1 := Ectx.fill [] w1.1) (e2 := Exp.ofVal w2) rfl rfl
  imodintro
  iexact HwA

/-- Compatibility of `store`: opens the `lrel_ref A` invariant around the atomic left store. -/
theorem refines_store {e1 e2 e1' e2' : Exp rT} {A : lrel rT GF} : iprop%
    refines L ⊤ e1 e1' (lrel_ref A) ⊢
    refines L ⊤ e2 e2' A -∗ refines L ⊤ (.store e1 e2) (.store e1' e2') lrel_unit := by
  show _ ⊢ refines L ⊤ e2 e2' A -∗
    refines L ⊤ (Ectx.fill [EctxItem.storeR e1] e2) (Ectx.fill [EctxItem.storeR e1'] e2') lrel_unit
  iintro IH1 IH2
  iapply refines_bind [EctxItem.storeR e1] [EctxItem.storeR e1'] $$ IH2
  iintro %w %w' #HwA
  rw [show Ectx.fill [EctxItem.storeR e1] w.1 = Ectx.fill [EctxItem.storeL w] e1 from rfl,
    show Ectx.fill [EctxItem.storeR e1'] w'.1 = Ectx.fill [EctxItem.storeL w'] e1' from rfl]
  iapply refines_bind [EctxItem.storeL w] [EctxItem.storeL w'] $$ IH1
  iintro %v %v' HRef
  iunfold lrel_ref at HRef
  icases HRef with ⟨%l, %l', %heq, %heq', #Hinv⟩
  rw [show Ectx.fill [EctxItem.storeL w] v.1 = Exp.store v.1 w.1 from rfl,
    show Ectx.fill [EctxItem.storeL w'] v'.1 = Exp.store v'.1 w'.1 from rfl, heq, heq',
    Ectx.eq_fill_nil (Exp.store pl(#(.loc l)) w.1)]
  iapply refines_atomic_l (OpenInv.of_atomic (Atomic.store' l w))
  iintro %K' Hr
  iinv Hinv with ⟨%v1, %v2, >Hv1, >Hv2, -⟩ Hclose
  imodintro
  ihave HStep := step_store K' w'.2 (Exp.toVal?_ofVal w') $$ [$Hr $Hv2]
  iapply specUpdate_wp
  iapply specUpdate_bind Std.LawfulSet.subset_refl
  iframe HStep
  iintro ⟨HKRes, Hv2'⟩
  iapply specUpdate_ret
  rw [show Exp.store pl(#(.loc l)) w.1 = .store pl(#(.loc l)) (.ofVal w) from rfl]
  iapply wp_store
  iframe Hv1
  iintro Hw1'
  imod Hclose $$ [Hw1' Hv2' HwA] with -
  · iintro !>
    iexists w, w'
    iframe Hw1' Hv2' HwA
  imodintro
  iexists pl(#(.unit))
  iframe HKRes
  iapply refines_ret (e1 := Ectx.fill [] pl(#(.unit))) (v1 := .unit) (v2 := .unit) rfl rfl
  imodintro
  iapply lrel_unit_lit

/-! ### Sampling: shared machinery -/

/-- Closes the tape invariant again once both tapes are handed back empty. -/
theorem natTapes_empty_close {α α' : Loc} {z : Int} : iprop%
    appNatTape α z [] ∗ specNatTape α' z [] ⊢@{IProp GF}
    ▷ (appTapesFrag α ⟨z, []⟩ ∗ specTapesFrag α' ⟨z, []⟩) :=
  (sep_mono app_natTape_to_empty spec_natTape_to_empty).trans later_intro

/-- Two draws `rand z` from tapes shared through an `lrel_tape` invariant, coupled along the
identity; the tape bound `N` need not equal `z`. -/
theorem refines_rand_lbl_of_pos {A : lrel rT GF} {α α' : Loc} {N z : Int} (hz : 0 < z)
    (HA : ∀ m : Int, 0 ≤ m → m < z → ⊢ A.car (.int m) (.int m)) :
    Iris.inv (logN.@ (α, α')) iprop(appTapesFrag α ⟨N, []⟩ ∗ specTapesFrag α' ⟨N, []⟩) ⊢
    refines L ⊤ pl(rand(#(.int z), #(.lbl α))) pl(rand(#(.int z), #(.lbl α'))) A := by
  iintro #Hinv
  rw [Ectx.eq_fill_nil (pl(rand(#(.int z), #(.lbl α))) : Exp rT)]
  iapply refines_atomic_l (OpenInv.of_atomic (Atomic.rand_lbl' z α))
  iintro %K' Hr
  iinv Hinv with ⟨>Hα, >Hα'⟩ Hclose
  imodintro
  ihave HαN := app_empty_to_natTape $$ Hα
  ihave Hα'N := spec_empty_to_natTape $$ Hα'
  rcases eq_or_ne z N with rfl | hNz
  on_goal 1 => iapply wp_couple_rand_lbl_rand_lbl z id id_dom_range id_bij_range hz K' _ α α'
  on_goal 2 =>
    iapply wp_couple_rand_lbl_rand_lbl_wrong z N id id_dom_range id_bij_range hz hNz K' _ α α' [] []
  all_goals
    iframe HαN Hα'N Hr
    iintro %m ⟨HαRet, Hα'Ret, HKRes, %hm⟩
    ihave HCloseArg := natTapes_empty_close $$ [$HαRet $Hα'Ret]
    imod Hclose $$ HCloseArg with -
    imodintro
    iexists pl(#(.int (id m)))
    iframe HKRes
    iapply refines_ret (e1 := Ectx.fill [] (Val.int m : Val rT).1) (e2 := pl(#(.int (id m))))
      (v1 := .int m) (v2 := .int m) rfl rfl
    imodintro
    iapply HA m hm.1 hm.2

/-- Two unlabelled draws `rand z #()`, coupled along the identity. -/
theorem refines_rand_unit_of_pos {A : lrel rT GF} {z : Int} (hz : 0 < z)
    (HA : ∀ m : Int, 0 ≤ m → m < z → ⊢ A.car (.int m) (.int m)) :
    ⊢ refines L ⊤ pl(rand(#(.int z), #(.unit))) pl(rand(#(.int z), #(.unit))) A := by
  rw [Ectx.eq_fill_nil (pl(rand(#(.int z), #(.unit))) : Exp rT)]
  iapply refines_couple_rands_lr id id_dom_range id_bij_range hz
  iintro %m ⟨%hm0, %hmz⟩
  iapply refines_ret (e1 := Ectx.fill [] pl(#(.int m))) (e2 := Ectx.fill [] pl(#(.int (id m))))
    (v1 := .int m) (v2 := .int m) rfl rfl
  imodintro
  iapply HA m hm0 hmz

/-! ### Sampling: compatibility at `nat` -/

/-- Compatibility of `rand` with a tape at `nat`; the fundamental theorem uses
`refines_rand_tape_int`. -/
theorem refines_rand_tape {e1 e1' e2 e2' : Exp rT} : iprop%
    refines L ⊤ e1 e1' lrel_pos_nat ⊢@{IProp GF}
    refines L ⊤ e2 e2' lrel_tape -∗ refines L ⊤ (.rand e1 e2) (.rand e1' e2') lrel_nat := by
  show _ ⊢@{IProp GF} refines L ⊤ e2 e2' lrel_tape -∗
    refines L ⊤ (Ectx.fill [EctxItem.randR e1] e2) (Ectx.fill [EctxItem.randR e1'] e2') lrel_nat
  iintro IH1 IH2
  iapply refines_bind [EctxItem.randR e1] [EctxItem.randR e1'] $$ IH2
  iintro %w %w' HTapeRel
  iunfold lrel_tape at HTapeRel
  icases HTapeRel with ⟨%α, %α', %N, %hw, %hw', #Hinv⟩
  rw [show Ectx.fill [EctxItem.randR e1] w.1 = Ectx.fill [EctxItem.randL w] e1 from rfl,
    show Ectx.fill [EctxItem.randR e1'] w'.1 = Ectx.fill [EctxItem.randL w'] e1' from rfl]
  iapply refines_bind [EctxItem.randL w] [EctxItem.randL w'] $$ IH1
  iintro %v %v' HPosNat
  iunfold lrel_pos_nat at HPosNat
  icases HPosNat with ⟨%M, %hM, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.randL w] v.1 = Exp.rand v.1 w.1 from rfl,
    show Ectx.fill [EctxItem.randL w'] v'.1 = Exp.rand v'.1 w'.1 from rfl, hv, hv', hw, hw']
  iapply refines_rand_lbl_of_pos (by exact_mod_cast hM) (fun m h0 _ => lrel_nat_lit h0) $$ Hinv

/-- Compatibility of `rand` without a tape at `nat`; the fundamental theorem uses
`refines_rand_unit_int`. -/
theorem refines_rand_unit {e e' : Exp rT} : iprop%
    refines L ⊤ e e' lrel_pos_nat ⊢@{IProp GF}
    refines L ⊤ (Ectx.fill [EctxItem.randL .unit] e) (Ectx.fill [EctxItem.randL .unit] e')
      lrel_nat := by
  iintro IH
  iapply refines_bind [EctxItem.randL .unit] [EctxItem.randL .unit] $$ IH
  iintro %v %v' HPosNat
  iunfold lrel_pos_nat at HPosNat
  icases HPosNat with ⟨%n, %hn, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.randL .unit] v.1 = Exp.rand v.1 pl(#(.unit)) from rfl,
    show Ectx.fill [EctxItem.randL .unit] v'.1 = Exp.rand v'.1 pl(#(.unit)) from rfl, hv, hv']
  iapply refines_rand_unit_of_pos (by exact_mod_cast hn) fun m h0 _ => lrel_nat_lit h0

/-! ### Sampling: compatibility at `int` -/

/-- Compatibility of `rand` with a tape at `int`; a non-positive bound returns `-1` on both
sides. -/
theorem refines_rand_tape_int {e1 e1' e2 e2' : Exp rT} : iprop%
    refines L ⊤ e1 e1' lrel_int ⊢@{IProp GF}
    refines L ⊤ e2 e2' lrel_tape -∗ refines L ⊤ (.rand e1 e2) (.rand e1' e2') lrel_int := by
  show _ ⊢@{IProp GF} refines L ⊤ e2 e2' lrel_tape -∗
    refines L ⊤ (Ectx.fill [EctxItem.randR e1] e2) (Ectx.fill [EctxItem.randR e1'] e2') lrel_int
  iintro IH1 IH2
  iapply refines_bind [EctxItem.randR e1] [EctxItem.randR e1'] $$ IH2
  iintro %w %w' HTapeRel
  iunfold lrel_tape at HTapeRel
  icases HTapeRel with ⟨%α, %α', %N, %hw, %hw', #Hinv⟩
  rw [show Ectx.fill [EctxItem.randR e1] w.1 = Ectx.fill [EctxItem.randL w] e1 from rfl,
    show Ectx.fill [EctxItem.randR e1'] w'.1 = Ectx.fill [EctxItem.randL w'] e1' from rfl]
  iapply refines_bind [EctxItem.randL w] [EctxItem.randL w'] $$ IH1
  iintro %v %v' HInt
  iunfold lrel_int at HInt
  icases HInt with ⟨%n, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.randL w] v.1 = Exp.rand v.1 w.1 from rfl,
    show Ectx.fill [EctxItem.randL w'] v'.1 = Exp.rand v'.1 w'.1 from rfl, hv, hv', hw, hw']
  by_cases hnpos : 0 < n
  · iapply refines_rand_lbl_of_pos hnpos (fun m _ _ => lrel_int_lit m) $$ Hinv
  · rw [Ectx.eq_fill_nil (pl(rand(#(.int n), #(.lbl α))) : Exp rT)]
    iapply refines_atomic_l (OpenInv.of_atomic (Atomic.rand_lbl' n α))
    iintro %K' Hr
    iinv Hinv with ⟨>Hα, >Hα'⟩ Hclose
    imodintro
    iapply wp_rand_lbl_nonpos_r K' hnpos
    iframe Hr Hα'
    iintro Hα'New HKRes
    iapply wp_rand_lbl_nonpos hnpos
    iframe Hα
    iintro HαNew
    imod Hclose $$ [HαNew Hα'New] with -
    · iintro !>; iframe HαNew Hα'New
    imodintro
    iexists pl(#(.int (-1)))
    iframe HKRes
    iapply refines_ret (e1 := Ectx.fill [] pl(#(.int (-1)))) (v1 := .int (-1)) (v2 := .int (-1))
      rfl rfl
    imodintro
    iapply lrel_int_lit (-1)

/-- Compatibility of the unlabelled `rand e #()` at `int`, stated in the hole form that
`bin_log_related_rand_unit` produces. -/
theorem refines_rand_unit_int {e e' : Exp rT} : iprop%
    refines L ⊤ e e' lrel_int ⊢@{IProp GF}
    refines L ⊤ (Ectx.fill [EctxItem.randL .unit] e) (Ectx.fill [EctxItem.randL .unit] e')
      lrel_int := by
  iintro IH
  iapply refines_bind [EctxItem.randL .unit] [EctxItem.randL .unit] $$ IH
  iintro %v %v' HInt
  iunfold lrel_int at HInt
  icases HInt with ⟨%n, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.randL .unit] v.1 = Exp.rand v.1 pl(#(.unit)) from rfl,
    show Ectx.fill [EctxItem.randL .unit] v'.1 = Exp.rand v'.1 pl(#(.unit)) from rfl, hv, hv']
  by_cases hnpos : 0 < n
  · iapply refines_rand_unit_of_pos hnpos fun m _ _ => lrel_int_lit m
  · iunfold refines
    iintro %K %b HK Hna Herr Hpos
    iapply wp_rand_nonpos_r K hnpos
    iframe HK
    iintro HK'
    iapply wp_rand_nonpos hnpos
    iexists (.int (-1) : Val _), b
    iframe HK' Hna Herr Hpos
    iapply lrel_int_lit (-1)

end Compatibility

end ProbLang
