module

public import Mathlib.Basic.ENNReal.Basic
public import Iris
public import Iris.Algebra.HeapView
public import Iris.Instances.IProp.Instance
public import Iris.Std.HeapInstances
public import Metrology.Iris.Algebra
public import Metrology.Iris.SpecProgram
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-!
# Program-side ghost state

Ghost state for the program heap and tapes (`appStateAuth`, `l ↦ v`, `l ↪ₐ t`) with lookup, update
and alloc rules; the spec side is `SpecProgram.lean`. `↦` and `↪N⟨z; ns⟩` need `open scoped AppGS`.
-/

section AppProgramRA
open Std Iris Iris.Std COFE ProbLang

variable {rT : Type _} [ProbLang.LawfulProbLangℝ rT]

/-! ## Ghost-state classes -/

/-- The ghost-state slots for the program heap and tapes. -/
class AppPreGS (rT : outParam (Type _)) [ProbLang.LawfulProbLangℝ rT] (GF : BundledGFunctors) where
  heap : ElemG GF (constOF (SpecHeap rT))
  tapes : ElemG GF (constOF SpecTapes)

attribute [reducible, instance] AppPreGS.heap AppPreGS.tapes

/-- The program ghost state with its ghost names. -/
class AppGS (rT : outParam (Type _)) [ProbLang.LawfulProbLangℝ rT] (GF : BundledGFunctors) extends
    AppPreGS rT GF where
  γheap : GName
  γtapes : GName

/-! ## Resources -/

section Resources

variable {GF : BundledGFunctors} [IApp : AppGS rT GF]

/-- The authoritative program heap. -/
def appHeapAuth (σ : LocHeap (Val rT)) : IProp GF :=
  iOwn (E := IApp.heap) IApp.γheap (HeapView.Auth (.own 1) (LocHeap.asAgree σ))

/-- Ownership of one heap cell. -/
def appHeapFrag (ℓ : Loc) (v : Val rT) : IProp GF :=
  iOwn (E := IApp.heap) IApp.γheap (HeapView.Frag ℓ (.own 1) (toAgree v))

/-- The authoritative program tapes. -/
def appTapesAuth (σ : LocHeap Tape) : IProp GF :=
  iOwn (E := IApp.tapes) IApp.γtapes (HeapView.Auth (.own 1) (LocHeap.asAgree σ))

/-- Ownership of one tape. -/
def appTapesFrag (ℓ : Loc) (t : Tape) : IProp GF :=
  iOwn (E := IApp.tapes) IApp.γtapes (HeapView.Frag ℓ (.own 1) (toAgree t))

/-- The authoritative program state: heap and tapes. -/
def appStateAuth (σ : State rT) : IProp GF :=
  iprop(appHeapAuth σ.heap ∗ appTapesAuth σ.tapes)

end Resources

/-! ## Points-to notation -/

namespace AppGS
scoped notation:51 l:51 " ↦ " v:51 => appHeapFrag l v
end AppGS
-- `↪ₐ`, not `↪`: Mathlib's `Function.Embedding` binds `↪` globally.
notation:51 l:51 " ↪ₐ " v:51 => appTapesFrag l v

/-! ## Lookup, update, alloc -/

section Algebra
open scoped AppGS

variable {GF : BundledGFunctors} [IApp : AppGS rT GF]
local bi IProp GF

/-- Owning `l ↦ v` against the authoritative state shows the heap holds `v` at `l`. -/
theorem app_state_lookup_heap {σ : State rT} {l : Loc} {v : Val rT} :
    ⊢ appStateAuth σ -∗ l ↦ v -∗ ⌜σ.heap[l]? = some v⌝ := by
  unfold appStateAuth appHeapAuth appHeapFrag
  iintro ⟨Hh, -⟩ Hf
  icombine Hh Hf gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  obtain ⟨_, _, _, hlookup, _, hinc⟩ := HeapView.auth_op_frag_valid_total_discrete_iff hv
  exact LocHeap.get?_of_asAgree_get? hlookup hinc

/-- Writing `w` at `l` updates the authoritative state and the points-to. -/
theorem app_state_update_heap {σ : State rT} {l : Loc} {v w : Val rT} :
    ⊢ appStateAuth σ -∗ l ↦ v ==∗
      appStateAuth (σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l w)) ∗
        l ↦ w := by
  unfold appStateAuth appHeapAuth appHeapFrag
  iintro ⟨Hh, Ht⟩ Hf
  have hupd :
      HeapView.Auth (.own 1) (LocHeap.asAgree σ.heap) •
        HeapView.Frag l (.own 1) (toAgree v) ~~>
      HeapView.Auth (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.heap) l (toAgree w)) •
        HeapView.Frag l (.own 1) (toAgree w) :=
    HeapView.update_replace fun _ => by simp
  imod (iOwn_update_op (E := IApp.heap) hupd) $$ [$Hh $Hf] with Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_heap, LocHeap.asAgree_insert]
  iframe

/-- Allocating `v` yields a fresh heap cell `σ.heap.fresh ↦ v`. -/
theorem app_state_heap_alloc {σ : State rT} (v : Val rT) :
    ⊢ appStateAuth σ ==∗
      appStateAuth (σ.update_heap
          (fun h : LocHeap (Val rT) => PartialMap.insert h σ.heap.fresh v)) ∗
        σ.heap.fresh ↦ v := by
  unfold appStateAuth appHeapAuth appHeapFrag
  iintro ⟨Hh, Ht⟩
  have hupd :
      HeapView.Auth (.own 1) (LocHeap.asAgree σ.heap) ~~>
      HeapView.Auth (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.heap) σ.heap.fresh (toAgree v)) •
        HeapView.Frag σ.heap.fresh (.own 1) (toAgree v) :=
    HeapView.update_one_alloc (LocHeap.asAgree_get?_fresh σ.heap) DFrac.valid_own_one
      fun _ => by simp
  imod (iOwn_update hupd) $$ Hh with Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_heap, LocHeap.asAgree_insert]
  iframe

/-- Owning `l ↪ₐ t` against the authoritative state shows the tape at `l` is `t`. -/
theorem app_state_lookup_tape {σ : State rT} {l : Loc} {t : Tape} :
    ⊢ appStateAuth σ -∗ l ↪ₐ t -∗ ⌜σ.tapes[l]? = some t⌝ := by
  unfold appStateAuth appTapesAuth appTapesFrag
  iintro ⟨-, Ht⟩ Hf
  icombine Ht Hf gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  obtain ⟨_, _, _, hlookup, _, hinc⟩ := HeapView.auth_op_frag_valid_total_discrete_iff hv
  exact LocHeap.get?_of_asAgree_get? hlookup hinc

/-- Replacing the tape at `l` updates the authoritative state and the points-to. -/
theorem app_state_update_tape {σ : State rT} {l : Loc} {t s : Tape} :
    ⊢ appStateAuth σ -∗ l ↪ₐ t ==∗
      appStateAuth (σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l s)) ∗
        l ↪ₐ s := by
  unfold appStateAuth appTapesAuth appTapesFrag
  iintro ⟨Hh, Ht⟩ Hf
  have hupd :
      HeapView.Auth (.own 1) (LocHeap.asAgree σ.tapes) •
        HeapView.Frag l (.own 1) (toAgree t) ~~>
      HeapView.Auth (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.tapes) l (toAgree s)) •
        HeapView.Frag l (.own 1) (toAgree s) :=
    HeapView.update_replace fun _ => by simp
  imod (iOwn_update_op (E := IApp.tapes) hupd) $$ [$Ht $Hf] with Hu
  imodintro
  ihave ⟨Ht, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_tapes, LocHeap.asAgree_insert]
  iframe

/-- Allocating a tape `t` yields a fresh tape `σ.tapes.fresh ↪ₐ t`. -/
theorem app_state_tape_alloc {σ : State rT} (t : Tape) :
    ⊢ appStateAuth σ ==∗
      appStateAuth (σ.update_tapes
          (fun h : LocHeap Tape => PartialMap.insert h σ.tapes.fresh t)) ∗
        σ.tapes.fresh ↪ₐ t := by
  unfold appStateAuth appTapesAuth appTapesFrag
  iintro ⟨Hh, Ht⟩
  have hupd :
      HeapView.Auth (.own 1) (LocHeap.asAgree σ.tapes) ~~>
      HeapView.Auth (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.tapes) σ.tapes.fresh (toAgree t)) •
        HeapView.Frag σ.tapes.fresh (.own 1) (toAgree t) :=
    HeapView.update_one_alloc (LocHeap.asAgree_get?_fresh σ.tapes) DFrac.valid_own_one
      fun _ => by simp
  imod (iOwn_update hupd) $$ Ht with Hu
  imodintro
  ihave ⟨Ht, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_tapes, LocHeap.asAgree_insert]
  iframe

end Algebra

/-! ## `natTape`: tapes as plain integer lists -/

section NatTape
open scoped AppGS

variable {GF : BundledGFunctors} [AppGS rT GF]

/-- The tape at `l` of bound `z` holds exactly the integers `ns` (Rocq `nat_tape`). -/
noncomputable def appNatTape (l : Loc) (z : Int) (ns : List Int) : IProp GF :=
  iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
    ⌜fs.map (fun x => x.val) = ns⌝ ∗ l ↪ₐ ⟨z, fs⟩)

end NatTape

namespace AppGS
scoped notation:51 l:51 " ↪N⟨" z:51 "; " ns:51 "⟩" => appNatTape l z ns
end AppGS

section NatTapeInterface
open scoped AppGS

variable {GF : BundledGFunctors} [AppGS rT GF]
local bi IProp GF

/-- An empty integer tape is an empty `↪ₐ` tape. -/
theorem app_natTape_to_empty {l : Loc} {z : Int} :
    appNatTape (GF := GF) l z [] ⊢ l ↪ₐ ⟨z, []⟩ := by
  unfold appNatTape
  iintro ⟨%fs, %hmap, Hl⟩
  obtain rfl := List.map_eq_nil_iff.mp hmap
  iexact Hl

/-- An empty `↪ₐ` tape is an empty integer tape. -/
theorem app_empty_to_natTape {l : Loc} {z : Int} :
    (l ↪ₐ ⟨z, ([] : List { z' : Int // 0 ≤ z' ∧ z' < z })⟩) ⊢
      appNatTape l z [] := by
  unfold appNatTape
  iintro Hl
  iexists []
  isplitr
  · ipureintro; rfl
  iexact Hl

/-- An integer tape with head `n` exposes its first entry, and can be rebuilt from the tail. -/
theorem app_read_natTape_head {l : Loc} {z : Int} {n : Int} {ns : List Int} :
    appNatTape (GF := GF) l z (n :: ns) ⊢
      iprop(∃ (x : { z' : Int // 0 ≤ z' ∧ z' < z })
              (xs : List { z' : Int // 0 ≤ z' ∧ z' < z }),
        l ↪ₐ ⟨z, x :: xs⟩ ∗ ⌜x.val = n⌝ ∗
        (l ↪ₐ ⟨z, xs⟩ -∗ appNatTape l z ns)) := by
  unfold appNatTape
  iintro ⟨%fs, %hmap, Hl⟩
  obtain ⟨x, xs, rfl, hx, hxs⟩ := List.map_eq_cons_iff.mp hmap
  iexists x, xs
  iframe %hx Hl
  iintro Hl
  iexists xs
  iframe %hxs Hl

end NatTapeInterface

/-- Allocating the program ghost state from any initial state `σ`. -/
theorem app_ra_init {GF : BundledGFunctors} [IAPre : AppPreGS rT GF]
    (σ : State rT) :
    ⊢@{IProp GF} |==> ∃ IA : AppGS rT GF,
      appStateAuth (IApp := IA) σ := by
  imod (iOwn_alloc (E := IAPre.heap)
    (HeapView.Auth (.own 1) (LocHeap.asAgree σ.heap))
    HeapView.auth_one_valid) with ⟨%γH, HH⟩
  imod (iOwn_alloc (E := IAPre.tapes)
    (HeapView.Auth (.own 1) (LocHeap.asAgree σ.tapes))
    HeapView.auth_one_valid) with ⟨%γT, HT⟩
  imodintro
  iexists { toAppPreGS := IAPre, γheap := γH, γtapes := γT }
  unfold appStateAuth appHeapAuth appTapesAuth
  iframe

/-! ## Two full fragments at one location are inconsistent -/

section ValidHelpers
variable {GF : BundledGFunctors} [IApp : AppGS rT GF]
local bi IProp GF

/-- Two full cells at one location are contradictory. -/
theorem appHeapFrag_valid_2 {l : Loc} {v1 v2 : Val rT} :
    ⊢ appHeapFrag l v1 -∗ appHeapFrag l v2 -∗ False := by
  unfold appHeapFrag
  iintro H1 H2
  icombine H1 H2 gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  exfalso
  exact absurd (DFrac.valid_own_op (HeapView.frag_op_valid_iff.mp hv).1) (lt_irrefl _)

/-- Two full tapes at one location are contradictory. -/
theorem appTapesFrag_valid_2 {l : Loc} {t1 t2 : Tape} :
    ⊢ appTapesFrag l t1 -∗ appTapesFrag l t2 -∗ False := by
  unfold appTapesFrag
  iintro H1 H2
  icombine H1 H2 gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  exfalso
  exact absurd (DFrac.valid_own_op (HeapView.frag_op_valid_iff.mp hv).1) (lt_irrefl _)

end ValidHelpers

end AppProgramRA
