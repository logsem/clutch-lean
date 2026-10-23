module

public import Mathlib.Basic.ENNReal.Basic
public import Iris
public import Iris.Algebra.HeapView
public import Iris.Instances.IProp.Instance
public import Iris.Std.HeapInstances
public import Metrology.Iris.SpecProgram
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-!
# Program-side ghost state

Ghost state for the program heap and tapes, with lookup, update and alloc rules.
-/

@[expose] public section

section AppProgramRA
open Std Iris Iris.Std COFE ProbLang AgreeHeap

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-! ## Ghost-state classes -/

/-- The ghost-state slots for the program heap and tapes. -/
class AppPreGS (rT : outParam (Type _)) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (GF : BundledGFunctors) where
  /-- The slot for the program heap. -/
  heap : ElemG GF (constOF (SpecHeap rT))
  /-- The slot for the program tapes. -/
  tapes : ElemG GF (constOF SpecTapes)

attribute [reducible, instance] AppPreGS.heap AppPreGS.tapes

/-- The program ghost state with its ghost names. -/
class AppGS (rT : outParam (Type _)) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (GF : BundledGFunctors) extends
    AppPreGS rT GF where
  /-- The ghost name of the program heap. -/
  γheap : GName
  /-- The ghost name of the program tapes. -/
  γtapes : GName

/-! ## Resources -/

section Resources

variable {GF : BundledGFunctors} [IApp : AppGS rT GF]
variable {σ : State rT} {l : Loc}
local bi IProp GF

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

/-! ## Points-to notation -/

namespace AppGS
scoped notation:51 l:51 " ↦ " v:51 => appHeapFrag l v
end AppGS
-- `↪ₐ`, not `↪`: Mathlib's `Function.Embedding` binds `↪` globally.
notation:51 l:51 " ↪ₐ " v:51 => appTapesFrag l v

/-! ## Lookup, update, alloc -/

open scoped AppGS

/-- Owning `l ↦ v` against the authoritative state shows the heap holds `v` at `l`. -/
theorem app_state_lookup_heap {v : Val rT} :
    ⊢ appStateAuth σ -∗ l ↦ v -∗ ⌜σ.heap[l]? = some v⌝ := by
  unfold appStateAuth appHeapAuth appHeapFrag
  iintro ⟨Hh, -⟩ Hf
  iapply lookup $$ Hh Hf

/-- Writing `w` at `l` updates the authoritative state and the points-to. -/
theorem app_state_update_heap {v w : Val rT} :
    ⊢ appStateAuth σ -∗ l ↦ v ==∗
      appStateAuth (σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l w)) ∗
        l ↦ w := by
  unfold appStateAuth appHeapAuth appHeapFrag
  iintro ⟨Hh, Ht⟩ Hf
  imod update (E := IApp.heap) (w := w) $$ [$Hh $Hf] with ⟨Hh, Hf⟩
  imodintro
  simp only [State.update_heap]
  iframe

/-- Allocating `v` yields a fresh heap cell `σ.heap.fresh ↦ v`. -/
theorem app_state_heap_alloc (v : Val rT) :
    ⊢ appStateAuth σ ==∗
      appStateAuth (σ.update_heap
          (fun h : LocHeap (Val rT) => PartialMap.insert h σ.heap.fresh v)) ∗
        σ.heap.fresh ↦ v := by
  unfold appStateAuth appHeapAuth appHeapFrag
  iintro ⟨Hh, Ht⟩
  imod alloc (E := IApp.heap) v $$ Hh with ⟨Hh, Hf⟩
  imodintro
  simp only [State.update_heap]
  iframe

/-- Owning `l ↪ₐ t` against the authoritative state shows the tape at `l` is `t`. -/
theorem app_state_lookup_tape {t : Tape} :
    ⊢ appStateAuth σ -∗ l ↪ₐ t -∗ ⌜σ.tapes[l]? = some t⌝ := by
  unfold appStateAuth appTapesAuth appTapesFrag
  iintro ⟨-, Ht⟩ Hf
  iapply lookup $$ Ht Hf

/-- Replacing the tape at `l` updates the authoritative state and the points-to. -/
theorem app_state_update_tape {t s : Tape} :
    ⊢ appStateAuth σ -∗ l ↪ₐ t ==∗
      appStateAuth (σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l s)) ∗
        l ↪ₐ s := by
  unfold appStateAuth appTapesAuth appTapesFrag
  iintro ⟨Hh, Ht⟩ Hf
  imod update (E := IApp.tapes) (w := s) $$ [$Ht $Hf] with ⟨Ht, Hf⟩
  imodintro
  simp only [State.update_tapes]
  iframe

/-- Allocating a tape `t` yields a fresh tape `σ.tapes.fresh ↪ₐ t`. -/
theorem app_state_tape_alloc (t : Tape) :
    ⊢ appStateAuth σ ==∗
      appStateAuth (σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h σ.tapes.fresh t)) ∗
        σ.tapes.fresh ↪ₐ t := by
  unfold appStateAuth appTapesAuth appTapesFrag
  iintro ⟨Hh, Ht⟩
  imod alloc (E := IApp.tapes) t $$ Ht with ⟨Ht, Hf⟩
  imodintro
  simp only [State.update_tapes]
  iframe

/-! ## `natTape`: tapes as plain integer lists -/

/-- The tape at `l` of bound `z` holds exactly the integers `ns` (Rocq `nat_tape`). -/
noncomputable def appNatTape (l : Loc) (z : Int) (ns : List Int) : IProp GF :=
  iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
    ⌜fs.map (fun x ↦ x.val) = ns⌝ ∗ l ↪ₐ ⟨z, fs⟩)

namespace AppGS
scoped notation:51 l:51 " ↪N⟨" z:51 "; " ns:51 "⟩" => appNatTape l z ns
end AppGS

/-- An empty integer tape is an empty `↪ₐ` tape. -/
theorem app_natTape_to_empty {z : Int} :
    appNatTape l z [] ⊢ l ↪ₐ ⟨z, []⟩ := by
  unfold appNatTape
  exact natTape_to_empty

/-- An empty `↪ₐ` tape is an empty integer tape. -/
theorem app_empty_to_natTape {z : Int} :
    l ↪ₐ ⟨z, []⟩ ⊢ appNatTape l z [] := by
  unfold appNatTape
  exact empty_to_natTape

/-- An integer tape with head `n` exposes its first entry, and can be rebuilt from the tail. -/
theorem app_read_natTape_head {z : Int} {n : Int} {ns : List Int} :
    appNatTape l z (n :: ns) ⊢
      iprop(∃ x xs,
        l ↪ₐ ⟨z, x :: xs⟩ ∗ ⌜x.val = n⌝ ∗
        (l ↪ₐ ⟨z, xs⟩ -∗ appNatTape l z ns)) := by
  unfold appNatTape
  exact read_natTape_head

/-! ## Two full fragments at one location are inconsistent -/

/-- Two full cells at one location are contradictory. -/
theorem appHeapFrag_valid_2 {v1 v2 : Val rT} :
    ⊢ appHeapFrag l v1 -∗ appHeapFrag l v2 -∗ False := by
  unfold appHeapFrag
  exact frag_valid_2

/-- Two full tapes at one location are contradictory. -/
theorem appTapesFrag_valid_2 {t1 t2 : Tape} :
    ⊢ appTapesFrag l t1 -∗ appTapesFrag l t2 -∗ False := by
  unfold appTapesFrag
  exact frag_valid_2

end Resources

/-- Allocating the program ghost state from any initial state `σ`. -/
theorem app_ra_init {GF : BundledGFunctors} [IAPre : AppPreGS rT GF] (σ : State rT) :
    ⊢@{IProp GF} |==> ∃ IA : AppGS rT GF, appStateAuth (IApp := IA) σ := by
  imod alloc_auth (E := IAPre.heap) σ.heap with ⟨%γH, HH⟩
  imod alloc_auth (E := IAPre.tapes) σ.tapes with ⟨%γT, HT⟩
  imodintro
  iexists { toAppPreGS := IAPre, γheap := γH, γtapes := γT }
  unfold appStateAuth appHeapAuth appTapesAuth
  iframe

end AppProgramRA
