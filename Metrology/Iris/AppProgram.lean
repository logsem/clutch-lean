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
open Std Iris Iris.Std COFE ProbLang AgreeHeap PartialMap

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-! ## Ghost-state classes -/

/-- The ghost-state slots for the program heap, tapes and random variables. -/
class AppPreGS (rT : outParam (Type _)) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (GF : BundledGFunctors) where
  /-- The slot for the program heap. -/
  heap : ElemG GF (constOF (SpecHeap rT))
  /-- The slot for the program tapes. -/
  tapes : ElemG GF (constOF (SpecTapes rT))
  /-- The slot for the program random variables. -/
  rvs : ElemG GF (constOF (SpecRvs rT))

attribute [reducible, instance] AppPreGS.heap AppPreGS.tapes AppPreGS.rvs

/-- The program ghost state with its ghost names. -/
class AppGS (rT : outParam (Type _)) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (GF : BundledGFunctors) extends
    AppPreGS rT GF where
  /-- The ghost name of the program heap. -/
  γheap : GName
  /-- The ghost name of the program tapes. -/
  γtapes : GName
  /-- The ghost name of the program random variables. -/
  γrvs : GName

/-! ## Resources -/

section Resources

variable {GF : BundledGFunctors} [IApp : AppGS rT GF]
variable {σ : State rT} {l : Loc}
local bi (IProp GF)

/-- The authoritative program heap. -/
def appHeapAuth (σ : LocHeap (Val rT)) :=
  iOwn (E := IApp.heap) IApp.γheap (HeapView.Auth (.own 1) (LocHeap.asAgree σ))

/-- Ownership of one heap cell. -/
def appHeapFrag (ℓ : Loc) (v : Val rT) :=
  iOwn (E := IApp.heap) IApp.γheap (HeapView.Frag ℓ (.own 1) (toAgree v))

/-- The authoritative program tapes. -/
def appTapesAuth (σ : LocHeap (Tape rT)) :=
  iOwn (E := IApp.tapes) IApp.γtapes (HeapView.Auth (.own 1) (LocHeap.asAgree σ))

/-- Ownership of one tape. -/
def appTapesFrag (ℓ : Loc) (t : Tape rT) :=
  iOwn (E := IApp.tapes) IApp.γtapes (HeapView.Frag ℓ (.own 1) (toAgree t))

/-- The authoritative program random variables. -/
def appRvsAuth (ρ : LocHeap (RvCell rT)) :=
  iOwn (E := IApp.rvs) IApp.γrvs (HeapView.Auth (.own 1) (LocHeap.asAgree ρ))

/-- Ownership of one random variable. -/
def appRvsFrag (ℓ : Loc) (c : RvCell rT) :=
  iOwn (E := IApp.rvs) IApp.γrvs (HeapView.Frag ℓ (.own 1) (toAgree c))

/-- The authoritative program state: heap, tapes and random variables. -/
def appStateAuth (σ : State rT) : IProp GF :=
  iprop(appHeapAuth σ.heap ∗ appTapesAuth σ.tapes ∗ appRvsAuth σ.rvs)

/-! ## Points-to notation -/

namespace AppGS
scoped notation:51 l:51 " ↦ " v:51 => appHeapFrag l v
end AppGS
-- `↪ₐ`, not `↪`: Mathlib's `Function.Embedding` binds `↪` globally.
notation:51 l:51 " ↪ₐ " v:51 => appTapesFrag l v

/-- A program tape with an explicit distribution family and contents. -/
def appTape (l : Loc) (n : ℕ) (v : Val rT) (c : ℕ → Option (Val rT)) : IProp GF :=
  appTapesFrag l ⟨n, v, c⟩

/-- A program tape whose contents are a finite prefix followed by empty positions. -/
def appTapeList (l : Loc) (n : ℕ) (v : Val rT) (ws : List (Val rT)) : IProp GF :=
  appTapesFrag l (Tape.ofList n v ws)

notation:51 l:51 " ↪ₐ⟨" n:51 "; " v:51 "; " c:51 "⟩" => appTape l n v c
notation:51 l:51 " ↪ₐL⟨" n:51 "; " v:51 "; " ws:51 "⟩" => appTapeList l n v ws

/-! ## Lookup, update, alloc -/

open scoped AppGS

/-- Owning `l ↦ v` against the authoritative state shows the heap holds `v` at `l`. -/
theorem app_state_lookup_heap {v : Val rT} :
    ⊢ appStateAuth σ -∗ l ↦ v -∗ ⌜σ.heap[l]? = some v⌝ := by
  unfold appStateAuth appHeapAuth appHeapFrag
  iintro ⟨Hh, -⟩ Hf
  iapply lookup $$ Hh Hf

/-- Writing `w` at `l` updates the authoritative state and the points-to. -/
theorem app_state_updateHeap {v w : Val rT} :
    ⊢ appStateAuth σ -∗ l ↦ v ==∗
      appStateAuth (σ.updateHeap (fun h : LocHeap (Val rT) => insert h l w)) ∗
        l ↦ w := by
  unfold appStateAuth appHeapAuth appHeapFrag
  iintro ⟨Hh, Ht⟩ Hf
  imod update (E := IApp.heap) (w := w) $$ [$Hh $Hf] with ⟨Hh, Hf⟩
  imodintro
  simp only [State.updateHeap]
  iframe

/-- Allocating `v` yields a fresh heap cell `σ.heap.fresh ↦ v`. -/
theorem app_state_heap_alloc (v : Val rT) :
    ⊢ appStateAuth σ ==∗
      appStateAuth (σ.updateHeap (fun h : LocHeap (Val rT) => insert h σ.heap.fresh v)) ∗
        σ.heap.fresh ↦ v := by
  unfold appStateAuth appHeapAuth appHeapFrag
  iintro ⟨Hh, Ht⟩
  imod alloc (E := IApp.heap) v $$ Hh with ⟨Hh, Hf⟩
  imodintro
  simp only [State.updateHeap]
  iframe

/-- Owning `l ↪ₐ t` against the authoritative state shows the tape at `l` is `t`. -/
theorem app_state_lookup_tape {t : Tape rT} :
    ⊢ appStateAuth σ -∗ l ↪ₐ t -∗ ⌜σ.tapes[l]? = some t⌝ := by
  unfold appStateAuth appTapesAuth appTapesFrag
  iintro ⟨-, Ht, -⟩ Hf
  iapply lookup $$ Ht Hf

/-- Replacing the tape at `l` updates the authoritative state and the points-to. -/
theorem app_state_update_tape {t s : Tape rT} :
    ⊢ appStateAuth σ -∗ l ↪ₐ t ==∗
      appStateAuth (σ.updateTapes (fun h : LocHeap (Tape rT) => insert h l s)) ∗
        l ↪ₐ s := by
  unfold appStateAuth appTapesAuth appTapesFrag
  iintro ⟨Hh, Ht, Hr⟩ Hf
  imod update (E := IApp.tapes) (w := s) $$ [$Ht $Hf] with ⟨Ht, Hf⟩
  imodintro
  simp only [State.updateTapes]
  iframe

/-- Allocating a tape `t` yields a fresh tape `σ.tapes.fresh ↪ₐ t`. -/
theorem app_state_tape_alloc (t : Tape rT) :
    ⊢ appStateAuth σ ==∗
      appStateAuth (σ.updateTapes (fun h : LocHeap (Tape rT) => insert h σ.tapes.fresh t)) ∗
        σ.tapes.fresh ↪ₐ t := by
  unfold appStateAuth appTapesAuth appTapesFrag
  iintro ⟨Hh, Ht, Hr⟩
  imod alloc (E := IApp.tapes) t $$ Ht with ⟨Ht, Hf⟩
  imodintro
  simp only [State.updateTapes]
  iframe

/-- Owning the random variable at `l` against the authoritative state shows it is `c`. -/
theorem app_state_lookup_rvsFrag {c : RvCell rT} :
    ⊢ appStateAuth σ -∗ appRvsFrag l c -∗ ⌜σ.rvs[l]? = some c⌝ := by
  unfold appStateAuth appRvsAuth appRvsFrag
  iintro ⟨-, -, Hr⟩ Hf
  iapply lookup $$ Hr Hf

/-- Replacing the random variable at `l` updates the authoritative state and the points-to. -/
theorem app_state_update_rvsFrag {c d : RvCell rT} :
    ⊢ appStateAuth σ -∗ appRvsFrag l c ==∗
      appStateAuth (σ.updateRvs (fun h : LocHeap (RvCell rT) => insert h l d)) ∗
        appRvsFrag l d := by
  unfold appStateAuth appRvsAuth appRvsFrag
  iintro ⟨Hh, Ht, Hr⟩ Hf
  imod update (E := IApp.rvs) (w := d) $$ [$Hr $Hf] with ⟨Hr, Hf⟩
  imodintro
  simp only [State.updateRvs]
  iframe

/-- Allocating a random variable `c` yields ownership of a fresh label holding it. -/
theorem app_state_rvsFrag_alloc (c : RvCell rT) :
    ⊢ appStateAuth σ ==∗
      appStateAuth (σ.updateRvs (fun h : LocHeap (RvCell rT) => insert h σ.rvs.fresh c)) ∗
        appRvsFrag σ.rvs.fresh c := by
  unfold appStateAuth appRvsAuth appRvsFrag
  iintro ⟨Hh, Ht, Hr⟩
  imod alloc (E := IApp.rvs) c $$ Hr with ⟨Hr, Hf⟩
  imodintro
  simp only [State.updateRvs]
  iframe

/-! ## `natTape`: tapes as plain integer lists -/

/-- The tape at `l` of bound `z` holds exactly the integers `ns` (Rocq `nat_tape`). -/
noncomputable def appNatTape (l : Loc) (z : Int) (ns : List Int) : IProp GF :=
  iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
    ⌜fs.map (fun x ↦ x.val) = ns⌝ ∗
      l ↪ₐL⟨unifIntName; Val.int z; fs.map fun x ↦ Val.int x.val⟩)

namespace AppGS
scoped notation:51 l:51 " ↪N⟨" z:51 "; " ns:51 "⟩" => appNatTape l z ns
end AppGS

/-- An empty integer tape is an empty `↪ₐ` tape. -/
theorem app_natTape_to_empty {z : Int} :
    appNatTape l z [] ⊢ l ↪ₐ Tape.empty unifIntName (Val.int z) := by
  unfold appNatTape
  exact natTape_to_empty

/-- An empty `↪ₐ` tape is an empty integer tape. -/
theorem app_empty_to_natTape {z : Int} :
    l ↪ₐ Tape.empty unifIntName (Val.int z) ⊢ appNatTape l z [] := by
  unfold appNatTape
  exact empty_to_natTape

/-- An integer tape with head `n` exposes its first entry, and can be rebuilt from the tail. -/
theorem app_read_natTape_head {z : Int} {n : Int} {ns : List Int} :
    appNatTape l z (n :: ns) ⊢
      iprop(∃ (x : { z' : Int // 0 ≤ z' ∧ z' < z }) (xs : List { z' : Int // 0 ≤ z' ∧ z' < z }),
        l ↪ₐL⟨unifIntName; Val.int z; (x :: xs).map fun q ↦ Val.int q.val⟩ ∗
          ⌜x.val = n⌝ ∗
          (l ↪ₐL⟨unifIntName; Val.int z; xs.map fun q ↦ Val.int q.val⟩ -∗
            appNatTape l z ns)) := by
  unfold appNatTape
  exact read_natTape_head

/-! ## Two full fragments at one location are inconsistent -/

/-- Two full cells at one location are contradictory. -/
theorem appHeapFrag_valid_2 {v1 v2 : Val rT} :
    ⊢ appHeapFrag l v1 -∗ appHeapFrag l v2 -∗ False := by
  unfold appHeapFrag
  exact frag_valid_2

/-- Two full tapes at one location are contradictory. -/
theorem appTapesFrag_valid_2 {t1 t2 : Tape rT} :
    ⊢ appTapesFrag l t1 -∗ appTapesFrag l t2 -∗ False := by
  unfold appTapesFrag
  exact frag_valid_2

/-- Two random variables at one location are contradictory. -/
theorem appRvsFrag_valid_2 {c1 c2 : RvCell rT} :
    ⊢ appRvsFrag l c1 -∗ appRvsFrag l c2 -∗ False := by
  unfold appRvsFrag
  exact frag_valid_2

end Resources

/-- Allocating the program ghost state from any initial state `σ`. -/
theorem app_ra_init {GF : BundledGFunctors} [IAPre : AppPreGS rT GF] (σ : State rT) :
    ⊢@{IProp GF} |==> ∃ _ : AppGS rT GF, appStateAuth σ := by
  imod alloc_auth (E := IAPre.heap) σ.heap with ⟨%γH, HH⟩
  imod alloc_auth (E := IAPre.tapes) σ.tapes with ⟨%γT, HT⟩
  imod alloc_auth (E := IAPre.rvs) σ.rvs with ⟨%γR, HR⟩
  imodintro
  iexists { toAppPreGS := IAPre, γheap := γH, γtapes := γT, γrvs := γR }
  unfold appStateAuth appHeapAuth appTapesAuth appRvsAuth
  iframe

end AppProgramRA
