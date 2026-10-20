module

public import Mathlib.Basic.ENNReal.Basic
public import Iris
public import Iris.Algebra.HeapView
public import Iris.Instances.IProp.Instance
public import Iris.Std.HeapInstances
public import Metrology.Iris.Algebra
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Discrete

@[expose] public section

/-! # Spec-side ghost state

Ghost state for the spec program, heap and tapes, with `⤇`, `↦ₛ`, `↪ₛ` and their update rules.
`AppProgram` reuses the heap and tape cameras for the program side. -/

section SpecRA
open Std Iris Iris.Std COFE ProbLang

variable {rT : Type _} [ProbLang.LawfulProbLangℝ rT]

/-! ## Cameras and discrete OFE instances -/

instance cofe_exp : COFE (Exp rT) := COFE.ofDiscrete _
instance discrete_exp : OFE.Discrete (Exp rT) := ⟨id⟩
instance discreteE_exp (x : Exp rT) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance cofe_tape : COFE Tape := COFE.ofDiscrete _
instance discrete_tape : OFE.Discrete Tape := ⟨id⟩
instance discreteE_tape (x : Tape) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance cofe_val : COFE (Val rT) := COFE.ofDiscrete _
instance discrete_val : OFE.Discrete (Val rT) := ⟨id⟩
instance discreteE_val (x : Val rT) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

/-- Ghost state for the spec-side program: an exclusive expression. -/
abbrev SpecProg (α : Type _) [ProbLang.LawfulProbLangℝ α] :=
  Auth (Option (Excl (Exp α)))
/-- Heap camera with values in `Agree`; used for both the spec heap and the program heap
(`AppProgram`). -/
abbrev SpecHeap (rT : Type _) [ProbLang.LawfulProbLangℝ rT] :=
  HeapView Loc (Agree (Val rT)) LocHeap
/-- Tape camera with tapes in `Agree`; used for both the spec tapes and the program tapes
(`AppProgram`). -/
abbrev SpecTapes := HeapView Loc (Agree Tape) LocHeap

/-- Authoritative element of `SpecProg`: the spec program is `e`. -/
def SpecProg.auth (e : Exp rT) : SpecProg rT := ● (some <| .excl e)
/-- Fragment of `SpecProg`: ownership of the spec program `e`. -/
def SpecProg.frag (e : Exp rT) : SpecProg rT := ◯ (some <| .excl e)

/-! ## Heaps of `Agree` values

The ghost heap stores each value in `Agree`; these lemmas move between it and the plain heap. -/

/-- Wraps every heap value in `Agree` (also used by `AppProgram`). -/
def LocHeap.asAgree [OFE V] (h : LocHeap V) : LocHeap (Agree V) :=
  PartialMap.map LocHeap toAgree h

/-- Reading the wrapped heap is reading the heap, then wrapping. -/
theorem LocHeap.asAgree_get? [OFE V] (h : LocHeap V) (l : Loc) :
    PartialMap.get? (LocHeap.asAgree h) l = (PartialMap.get? h l).map toAgree := by
  simp only [LocHeap.asAgree, PartialMap.map, LawfulPartialMap.get?_bindAlter]
  cases PartialMap.get? h l <;> rfl

/-- The operational semantics updates heaps with `ExtTreeMap.insert`, the ghost-state lemmas with
`PartialMap.insert`; they agree. -/
theorem Std.ExtTreeMap.insert_eq_PartialMap_insert {V : Type _}
    (h : LocHeap V) (l : Loc) (v : V) :
    h.insert l v = PartialMap.insert h l v :=
  ExtTreeMap.ext_getElem? fun k => by
    show (h.insert l v)[k]? = (h.alter l (fun _ => some v))[k]?
    simp [ExtTreeMap.getElem?_insert, ExtTreeMap.getElem?_alter]

/-- Wrapping commutes with insertion. -/
theorem LocHeap.asAgree_insert [OFE V] (h : LocHeap V) (l : Loc) (v : V) :
    LocHeap.asAgree (PartialMap.insert h l v) =
      PartialMap.insert (LocHeap.asAgree h) l (toAgree v) := by
  refine LawfulPartialMap.equiv_iff_eq.mp fun k => ?_
  by_cases hk : l = k
  · subst hk
    rw [LocHeap.asAgree_get?, LawfulPartialMap.get?_insert_eq rfl,
        LawfulPartialMap.get?_insert_eq rfl]
    rfl
  · rw [LocHeap.asAgree_get?, LawfulPartialMap.get?_insert_ne hk,
        LawfulPartialMap.get?_insert_ne hk, LocHeap.asAgree_get?]

/-- The fresh location is unmapped in the wrapped heap. -/
theorem LocHeap.asAgree_get?_fresh [OFE V] (h : LocHeap V) :
    PartialMap.get? (LocHeap.asAgree h) h.fresh = none := by
  rw [LocHeap.asAgree_get?]
  show (h[h.fresh]?).map toAgree = none
  rw [ExtTreeMap.fresh_get?]; rfl

/-- A fragment included in the wrapped heap's value pins down the plain heap's value. -/
theorem LocHeap.get?_of_asAgree_get? [OFE V] {h : LocHeap V} {l : Loc} {v : V} {a : Agree V}
    (hget : PartialMap.get? (LocHeap.asAgree h) l = some a) (hinc : toAgree v ≼ a) :
    PartialMap.get? h l = some v := by
  rw [LocHeap.asAgree_get?] at hget
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hget
  rw [hw, Agree.toAgree_included.mp hinc]

/-! ## Ghost-state classes -/

/-- Ghost-state resources needed for the spec side. -/
class SpecPreGS (rT : outParam (Type _)) [ProbLang.LawfulProbLangℝ rT] (GF : BundledGFunctors) where
  prog : ElemG GF (constOF (SpecProg rT))
  heap : ElemG GF (constOF (SpecHeap rT))
  tapes : ElemG GF (constOF SpecTapes)

attribute [reducible, instance] SpecPreGS.prog SpecPreGS.heap SpecPreGS.tapes

/-- `SpecPreGS` together with the ghost names. -/
class SpecGS (rT : outParam (Type _)) [ProbLang.LawfulProbLangℝ rT] (GF : BundledGFunctors)
   extends SpecPreGS rT GF where
  γprog : GName
  γheap : GName
  γtapes : GName

section Resources

/-! ## Spec ownership assertions -/

variable {GF : BundledGFunctors} [ISpec : SpecGS rT GF]

/-- Authoritative ownership of the spec program. -/
def specProgAuth (e : Exp rT) : IProp GF := iOwn (E := ISpec.prog) ISpec.γprog (.auth e)
/-- Ownership of the spec program `e`, written `⤇ e`. -/
def specProgFrag (e : Exp rT) : IProp GF := iOwn (E := ISpec.prog) ISpec.γprog (.frag e)

/-- Authoritative ownership of the spec heap. -/
def specHeapAuth (σ : LocHeap (Val rT)) : IProp GF :=
  iOwn (E := ISpec.heap) ISpec.γheap (HeapView.Auth (.own 1) (LocHeap.asAgree σ))
/-- Spec-heap points-to, written `ℓ ↦ₛ v`. -/
def specHeapFrag (ℓ : Loc) (v : Val rT) : IProp GF :=
  iOwn (E := ISpec.heap) ISpec.γheap (HeapView.Frag ℓ (.own 1) (toAgree v))

/-- Authoritative ownership of the spec tapes. -/
def specTapesAuth (σ : LocHeap Tape) : IProp GF :=
  iOwn (E := ISpec.tapes) ISpec.γtapes (HeapView.Auth (.own 1) (LocHeap.asAgree σ))
/-- Spec-tape points-to, written `ℓ ↪ₛ t`. -/
def specTapesFrag (ℓ : Loc) (t : Tape) : IProp GF :=
  iOwn (E := ISpec.tapes) ISpec.γtapes (HeapView.Frag ℓ (.own 1) (toAgree t))

/-- Authoritative ownership of a whole spec configuration. -/
def ProbLang.Cfg.specAuth (c : Cfg rT) : IProp GF :=
  let ⟨e, ⟨σ, τ⟩⟩ := c
  iprop(specProgAuth e ∗ specHeapAuth σ ∗ specTapesAuth τ)

notation "⤇ " t:50 => specProgFrag t
notation l:50 " ↦ₛ " v:50 => specHeapFrag l v
notation l:50 " ↪ₛ " τ:50 => specTapesFrag l τ

end Resources

section Algebra

variable {GF : BundledGFunctors} [ISpec : SpecGS rT GF]

open ProbLang.Cfg

/-! ## Authority-fragment lemmas -/

omit [LawfulProbLangℝ rT] in
/-- Inclusion of exclusive elements forces equality. -/
theorem some_excl_inc_excl_exp_eq {e1 e2 : Exp rT} (H : some (Excl.excl e1) ≼ some (Excl.excl e2)) :
    e1 = e2 := by
  have h := Option.inc_iff.mp H
  simp at h
  rcases h with h | h
  · exact h
  · simpa using Excl.inc_iff.mp h

/-- The authority and the fragment `⤇ e2` agree on the spec expression. -/
theorem specAuth_specFrag_agree {e1 e2 : Exp rT} {σ : State rT} :
    ⊢@{IProp GF} specAuth ⟨e1, σ⟩ -∗ ⤇ e2 -∗ ⌜e1 = e2⌝ := by
  unfold specAuth specProgAuth specProgFrag
  iintro ⟨He, -, -⟩ Hf
  icombine He Hf gives Hv
  ihave %hv := internalCmraValid_discrete (A := SpecProg rT) $$ Hv
  ipureintro
  obtain ⟨hinc, _⟩ := Auth.auth_both_valid_discrete.mp hv
  exact some_excl_inc_excl_exp_eq hinc |>.symm

/-- Authority and fragment of the spec program are updated together, e.g. when the spec steps. -/
theorem specProg_update {e1 e2 e3 : Exp rT} {σ : State rT} :
    ⊢@{IProp GF} specAuth ⟨e1, σ⟩ -∗ ⤇ e2 ==∗ specAuth ⟨e3, σ⟩ ∗ ⤇ e3 := by
  iintro Ha Hf
  ihave %rfl := specAuth_specFrag_agree $$ Ha Hf
  unfold specAuth specProgAuth specProgFrag; simp only []
  ihave ⟨He, Hh, Ht⟩ := Ha
  have hupd : SpecProg.frag e1 • SpecProg.auth e1 ~~> SpecProg.frag e3 • SpecProg.auth e3 :=
    Auth.auth_update (.option (.exclusive trivial))
  ihave Hu := iOwn_update_op (E := ISpec.prog) hupd $$ [$Hf $He]
  imod Hu
  imodintro
  ihave ⟨Hf, Ha⟩ := iOwn_op $$ Hu
  iframe

/-- A points-to `l ↦ₛ v` agrees with the authoritative heap. -/
theorem spec_auth_lookup_heap {e : Exp rT} {σ : State rT} {l : Loc} {v : Val rT} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↦ₛ v -∗ ⌜σ.heap[l]? = some v⌝ := by
  unfold specAuth specHeapAuth specHeapFrag
  iintro ⟨-, Hh, -⟩ Hf
  icombine Hh Hf gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  obtain ⟨_, _, _, hget, _, hinc⟩ := HeapView.auth_op_frag_valid_total_discrete_iff hv
  exact LocHeap.get?_of_asAgree_get? hget hinc

/-- Overwriting a spec location updates the authoritative heap and the points-to together. -/
theorem spec_auth_update_heap {e : Exp rT} {σ : State rT} {l : Loc} {v w : Val rT} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↦ₛ v ==∗
      specAuth ⟨e, σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l w)⟩ ∗
        l ↦ₛ w := by
  unfold specAuth specHeapAuth specHeapFrag
  iintro ⟨He, Hh, Ht⟩ Hf
  ihave Hu := iOwn_update_op (E := ISpec.heap)
    (HeapView.update_replace (Agree.toAgree_valid (a := w))) $$ [$Hh $Hf]
  imod Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_heap, LocHeap.asAgree_insert]
  iframe

/-- Allocating a fresh spec location. -/
theorem spec_auth_heap_alloc {e : Exp rT} {σ : State rT} (v : Val rT) :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ ==∗
      specAuth ⟨e, σ.update_heap
          (fun h : LocHeap (Val rT) => PartialMap.insert h σ.heap.fresh v)⟩ ∗
        σ.heap.fresh ↦ₛ v := by
  unfold specAuth specHeapAuth specHeapFrag
  iintro ⟨He, Hh, Ht⟩
  ihave Hu := iOwn_update (HeapView.update_one_alloc (LocHeap.asAgree_get?_fresh σ.heap)
    DFrac.valid_own_one (Agree.toAgree_valid (a := v))) $$ Hh
  imod Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_heap, LocHeap.asAgree_insert]
  iframe

/-- A tape points-to `l ↪ₛ t` agrees with the authoritative tapes. -/
theorem spec_auth_lookup_tape {e : Exp rT} {σ : State rT} {l : Loc} {t : Tape} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↪ₛ t -∗ ⌜σ.tapes[l]? = some t⌝ := by
  unfold specAuth specTapesAuth specTapesFrag
  iintro ⟨-, -, Ht⟩ Hf
  icombine Ht Hf gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  obtain ⟨_, _, _, hget, _, hinc⟩ := HeapView.auth_op_frag_valid_total_discrete_iff hv
  exact LocHeap.get?_of_asAgree_get? hget hinc

/-- Overwriting a spec tape updates the authoritative tapes and the points-to together. -/
theorem spec_auth_update_tape {e : Exp rT} {σ : State rT} {l : Loc} {t s : Tape} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↪ₛ t ==∗
      specAuth ⟨e, σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l s)⟩ ∗
        l ↪ₛ s := by
  unfold specAuth specTapesAuth specTapesFrag
  iintro ⟨He, Hh, Ht⟩ Hf
  ihave Hu := iOwn_update_op (E := ISpec.tapes)
    (HeapView.update_replace (Agree.toAgree_valid (a := s))) $$ [$Ht $Hf]
  imod Hu
  imodintro
  ihave ⟨Ht, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_tapes, LocHeap.asAgree_insert]
  iframe

/-- Allocating a fresh spec tape. -/
theorem spec_auth_tape_alloc {e : Exp rT} {σ : State rT} (t : Tape) :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ ==∗
      specAuth ⟨e, σ.update_tapes
          (fun h : LocHeap Tape => PartialMap.insert h σ.tapes.fresh t)⟩ ∗
        σ.tapes.fresh ↪ₛ t := by
  unfold specAuth specTapesAuth specTapesFrag
  iintro ⟨He, Hh, Ht⟩
  ihave Hu := iOwn_update (HeapView.update_one_alloc (LocHeap.asAgree_get?_fresh σ.tapes)
    DFrac.valid_own_one (Agree.toAgree_valid (a := t))) $$ Ht
  imod Hu
  imodintro
  ihave ⟨Ht, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_tapes, LocHeap.asAgree_insert]
  iframe

/-! ## Allocation -/

/-- Initialises the spec ghost state for configuration `⟨e, σ⟩`, giving `specAuth` and `⤇ e`
(no heap or tape fragments). -/
theorem spec_ra_init {GF : BundledGFunctors} [ISPre : SpecPreGS rT GF]
    (e : Exp rT) (σ : State rT) :
    ⊢@{IProp GF} |==> ∃ IS : SpecGS rT GF,
      Cfg.specAuth (ISpec := IS) ⟨e, σ⟩ ∗ specProgFrag (ISpec := IS) e := by
  imod (iOwn_alloc (E := ISPre.prog) (SpecProg.auth e • SpecProg.frag e)
    (Auth.auth_both_valid_2 trivial .rfl)) with ⟨%γp, Hp⟩
  imod (iOwn_alloc (E := ISPre.heap)
    (HeapView.Auth (.own 1) (LocHeap.asAgree σ.heap))
    HeapView.auth_one_valid) with ⟨%γH, HH⟩
  imod (iOwn_alloc (E := ISPre.tapes)
    (HeapView.Auth (.own 1) (LocHeap.asAgree σ.tapes))
    HeapView.auth_one_valid) with ⟨%γT, HT⟩
  imodintro
  let IS : SpecGS rT GF := {
    toSpecPreGS := ISPre
    γprog := γp
    γheap := γH
    γtapes := γT }
  iexists IS
  unfold ProbLang.Cfg.specAuth specProgAuth specHeapAuth specTapesAuth specProgFrag
  ihave ⟨Hpa, Hpf⟩ := iOwn_op $$ Hp
  simp only []
  iframe

end Algebra

/-! ## Spec tapes over plain integers

Analogue of `appNatTape`. -/

section NatSpecTape

variable {GF : BundledGFunctors} [ISpec : SpecGS rT GF]

/-- Spec-side tape holding the integers `ns`, each below `z`. -/
noncomputable def specNatTape (l : Loc) (z : Int) (ns : List Int) : IProp GF :=
  iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
    ⌜fs.map (fun x => x.val) = ns⌝ ∗ specTapesFrag l ⟨z, fs⟩)

notation:51 l:51 " ↪ₛN⟨" z:51 "; " ns:51 "⟩" => specNatTape l z ns

/-- An empty integer tape is an empty spec tape. -/
theorem spec_natTape_to_empty {l : Loc} {z : Int} :
    specNatTape (GF := GF) l z [] ⊢ l ↪ₛ ⟨z, []⟩ := by
  unfold specNatTape
  iintro ⟨%fs, %hmap, Hl⟩
  obtain rfl := List.map_eq_nil_iff.mp hmap
  iexact Hl

/-- An empty spec tape is an empty integer tape. -/
theorem spec_empty_to_natTape {l : Loc} {z : Int} :
    (l ↪ₛ ⟨z, ([] : List { z' : Int // 0 ≤ z' ∧ z' < z })⟩) ⊢@{IProp GF}
      specNatTape l z [] := by
  unfold specNatTape
  iintro Hl
  iexists []
  isplitr; · ipureintro; rfl
  iexact Hl

/-- Reading the head of an integer tape exposes the head of the spec tape, with a way back. -/
theorem spec_read_natTape_head {l : Loc} {z : Int} {n : Int} {ns : List Int} :
    specNatTape (GF := GF) l z (n :: ns) ⊢
      iprop(∃ (x : { z' : Int // 0 ≤ z' ∧ z' < z })
              (xs : List { z' : Int // 0 ≤ z' ∧ z' < z }),
        l ↪ₛ ⟨z, x :: xs⟩ ∗ ⌜x.val = n⌝ ∗
        (l ↪ₛ ⟨z, xs⟩ -∗ specNatTape l z ns)) := by
  unfold specNatTape
  iintro ⟨%fs, %hmap, Hl⟩
  obtain ⟨x, xs, rfl, hx, hxs⟩ := List.map_eq_cons_iff.mp hmap
  iexists x, xs
  isplitl [Hl]; · iexact Hl
  isplitr; · ipureintro; exact hx
  iintro Hl
  iexists xs
  isplitr; · ipureintro; exact hxs
  iexact Hl

end NatSpecTape

/-! ## Exclusivity of points-to assertions -/

section ValidHelpers
variable {GF : BundledGFunctors} [ISpec : SpecGS rT GF]

/-- Two heap points-to assertions at one location are contradictory. -/
theorem specHeapFrag_valid_2 {l : Loc} {v1 v2 : Val rT} :
    ⊢@{IProp GF} specHeapFrag l v1 -∗ specHeapFrag l v2 -∗ False := by
  unfold specHeapFrag
  iintro H1 H2
  icombine H1 H2 gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  exfalso
  exact absurd (DFrac.valid_own_op (HeapView.frag_op_valid_iff.mp hv).1) (lt_irrefl _)

/-- Two tape points-to assertions at one location are contradictory. -/
theorem specTapesFrag_valid_2 {l : Loc} {t1 t2 : Tape} :
    ⊢@{IProp GF} specTapesFrag l t1 -∗ specTapesFrag l t2 -∗ False := by
  unfold specTapesFrag
  iintro H1 H2
  icombine H1 H2 gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  exfalso
  exact absurd (DFrac.valid_own_op (HeapView.frag_op_valid_iff.mp hv).1) (lt_irrefl _)

end ValidHelpers

end SpecRA
