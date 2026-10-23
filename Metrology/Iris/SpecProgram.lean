module

public import Mathlib.Basic.ENNReal.Basic
public import Iris
public import Iris.Algebra.HeapView
public import Iris.Instances.IProp.Instance
public import Iris.Std.HeapInstances
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Discrete
public import Metrology.Iris.AgreeHeap
import Metrology.Iris.LocalBI

/-! # Spec-side ghost state

Ghost state for the spec program, heap and tapes, with `⤇`, `↦ₛ`, `↪ₛ` and their update rules. -/

@[expose] public section

section SpecRA
open Std Iris Iris.Std COFE OFE Excl AgreeHeap ProbLang

variable {rT : Type _}

/-! ## Cameras and discrete OFE instances -/

instance cofe_exp : COFE (Exp rT) := ofDiscrete _
instance discrete_exp : Discrete (Exp rT) := ⟨id⟩

instance cofe_tape : COFE Tape := ofDiscrete _
instance discrete_tape : Discrete Tape := ⟨id⟩

instance cofe_val : COFE (Val rT) := ofDiscrete _
instance discrete_val : Discrete (Val rT) := ⟨id⟩

/-- Inclusion of exclusive elements forces equality. -/
theorem some_excl_inc_excl_exp_eq {e1 e2 : Exp rT}
    (H : some (excl e1) ≼ some (excl e2)) : e1 = e2 := by
  have h := Option.inc_iff.mp H
  simp at h
  rcases h with h | h
  · exact h
  · simpa using inc_iff.mp h

variable [LawfulProbLangℝ rT]

/-- Ghost state for the spec-side program: an exclusive expression. -/
abbrev SpecProg (α : Type _) [LawfulProbLangℝ α] :=
  Auth (Option (Excl (Exp α)))
/-- Heap camera with values in `Agree`. -/
abbrev SpecHeap (rT : Type _) [LawfulProbLangℝ rT] :=
  HeapView Loc (Agree (Val rT)) LocHeap
/-- Tape camera with tapes in `Agree`. -/
abbrev SpecTapes := HeapView Loc (Agree Tape) LocHeap

/-- Authoritative element of `SpecProg`: the spec program is `e`. -/
def SpecProg.auth (e : Exp rT) : SpecProg rT := ● (some <| .excl e)
/-- Fragment of `SpecProg`: ownership of the spec program `e`. -/
def SpecProg.frag (e : Exp rT) : SpecProg rT := ◯ (some <| .excl e)

/-! ## Ghost-state classes -/

/-- Ghost-state resources needed for the spec side. -/
class SpecPreGS (rT : outParam (Type _)) [LawfulProbLangℝ rT] (GF : BundledGFunctors) where
  /-- Ghost cell for the spec program. -/
  prog : ElemG GF (constOF (SpecProg rT))
  /-- Ghost cell for the spec heap. -/
  heap : ElemG GF (constOF (SpecHeap rT))
  /-- Ghost cell for the spec tapes. -/
  tapes : ElemG GF (constOF SpecTapes)

attribute [reducible, instance] SpecPreGS.prog SpecPreGS.heap SpecPreGS.tapes

/-- `SpecPreGS` together with the ghost names. -/
class SpecGS (rT : outParam (Type _)) [LawfulProbLangℝ rT] (GF : BundledGFunctors)
    extends SpecPreGS rT GF where
  /-- Ghost name of the spec program. -/
  γprog : GName
  /-- Ghost name of the spec heap. -/
  γheap : GName
  /-- Ghost name of the spec tapes. -/
  γtapes : GName

/-! ## Spec ownership assertions -/

variable {GF : BundledGFunctors} [ISpec : SpecGS rT GF]
local bi IProp GF
variable {e : Exp rT} {σ : State rT} {l : Loc}

open ProbLang.Cfg

/-- Authoritative ownership of the spec program. -/
def specProgAuth (e : Exp rT) := iOwn (E := ISpec.prog) ISpec.γprog (.auth e)
/-- Ownership of the spec program `e`, written `⤇ e`. -/
def specProgFrag (e : Exp rT) := iOwn (E := ISpec.prog) ISpec.γprog (.frag e)

/-- Authoritative ownership of the spec heap. -/
def specHeapAuth (σ : LocHeap (Val rT)) :=
  iOwn (E := ISpec.heap) ISpec.γheap (HeapView.Auth (.own 1) (LocHeap.asAgree σ))
/-- Spec-heap points-to, written `ℓ ↦ₛ v`. -/
def specHeapFrag (ℓ : Loc) (v : Val rT) :=
  iOwn (E := ISpec.heap) ISpec.γheap (HeapView.Frag ℓ (.own 1) (toAgree v))

/-- Authoritative ownership of the spec tapes. -/
def specTapesAuth (σ : LocHeap Tape) :=
  iOwn (E := ISpec.tapes) ISpec.γtapes (HeapView.Auth (.own 1) (LocHeap.asAgree σ))
/-- Spec-tape points-to, written `ℓ ↪ₛ t`. -/
def specTapesFrag (ℓ : Loc) (t : Tape) :=
  iOwn (E := ISpec.tapes) ISpec.γtapes (HeapView.Frag ℓ (.own 1) (toAgree t))

/-- Authoritative ownership of a whole spec configuration. -/
def ProbLang.Cfg.specAuth (c : Cfg rT) : IProp GF :=
  let ⟨e, ⟨σ, τ⟩⟩ := c
  iprop(specProgAuth e ∗ specHeapAuth σ ∗ specTapesAuth τ)

notation "⤇ " t:50 => specProgFrag t
notation l:50 " ↦ₛ " v:50 => specHeapFrag l v
notation l:50 " ↪ₛ " τ:50 => specTapesFrag l τ

/-! ## Authority-fragment lemmas -/

/-- The authority and the fragment `⤇ e2` agree on the spec expression. -/
theorem specAuth_specFrag_agree {e1 e2 : Exp rT} {σ : State rT} :
    ⊢ specAuth ⟨e1, σ⟩ -∗ ⤇ e2 -∗ ⌜e1 = e2⌝ := by
  unfold specAuth specProgAuth specProgFrag
  iintro ⟨He, -, -⟩ Hf
  icombine He Hf gives Hv
  ihave %hv := internalCmraValid_discrete (A := SpecProg rT) $$ Hv
  ipureintro
  obtain ⟨hinc, _⟩ := Auth.auth_both_valid_discrete.mp hv
  exact some_excl_inc_excl_exp_eq hinc |>.symm

/-- Authority and fragment of the spec program are updated together, e.g. when the spec steps. -/
theorem specProg_update {e1 e2 e3 : Exp rT} {σ : State rT} :
    ⊢ specAuth ⟨e1, σ⟩ -∗ ⤇ e2 ==∗ specAuth ⟨e3, σ⟩ ∗ ⤇ e3 := by
  iintro Ha Hf
  ihave %rfl := specAuth_specFrag_agree $$ Ha Hf
  unfold specAuth specProgAuth specProgFrag
  dsimp only
  ihave ⟨He, Hh, Ht⟩ := Ha
  have hupd : SpecProg.frag e1 • SpecProg.auth e1 ~~> SpecProg.frag e3 • SpecProg.auth e3 :=
    Auth.auth_update (.option (.exclusive trivial))
  ihave Hu := iOwn_update_op (E := ISpec.prog) hupd $$ [$Hf $He]
  imod Hu
  imodintro
  ihave ⟨Hf, Ha⟩ := iOwn_op $$ Hu
  iframe

/-- A points-to `l ↦ₛ v` agrees with the authoritative heap. -/
theorem spec_auth_lookup_heap {v : Val rT} :
    ⊢ specAuth ⟨e, σ⟩ -∗ l ↦ₛ v -∗ ⌜σ.heap[l]? = some v⌝ := by
  unfold specAuth specHeapAuth specHeapFrag
  iintro ⟨-, Hh, -⟩ Hf
  iapply lookup $$ Hh Hf

/-- Overwriting a spec location updates the authoritative heap and the points-to together. -/
theorem spec_auth_update_heap {v w : Val rT} :
    ⊢ specAuth ⟨e, σ⟩ -∗ l ↦ₛ v ==∗
      specAuth ⟨e, σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l w)⟩ ∗
        l ↦ₛ w := by
  unfold specAuth specHeapAuth specHeapFrag
  iintro ⟨He, Hh, Ht⟩ Hf
  imod update (E := ISpec.heap) (w := w) $$ [$Hh $Hf] with ⟨Hh, Hf⟩
  imodintro
  simp only [State.update_heap]
  iframe

/-- Allocating a fresh spec location. -/
theorem spec_auth_heap_alloc (v : Val rT) :
    ⊢ specAuth ⟨e, σ⟩ ==∗
      specAuth ⟨e, σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h σ.heap.fresh v)⟩ ∗
        σ.heap.fresh ↦ₛ v := by
  unfold specAuth specHeapAuth specHeapFrag
  iintro ⟨He, Hh, Ht⟩
  imod alloc (E := ISpec.heap) v $$ Hh with ⟨Hh, Hf⟩
  imodintro
  simp only [State.update_heap]
  iframe

/-- A tape points-to `l ↪ₛ t` agrees with the authoritative tapes. -/
theorem spec_auth_lookup_tape {t : Tape} :
    ⊢ specAuth ⟨e, σ⟩ -∗ l ↪ₛ t -∗ ⌜σ.tapes[l]? = some t⌝ := by
  unfold specAuth specTapesAuth specTapesFrag
  iintro ⟨-, -, Ht⟩ Hf
  iapply lookup $$ Ht Hf

/-- Overwriting a spec tape updates the authoritative tapes and the points-to together. -/
theorem spec_auth_update_tape {t s : Tape} :
    ⊢ specAuth ⟨e, σ⟩ -∗ l ↪ₛ t ==∗
      specAuth ⟨e, σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l s)⟩ ∗
        l ↪ₛ s := by
  unfold specAuth specTapesAuth specTapesFrag
  iintro ⟨He, Hh, Ht⟩ Hf
  imod update (E := ISpec.tapes) (w := s) $$ [$Ht $Hf] with ⟨Ht, Hf⟩
  imodintro
  simp only [State.update_tapes]
  iframe

/-- Allocating a fresh spec tape. -/
theorem spec_auth_tape_alloc (t : Tape) :
    ⊢ specAuth ⟨e, σ⟩ ==∗
      specAuth ⟨e, σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h σ.tapes.fresh t)⟩ ∗
        σ.tapes.fresh ↪ₛ t := by
  unfold specAuth specTapesAuth specTapesFrag
  iintro ⟨He, Hh, Ht⟩
  imod alloc (E := ISpec.tapes) t $$ Ht with ⟨Ht, Hf⟩
  imodintro
  simp only [State.update_tapes]
  iframe

/-! ## Allocation -/

/-- Initialises the spec ghost state for configuration `⟨e, σ⟩`, giving `specAuth` and `⤇ e`
(no heap or tape fragments). -/
theorem spec_ra_init {GF : BundledGFunctors} [ISPre : SpecPreGS rT GF]
    (e : Exp rT) (σ : State rT) :
    ⊢@{IProp GF} |==> ∃ IS : SpecGS rT GF,
      specAuth (ISpec := IS) ⟨e, σ⟩ ∗ specProgFrag (ISpec := IS) e := by
  imod (iOwn_alloc (E := ISPre.prog) (SpecProg.auth e • SpecProg.frag e)
    (Auth.auth_both_valid_2 trivial .rfl)) with ⟨%γp, Hp⟩
  imod alloc_auth (E := ISPre.heap) σ.heap with ⟨%γH, HH⟩
  imod alloc_auth (E := ISPre.tapes) σ.tapes with ⟨%γT, HT⟩
  imodintro
  let IS : SpecGS rT GF := {
    toSpecPreGS := ISPre
    γprog := γp
    γheap := γH
    γtapes := γT }
  iexists IS
  unfold specAuth specProgAuth specHeapAuth specTapesAuth specProgFrag
  ihave ⟨Hpa, Hpf⟩ := iOwn_op $$ Hp
  dsimp only
  iframe

/-! ## Spec tapes over plain integers -/

/-- Spec-side tape holding the integers `ns`, each below `z`. -/
noncomputable def specNatTape (l : Loc) (z : Int) (ns : List Int) : IProp GF :=
  iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
    ⌜fs.map (fun x => x.val) = ns⌝ ∗ specTapesFrag l ⟨z, fs⟩)

notation:51 l:51 " ↪ₛN⟨" z:51 "; " ns:51 "⟩" => specNatTape l z ns

/-- An empty integer tape is an empty spec tape. -/
theorem spec_natTape_to_empty {z : Int} :
    specNatTape l z [] ⊢ l ↪ₛ ⟨z, []⟩ := by
  unfold specNatTape
  exact natTape_to_empty

/-- An empty spec tape is an empty integer tape. -/
theorem spec_empty_to_natTape {z : Int} :
    (l ↪ₛ ⟨z, ([] : List { z' : Int // 0 ≤ z' ∧ z' < z })⟩) ⊢
      specNatTape l z [] := by
  unfold specNatTape
  exact empty_to_natTape

/-- Reading the head of an integer tape exposes the head of the spec tape, with a way back. -/
theorem spec_read_natTape_head {z : Int} {n : Int} {ns : List Int} :
    specNatTape l z (n :: ns) ⊢
      iprop(∃ (x : { z' : Int // 0 ≤ z' ∧ z' < z }) (xs : List { z' : Int // 0 ≤ z' ∧ z' < z }),
        l ↪ₛ ⟨z, x :: xs⟩ ∗ ⌜x.val = n⌝ ∗
        (l ↪ₛ ⟨z, xs⟩ -∗ specNatTape l z ns)) := by
  unfold specNatTape
  exact read_natTape_head

/-! ## Exclusivity of points-to assertions -/

/-- Two heap points-to assertions at one location are contradictory. -/
theorem specHeapFrag_valid_2 {v1 v2 : Val rT} :
    ⊢ specHeapFrag l v1 -∗ specHeapFrag l v2 -∗ False := by
  unfold specHeapFrag
  exact frag_valid_2

/-- Two tape points-to assertions at one location are contradictory. -/
theorem specTapesFrag_valid_2 {t1 t2 : Tape} :
    ⊢ specTapesFrag l t1 -∗ specTapesFrag l t2 -∗ False := by
  unfold specTapesFrag
  exact frag_valid_2

end SpecRA
