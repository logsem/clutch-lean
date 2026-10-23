module

public import Metrology.ProbLang.Syntax.Syntax

/-! # Assembly interaction semantics -/

@[expose] public section

namespace ProbLang.Asm

variable {C V : Type}

/-- The physical addresses chosen for one foreign call. -/
structure Placement where
  /-- The address of each logical cell. -/
  addr : Loc → BitVec 64
  /-- The code image's base address. -/
  codeBase : BitVec 64
  /-- The address at which each import stops execution. -/
  importAddr : String → BitVec 64
  /-- The address at which the foreign call returns. -/
  retAddr : BitVec 64

/-- A decoded machine stop at a return or an import. -/
inductive Stop (V : Type) where
  | ret (value : V) (heap : LocHeap V)
  | call (name : String) (args : List V) (heap : LocHeap V)

/-- The finite script of returns and callbacks visible to ProbLang. -/
inductive Interaction (V : Type) where
  | ret (value : V) (heap : LocHeap V)
  | call (name : String) (args : List V) (heap : LocHeap V)
      (next : V → LocHeap V → Interaction V)

/-- A machine interface for code values and finite heap fragments. -/
structure AsmSemantics (C V : Type) where
  /-- The machine state. -/
  Mach : Type
  /-- Every execution terminates at a stop satisfying the postcondition. -/
  runs : Placement → C → Mach → (Mach → Prop) → Prop
  /-- Entry states compatible with the code, arguments and fragment. -/
  Compat : Placement → C → List V → LocHeap V → Mach → Prop
  /-- The observable result of a stop, relative to the entry state. -/
  ExitCompat : Placement → C → List V → Finset Loc → Mach → Mach → Stop V → Prop
  /-- Resumption states after a callback returns a value and a fragment. -/
  Resume : Placement → C → List V → Finset Loc → Mach → V → LocHeap V → Mach → Prop
  /-- Responses representable by an import's signature on the fixed footprint. -/
  ResponseOK : C → List V → Finset Loc → String → V → LocHeap V → Prop
  /-- The fixed return value for unrepresentable responses. -/
  invalidResult : V

namespace AsmSemantics

variable (M : AsmSemantics C V) (c : C) (entryArgs : List V) (F : Finset Loc)

/-- The fixed subtree used for responses outside the import signature. -/
def invalidTree : Interaction V := .ret M.invalidResult ∅

/-- A tree whose unrepresentable responses have fixed continuations. -/
def Canonical : Interaction V → Prop
  | .ret _ _ => True
  | .call name _ _ next => ∀ r h,
      (M.ResponseOK c entryArgs F name r h → Canonical (next r h)) ∧
      (¬ M.ResponseOK c entryArgs F name r h → next r h = M.invalidTree)

/-- Replace every unrepresentable callback continuation with the fixed subtree. -/
noncomputable def canonicalize : Interaction V → Interaction V
  | .ret value heap => .ret value heap
  | .call name args heap next =>
    open Classical in
    .call name args heap fun r h =>
      if M.ResponseOK c entryArgs F name r h then canonicalize (next r h) else M.invalidTree

/-- Canonicalization produces a canonical tree. -/
theorem canonicalize_canonical (tree : Interaction V) :
    M.Canonical c entryArgs F (M.canonicalize c entryArgs F tree) := by
  classical
  induction tree with
  | ret => trivial
  | call name args heap next ih =>
    intro r h
    constructor
    · intro hr
      simpa only [ite_eq_left hr] using ih r h
    · intro hr
      simp only [ite_eq_right hr]

/-- Canonicalization preserves a tree whose invalid continuations are already fixed. -/
theorem canonicalize_eq_self {tree : Interaction V} (h : M.Canonical c entryArgs F tree) :
    M.canonicalize c entryArgs F tree = tree := by
  classical
  induction tree with
  | ret => rfl
  | call name args heap next ih =>
    simp only [canonicalize]
    congr 1
    funext r heap'
    by_cases hr : M.ResponseOK c entryArgs F name r heap'
    · simpa only [ite_eq_left hr] using ih r heap' ((h r heap').1 hr)
    · simpa only [ite_eq_right hr] using ((h r heap').2 hr).symm

/-- Every phase follows the tree while retaining the original call-entry frame. -/
def FollowsFrom (origin : M.Mach) (ι : Placement) (t : M.Mach) : Interaction V → Prop
  | .ret value heap =>
    M.runs ι c t (fun t' => M.ExitCompat ι c entryArgs F origin t' (.ret value heap))
  | .call name args heap next => M.runs ι c t (fun t' =>
      M.ExitCompat ι c entryArgs F origin t' (.call name args heap) ∧
      ∀ r h, M.ResponseOK c entryArgs F name r h →
        ∀ t'', M.Resume ι c entryArgs F t' r h t'' → FollowsFrom origin ι t'' (next r h))

/-- A complete foreign call follows the tree relative to its own entry state. -/
def Follows (ι : Placement) (t : M.Mach) (tree : Interaction V) : Prop :=
  M.FollowsFrom c entryArgs F t ι t tree

/-- A plain machine specification quantified over every compatible placement and state. -/
def Spec (heap : LocHeap V) (tree : Interaction V) : Prop :=
  ∀ ι t, M.Compat ι c entryArgs heap t → M.Follows c entryArgs F ι t tree

/-- A nonvacuous canonical specification. -/
def Evaluates (heap : LocHeap V) (tree : Interaction V) : Prop :=
  (∃ ι t, M.Compat ι c entryArgs heap t) ∧ M.Canonical c entryArgs F tree ∧
    M.Spec c entryArgs F heap tree

/-- The unique canonical interaction tree of a foreign call, when it exists. -/
noncomputable def eval (heap : LocHeap V) : Option (Interaction V) :=
  open Classical in
  if h : ∃! tree, M.Evaluates c entryArgs F heap tree then some h.exists.choose else none

/-- A specified tree selected uniquely by the interface is the evaluator's result. -/
theorem eval_eq_some_of_unique {heap : LocHeap V} {tree : Interaction V}
    (h : M.Evaluates c entryArgs F heap tree)
    (hu : ∀ other, M.Evaluates c entryArgs F heap other → other = tree) :
    M.eval c entryArgs F heap = some tree := by
  classical
  have unique : ∃! other, M.Evaluates c entryArgs F heap other := ⟨tree, h, hu⟩
  rw [eval, dite_eq_left unique]
  congr 1
  exact unique.unique unique.exists.choose_spec h

/-- A total return specification needs only stop determinism to determine evaluation. -/
theorem eval_ret_eq_some (heap output : LocHeap V) (value : V)
    (hagree : ∀ ι t P Q, M.runs ι c t P → M.runs ι c t Q → ∃ t', P t' ∧ Q t')
    (hdet : ∀ ι t t' s u, M.ExitCompat ι c entryArgs F t t' s →
      M.ExitCompat ι c entryArgs F t t' u → s = u)
    (hentry : ∃ ι t, M.Compat ι c entryArgs heap t)
    (hspec : M.Spec c entryArgs F heap (.ret value output)) :
    M.eval c entryArgs F heap = some (.ret value output) := by
  apply M.eval_eq_some_of_unique c entryArgs F (tree := .ret value output)
    ⟨hentry, True.intro, hspec⟩
  intro other hother
  obtain ⟨ι, t, ht⟩ := hentry
  cases other with
  | ret value' output' =>
    obtain ⟨t', hu, hs⟩ := hagree ι t _ _ (hother.2.2 ι t ht) (hspec ι t ht)
    cases hdet ι t t' _ _ hu hs
    rfl
  | call name args heap next =>
    obtain ⟨t', hu, hs⟩ := hagree ι t _ _ (hother.2.2 ι t ht) (hspec ι t ht)
    cases hdet ι t t' _ _ hu.1 hs

end AsmSemantics

/-- The machine laws used to establish uniqueness of canonical interaction trees. -/
structure LawfulAsmSemantics (M : AsmSemantics C V) : Prop where
  /-- Two total execution specifications share a stop. -/
  runs_agree : ∀ ι c t Q R, M.runs ι c t Q → M.runs ι c t R → ∃ t', Q t' ∧ R t'
  /-- A stopped state has at most one decoded observation. -/
  exit_det : ∀ ι c entryArgs F t t' s₁ s₂,
    M.ExitCompat ι c entryArgs F t t' s₁ → M.ExitCompat ι c entryArgs F t t' s₂ → s₁ = s₂
  /-- Every representable callback response has a resumption state. -/
  resume_nonempty : ∀ ι c entryArgs F t t' name args heap r h,
    M.ExitCompat ι c entryArgs F t t' (.call name args heap) → M.ResponseOK c entryArgs F name r h →
      ∃ t'', M.Resume ι c entryArgs F t' r h t''

namespace AsmSemantics

variable {M : AsmSemantics C V} (law : LawfulAsmSemantics M) {c : C}
  {entryArgs : List V} {F : Finset Loc}

include law

/-- Two canonical trees followed with one original frame and current state are equal. -/
theorem followedFrom_unique {ι : Placement} {origin t : M.Mach} {T U : Interaction V}
    (hT : M.Canonical c entryArgs F T) (hU : M.Canonical c entryArgs F U)
    (fT : M.FollowsFrom c entryArgs F origin ι t T)
    (fU : M.FollowsFrom c entryArgs F origin ι t U) : T = U := by
  induction T generalizing t U with
  | ret value heap =>
    cases U with
    | ret value' heap' =>
      obtain ⟨s, hs, hs'⟩ := law.runs_agree _ _ _ _ _ fT fU
      have he := law.exit_det _ _ _ _ _ _ _ _ hs hs'
      cases he
      rfl
    | call name args heap' next =>
      obtain ⟨s, hs, hs'⟩ := law.runs_agree _ _ _ _ _ fT fU
      have he := law.exit_det _ _ _ _ _ _ _ _ hs hs'.1
      cases he
  | call name args heap next ih =>
    cases U with
    | ret value heap' =>
      obtain ⟨s, hs, hs'⟩ := law.runs_agree _ _ _ _ _ fT fU
      have he := law.exit_det _ _ _ _ _ _ _ _ hs.1 hs'
      cases he
    | call name' args' heap' next' =>
      obtain ⟨s, hs, hs'⟩ := law.runs_agree _ _ _ _ _ fT fU
      have he := law.exit_det _ _ _ _ _ _ _ _ hs.1 hs'.1
      cases he
      congr 1
      funext r h
      by_cases hr : M.ResponseOK c entryArgs F name r h
      · obtain ⟨t'', ht''⟩ := law.resume_nonempty _ _ _ _ _ _ _ _ _ _ _ hs.1 hr
        exact ih r h ((hT r h).1 hr) ((hU r h).1 hr) (hs.2 r h hr t'' ht'') (hs'.2 r h hr t'' ht'')
      · exact ((hT r h).2 hr).trans ((hU r h).2 hr).symm

/-- Two canonical trees followed from one machine state are equal. -/
theorem followed_unique {ι : Placement} {t : M.Mach} {T U : Interaction V}
    (hT : M.Canonical c entryArgs F T) (hU : M.Canonical c entryArgs F U)
    (fT : M.Follows c entryArgs F ι t T) (fU : M.Follows c entryArgs F ι t U) : T = U :=
  followedFrom_unique law hT hU fT fU

/-- A nonvacuous canonical machine specification determines the evaluator's result. -/
theorem eval_eq_some {heap : LocHeap V} {T : Interaction V}
    (h : M.Evaluates c entryArgs F heap T) : M.eval c entryArgs F heap = some T := by
  apply M.eval_eq_some_of_unique c entryArgs F h
  intro U hU
  obtain ⟨ι, t, ht⟩ := h.1
  exact followed_unique law hU.2.1 h.2.1 (hU.2.2 ι t ht) (h.2.2 ι t ht)

end AsmSemantics

/-- Replay a list of callback responses to select a subtree. -/
def Interaction.replay : Interaction V → List (V × LocHeap V) → Option (Interaction V)
  | tree, [] => some tree
  | .ret _ _, _ :: _ => none
  | .call _ _ _ next, (r, h) :: rest => (next r h).replay rest

/-- Replaying one more response continues from the previously selected subtree. -/
theorem Interaction.replay_append (tree : Interaction V) (xs ys : List (V × LocHeap V)) :
    tree.replay (xs ++ ys) = (tree.replay xs).bind (fun t => t.replay ys) := by
  induction xs generalizing tree with
  | nil => cases tree <;> rfl
  | cons x xs ih =>
    cases tree with
    | ret => rfl
    | call name args heap next => exact ih (next x.1 x.2)

end ProbLang.Asm
