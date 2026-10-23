module

public import Metrology.ProbLang.Asm.Boundary
import Metrology.Meta.TCB

/-! # Callback semantics regression checks -/

@[expose] public section

namespace ProbLang.Asm.Test

/-- The decoded observation of a two-phase echo machine. -/
def echoStop : Option Int → Stop Int
  | none => .call "echo" [] ∅
  | some r => .ret r ∅

/-- A deterministic callback fixture with nonnegative integer responses. -/
def echo : AsmSemantics Unit Int where
  Mach := Option Int
  runs := fun _ _ t Q => Q t
  Compat := fun _ _ _ _ t => t = none
  ExitCompat := fun _ _ _ _ _ t' s => s = echoStop t'
  Resume := fun _ _ _ _ t r _ t' => t = none ∧ t' = some r
  ResponseOK := fun _ _ _ _ r h => 0 ≤ r ∧ h = ∅
  invalidResult := 0

/-- The callback fixture satisfies deterministic-stop and resumption laws. -/
theorem echo_lawful : LawfulAsmSemantics echo where
  runs_agree := by
    intro ι c t Q R hQ hR
    exact ⟨t, hQ, hR⟩
  exit_det := by
    intro ι c args F t t' s₁ s₂ h₁ h₂
    exact h₁.trans h₂.symm
  resume_nonempty := by
    intro ι c args F t t' name vs heap r h hs hr
    cases t' with
    | none => exact ⟨some r, rfl, rfl⟩
    | some n => cases hs

/-- The canonical echo tree fixes every response outside the callback's signature. -/
noncomputable def echoTree : Interaction Int :=
  echo.canonicalize () [] ∅ (.call "echo" [] ∅ fun r _ => .ret r ∅)

/-- The echo fixture follows its tree for every placement. -/
theorem echo_follows (ι : Placement) : echo.Follows () [] ∅ ι none echoTree := by
  change (Stop.call "echo" [] ∅ = echoStop none) ∧ _
  refine ⟨rfl, ?_⟩
  intro r h hr t ht
  obtain ⟨_, rfl⟩ := ht
  dsimp [echoTree, AsmSemantics.canonicalize]
  rw [ite_eq_left hr]
  rfl

/-- A callback with a restricted response domain has a unique canonical evaluation. -/
theorem echo_eval : echo.eval () [] ∅ ∅ = some echoTree := by
  apply AsmSemantics.eval_eq_some echo_lawful
  refine ⟨⟨⟨fun _ => 0, 0, fun _ => 0, 0⟩, none, rfl⟩, ?_, ?_⟩
  · exact echo.canonicalize_canonical () [] ∅ _
  · intro ι t ht
    cases ht
    exact echo_follows ι

/-- Callback replay uses the heap supplied by the callback response. -/
theorem replay_callback_heap (h : LocHeap Int) :
    (Interaction.call "fill" [] ∅ fun _ h' => .ret 0 h').replay [(0, h)] =
      some (.ret 0 h) := rfl

/-- Footprint replacement retains every surrounding cell. -/
theorem overwrite_frame (heap fragment : LocHeap Int) (l : Loc) (hl : l ≠ 1) :
    (overwrite {1} heap fragment)[l]? = heap[l]? := by
  rw [overwrite_get, ite_eq_right]
  simpa using hl

/-- Omitting an owned cell from a replacement removes that cell. -/
theorem overwrite_missing (F : Finset Loc) (heap fragment : LocHeap Int) (l : Loc)
    (hl : l ∈ F) (h : fragment[l]? = none) : (overwrite F heap fragment)[l]? = none := by
  rw [overwrite_get, ite_eq_left hl, h]

/-- A three-byte heap used to check pointer aliasing at the boundary. -/
def bytes : LocHeap (Val Empty) :=
  ((∅ : LocHeap (Val Empty)).insert 1 (.int 11)).insert 2 (.int 22) |>.insert 3 (.int 33)

/-- Array arguments may alias when their ranges and element representations coincide. -/
theorem check_identical_arrays :
    check { args := [.array 8 (.const 2), .array 8 (.const 2)], result := .unit }
      [.loc 1, .loc 1] bytes = true := by decide +kernel

/-- Partially overlapping array arguments fail the dynamic boundary check. -/
theorem check_partial_overlap :
    check { args := [.array 8 (.const 2), .array 8 (.const 2)], result := .unit }
      [.loc 1, .loc 2] bytes = false := by decide +kernel

/-- Negative array lengths supplied through integer arguments are rejected. -/
theorem check_negative_length :
    check { args := [.array 8 (.arg 1), .int 64], result := .unit }
      [.loc 1, .int (-1)] bytes = false := by decide +kernel

/-- Result pointers may identify the location just past an array's last element. -/
theorem check_one_past_pointer :
    checkResult (rT := Empty) { args := [.array 8 (.const 2)], result := .loc }
      [.loc 1] .loc (.loc 3) = true := by decide +kernel

/-- Import names must identify one callback signature. -/
theorem reject_duplicate_imports :
    (Sig.mk ⟨[], .unit⟩ 0 [("r", ⟨[], .unit⟩), ("r", ⟨[], .unit⟩)]).valid = false := by
  decide +kernel

#print axioms echo_eval
#tcb echo_eval

/-- The fixture pauses with an eight-byte frame and returns after restoring sixteen. -/
def frameStop (current : Nat) : Stop Unit :=
  if current = 8 then .call "frame" [] ∅ else .ret () ∅

/-- A two-phase fixture requires its final counter to match the original entry counter. -/
def frameMachine : AsmSemantics Unit Unit where
  Mach := Nat
  runs := fun _ _ current Q => Q (if current = 16 then 8 else 16)
  Compat := fun _ _ _ _ current => current = 16
  ExitCompat := fun _ _ _ _ origin current stop =>
    stop = frameStop current ∧ if current = 8 then origin = 16 else current = origin
  Resume := fun _ _ _ _ _ _ _ current => current = 8
  ResponseOK := fun _ _ _ _ _ _ => True
  invalidResult := ()

/-- The frame fixture invokes one callback before its unit return. -/
def frameTree : Interaction Unit := .call "frame" [] ∅ fun _ _ => .ret () ∅

/-- Callback resumption retains the original frame anchor through the final return. -/
theorem frame_follows (ι : Placement) : frameMachine.Follows () [] ∅ ι (16 : Nat) frameTree := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  intro r heap _ current hcurrent
  subst current
  exact ⟨rfl, rfl⟩

end ProbLang.Asm.Test
