import RiscvZkvm.Sail.Step

/-! # Sail execution boundary

The adapter stops before executing an address outside the code image.
-/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail.ConcurrencyInterfaceV1

/-- The unmodified Sail machine state with its deterministic choice source. -/
abbrev Mach := SequentialState RegisterType trivialChoiceSource

/-- The optional program counter of a Sail state. -/
noncomputable def pc (s : Mach) : Option (BitVec 64) := s.regs.get? Register.PC

/-- Run a Sail computation, rejecting exceptions and retaining its final state. -/
noncomputable def runSail {α : Type} (m : SailM α) (s : Mach) : Option (α × Mach) :=
  match m s with
  | .ok a s' => some (a, s')
  | .error _ _ => none

/-- Execute one official Sail instruction, rejecting errors and waiting states. -/
noncomputable def rvStep (s : Mach) : Option Mach :=
  match runSail (try_step 0 false) s with
  | some (false, s') => some s'
  | _ => none

/-- A terminating run of the official model to the first address outside the code. -/
inductive RunsTo (code : BitVec 64 → Prop) (Q : Mach → Prop) : Mach → Prop where
  /-- Stop before stepping an address outside the code image. -/
  | leave {s : Mach} {p : BitVec 64} :
      pc s = some p → ¬code p → Q s → RunsTo code Q s
  /-- Step an address within the image and continue the terminating run. -/
  | step {s s' : Mach} {p : BitVec 64} :
      pc s = some p → code p → rvStep s = some s' → RunsTo code Q s' → RunsTo code Q s

/-- A stronger stopping postcondition entails a weaker stopping postcondition. -/
theorem RunsTo.mono {code : BitVec 64 → Prop} {P Q : Mach → Prop} {s : Mach}
    (h : RunsTo code P s) (hPQ : ∀ s', P s' → Q s') : RunsTo code Q s := by
  induction h with
  | leave hp hc hP => exact .leave hp hc (hPQ _ hP)
  | step hp hc hs _ ih => exact .step hp hc hs ih

/-- Two terminating runs satisfy their postconditions at the same stopping state. -/
theorem RunsTo.agree {code : BitVec 64 → Prop} {P Q : Mach → Prop} {s : Mach}
    (hP : RunsTo code P s) (hQ : RunsTo code Q s) : ∃ t, P t ∧ Q t := by
  induction hP with
  | leave hp hc hP =>
    cases hQ with
    | leave _ _ hQ => exact ⟨_, hP, hQ⟩
    | step hp' hc' _ _ =>
      have heq := Option.some.inj (hp.symm.trans hp')
      cases heq
      exact False.elim (hc hc')
  | step hp hc hs _ ih =>
    cases hQ with
    | leave hp' hc' _ =>
      have heq := Option.some.inj (hp.symm.trans hp')
      cases heq
      exact False.elim (hc' hc)
    | step _ _ hs' hQ =>
      have heq := Option.some.inj (hs.symm.trans hs')
      subst heq
      exact ih hQ

/-- Every terminating run has a unique terminal machine state. -/
theorem RunsTo.unique {code : BitVec 64 → Prop} {s t u : Mach}
    (ht : RunsTo code (· = t) s) (hu : RunsTo code (· = u) s) : t = u := by
  obtain ⟨v, ht, hu⟩ := ht.agree hu
  exact ht.symm.trans hu

end MetrologyAsm
