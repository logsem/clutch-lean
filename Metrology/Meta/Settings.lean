module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.ElabTerm

/-! # The `problang` settings panel

A section-local panel whose clauses each set one default, and the tactic that type families use
to read a default for an argument written bare. -/

open Lean Elab Command Tactic

namespace Metrology.Settings

public section

/-! ## The panel -/

/-- One clause of the `problang` panel; each layer adds its own. -/
declare_syntax_cat problang_opt (behavior := both)

/-- `problang` followed by one clause per line sets defaults for the rest of the section. -/
syntax (name := problangCmd) "problang" (ppLine withPosition(problang_opt))+ : command

/-- A single panel clause, the command each clause elaborates through. -/
syntax (name := problangClauseCmd) "problang_clause " problang_opt : command

/-- Elaborates the panel clause by clause. -/
@[command_elab problangCmd]
meta def elabProblangCmd : CommandElab := fun stx => do
  for c in stx[1].getArgs do
    withRef c <| elabCommand (← `(problang_clause $(⟨c⟩)))

/-! ## Named settings

Clauses record what they set under a role name (`reals`, `grade`, …) for later clauses and
elaborators to read. -/

/-- The settings recorded by the clauses of the current section, by role. -/
meta initialize settingExt : SimpleScopedEnvExtension (Name × Syntax) (NameMap Syntax) ←
  registerSimpleScopedEnvExtension { addEntry m p := m.insert p.1 p.2, initial := {} }

/-- Records `stx` as the setting `role` for the rest of the section. -/
meta def setSetting (role : Name) (stx : Syntax) : CommandElabM Unit :=
  settingExt.add (role, stx) .local

/-- The setting `role` of the current section, if a clause set it. -/
meta def getSetting? {m : Type → Type} [Monad m] [MonadEnv m] (role : Name) : m (Option Syntax) :=
  return (settingExt.getState (← getEnv)).find? role

/-- The setting `role`, or an error naming the clause that sets it. -/
meta def getSetting (role : Name) (clause : String) : CommandElabM Syntax := do
  let some s ← getSetting? role | throwError "`problang`: set `{clause}` first"
  return s

/-! ## Defaults from the panel

A type family declared `Exp (rT : Type := by from_setting reals)` reads its argument from the
panel when written bare.

Lean runs autoParam tactics after default instances, so a bare numeral fixes the argument
first: under `reals := Int`, `(Exp.lit (.real 3) : Exp)` is an `Exp ℕ`. The tactic then sees no
goal and cannot object; reading the panel earlier needs an elaborator hook. `pl(…)` and
`(3 : rt%)` read the panel eagerly. -/

/-- `from_setting role` fills the goal with the section's setting `role`. -/
syntax (name := fromSettingTac) "from_setting " ident : tactic

/-- Fills the goal with the setting `role`. -/
@[tactic fromSettingTac]
meta def evalFromSetting : Tactic := fun stx => do
  let role := stx[1].getId
  -- the goal is gone when it was solved before the tactic ran
  let [g] ← getGoals | return
  let some T ← getSetting? role |
    throwError "no `{role}` setting: write the argument, or set `{role}` in a `problang` panel"
  g.assign (← elabTermEnsuringType T (← g.getType))
  setGoals []

end

end Metrology.Settings
