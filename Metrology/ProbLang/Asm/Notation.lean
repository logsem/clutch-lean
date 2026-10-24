module

public import Metrology.ProbLang.Asm.Parser
public meta import Metrology.ProbLang.Asm.Parser
public meta import Lean.Elab.Term

/-! # Assembly string notation -/

public meta section

open Lean Elab Term ProbLang.Asm

deriving instance ToExpr for Imm
deriving instance ToExpr for Operand
deriving instance ToExpr for Instr
deriving instance ToExpr for Section
deriving instance ToExpr for Directive
deriving instance ToExpr for Line
deriving instance ToExpr for AsmProg

/-- Parse a GNU assembly string into a quoted AST during elaboration. -/
elab "riscv_asm!" source:str : term => do
  match parse source.getString with
  | .error e => throwErrorAt source "{e}"
  | .ok prog => return toExpr prog
