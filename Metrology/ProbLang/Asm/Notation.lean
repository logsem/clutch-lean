module

public import Metrology.ProbLang.Asm.Parser
public meta import Metrology.ProbLang.Asm.Parser
public meta import Lean.Elab.Term

/-! # Assembly string notation -/

public meta section

open Lean Elab Term ProbLang.Asm

instance : ToExpr Imm where
  toTypeExpr := mkConst ``Imm
  toExpr
    | .int z => mkApp (mkConst ``Imm.int) (toExpr z)
    | .symbol name z => mkApp2 (mkConst ``Imm.symbol) (toExpr name) (toExpr z)
    | .hi name => mkApp (mkConst ``Imm.hi) (toExpr name)
    | .lo name => mkApp (mkConst ``Imm.lo) (toExpr name)
    | .pcrelHi name => mkApp (mkConst ``Imm.pcrelHi) (toExpr name)
    | .pcrelLo name => mkApp (mkConst ``Imm.pcrelLo) (toExpr name)

instance : ToExpr Operand where
  toTypeExpr := mkConst ``Operand
  toExpr
    | .reg r => mkApp (mkConst ``Operand.reg) (toExpr r)
    | .imm i => mkApp (mkConst ``Operand.imm) (toExpr i)
    | .mem i r => mkApp2 (mkConst ``Operand.mem) (toExpr i) (toExpr r)

instance : ToExpr Instr where
  toTypeExpr := mkConst ``Instr
  toExpr i := mkApp2 (mkConst ``Instr.mk) (toExpr i.mnemonic) (toExpr i.operands)

instance : ToExpr Section where
  toTypeExpr := mkConst ``Section
  toExpr
    | .text => mkConst ``Section.text
    | .rodata => mkConst ``Section.rodata

instance : ToExpr Directive where
  toTypeExpr := mkConst ``Directive
  toExpr
    | .section kind => mkApp (mkConst ``Directive.section) (toExpr kind)
    | .align n => mkApp (mkConst ``Directive.align) (toExpr n)
    | .data width values => mkApp2 (mkConst ``Directive.data) (toExpr width) (toExpr values)
    | .ascii value terminated =>
      mkApp2 (mkConst ``Directive.ascii) (toExpr value) (toExpr terminated)
    | .zero n => mkApp (mkConst ``Directive.zero) (toExpr n)
    | .metadata name args => mkApp2 (mkConst ``Directive.metadata) (toExpr name) (toExpr args)

instance : ToExpr Line where
  toTypeExpr := mkConst ``Line
  toExpr
    | .label name => mkApp (mkConst ``Line.label) (toExpr name)
    | .instr i => mkApp (mkConst ``Line.instr) (toExpr i)
    | .directive d => mkApp (mkConst ``Line.directive) (toExpr d)

instance : ToExpr AsmProg where
  toTypeExpr := mkConst ``AsmProg
  toExpr p := mkApp2 (mkConst ``AsmProg.mk) (toExpr p.lines) (toExpr p.entry)

/-- Parse a GNU assembly string into a quoted AST during elaboration. -/
elab "riscv_asm!" source:str : term => do
  match parse source.getString with
  | .error e => throwErrorAt source "{e}"
  | .ok prog => return toExpr prog
