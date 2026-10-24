module

public import Mathlib.Basic.Countable.Basic
public import Mathlib.Logic.Equiv.List
public import Mathlib.Tactic.DeriveCountable
import all Mathlib.Tactic.DeriveCountable

/-! # Assembly syntax and signatures -/

@[expose] public section

instance instCountableChar : Countable Char where
  exists_injective_nat' := by
    exists (·.1.toNat)
    rintro ⟨v1, _⟩ ⟨v2, _⟩
    simp only [Char.mk.injEq]
    exact UInt32.toNat_inj.mp

instance instCountableString : Countable String where
  exists_injective_nat' := by
    have ⟨f, hf⟩ : Countable (List Char) := by infer_instance
    exists (fun s => f s.toList)
    exact fun _ _ h => String.toList_inj.mp (hf h)

namespace ProbLang.Asm

/-- An integer register index. -/
abbrev Reg := Fin 32

/-- The length of an array argument. -/
inductive Len where
  | const (n : Nat)
  | arg (index : Nat)
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- The representation of a boundary argument or result. -/
inductive ArgKind where
  | int (width : Nat)
  | uint (width : Nat)
  | loc
  | array (width : Nat) (len : Len)
  | unit
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- The register arguments and result of an imported function. -/
structure CallSig where
  /-- The argument kinds in register order. -/
  args : List ArgKind
  /-- The result representation in the return register. -/
  result : ArgKind
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- The boundary signature and stack requirement of an assembly fragment. -/
structure Sig extends CallSig where
  /-- The number of scratch bytes owned below the entry stack pointer. -/
  stackBound : Nat := 0
  /-- The named callback signatures. -/
  imports : List (String × CallSig) := []
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- A symbolic immediate, possibly relocated relative to an instruction. -/
inductive Imm where
  | int (value : Int)
  | symbol (name : String) (offset : Int := 0)
  | hi (name : String)
  | lo (name : String)
  | pcrelHi (name : String)
  | pcrelLo (name : String)
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- An instruction operand. -/
inductive Operand where
  | reg (index : Reg)
  | imm (value : Imm)
  | mem (offset : Imm) (base : Reg)
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- A RISC-V instruction in GNU assembler notation. -/
structure Instr where
  /-- The GNU instruction name. -/
  mnemonic : String
  /-- The instruction operands in source order. -/
  operands : List Operand
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- A section containing code or read-only data. -/
inductive Section where
  | text
  | rodata
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- An assembly directive with layout significance. -/
inductive Directive where
  | section (kind : Section)
  | align (power : Nat)
  | data (width : Nat) (values : List Int)
  | ascii (value : String) (terminated : Bool)
  | zero (count : Nat)
  | metadata (name : String) (arguments : String)
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- A label, instruction or directive line of a parsed assembly fragment. -/
inductive Line where
  | label (name : String)
  | instr (instruction : Instr)
  | directive (directive : Directive)
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- Parsed assembly with a named entry point. -/
structure AsmProg where
  /-- The parsed source lines. -/
  lines : List Line
  /-- The symbol at which execution starts. -/
  entry : String
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- A first-class assembly value and its boundary signature. -/
structure Code where
  /-- The parsed assembly fragment. -/
  prog : AsmProg
  /-- The boundary and stack contract. -/
  sig : Sig
  deriving DecidableEq, Repr, Countable, Inhabited

/-- A scalar value representable at the assembly boundary. -/
inductive BoundaryValue where
  | int (value : Int)
  | loc (location : Int)
  | unit
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

/-- A finite snapshot of integer-valued logical cells. -/
abbrev HeapSnapshot := List (Int × Int)

/-- The first-order archive needed to replay a paused assembly call. -/
structure Replay where
  /-- The original code value. -/
  code : Code
  /-- The original boundary arguments. -/
  args : List BoundaryValue
  /-- The entry fragment. -/
  entry : HeapSnapshot
  /-- Completed callbacks and their returned fragments. -/
  responses : List (BoundaryValue × HeapSnapshot) := []
  deriving DecidableEq, BEq, Repr, Countable, Inhabited

end ProbLang.Asm
