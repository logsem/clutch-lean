module

public import Metrology.ProbLang.Asm.Assembler
public import Metrology.ProbLang.Asm.Notation

/-! # Assembly encoding examples -/

@[expose] public section

namespace ProbLang.Asm

/-- An in-place exchange of two 64-bit cells. -/
def swapAsm : AsmProg := riscv_asm!
  "\t.text
\t.globl\tswap
swap:
\tld\ta2, 0(a0)
\tld\ta3, 0(a1)
\tsd\ta3, 0(a0)
\tsd\ta2, 0(a1)
\tret"

/-- The void signature of the in-place exchange. -/
def swapSig : Sig := { args := [.loc, .loc], result := .unit }

/-- The first-class exchange fragment. -/
def swapCode : Code := ⟨swapAsm, swapSig⟩

/-- The exchange fragment's five uncompressed machine words. -/
theorem swapAsm_words :
    (assemble swapAsm).toOption.map (fun i => i.instructions.map (·.word.toNat)) =
      some [0x00053603, 0x0005b683, 0x00d53023, 0x00c5b023, 0x00008067] := by decide +kernel

/-- The exchange entry point and executable region. -/
theorem swapAsm_layout :
    (assemble swapAsm).toOption.map (fun i => (i.entry, i.textLen, i.rodataOff)) =
      some (0, 20, 24) := by decide +kernel

end ProbLang.Asm
