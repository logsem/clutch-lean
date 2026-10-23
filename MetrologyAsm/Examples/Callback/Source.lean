import Metrology.ProbLang.Asm.Notation
import Metrology.ProbLang.Asm.Assembler

/-! # An actual assembly callback fragment -/

namespace MetrologyAsm

open ProbLang.Asm

/-- Preserve ra on a scratch stack while calling one imported integer callback. -/
def importToyAsm : AsmProg := riscv_asm!
  "\t.text
\t.globl\ttoy
toy:
\taddi\tsp, sp, -16
\tsd\tra, 8(sp)
\tcall\tcb
\tld\tra, 8(sp)
\taddi\tsp, sp, 16
\tret"

/-- The callback has no arguments or logical heap footprint and returns a signed doubleword. -/
def importToyCode : Code :=
  ⟨importToyAsm,
    { args := [], result := .int 64, stackBound := 16,
      imports := [("cb", ⟨[], .int 64⟩)] }⟩

/-- The actual assembler output of the callback fragment. -/
def importToyImage : Image :=
  (assemble importToyAsm).toOption.getD ⟨[], 0, 0, 0, [], [], []⟩

/-- The callback source assembles successfully to its declared image. -/
theorem assemble_importToyImage : assemble importToyAsm = .ok importToyImage := by
  rfl

end MetrologyAsm
