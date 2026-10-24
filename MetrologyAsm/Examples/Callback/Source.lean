import Metrology.ProbLang.Asm.Notation
import Metrology.ProbLang.Asm.Assembler

/-! # An actual assembly callback fragment -/

namespace MetrologyAsm

open ProbLang.Asm

/-- The callback fragment saves ra on a scratch stack and calls the imported callback. -/
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

/-- The import toy takes no arguments, has no logical heap footprint, and returns a doubleword. -/
def importToyCode : Code :=
  ⟨importToyAsm,
    { args := [], result := .int 64, stackBound := 16,
      imports := [("cb", ⟨[], .int 64⟩)] }⟩

/-- The actual assembler output of the callback fragment. -/
def importToyImage : Image :=
  (assemble importToyAsm).toOption.getD ⟨[], 0, 0, 0, [], [], []⟩

/-- The callback source assembles successfully to its image. -/
theorem assemble_importToyImage : assemble importToyAsm = .ok importToyImage := by
  rfl

/-- The callback fragment imports the empty-argument integer callback `cb`. -/
theorem importToyCode_mem_imports :
    ("cb", ⟨[], .int 64⟩) ∈ importToyCode.sig.imports := by
  simp [importToyCode]

end MetrologyAsm
