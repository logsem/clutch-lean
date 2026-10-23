import RiscvZkvm.Sail.InstsEnd

/-! # Sail instruction-body leaves -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail

/-- The Sail ADDI body writes its immediate when its source is the zero register. -/
theorem execute_addi_zero_seven
    (s : PreSail.SequentialState RegisterType trivialChoiceSource) :
    (execute_ITYPE 7#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI) s =
      .ok (.Retire_Success ()) { s with regs := s.regs.insert Register.x10 7#64 } := by
  rfl

end MetrologyAsm
