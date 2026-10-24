import MetrologyAsm.ABI.Interface
import MetrologyAsm.Profile.Witness

/-! # Shared concrete placements and states for assembly examples -/

set_option maxRecDepth 100000

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions
open Sail.ConcurrencyInterfaceV1

/-- A concrete aligned placement for two distinct logical cells. -/
def witnessPlacement (l : Loc) : Placement where
  addr k := if k = l then 0x80001000#64 else 0x80001008#64
  codeBase := 0x80000000#64
  importAddr _ := 0x80005000#64
  retAddr := 0x80002000#64

/-- The witness's active register state keeps the formal profile and installs the ABI bindings. -/
noncomputable def witnessRegisters : Mach :=
  let s := profileWitness
  let regs := s.regs.insert .PC 0x80000000#64
  let regs := regs.insert .x1 0x80002000#64
  let regs := regs.insert .x2 0x80004000#64
  let regs := regs.insert .x10 0x80001000#64
  let regs := regs.insert .x11 0x80001008#64
  let regs := regs.insert .mtvec 0x80003000#64
  let regs := regs.insert .stvec 0x80003000#64
  { s with regs }

/-- The witness's register installation satisfies the complete open user profile. -/
theorem witnessRegisters_config : UserConfig witnessRegisters :=
  (((((((profileWitness_config.insert .PC _ trivial).insert .x1 _ trivial).insert
    .x2 _ trivial).insert .x10 _ trivial).insert .x11 _ trivial).insert .mtvec _
    (by simp only [userRegPolicy]; decide +kernel)).insert .stvec _
    (by simp only [userRegPolicy]; decide +kernel))

end MetrologyAsm
