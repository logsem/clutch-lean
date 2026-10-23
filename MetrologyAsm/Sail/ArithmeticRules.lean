import MetrologyAsm.Sail.InstructionRules
import MetrologyAsm.Sail.RegisterRules

/-! # Sail integer arithmetic and linking instruction rules -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail

/-- Adding two signed displacements composes their modular word additions. -/
theorem addInt_compose (value : BitVec 64) (a b : Int) :
    BitVec.addInt (BitVec.addInt value a) b = BitVec.addInt value (a + b) := by
  unfold BitVec.addInt
  rw [BitVec.add_assoc, ← BitVec.ofInt_add]

/-- Reading sp returns its raw architectural register value. -/
theorem rX_bits_sp {s : Mach} {v : BitVec 64}
    (h : s.regs.get? Register.x2 = some v) :
    rX_bits (.Regidx 2#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading the import trampoline temporary returns its raw register value. -/
theorem rX_bits_t3 {s : Mach} {v : BitVec 64}
    (h : s.regs.get? Register.x28 = some v) :
    rX_bits (.Regidx 28#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Writing sp changes only its raw architectural register. -/
theorem wX_bits_sp (s : Mach) (v : BitVec 64) :
    wX_bits (.Regidx 2#5) v s = .ok () { s with regs := s.regs.insert Register.x2 v } := by
  rfl

/-- Writing ra changes only its raw architectural register. -/
theorem wX_bits_ra (s : Mach) (v : BitVec 64) :
    wX_bits (.Regidx 1#5) v s = .ok () { s with regs := s.regs.insert Register.x1 v } := by
  rfl

/-- Writing the trampoline temporary changes only that raw architectural register. -/
theorem wX_bits_t3 (s : Mach) (v : BitVec 64) :
    wX_bits (.Regidx 28#5) v s = .ok () { s with regs := s.regs.insert Register.x28 v } := by
  rfl

/-- The generated ADDI body composes a register read, signed addition, and register write. -/
theorem execute_ADDI_of_registers {s t : Mach} (imm : BitVec 12) (rs rd : regidx)
    (value : BitVec 64) (hread : rX_bits rs s = .ok value s)
    (hwrite : wX_bits rd (value + sign_extend (m := 64) imm) s = .ok () t) :
    execute_ITYPE imm rs rd .ADDI s = .ok (.Retire_Success ()) t := by
  simp [execute_ITYPE, hread, hwrite, bind, EStateM.bind, pure, EStateM.pure, RETIRE_SUCCESS]

/-- The generated AUIPC body uses the current architectural PC and its signed upper immediate. -/
theorem execute_AUIPC_of_registers {s t : Mach} (imm : BitVec 20) (rd : regidx)
    (pc : BitVec 64) (hpc : s.regs.get? Register.PC = some pc)
    (hwrite : wX_bits rd (pc + sign_extend (m := 64) (imm +++ 0#12)) s = .ok () t) :
    execute_UTYPE imm rd .AUIPC s = .ok (.Retire_Success ()) t := by
  simp [execute_UTYPE, get_arch_pc, readReg_eq hpc, hwrite,
    bind, EStateM.bind, pure, EStateM.pure, RETIRE_SUCCESS]

/-- An aligned JALR jumps and writes its link through the actual user-mode control checks. -/
theorem execute_JALR_of_registers {s t : Mach} (h : UserConfig s)
    (imm : BitVec 12) (rs rd : regidx) (value next : BitVec 64)
    (hread : rX_bits rs s = .ok value s)
    (hnext : s.regs.get? Register.nextPC = some next)
    (halign : (BitVec.update (value + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hwrite : wX_bits rd next { s with
        regs := s.regs.insert Register.nextPC
          (BitVec.update (value + sign_extend (m := 64) imm) 0 0#1) } = .ok () t) :
    execute_JALR imm rs rd s = .ok (.Retire_Success ()) t := by
  have help := (runSail_eq_some_iff _ _ _ _).mp (h.update_elp_state_eq rs)
  have hbits := aligned4_access halign
  have hjump := (runSail_eq_some_iff _ _ _ _).mp (jump_to_eq h _ hbits.1 hbits.2)
  simp [execute_JALR, help, get_next_pc, readReg_eq hnext, hread, hjump, hwrite,
    bind, EStateM.bind, pure, EStateM.pure]

/-- The generated XOR body composes its actual register reads and destination write. -/
theorem execute_XOR_of_registers {s t : Mach} (rs1 rs2 rd : regidx) (left right : BitVec 64)
    (hleft : rX_bits rs1 s = .ok left s) (hright : rX_bits rs2 s = .ok right s)
    (hwrite : wX_bits rd (left ^^^ right) s = .ok () t) :
    execute_RTYPE rs2 rs1 rd .XOR s = .ok (.Retire_Success ()) t := by
  simp [execute_RTYPE, hleft, hright, hwrite,
    bind, EStateM.bind, pure, EStateM.pure, RETIRE_SUCCESS]

end MetrologyAsm
