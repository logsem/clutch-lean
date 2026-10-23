import MetrologyAsm.Sail.Monad

/-! # Sail register rules for the exchange calling convention -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail

/-- Reading the architectural zero register returns zero without consulting state. -/
theorem rX_bits_zero (s : Mach) : rX_bits (.Regidx 0#5) s = .ok 0#64 s := by
  rfl

section Reads

variable {s : Mach} {v : BitVec 64}

/-- Reading ra returns its raw architectural register value. -/
theorem rX_bits_ra
    (h : s.regs.get? Register.x1 = some v) :
    rX_bits (.Regidx 1#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading a0 returns its raw architectural register value. -/
theorem rX_bits_a0
    (h : s.regs.get? Register.x10 = some v) :
    rX_bits (.Regidx 10#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading a1 returns its raw architectural register value. -/
theorem rX_bits_a1
    (h : s.regs.get? Register.x11 = some v) :
    rX_bits (.Regidx 11#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading a2 returns its raw architectural register value. -/
theorem rX_bits_a2
    (h : s.regs.get? Register.x12 = some v) :
    rX_bits (.Regidx 12#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading a3 returns its raw architectural register value. -/
theorem rX_bits_a3
    (h : s.regs.get? Register.x13 = some v) :
    rX_bits (.Regidx 13#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading s0 returns its raw architectural register value. -/
theorem rX_bits_s0 (h : s.regs.get? Register.x8 = some v) :
    rX_bits (.Regidx 8#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading s1 returns its raw architectural register value. -/
theorem rX_bits_s1 (h : s.regs.get? Register.x9 = some v) :
    rX_bits (.Regidx 9#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

end Reads

section Writes

variable (s : Mach) (v : BitVec 64)

/-- Writing a2 changes only its raw architectural register. -/
theorem wX_bits_a2 :
    wX_bits (.Regidx 12#5) v s = .ok () { s with regs := s.regs.insert Register.x12 v } := by
  rfl

/-- Writing a3 changes only its raw architectural register. -/
theorem wX_bits_a3 :
    wX_bits (.Regidx 13#5) v s = .ok () { s with regs := s.regs.insert Register.x13 v } := by
  rfl

/-- Writing a0 changes only its raw architectural register. -/
theorem wX_bits_a0 :
    wX_bits (.Regidx 10#5) v s = .ok () { s with regs := s.regs.insert Register.x10 v } := by
  rfl

/-- Writing a1 changes only its raw architectural register. -/
theorem wX_bits_a1 :
    wX_bits (.Regidx 11#5) v s = .ok () { s with regs := s.regs.insert Register.x11 v } := by
  rfl

/-- Writing s0 changes only its raw architectural register. -/
theorem wX_bits_s0 :
    wX_bits (.Regidx 8#5) v s = .ok () { s with regs := s.regs.insert Register.x8 v } := by
  rfl

/-- Writing s1 changes only its raw architectural register. -/
theorem wX_bits_s1 :
    wX_bits (.Regidx 9#5) v s = .ok () { s with regs := s.regs.insert Register.x9 v } := by
  rfl

end Writes

end MetrologyAsm
