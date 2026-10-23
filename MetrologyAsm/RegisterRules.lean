import MetrologyAsm.Monad

/-! # Sail register rules for the exchange calling convention -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail

/-- Reading ra returns its raw architectural register value. -/
theorem rX_bits_ra {s : Mach} {v : BitVec 64}
    (h : s.regs.get? Register.x1 = some v) :
    rX_bits (.Regidx 1#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading a0 returns its raw architectural register value. -/
theorem rX_bits_a0 {s : Mach} {v : BitVec 64}
    (h : s.regs.get? Register.x10 = some v) :
    rX_bits (.Regidx 10#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading a1 returns its raw architectural register value. -/
theorem rX_bits_a1 {s : Mach} {v : BitVec 64}
    (h : s.regs.get? Register.x11 = some v) :
    rX_bits (.Regidx 11#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading a2 returns its raw architectural register value. -/
theorem rX_bits_a2 {s : Mach} {v : BitVec 64}
    (h : s.regs.get? Register.x12 = some v) :
    rX_bits (.Regidx 12#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Reading a3 returns its raw architectural register value. -/
theorem rX_bits_a3 {s : Mach} {v : BitVec 64}
    (h : s.regs.get? Register.x13 = some v) :
    rX_bits (.Regidx 13#5) s = .ok v s := by
  simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq h,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Writing a2 changes only its raw architectural register. -/
theorem wX_bits_a2 (s : Mach) (v : BitVec 64) :
    wX_bits (.Regidx 12#5) v s = .ok () { s with regs := s.regs.insert Register.x12 v } := by
  rfl

/-- Writing a3 changes only its raw architectural register. -/
theorem wX_bits_a3 (s : Mach) (v : BitVec 64) :
    wX_bits (.Regidx 13#5) v s = .ok () { s with regs := s.regs.insert Register.x13 v } := by
  rfl

end MetrologyAsm
