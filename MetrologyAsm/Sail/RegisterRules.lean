import MetrologyAsm.Sail.Monad
import Std.Tactic.BVDecide

/-! # Sail register rules for the exchange calling convention -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail
open Register (x1 x10 x11 x12 x13 x2 x28 x8 x9)

/-- Restoring an extracted supervisor shadow-stack bit leaves its register unchanged. -/
theorem update_senvcfg_sse_self (v : BitVec 64) :
    _update_SEnvcfg_SSE v (_get_SEnvcfg_SSE v) = v := by
  unfold _update_SEnvcfg_SSE _get_SEnvcfg_SSE Sail.BitVec.updateSubrange
    Sail.BitVec.updateSubrange' Sail.BitVec.extractLsb
  bv_decide

/-- Extracting all bits of an address preserves that address. -/
theorem extract_full_address (v : BitVec 64) : Sail.BitVec.extractLsb v 63 0 = v := by
  unfold Sail.BitVec.extractLsb
  bv_normalize

/-- Reading the architectural zero register returns zero without consulting state. -/
theorem rX_bits_zero (s : Mach) : rX_bits (.Regidx 0#5) s = .ok 0#64 s := by
  rfl

section Reads

/-- Reduces `rX_bits` at a literal register index, given the register's contents. -/
local macro "rX_bits_simp " h:term : tactic =>
  `(tactic| simp [rX_bits, rX, BitVec.toNatInt, regval_from_reg, readReg_eq $h,
    bind, EStateM.bind, pure, EStateM.pure])

variable {s : Mach} {v : BitVec 64}

/-- Reading ra returns its raw architectural register value. -/
theorem rX_bits_ra
    (h : s.regs.get? x1 = some v) :
    rX_bits (.Regidx 1#5) s = .ok v s := by
  rX_bits_simp h

/-- Reading a0 returns its raw architectural register value. -/
theorem rX_bits_a0
    (h : s.regs.get? x10 = some v) :
    rX_bits (.Regidx 10#5) s = .ok v s := by
  rX_bits_simp h

/-- Reading a1 returns its raw architectural register value. -/
theorem rX_bits_a1
    (h : s.regs.get? x11 = some v) :
    rX_bits (.Regidx 11#5) s = .ok v s := by
  rX_bits_simp h

/-- Reading a2 returns its raw architectural register value. -/
theorem rX_bits_a2
    (h : s.regs.get? x12 = some v) :
    rX_bits (.Regidx 12#5) s = .ok v s := by
  rX_bits_simp h

/-- Reading a3 returns its raw architectural register value. -/
theorem rX_bits_a3
    (h : s.regs.get? x13 = some v) :
    rX_bits (.Regidx 13#5) s = .ok v s := by
  rX_bits_simp h

/-- Reading s0 returns its raw architectural register value. -/
theorem rX_bits_s0 (h : s.regs.get? x8 = some v) :
    rX_bits (.Regidx 8#5) s = .ok v s := by
  rX_bits_simp h

/-- Reading s1 returns its raw architectural register value. -/
theorem rX_bits_s1 (h : s.regs.get? x9 = some v) :
    rX_bits (.Regidx 9#5) s = .ok v s := by
  rX_bits_simp h

/-- Reading sp returns its raw architectural register value. -/
theorem rX_bits_sp
    (h : s.regs.get? x2 = some v) :
    rX_bits (.Regidx 2#5) s = .ok v s := by
  rX_bits_simp h

/-- Reading the import trampoline temporary returns its raw register value. -/
theorem rX_bits_t3
    (h : s.regs.get? x28 = some v) :
    rX_bits (.Regidx 28#5) s = .ok v s := by
  rX_bits_simp h

end Reads

section Writes

variable (s : Mach) (v : BitVec 64)

/-- Writing a0 changes only its raw architectural register. -/
theorem wX_bits_a0 :
    wX_bits (.Regidx 10#5) v s = .ok () { s with regs := s.regs.insert x10 v } := by
  rfl

/-- Writing a1 changes only its raw architectural register. -/
theorem wX_bits_a1 :
    wX_bits (.Regidx 11#5) v s = .ok () { s with regs := s.regs.insert x11 v } := by
  rfl

/-- Writing a2 changes only its raw architectural register. -/
theorem wX_bits_a2 :
    wX_bits (.Regidx 12#5) v s = .ok () { s with regs := s.regs.insert x12 v } := by
  rfl

/-- Writing a3 changes only its raw architectural register. -/
theorem wX_bits_a3 :
    wX_bits (.Regidx 13#5) v s = .ok () { s with regs := s.regs.insert x13 v } := by
  rfl

/-- Writing s0 changes only its raw architectural register. -/
theorem wX_bits_s0 :
    wX_bits (.Regidx 8#5) v s = .ok () { s with regs := s.regs.insert x8 v } := by
  rfl

/-- Writing s1 changes only its raw architectural register. -/
theorem wX_bits_s1 :
    wX_bits (.Regidx 9#5) v s = .ok () { s with regs := s.regs.insert x9 v } := by
  rfl

/-- Writing sp changes only its raw architectural register. -/
theorem wX_bits_sp :
    wX_bits (.Regidx 2#5) v s = .ok () { s with regs := s.regs.insert x2 v } := by
  rfl

/-- Writing ra changes only its raw architectural register. -/
theorem wX_bits_ra :
    wX_bits (.Regidx 1#5) v s = .ok () { s with regs := s.regs.insert x1 v } := by
  rfl

/-- Writing the trampoline temporary changes only that raw architectural register. -/
theorem wX_bits_t3 :
    wX_bits (.Regidx 28#5) v s = .ok () { s with regs := s.regs.insert x28 v } := by
  rfl

end Writes

end MetrologyAsm
