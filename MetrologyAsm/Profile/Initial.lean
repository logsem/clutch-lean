import MetrologyAsm.Profile.Config
import RiscvZkvm.Sail

/-! # Concrete Sail spike state -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail.ConcurrencyInterfaceV1
open Register Vector

/-- A default value for each generated register type. -/
noncomputable def defaultRegister (r : Register) : RegisterType r := by
  cases r <;> exact default

/-- All generated registers, in their declaration order. -/
def allRegisters : List Register := [
  hart_state, satp, tlb, pma_regions, htif_payload_writes, htif_cmd_write, htif_exit_code,
  htif_done, htif_tohost, stimecmp, mtimecmp, htif_tohost_base, pc_reset_address, elp,
  minstretcfg, mcyclecfg, vcsr, vtype, vl, vstart, vr31, vr30, vr29, vr28, vr27, vr26, vr25,
  vr24, vr23, vr22, vr21, vr20, vr19, vr18, vr17, vr16, vr15, vr14, vr13, vr12, vr11, vr10, vr9,
  vr8, vr7, vr6, vr5, vr4, vr3, vr2, vr1, vr0, fcsr, f31, f30, f29, f28, f27, f26, f25, f24,
  f23, f22, f21, f20, f19, f18, f17, f16, f15, f14, f13, f12, f11, f10, f9, f8, f7, f6, f5, f4,
  f3, f2, f1, f0, pmpaddr_n, pmpcfg_n, sig_seip, sig_meip, mideleg, medeleg, mip, mie, tselect,
  stval, scause, sepc, sscratch, stvec, mconfigptr, mhartid, marchid, mimpid, mvendorid,
  minstret_increment, minstret, mtime, mcycle, mcountinhibit, mcounteren, scounteren, mscratch,
  mtval, mepc, mcause, mtvec, cur_inst, x31, x30, x29, x28, x27, x26, x25, x24, x23, x22, x21,
  x20, x19, x18, x17, x16, x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1,
  nextPC, PC, menvcfg, mseccfg, senvcfg, sstateen3, sstateen2, sstateen1, sstateen0, mstateen3,
  mstateen2, mstateen1, mstateen0, hstateen3, hstateen2, hstateen1, hstateen0, mstatus, misa,
  cur_privilege, rvfi_mem_data_present, rvfi_mem_data, rvfi_int_data_present, rvfi_int_data,
  rvfi_pc_data, rvfi_inst_data, rvfi_instruction, fp_rounding_global]

/-- A state whose generated registers all hold the given values. -/
noncomputable def fillRegisters (f : (r : Register) → RegisterType r) : Mach :=
  { (default : Mach) with
    regs := allRegisters.foldl (fun m r => m.insert r (f r)) default }

/-- A state with every generated register present. -/
noncomputable def zeroState : Mach := fillRegisters defaultRegister

/-- The state after running the Sail model initializer on `zeroState`. -/
noncomputable def modelInitial : Option Mach :=
  (runSail (sail_model_init ()) zeroState).map Prod.snd

/-- Put one little-endian word into Sail memory. -/
def writeWord (s : Mach) (a : Nat) (w : BitVec 32) : Mach :=
  (List.range 4).foldl (fun s i =>
    { s with mem := s.mem.insert (a + i) (BitVec.ofNat 8 (w.toNat / 2 ^ (8 * i))) }) s

/-- A user-mode RV64IM state with bare address translation and a permissive PMP region. -/
noncomputable def userInitial : Option Mach := modelInitial.map fun s =>
  let regs := s.regs.insert cur_privilege Privilege.User
  let regs := regs.insert PC 0x80000000#64
  let regs := regs.insert nextPC 0x80000004#64
  let regs := regs.insert misa 0x8000000000141100#64
  let regs := regs.insert mcountinhibit 4#32
  let regs := regs.insert pmpcfg_n ((replicate 64 0#8).set 0 0x0f#8)
  let regs := regs.insert pma_regions [userRamRegion]
  let regs := regs.insert pmpaddr_n ((replicate 64 0#64).set 0 0x40000000#64)
  let regs := regs.insert mtvec 0x80003000#64
  let regs := regs.insert stvec 0x80003000#64
  let regs := regs.insert x1 0x80002000#64
  let regs := regs.insert x2 0x80004000#64
  let regs := regs.insert x10 0x80001000#64
  let regs := regs.insert x11 0x80001008#64
  { s with regs }

end MetrologyAsm
