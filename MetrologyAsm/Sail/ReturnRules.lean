import MetrologyAsm.Profile.Rules

/-! # Sail return-instruction rules -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail
open Register (nextPC x1)

/-- A jump to an aligned address under UserConfig retires successfully and sets the next program
counter. -/
theorem jump_to_eq {s : Mach} (h : UserConfig s) (ra : BitVec 64)
    (halign0 : BitVec.access ra 0 = 0#1) (halign1 : BitVec.access ra 1 = 0#1) :
    runSail (jump_to ra) s =
      some (.Retire_Success (), { s with regs := s.regs.insert nextPC ra }) := by
  have hzca := (runSail_eq_some_iff _ _ _ _).mp h.disabled_Zca
  simp [runSail, jump_to, ext_control_check_pc, halign0, halign1, hzca,
    SailME.run, PreSail.PreSailME.run, bind, EStateM.bind, EStateM.map,
    pure, EStateM.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.lift, ExceptT.pure, MonadLift.monadLift, monadLift, liftM, Functor.map,
    Sail.assert, PreSail.assert, bit_to_bool, bool_bit_backwards,
    RiscvZkvm.Sail.Functions.not, set_next_pc, writeReg_eq,
    redirect_callback, RETIRE_SUCCESS]

/-- Clearing an already clear low address bit preserves the address. -/
theorem clear_lowbit_self (v : BitVec 64) (h : BitVec.access v 0 = 0#1) :
    BitVec.update v 0 0#1 = v := by
  change _root_.BitVec.ofBool (v.getLsbD 0) = 0#1 at h
  have hzero : v.getLsbD 0 = false := by
    cases hb : v.getLsbD 0 <;> simp [hb] at h ⊢
  unfold BitVec.update BitVec.updateSubrange'
  apply _root_.BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [_root_.BitVec.getLsbD_or, _root_.BitVec.getLsbD_and,
    _root_.BitVec.getLsbD_not, _root_.BitVec.getLsbD_shiftLeft,
    _root_.BitVec.zeroExtend_eq_setWidth, _root_.BitVec.getLsbD_setWidth,
    _root_.BitVec.getLsbD_allOnes, _root_.BitVec.getLsbD_zero]
  by_cases heq : i = 0
  · subst i
    simp [-_root_.BitVec.getLsbD_eq_getElem, hzero]
  · have hpos : ¬i < 1 := by omega
    simp [hi, hpos]

/-- The exchange return reads ra and changes only the next program counter. -/
theorem execute_ret_eq {s : Mach} (h : UserConfig s) (ra next : BitVec 64)
    (hra : s.regs.get? x1 = some ra)
    (hnext : s.regs.get? nextPC = some next)
    (halign0 : BitVec.access ra 0 = 0#1) (halign1 : BitVec.access ra 1 = 0#1) :
    runSail (execute_JALR 0#12 (.Regidx 1#5) (.Regidx 0#5)) s =
      some (.Retire_Success (), { s with regs := s.regs.insert nextPC ra }) := by
  have help := (runSail_eq_some_iff _ _ _ _).mp (h.update_elp_state_eq (.Regidx 1#5))
  have hjump := (runSail_eq_some_iff _ _ _ _).mp (jump_to_eq h ra halign0 halign1)
  have hmask := clear_lowbit_self ra halign0
  simp [runSail, execute_JALR, help, get_next_pc, readReg_eq hnext, rX_bits, rX,
    readReg_eq hra, sign_extend, Sail.BitVec.signExtend, hmask, hjump,
    wX_bits, wX, BitVec.toNatInt, regval_from_reg, bind, EStateM.bind, pure, EStateM.pure]

end MetrologyAsm
