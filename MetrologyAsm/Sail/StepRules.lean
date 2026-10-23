import MetrologyAsm.Sail.Monad
import Std.Data.ExtDHashMap.Lemmas

/-! # Full Sail instruction-step rules -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail

/-- The state after the wrapper disables retirement counting for this instruction. -/
def counterState (s : Mach) : Mach :=
  { s with regs := s.regs.insert Register.minstret_increment false }

/-- Committing the next program counter changes only the program-counter register. -/
theorem tick_pc_eq {s : Mach} {next : BitVec 64}
    (hnext : s.regs.get? Register.nextPC = some next) :
    tick_pc () s = .ok () { s with regs := s.regs.insert Register.PC next } := by
  have hpc : ({ s with regs := s.regs.insert Register.PC next } : Mach).regs.get?
      Register.PC = some next := by
    simp
  have hreadpc := readReg_eq (s := { s with regs := s.regs.insert Register.PC next }) hpc
  simp [tick_pc, bind, EStateM.bind, readReg_eq hnext, writeReg_eq, hreadpc, pure,
    EStateM.pure, pc_write_callback]

/-- The sequential next-program-counter value prepared before instruction execution. -/
def sequentialState (s : Mach) (pc : BitVec 64) : Mach :=
  { s with regs := s.regs.insert Register.nextPC (BitVec.addInt pc 4) }

/-- Successful fetch, decode, and instruction execution compose into one active-hart result. -/
theorem run_hart_active_of_execute (s t : Mach) (priv : Privilege) (pc : BitVec 64)
    (word : BitVec 32) (inst : instruction)
    (hpriv : s.regs.get? Register.cur_privilege = some priv)
    (hpending : runSail (dispatchInterrupt priv) s = some (none, s))
    (hfetch : runSail (fetch ()) s = some (.F_Base word, s))
    (hdecode : runSail (ext_decode word) s = some (inst, s))
    (help : s.regs.get? Register.elp = some 0#1)
    (hpc : s.regs.get? Register.PC = some pc)
    (hexec : runSail (execute inst) (sequentialState s pc) = some (.Retire_Success (), t)) :
    runSail (run_hart_active 0) s = some (.Step_Execute (.Retire_Success (), word), t) := by
  have hpending' := (runSail_eq_some_iff _ _ _ _).mp hpending
  have hfetch' := (runSail_eq_some_iff _ _ _ _).mp hfetch
  have hdecode' := (runSail_eq_some_iff _ _ _ _).mp hdecode
  have hexec' := (runSail_eq_some_iff _ _ _ _).mp hexec
  dsimp [sequentialState] at hexec'
  simp [runSail, run_hart_active, SailME.run, PreSail.PreSailME.run, bind, EStateM.bind,
    EStateM.map, pure, EStateM.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.lift, ExceptT.pure, MonadLift.monadLift, monadLift, liftM, Functor.map,
    readReg_eq hpriv, hpending', hfetch', ext_fetch_hook, hdecode', is_landing_pad_expected,
    readReg_eq help, landing_pad_bits_backwards, get_config_print_instr, readReg_eq hpc,
    writeReg_eq, hexec', zero_extend, Sail.BitVec.zeroExtend]

/-- A retired instruction commits its next program counter and preserves the remaining state. -/
theorem rvStep_of_retired (s t : Mach) (priv : Privilege) (word : BitVec 32) (next : BitVec 64)
    (hpriv : s.regs.get? Register.cur_privilege = some priv)
    (hinitial : s.regs.get? Register.hart_state = some (.HART_ACTIVE ()))
    (hcount : runSail (should_inc_minstret priv) s = some (false, s))
    (hrun : runSail (run_hart_active 0) (counterState s) =
      some (.Step_Execute (.Retire_Success (), word), t))
    (hhart : t.regs.get? Register.hart_state = some (.HART_ACTIVE ()))
    (hnext : t.regs.get? Register.nextPC = some next)
    (hflag : t.regs.get? Register.minstret_increment = some false) :
    rvStep s = some { t with regs := t.regs.insert Register.PC next } := by
  have hcount' := (runSail_eq_some_iff _ _ _ _).mp hcount
  have hrun' := (runSail_eq_some_iff _ _ _ _).mp hrun
  have hprepared : (counterState s).regs.get? Register.hart_state = some (.HART_ACTIVE ()) := by
    simp [counterState, Std.ExtDHashMap.get?_insert, hinitial]
  have hreadyread := readReg_eq (s := counterState s) hprepared
  dsimp [counterState] at hreadyread hrun'
  have hflag' : ({ t with regs := t.regs.insert Register.PC next } : Mach).regs.get?
      Register.minstret_increment = some false := by
    simp [Std.ExtDHashMap.get?_insert, hflag]
  have hreadflag := readReg_eq (s := { t with regs := t.regs.insert Register.PC next }) hflag'
  simp [rvStep, runSail, try_step, bind, EStateM.bind, readReg_eq hpriv, hcount',
    writeReg_eq, hreadyread, hrun', readReg_eq hhart, hart_is_active, tick_pc_eq hnext,
    Sail.assert, PreSail.assert, pure, EStateM.pure, hreadflag, get_config_rvfi]

end MetrologyAsm
