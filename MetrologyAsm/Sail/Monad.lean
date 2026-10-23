import MetrologyAsm.Sail.Execution

/-! # Sail state-monad reduction rules -/

namespace MetrologyAsm

open Sail

variable {α β : Type}

/-- A successful raw Sail computation is exactly a successful observed computation. -/
theorem runSail_eq_some_iff (m : SailM α) (s t : Mach) (a : α) :
    runSail m s = some (a, t) ↔ m s = .ok a t := by
  cases h : m s <;> simp [runSail, h]

/-- A pure Sail computation preserves its machine state. -/
@[simp]
theorem runSail_pure (a : α) (s : Mach) :
    runSail (pure a : SailM α) s = some (a, s) := by
  rfl

/-- Sequential Sail computations compose their observed states. -/
theorem runSail_bind (m : SailM α) (f : α → SailM β) (s : Mach) :
    runSail (m >>= f) s = (runSail m s).bind (fun (a, s') => runSail (f a) s') := by
  cases h : m s <;> simp [runSail, bind, EStateM.bind, h]

/-- Reading a present Sail register preserves the machine state. -/
theorem readReg_eq {s : Mach} {r : Register} {v : RegisterType r}
    (h : s.regs.get? r = some v) : (readReg r) s = .ok v s := by
  simp [Sail.readReg, PreSail.readReg, h, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.get, get, MonadState.get, getThe, MonadStateOf.get]

/-- A present Sail register is returned by the observation wrapper. -/
theorem runSail_readReg {s : Mach} {r : Register} {v : RegisterType r}
    (h : s.regs.get? r = some v) : runSail (readReg r) s = some (v, s) := by
  rw [runSail_eq_some_iff]
  exact readReg_eq h

/-- A register write changes only that register in the raw Sail state. -/
theorem writeReg_eq (s : Mach) (r : Register) (v : RegisterType r) :
    (writeReg r v) s = .ok () { s with regs := s.regs.insert r v } := by
  rfl

/-- A register write changes only that register in the observed Sail state. -/
@[simp]
theorem runSail_writeReg (s : Mach) (r : Register) (v : RegisterType r) :
    runSail (writeReg r v) s = some ((), { s with regs := s.regs.insert r v }) := by
  rfl

end MetrologyAsm
