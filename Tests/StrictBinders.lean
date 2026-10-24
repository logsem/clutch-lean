import Tests.StrictSourceEquivalence
import RiscvZkvm.Sail.Specialization
import RiscvZkvm.Sail.RiscvExtras
import Lean

/-! # Strict binders for the unchanged Sail extraction -/

open Lean Lean.Elab

run_elab do
  let options ← getOptions
  if autoImplicit.get options || relaxedAutoImplicit.get options then
    throwError "Sail extraction checks require both auto-implicit options disabled"

namespace MetrologyAsm

universe u

/-- The parser shim preserves the generated width order and original function body. -/
theorem zeroExtend_explicit :
    (@zero_extend : (width resultWidth : Nat) → BitVec width → BitVec resultWidth) =
      (fun width resultWidth (value : BitVec width) =>
        Sail.BitVec.zeroExtend value resultWidth) := rfl

/-- The generated exception wrapper retains its original type and body. -/
theorem sailTryCatch_explicit :
    (@Sail.sailTryCatch : {α : Type} → SailM α → (exception → SailM α) → SailM α) =
      (fun {α : Type} (e : SailM α) (h : exception → SailM α) =>
        PreSail.sailTryCatch e h) := rfl

/-- The generated throw wrapper retains its original type and body. -/
theorem sailThrow_explicit :
    (@Sail.sailThrow : {α : Type} → exception → SailM α) =
      (fun {α : Type} (e : exception) => (PreSail.sailThrow e : SailM α)) := rfl

/-- The generated undefined-vector wrapper retains its original type and body. -/
theorem undefinedVector_explicit :
    (@Sail.undefined_vector : {α : Type} → (n : Nat) → α → SailM (Vector α n)) =
      (fun {α : Type} (n : Nat) (value : α) => PreSail.undefined_vector n value) := rfl

/-- The generated register-read wrapper retains its original type and body. -/
theorem readRegRef_explicit :
    (@Sail.readRegRef : {α : Type} → Sail.RegisterRef α → SailM α) =
      (fun {α : Type} (reference : Sail.RegisterRef α) => PreSail.readRegRef reference) := rfl

/-- The generated register-write wrapper retains its original type and body. -/
theorem writeRegRef_explicit :
    (@Sail.writeRegRef : {α : Type} → Sail.RegisterRef α → α → SailM Unit) =
      (fun {α : Type} (reference : Sail.RegisterRef α) (value : α) =>
        PreSail.writeRegRef reference value) := rfl

/-- The generated register-dereference wrapper retains its original type and body. -/
theorem regDeref_explicit :
    (@Sail.reg_deref : {α : Type} → Sail.RegisterRef α → SailM α) =
      (fun {α : Type} (reference : Sail.RegisterRef α) => PreSail.reg_deref reference) := rfl

open Sail.ConcurrencyInterfaceV1

/-- The generated memory-write wrapper retains its original binder order and body. -/
theorem sailMemWrite_explicit :
    (@Sail.ConcurrencyInterfaceV1.sail_mem_write : {n vasize pa_size : Nat} →
      {ts arch : Type} → [Arch] → Mem_write_request n vasize (BitVec pa_size) ts arch →
          SailM (Sail.Result (Option Bool) Arch.abort)) =
      (fun {n vasize pa_size : Nat} {ts arch : Type} [Arch]
        (request : Mem_write_request n vasize (BitVec pa_size) ts arch) =>
          PreSail.sail_mem_write request) := rfl

/-- The generated memory-read wrapper retains its original binder order and body. -/
theorem sailMemRead_explicit :
    (@Sail.ConcurrencyInterfaceV1.sail_mem_read : {n vasize pa_size : Nat} →
      {ts arch : Type} → [Arch] → Mem_read_request n vasize (BitVec pa_size) ts arch →
          SailM (Sail.Result (BitVec (8 * n) × Option Bool) Arch.abort)) =
      (fun {n vasize pa_size : Nat} {ts arch : Type} [Arch]
        (request : Mem_read_request n vasize (BitVec pa_size) ts arch) =>
          PreSail.sail_mem_read request) := rfl

/-- The generated barrier wrapper retains its unrestricted source universe and body. -/
theorem sailBarrier_explicit :
    (@Sail.ConcurrencyInterfaceV1.sail_barrier : {α : Sort u} → α → SailM Unit) =
      (fun {α : Sort u} (value : α) => PreSail.sail_barrier value) := rfl

/-- The generated exception runner retains its original type and body. -/
theorem sailMERun_explicit :
    (@Sail.SailME.run : {α : Type} → SailME α α → SailM α) =
      (fun {α : Type} (computation : SailME α α) => PreSail.PreSailME.run computation) := rfl

/-- The generated exception throw retains its original binder order and body. -/
theorem sailMEThrow_explicit :
    (@Sail.SailME.throw : {α β : Type} → α → SailME α β) =
      (fun {α β : Type} (value : α) => (PreSail.PreSailME.throw value : SailME α β)) := rfl

/-- The generated exception catch retains its original binder order and body. -/
theorem sailTryCatchE_explicit :
    (@Sail.sailTryCatchE : {β α : Type} → SailME β α → (exception → SailME β α) → SailME β α) =
      (fun {β α : Type} (computation : SailME β α) (handler : exception → SailME β α) =>
        PreSail.sailTryCatchE computation handler) := rfl

/-- The generated observation helper retains its original type and body. -/
theorem unwrapValue_explicit :
    (@Sail.unwrapValue : {α : Type} → [Inhabited α] → SailM α → α) =
      (fun {α : Type} [Inhabited α] (computation : SailM α) =>
        match computation.run default with
        | .ok value _ => value
        | _ => default) := rfl

/-- The hand-owned print hook retains its inferred width and no-op body. -/
theorem printBits_explicit :
    (@print_bits : {n : Nat} → String → BitVec n → Unit) =
      (fun {n : Nat} (_text : String) (_bits : BitVec n) => ()) := rfl

end MetrologyAsm
