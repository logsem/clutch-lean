import MetrologyAsm.Sail.Execution
import RiscvZkvm.Sail.DecodeExt

/-! # Decoder effects and the standard return encoding -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions Sail.ConcurrencyInterfaceV1

/-- The decoder's extension-query effect followed by a fixed instruction. -/
noncomputable def guardedDecode (i : instruction) : SailM instruction := do
  let _ ← currentlyEnabled extension.Ext_Zicfilp
  pure i

/-- Proves a decoder equation that holds once the extension query has been answered. -/
macro "decode_guarded" : tactic =>
  `(tactic| (unfold ext_decode encdec_backwards guardedDecode
             apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
             funext enabled
             cases enabled <;> rfl))

/-- A return instruction decodes to an indirect jump through ra without a link. -/
theorem decode_ret :
    ext_decode 0x00008067#32 = guardedDecode (.JALR (0#12, .Regidx 1#5, .Regidx 0#5)) := by
  decode_guarded

/-- A successful extension query makes a checked decoder return its instruction unchanged. -/
theorem guardedDecode_result (i : instruction)
    (s : Mach) (enabled : Bool)
    (h : currentlyEnabled extension.Ext_Zicfilp s = .ok enabled s) :
    guardedDecode i s = .ok i s := by
  simp only [guardedDecode, Bind.bind, EStateM.bind, h]
  rfl

end MetrologyAsm
