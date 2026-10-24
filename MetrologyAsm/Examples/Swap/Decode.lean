import MetrologyAsm.Sail.Decode

/-! # Sail decoder checks for the exchange fragment -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions Sail.ConcurrencyInterfaceV1

/-- Close a decoder equation whose word decodes through the `Ext_Zicfilp` guard. -/
local macro "decode_via_guard" : tactic =>
  `(tactic| (unfold ext_decode encdec_backwards guardedDecode
             apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
             funext enabled
             cases enabled <;> rfl))

/-- The first exchange load decodes to a signed 64-bit load into a2. -/
theorem decode_swap_ld_a2 :
    ext_decode 0x00053603#32 =
      guardedDecode (.LOAD (0#12, .Regidx 10#5, .Regidx 12#5, false, 8)) := by
  decode_via_guard

/-- The second exchange load decodes to a signed 64-bit load into a3. -/
theorem decode_swap_ld_a3 :
    ext_decode 0x0005b683#32 =
      guardedDecode (.LOAD (0#12, .Regidx 11#5, .Regidx 13#5, false, 8)) := by
  decode_via_guard

/-- The first exchange store writes a3 through a0. -/
theorem decode_swap_sd_a3 :
    ext_decode 0x00d53023#32 = guardedDecode (.STORE (0#12, .Regidx 13#5, .Regidx 10#5, 8)) := by
  decode_via_guard

/-- The second exchange store writes a2 through a1. -/
theorem decode_swap_sd_a2 :
    ext_decode 0x00c5b023#32 = guardedDecode (.STORE (0#12, .Regidx 12#5, .Regidx 11#5, 8)) := by
  decode_via_guard

/-- The five source words and their checked Sail instructions. -/
def swapDecoderCases : List (BitVec 32 × instruction) :=
  [(0x00053603#32, .LOAD (0#12, .Regidx 10#5, .Regidx 12#5, false, 8)),
    (0x0005b683#32, .LOAD (0#12, .Regidx 11#5, .Regidx 13#5, false, 8)),
    (0x00d53023#32, .STORE (0#12, .Regidx 13#5, .Regidx 10#5, 8)),
    (0x00c5b023#32, .STORE (0#12, .Regidx 12#5, .Regidx 11#5, 8)),
    (0x00008067#32, .JALR (0#12, .Regidx 1#5, .Regidx 0#5))]

/-- Every exchange word has its checked decoder equation. -/
theorem swapDecoderCases_correct (entry : BitVec 32 × instruction)
    (h : entry ∈ swapDecoderCases) : ext_decode entry.1 = guardedDecode entry.2 := by
  simp only [swapDecoderCases, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only
  all_goals first
    | exact decode_swap_ld_a2
    | exact decode_swap_ld_a3
    | exact decode_swap_sd_a3
    | exact decode_swap_sd_a2
    | exact decode_ret

end MetrologyAsm
