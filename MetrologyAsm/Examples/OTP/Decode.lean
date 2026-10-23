import MetrologyAsm.Examples.OTP.Source
import MetrologyAsm.Sail.Decode

/-! # Official Sail decoder certificates for the compiled OTP source -/

namespace MetrologyAsm.OTP

open RiscvZkvm.Sail.Functions Sail.ConcurrencyInterfaceV1

/-- The compiler fragment and import trampoline expanded into twenty checked instructions. -/
def otpCases : List (BitVec 32 × instruction) :=
  [(0xfe010113#32, .ITYPE (0xfe0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)),
    (0x00113c23#32, .STORE (24#12, .Regidx 1#5, .Regidx 2#5, 8)),
    (0x00813823#32, .STORE (16#12, .Regidx 8#5, .Regidx 2#5, 8)),
    (0x00913423#32, .STORE (8#12, .Regidx 9#5, .Regidx 2#5, 8)),
    (0x00058413#32, .ITYPE (0#12, .Regidx 11#5, .Regidx 8#5, .ADDI)),
    (0x00050493#32, .ITYPE (0#12, .Regidx 10#5, .Regidx 9#5, .ADDI)),
    (0x00100593#32, .ITYPE (1#12, .Regidx 0#5, .Regidx 11#5, .ADDI)),
    (0x00040513#32, .ITYPE (0#12, .Regidx 8#5, .Regidx 10#5, .ADDI)),
    (0x00000097#32, .UTYPE (0#20, .Regidx 1#5, .AUIPC)),
    (0x024080e7#32, .JALR (36#12, .Regidx 1#5, .Regidx 1#5)),
    (0x00044503#32, .LOAD (0#12, .Regidx 8#5, .Regidx 10#5, true, 1)),
    (0x00954533#32, .RTYPE (.Regidx 9#5, .Regidx 10#5, .Regidx 10#5, .XOR)),
    (0x01813083#32, .LOAD (24#12, .Regidx 2#5, .Regidx 1#5, false, 8)),
    (0x01013403#32, .LOAD (16#12, .Regidx 2#5, .Regidx 8#5, false, 8)),
    (0x00813483#32, .LOAD (8#12, .Regidx 2#5, .Regidx 9#5, false, 8)),
    (0x02010113#32, .ITYPE (32#12, .Regidx 2#5, .Regidx 2#5, .ADDI)),
    (0x00008067#32, .JALR (0#12, .Regidx 1#5, .Regidx 0#5)),
    (0x00000e17#32, .UTYPE (0#20, .Regidx 28#5, .AUIPC)),
    (0x00ce3e03#32, .LOAD (12#12, .Regidx 28#5, .Regidx 28#5, false, 8)),
    (0x000e0067#32, .JALR (0#12, .Regidx 28#5, .Regidx 0#5))]

/-- The actual source assembler emits exactly the words certified against Sail. -/
theorem otp_source_words : otpImage.instructions.map (·.word) = otpCases.map (·.1) := by
  decide +kernel

/-- The OTP image has eighty text bytes and one aligned randombytes address slot. -/
theorem otp_layout :
    (otpImage.entry, otpImage.textLen, otpImage.rodataOff, otpImage.bytes.length,
      otpImage.importSlots) = (0, 80, 80, 88, [("randombytes", 80)]) := by
  rfl

/-- Each emitted OTP instruction has its exact official Sail decoding equation. -/
theorem otp_decoder_correct (entry : BitVec 32 × instruction) (h : entry ∈ otpCases) :
    ext_decode entry.1 = guardedDecode entry.2 := by
  simp only [otpCases, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold ext_decode encdec_backwards guardedDecode
    apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
    funext enabled
    cases enabled <;> rfl

end MetrologyAsm.OTP
