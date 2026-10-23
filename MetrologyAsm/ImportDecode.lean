import MetrologyAsm.ImportToy
import MetrologyAsm.DecodeChecks

/-! # Official Sail decoder certificates for the callback source -/

set_option maxRecDepth 100000

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions Sail.ConcurrencyInterfaceV1

/-- The ten actual instructions of the assembled callback fragment and trampoline. -/
def importToyCases : List (BitVec 32 × instruction) :=
  [(0xff010113#32, .ITYPE (0xff0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)),
    (0x00113423#32, .STORE (8#12, .Regidx 1#5, .Regidx 2#5, 8)),
    (0x00000097#32, .UTYPE (0#20, .Regidx 1#5, .AUIPC)),
    (0x014080e7#32, .JALR (20#12, .Regidx 1#5, .Regidx 1#5)),
    (0x00813083#32, .LOAD (8#12, .Regidx 2#5, .Regidx 1#5, false, 8)),
    (0x01010113#32, .ITYPE (16#12, .Regidx 2#5, .Regidx 2#5, .ADDI)),
    (0x00008067#32, .JALR (0#12, .Regidx 1#5, .Regidx 0#5)),
    (0x00000e17#32, .UTYPE (0#20, .Regidx 28#5, .AUIPC)),
    (0x00ce3e03#32, .LOAD (12#12, .Regidx 28#5, .Regidx 28#5, false, 8)),
    (0x000e0067#32, .JALR (0#12, .Regidx 28#5, .Regidx 0#5))]

/-- The actual assembler emits precisely the words certified against the official decoder. -/
theorem importToy_source_words :
    importToyImage.instructions.map (·.word) = importToyCases.map (·.1) := by
  decide +kernel

/-- The source's callback slot and executable interval have the intended concrete offsets. -/
theorem importToy_layout :
    (importToyImage.entry, importToyImage.textLen, importToyImage.bytes.length,
      importToyImage.importSlots) = (0, 40, 48, [("cb", 40)]) := by
  rfl

/-- The official decoder recognizes the callback fragment's reserve instruction. -/
theorem decode_importToy_reserve :
    ext_decode 0xff010113#32 =
      guardedDecode (.ITYPE (0xff0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
  unfold ext_decode encdec_backwards guardedDecode
  apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
  funext enabled
  cases enabled <;> rfl

/-- The official decoder recognizes the callback fragment's save instruction. -/
theorem decode_importToy_save :
    ext_decode 0x00113423#32 = guardedDecode (.STORE (8#12, .Regidx 1#5, .Regidx 2#5, 8)) := by
  unfold ext_decode encdec_backwards guardedDecode
  apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
  funext enabled
  cases enabled <;> rfl

/-- The official decoder recognizes the callback fragment's call upper instruction. -/
theorem decode_importToy_call_upper :
    ext_decode 0x00000097#32 = guardedDecode (.UTYPE (0#20, .Regidx 1#5, .AUIPC)) := by
  unfold ext_decode encdec_backwards guardedDecode
  apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
  funext enabled
  cases enabled <;> rfl

/-- The official decoder recognizes the callback fragment's call link instruction. -/
theorem decode_importToy_call_link :
    ext_decode 0x014080e7#32 = guardedDecode (.JALR (20#12, .Regidx 1#5, .Regidx 1#5)) := by
  unfold ext_decode encdec_backwards guardedDecode
  apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
  funext enabled
  cases enabled <;> rfl

/-- The official decoder recognizes the callback fragment's restore instruction. -/
theorem decode_importToy_restore :
    ext_decode 0x00813083#32 =
      guardedDecode (.LOAD (8#12, .Regidx 2#5, .Regidx 1#5, false, 8)) := by
  unfold ext_decode encdec_backwards guardedDecode
  apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
  funext enabled
  cases enabled <;> rfl

/-- The official decoder recognizes the callback fragment's release instruction. -/
theorem decode_importToy_release :
    ext_decode 0x01010113#32 = guardedDecode (.ITYPE (16#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
  unfold ext_decode encdec_backwards guardedDecode
  apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
  funext enabled
  cases enabled <;> rfl

/-- The official decoder recognizes the callback fragment's return instruction. -/
theorem decode_importToy_return :
    ext_decode 0x00008067#32 = guardedDecode (.JALR (0#12, .Regidx 1#5, .Regidx 0#5)) := by
  unfold ext_decode encdec_backwards guardedDecode
  apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
  funext enabled
  cases enabled <;> rfl

/-- The official decoder recognizes the callback fragment's stub upper instruction. -/
theorem decode_importToy_stub_upper :
    ext_decode 0x00000e17#32 = guardedDecode (.UTYPE (0#20, .Regidx 28#5, .AUIPC)) := by
  unfold ext_decode encdec_backwards guardedDecode
  apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
  funext enabled
  cases enabled <;> rfl

/-- The official decoder recognizes the callback fragment's stub load instruction. -/
theorem decode_importToy_stub_load :
    ext_decode 0x00ce3e03#32 =
      guardedDecode (.LOAD (12#12, .Regidx 28#5, .Regidx 28#5, false, 8)) := by
  unfold ext_decode encdec_backwards guardedDecode
  apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
  funext enabled
  cases enabled <;> rfl

/-- The official decoder recognizes the callback fragment's stub jump instruction. -/
theorem decode_importToy_stub_jump :
    ext_decode 0x000e0067#32 = guardedDecode (.JALR (0#12, .Regidx 28#5, .Regidx 0#5)) := by
  unfold ext_decode encdec_backwards guardedDecode
  apply congrArg (Bind.bind (currentlyEnabled extension.Ext_Zicfilp))
  funext enabled
  cases enabled <;> rfl

end MetrologyAsm
