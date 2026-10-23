import MetrologyAsm.Examples.Swap.Source
import MetrologyAsm.Examples.Swap.Decode

/-! # The assembly source-to-Sail decoder connection -/

namespace MetrologyAsm

open ProbLang.Asm RiscvZkvm.Sail.Functions

/-- Interpret the load, store, and return instructions used by the exchange fragment. -/
def toSailAst (i : Instr) : Option instruction :=
  match i.mnemonic, i.operands with
  | "ld", [.reg rd, .mem (.int offset) rs] =>
    some (.LOAD (BitVec.ofInt 12 offset, .Regidx (BitVec.ofNat 5 rs.val),
      .Regidx (BitVec.ofNat 5 rd.val), false, 8))
  | "sd", [.reg rs2, .mem (.int offset) rs1] =>
    some (.STORE (BitVec.ofInt 12 offset, .Regidx (BitVec.ofNat 5 rs2.val),
      .Regidx (BitVec.ofNat 5 rs1.val), 8))
  | "jalr", [.reg rd, .mem (.int offset) rs] =>
    some (.JALR (BitVec.ofInt 12 offset, .Regidx (BitVec.ofNat 5 rs.val),
      .Regidx (BitVec.ofNat 5 rd.val)))
  | _, _ => none

/-- The actual assembled source matches every checked decoder word and instruction. -/
theorem swapAssembler_decoderCases :
    (assemble swapAsm).toOption.map
        (fun image => image.instructions.map (fun e => (e.word, toSailAst e.instruction))) =
      some (swapDecoderCases.map (fun e => (e.1, some e.2))) := by
  rfl

/-- The executable source bytes are exactly the checked decoder words in little-endian order. -/
theorem swapAssembler_textBytes :
    (assemble swapAsm).toOption.map (fun image => image.bytes.take image.textLen) =
      some (swapDecoderCases.flatMap (fun e => bytesOf 4 e.1.toNat)) := by
  rfl

/-- Every emitted exchange instruction decodes to its source instruction's Sail meaning. -/
theorem swapAssembler_decodes (image : Image) (himage : assemble swapAsm = .ok image)
    (e : EncodedInstr) (he : e ∈ image.instructions) :
    ∃ i, toSailAst e.instruction = some i ∧ ext_decode e.word = guardedDecode i := by
  have h := swapAssembler_decoderCases
  rw [himage] at h
  have hm : (e.word, toSailAst e.instruction) ∈
      swapDecoderCases.map (fun entry => (entry.1, some entry.2)) := by
    rw [← Option.some.inj h]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hm
  have hw : entry.1 = e.word := congrArg Prod.fst heq
  have hi : some entry.2 = toSailAst e.instruction := congrArg Prod.snd heq
  refine ⟨entry.2, hi.symm, ?_⟩
  rw [← hw]
  exact swapDecoderCases_correct entry hentry

end MetrologyAsm
