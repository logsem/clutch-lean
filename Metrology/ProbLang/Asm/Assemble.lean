module

public meta import Metrology.ProbLang.Asm.Assembler
public meta import Metrology.ProbLang.Asm.Parser

/-! # Assembly encoding command -/

open ProbLang.Asm

/-- Assemble a source file to raw image bytes, printing the section sizes and import slots. -/
public meta def main (args : List String) : IO Unit := do
  let [source, destination] := args | throw (IO.userError "usage: source.s destination.bin")
  match parse (← IO.FS.readFile source) >>= assemble with
  | .error e => throw (IO.userError e)
  | .ok image =>
    IO.FS.writeBinFile destination (ByteArray.mk image.bytes.toArray)
    IO.println s!"text={image.textLen} rodata={image.rodataOff} entry={image.entry}"
    IO.println s!"instructions={image.instructions.length} imports={repr image.importSlots}"
