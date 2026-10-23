#!/usr/bin/env python3
"""Quote the committed GNU fixture into Keypair.lean; run with python3 -I."""

import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TARGET = ROOT / "MetrologyAsm/Keypair.lean"

HEADER = '''import Metrology.ProbLang.Asm.Notation
import Metrology.ProbLang.Asm.Assembler
import Metrology.ProbLang.Syntax.Notation

/-! # The statically linked TweetNaCl keypair input

The declared 2080-byte stack bound is a static measurement with no stack-safety or RVSpec proof. -/

-- Generated from fixtures/keypair/keypair-linked.s by fixtures/keypair/generate.py.
-- The retained GNU quotation exceeds the default recursion depth.
set_option maxRecDepth 100000

namespace MetrologyAsm

open ProbLang ProbLang.Asm

/-- The retained keypair closure with memcpy and memset linked as assembly functions. -/
def keypairAsm : AsmProg := riscv_asm!
  "'''

TAIL = '''

/-- The byte-array interface with a measured, unproved 2080-byte stack contract. -/
def keypairSig : Sig := {
    args := [.array 8 (.const 32), .array 8 (.const 32)]
    result := .int 32
    stackBound := 2080
    imports := [("randombytes", ⟨[.array 8 (.arg 1), .uint 64], .unit⟩)] }

/-- The first-class linked keypair code with its declared public/secret argument order. -/
def keypairCode : Code := ⟨keypairAsm, keypairSig⟩

/-- The assembler output of the retained linked source. -/
def keypairImage : Image :=
  (assemble keypairAsm).toOption.getD ⟨[], 0, 0, 0, [], [], []⟩

/-- The closed assembly check records successful layout and its sole external import slot. -/
def keypairAssemblyCheck : Bool :=
  match assemble keypairAsm with
  | .error _ => false
  | .ok image =>
    image.instructions.length == 882 && image.textLen == 3528 &&
      image.rodataOff == 3528 && image.entry == 0 &&
      image.importSlots == [("randombytes", 3688)] && image.bytes.length == 3696

/-- The declared keypair signature reserves the measured stack extent. -/
theorem keypair_stackBound : keypairCode.sig.stackBound = 2080 := rfl

/-- Allocate separate public/secret arrays, call the declared keypair, and return their pointers. -/
def keypairGame {rT : Type} : Exp rT := pl%
  let sk := allocN(#32, #0);
  let pk := allocN(#32, #0);
  asm(#(.code keypairCode), (pk, (sk, #())));
  (sk, pk)

end MetrologyAsm
'''


def generated_module() -> str:
    """Preserve source characters while keeping one GNU source line per Lean physical line."""
    source = (HERE / "keypair-linked.s").read_text()
    escaped = source.replace("\\", "\\\\").replace('"', '\\"').replace("\t", "\\t")
    return HEADER + escaped + '"' + TAIL


def main() -> None:
    """Check pinned fixture inputs and write or compare the single generated Lean module."""
    if sys.argv[1:] not in ([], ["--check"]):
        raise SystemExit("usage: python3 -I fixtures/keypair/generate.py [--check]")
    manifest = json.loads((HERE / "provenance.json").read_text())
    for name, expected in manifest["files"].items():
        data = (HERE / name).read_bytes()
        if len(data) != expected["bytes"] or hashlib.sha256(data).hexdigest() != expected["sha256"]:
            raise SystemExit(f"fixture provenance mismatch: {name}")
    text = generated_module()
    if sys.argv[1:] == ["--check"]:
        if TARGET.read_text() != text:
            raise SystemExit("Keypair.lean differs; rerun fixtures/keypair/generate.py")
        print("keypair fixture hashes and generated quotation match")
    else:
        TARGET.write_text(text)
        print("wrote MetrologyAsm/Keypair.lean from the committed linked source")


if __name__ == "__main__":
    main()
