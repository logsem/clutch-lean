#!/usr/bin/env python3
"""Quote the pinned compiler fragment into the OTP source module; run with python3 -I."""

import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
TARGET = HERE.parents[1] / 'MetrologyAsm/Examples/OTP/Source.lean'
HEADER = '''import Metrology.ProbLang.Asm.Notation
import Metrology.ProbLang.Asm.Assembler

/-! # The compiled one-byte one-time pad -/

namespace MetrologyAsm.OTP

open ProbLang.Asm

/-- The compiler's complete encryption function, retaining its GNU source verbatim. -/
def otpAsm : AsmProg := riscv_asm!
  "'''
TAIL = '''"

/-- Encrypt a byte message using a fresh byte written by the imported randombytes callback. -/
def otpSig : Sig := {
    args := [.uint 64, .array 8 (.const 1)]
    result := .uint 64
    stackBound := 32
    imports := [("randombytes", ⟨[.array 8 (.arg 1), .uint 64], .unit⟩)] }

/-- The first-class assembly code used by the OTP game. -/
def otpCode : Code := ⟨otpAsm, otpSig⟩

/-- The assembled text and relocated import-slot layout. -/
def otpImage : Image :=
  (assemble otpAsm).toOption.getD ⟨[], 0, 0, 0, [], [], []⟩

/-- The retained OTP source assembles successfully. -/
theorem assemble_otpImage : assemble otpAsm = .ok otpImage := by
  rfl

end MetrologyAsm.OTP
'''


def main() -> None:
    """Verify fixture provenance and write or compare its literal Lean quotation."""
    if sys.argv[1:] not in ([], ['--check']):
        raise SystemExit('usage: python3 -I fixtures/otp/generate.py [--check]')
    manifest = json.loads((HERE / 'provenance.json').read_text())
    for name, digest in manifest['files'].items():
        if hashlib.sha256((HERE / name).read_bytes()).hexdigest() != digest:
            raise SystemExit(f'OTP fixture hash mismatch: {name}')
    full = (HERE / 'otp.compiler.s').read_text()
    start = full.index('\t.globl\tencrypt_byte')
    end = full.index('\n', full.index('\t.size\tencrypt_byte', start))
    source = (HERE / 'otp.s').read_text()
    if source != '\t.text\n' + full[start:end] + '\n':
        raise SystemExit('OTP fragment differs from the retained compiler output')
    quoted = source.replace('\\', '\\\\').replace('"', '\\"').replace('\t', '\\t')
    generated = HEADER + quoted + TAIL
    if sys.argv[1:] == ['--check']:
        if TARGET.read_text() != generated:
            raise SystemExit('OTP Lean source differs; rerun fixtures/otp/generate.py')
        print('OTP hashes, compiler fragment and Lean quotation match')
    else:
        TARGET.write_text(generated)
        print('wrote MetrologyAsm/Examples/OTP/Source.lean')


if __name__ == '__main__':
    main()
