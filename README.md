# Metrology

## Assembly FFI examples

The Sail-backed assembly examples are part of this repository and its default Lake build.
[The module guide](MetrologyAsm/README.md) explains the directory layout and proof dependencies.

- [Swap assembly](MetrologyAsm/Examples/Swap/Source.lean) and
  [final Micrometer swap theorem](MetrologyAsm/Examples/Swap/Correctness.lean).
- [Callback assembly](MetrologyAsm/Examples/Callback/Source.lean) and
  [final Micrometer callback theorem](MetrologyAsm/Examples/Callback/Correctness.lean).
- [Linked keypair input and game skeleton](MetrologyAsm/Examples/Keypair/Source.lean), with
  [reproducible assembly fixtures](fixtures/keypair/README.md). Keypair correctness is unproved.
- [Evaluation report](docs/asm-ffi/REPORT.md) and [Sail provenance](docs/asm-ffi/PROVENANCE.md),
  with [statement dependency audits](docs/asm-ffi/TCB.md).

Run these commands from the repository root:

```sh
lake build
python3 -I scripts/check-sail-pin.py
python3 -I fixtures/keypair/generate.py --check
```

For just the verified assembly examples, use `lake build MetrologyAsm`. They use the pinned RV64IM
Lean extraction; the report documents the scope and known backend limitations.
