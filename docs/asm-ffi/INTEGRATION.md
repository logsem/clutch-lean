# Integration into Metrology

The assembly FFI prototype is part of the Metrology repository on branch `risc`.
It was imported from sibling commit `042e17d`; the original sibling checkout is no longer required.
All 182 imported Lean source files are byte-identical to that checkpoint. The theorem statements,
proof bodies, generated architecture, runtime compatibility shim and strict binder checks are preserved.

Repository layout:

- `MetrologyAsm/` and `MetrologyAsm.lean`: Sail adapter, ABI, plain specs and final example proofs.
- `RiscvZkvm/Sail/`: pinned generated architecture and explicitly owned platform hooks.
- `runtime/lean-sail/`: pinned local runtime, including the documented compatibility suffix.
- `sail-import/`: source/config/runtime hashes and strict binder metadata.
- `Tests/`: Sail observations, source-equivalence checks and executable keypair metadata check.
- `fixtures/keypair/`: linked assembly, helpers, notices and reproducible quotation generator.
- `docs/asm-ffi/`: evaluation, keypair frontier, regeneration and provenance reports.

Run from the Metrology root:

```sh
lake build
python3 -I scripts/check-sail-pin.py
python3 -I fixtures/keypair/generate.py --check
```

The default build includes the existing Metrology/widget targets, `MetrologyAsm`, and the Sail,
strict-binder and keypair regression targets. `lake build MetrologyAsm` builds only the assembly
library and its dependencies. Lean clients use `import MetrologyAsm`, or import individual examples.
No path dependency points outside this repository, and the existing git dependency pins are unchanged.
Both `autoImplicit` and `relaxedAutoImplicit` remain false. The legacy do option remains restricted to
`RiscvZkvm.Sail.RvfiDii`. Only the imported libraries use the prototype's larger Lean stack limit.

The evaluation reports retain historical sibling branch/checkpoint and build measurements.
They describe the same proof sources; current source paths are relative to the Metrology root.
The runtime's dependency-free Lake manifest is generated locally to make fresh root updates clean;
it does not modify upstream runtime source. Architectural and runtime pin checks continue to pass.

Validation in the integrated repository:

- Complete root `lake build`: **7126 jobs passed**; receipt in `audit/BUILD.txt`.
- Source/config/runtime pin checker and fixture quotation/hash check: passed.
- Existing git dependency manifest entries unchanged; module search path has no sibling checkout.
- All imported Lean files byte-identical to the completed sibling source/proof checkpoint.
- Seven top theorem axiom checks and complete statement-dependency receipts are in `audit/`.
- The only build warnings are the existing unrelated RandomWalk admission and preserved upstream
  Sail ambiguous-open warning. Neither affects the final example theorem axiom closures.
- Whitespace findings in imported generated files and the original authorship notice are preserved
  verbatim. Integration-owned config/docs/scripts are whitespace-clean.
