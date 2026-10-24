# Sail provenance

- Copied verbatim from `Verified-zkEVM/riscv-zkvm`, commit
  `6810fc14d9c40373101321cefaec59df8d82e3e7` (exact clone HEAD recorded below).
- Extraction manifest and configuration: `sail-import/PROVENANCE.toml` and
  `sail-import/rv64d_v256_e64.json` (upstream originals).
- Generated library: `RiscvZkvm/Sail.lean`, `RiscvZkvm/Sail/`.
- Runtime: upstream lean-sail `079463134b9c50450b8393e1566a09fc492a34d9`.
- This package builds with Lean 4.35.0; the upstream manifest records 4.33.1.
- Scope: RV64IM and selected Zicsr/Zicbo/K support; compressed, atomics, and
  floating-point instruction modules are absent.
- The original platform-hook/FP-axiom file is preserved in
  `sail-import/RiscvExtras.upstream.lean.txt`; installed hook realizations are listed below.
  Claimed results must pass `#print axioms` individually.

## Platform instantiation

`RiscvExtras.lean` is the upstream hand-owned hook file, not generated Sail code.
Its original is preserved in `sail-import/RiscvExtras.upstream.lean.txt`.
Local hook realizations reject terminal I/O, entropy, and load reservations with
Sail `Unreachable`; return false for reservation matching/validity and experimental
extensions; and make reservation cancellation a no-op. Unused FP hook declarations
are omitted, since no floating-point instruction modules were extracted. No generated
instruction or architectural semantics file is changed. This instantiation removes
upstream placeholder axioms without assigning fake results to unsupported effects.

## Lean 4.35 compatibility

The runtime is copied from the pinned upstream revision into `runtime/lean-sail`.
Its only source delta is the appended parser compatibility block in `Sail.lean`,
mirrored byte-for-byte in `sail-import/lean-4.35-assert-shim.lean.txt`:

- A non-reserved do-element parser maps legacy `assert condition message` to the
  existing runtime assertion. This disambiguates 466 calls from Lean 4.35's intrinsic assertion.
- A closed module/declaration/kind whitelist supplies the omitted binders of 82 pinned
  declarations, including `zero_extend`, generic helpers, and thin runtime aliases.
  Each entry records the original binder names, types, and order; the barrier alias
  retains its original `Sort u` universe. Unknown declarations use Lean's strict elaborator.
  There is no free-name discovery or automatic capture. `sail-import/strict-binders.json`
  mirrors the literal whitelist and binds it to the unchanged model digest.

All libraries in this package use `autoImplicit = false` and `relaxedAutoImplicit = false`,
including the generated model. `Tests.StrictBinders` checks the active options and readable
examples. Its dependency `Tests.StrictSourceEquivalence` contains 82 kernel-checked `rfl`
equalities against the original compiled declarations' fully printed types and bodies.
The hand-owned print hook receives its previously inferred `{n : Nat}` explicitly in both
installed and regeneration-source copies. Generated source and the pinned model digest
remain unchanged. The compatibility implementation adds a closed 82-row table and a small
command elaborator to the runtime root (124 added lines beyond the assertion shim,
including the 82 table rows). It prepends explicit binders while preserving existing
declaration modifiers, result types, and bodies.

The exact-module `RiscvZkvm.Sail.RvfiDii` library sets
`backward.do.legacy = true`; other generated modules keep the default elaborator. Lean 4.35's default
new do-elaborator spent over 17 minutes in the 18-print `print_rvfi_exec` function
without finishing. The unmodified full RvfiDii module elaborated in 4.96 seconds
with the legacy elaborator (typechecking 171 ms). This is a build compatibility
option; generated source remains byte-identical. Applying it to the whole model
is invalid: PhysMemInterface and Types use nested `← match` supported by the new
elaborator.
