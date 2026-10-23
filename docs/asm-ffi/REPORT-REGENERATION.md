# WS11: actual user-space Sail regeneration and strict compilation

The pinned Sail compiler was run successfully. After the existing audited normalization, the
candidate is **byte-identical** to the installed 121-file extraction. Its supported 85-module root
import closure compiles with both implicit-binder options false on Lean 4.35.0. A stronger scan of
all 121 files found 22 dormant-module failures, detailed below. No generated model, runtime, shim
whitelist, or existing source was changed during this experiment.

The pinned compiler also retains the known effectful Boolean short-circuit defect. Reproduction
does not repair or discharge that backend issue. The exact-model Lean proofs and byte-identity
result must not be read as a compiler-correctness theorem.

## Pins and tool acquisition

The following values were checked against `sail-import/PROVENANCE.toml` and the downloaded tools:

| Input | Exact pin |
|---|---|
| Sail-riscv | tag `0.13.1`, revision `27224ccb2290f022e46213c05b3e72e8a9ea635e` |
| Sail | version `0.20.3`, revision `60695b1ea377048f0adc39c62671cd099b2ed9f6` |
| lean-sail runtime | `079463134b9c50450b8393e1566a09fc492a34d9` |
| Runtime upstream Lean / local Lean | 4.33.1 / 4.35.0 |
| Config | `rv64d_v256_e64.json` |
| Config SHA-256 | `a3b545eb174247f5552a27dbb60f32c4ee95af85bdc8ea92ce0661254fbff674` |
| Normalized model digest | `559bb257093328400e5b47722b0bb8dd004396a8b8c45e32ecaefaa79256d992` |

The modules are `main I_insts M_insts Zicsr_insts K_core Zkr Zicboz Zicbom_insts`.
The official [Sail 0.20.3 binary release](https://github.com/rems-project/sail/releases/tag/0.20.3-binary)
provided `sail-Linux-aarch64.tar.gz` (39,735,802 bytes). Its SHA-256 was verified against the release
API asset digest **before extraction**:
`bdb1d68ca6b3a9eb74c409e42e54f71e77418debe3376dabdaabf3b6cd2bcf2d`.
Download wall time was 1.42s. Archive entries were checked for absolute/parent-traversal paths and
extracted with Python's data filter into an isolated scratch directory. No installer was run.

The compiler's `--version` reports the pinned revision. Its executable SHA-256 is
`28f529fc9d738c1659ee4681cf06d9d55f11dcb4d03b5e1cb7e3f2624b375bd3`.
Bundled Z3 reports 4.13.0, build `3049f578a8f98a0b0992eca193afe57a73b30ca3`; its SHA-256 is
`2c4f9116fefa860dc52d5542a3bbf8ef91f2cbc7f117c84fb2d492b80d7c26d9`.
The Sail-riscv tag was cloned into scratch and checked against its full revision. It remained clean.

## Command actually run

Working directory was the pinned Sail-riscv `model` directory. `SAIL` below denotes the verified
binary's absolute path; `OUT`, `CACHE`, and `CONFIG` denote isolated candidate output, memo cache,
and the repository's pinned JSON. This is the actual compiler argument list:

```sh
"$SAIL" --strict-var --strict-bitvector --strict-exponentials \
  --require-version 0.20.3 --memo-z3 --memo-z3-path "$CACHE" \
  --lean --lean-output-dir "$OUT" --lean-force-output \
  --lean-non-beq-type instruction --lean-non-beq-type ExecutionResult \
  --lean-non-beq-type Step --lean-noncomputable \
  --lean-noncomputable-function encdec_forwards \
  --lean-noncomputable-function encdec_backwards \
  --lean-noncomputable-function encdec_forwards_matches \
  --lean-noncomputable-function encdec_backwards_matches \
  --lean-noncomputable-function encdec_compressed_forwards \
  --lean-noncomputable-function encdec_compressed_backwards \
  --lean-noncomputable-function encdec_compressed_forwards_matches \
  --lean-noncomputable-function encdec_compressed_backwards_matches \
  --lean-import-file ../handwritten_support/RiscvExtras.lean \
  -o Out --variable 'TERMINATION_FILE = true' --config "$CONFIG" \
  riscv.sail_project main I_insts M_insts Zicsr_insts K_core Zkr Zicboz Zicbom_insts
```

The process was wrapped in `/usr/bin/time -v timeout 1200 nice -n 10`, with a PATH containing
the verified compiler/Z3 directory and system binaries. Downloaded code was treated as compiler
input. No downloaded script, Makefile, CMake configuration, opam package, or Lake build was run.

Generation exited zero: **5:56.03 wall, 174.33s user, 193.13s system, 496,248 KiB peak RSS**.
It emitted 120 Lean files. Two incomplete-pattern warnings concerned omitted extension cases;
the exact warnings are retained in `logs/regeneration.log`.

## Normalization and byte comparison

The raw `Out` package was copied/renamed into a separate candidate tree. Only the existing audited
hand-owned `scripts/normalize-extraction.py` was invoked (`python3 -I`, 0.17s), with the installed
hand-owned RuntimeCompat and RiscvExtras supplied to that candidate. The normalizer SHA-256 is
`1b6e2d55275d692a41ab7d599205deacaa699541229be84b85ea057ea92df5a2`;
RuntimeCompat's is `516a19a64db92494c8260ef2c43126989e77329e39bc99a3da86c10465b1bdbc`.

`diff -qr` against the installed `RiscvZkvm` tree exited zero with empty output. The candidate's
121-file manifest, using the preserved upstream Extras override required by the existing digest
procedure, matches the pinned model digest above. Both worktree and parent pin checks pass.
Candidate normalization occurred entirely in scratch; the installed extraction was never replaced.

## Strict candidate checks

Individual Lean commands were invoked directly in import order, with concurrency two and separate
candidate output/cache directories. There were no build-output symlinks. The compile command was:

```sh
lean --tstack=400000 -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -o <isolated-output>/<module>.olean <module>.lean
```

The one exact RvfiDii module also received its existing `-Dbackward.do.legacy=true` compatibility
option. This changes neither implicit-binder setting nor generated source.

| Check | Actual result | Wall / peak RSS |
|---|---|---|
| Initial stronger all-file attempt | stopped at dormant DecBits unknown `k_n` | 57.48s / 1,673,304 KiB |
| Supported root import closure | all 85 modules strict-compiled; 13 fresh outputs reused from previous attempt, 72 further modules | additional 2:53.59 / 1,419,096 KiB |
| `Tests/StrictSourceEquivalence.lean` against candidate | exit 0; existing original-type/body equality certificates | 2.61s / 1,231,408 KiB |
| `Tests/SailSpike.lean` against candidate | exit 0; initializer, ADDI, swap and return guards; execution aliases have standard-three axiom closures | 4.41s / 1,289,556 KiB |
| Remaining 36 dormant files, direct strict inventory | 14 compile, 22 fail | 36.65s process wall / 1,224,444 KiB |

The inventory script itself exits zero when it has collected every status. That does **not** mean
the stronger all121 compilation passed. The 36-file scan used isolated original-signature
dependencies to expose each file's own errors rather than cascading missing-import failures.
The separately compiled 85-module supported closure used strict dependencies throughout.

## Complete stronger-gate failure inventory

Twenty-one dormant files contain 47 additional declarations with omitted width/type binders;
DeviceTree has a separate reserved-word parse incompatibility. The exact declaration list and
source lines are below. These are outside the actual default/root closure. Per task direction,
no broad shim or generated-source repair was made for dormant extensions.

For the 47 declarations, original signatures were captured in an isolated diagnostic environment
with command-line `autoImplicit=true` and `relaxedAutoImplicit=true`; no repository option changed.
Those captures are evidence for any future exact closed-whitelist repair, not claimed strict tests.
The original auto-implicit mode still fails DeviceTree.

`RiscvZkvm/Sail/DeviceTree.lean:288` names a binder `prefix`, which Lean 4.35 parses as a reserved
token. Errors at lines 292, 368, 371, and 374 cascade from the absent `generate_cbo_block_size`.
This is a parser incompatibility, so merely adding omitted-binder whitelist rows cannot fix it.

| Dormant source file | Exact omitted-binder declarations and lines |
|---|---|
| `ArithInternal.lean` | `float_is_lt_internal:202` (k_n); `float_is_eq_internal:216` (k_n); `float_is_ne_internal:221` (k_n); `float_is_le_internal:225` (k_n); `float_is_gt_internal:229` (k_n); `float_is_ge_internal:233` (k_n); `float_propagate_nan:237` (k_n); `float_rounding_increment:253` (k_n); `float_compose_after_round:272` (k_n); `float_get_sign_with_all_ones_exp:307` (k_n); `float_round_and_compose:316` (k_n); `float_add_same_exp_internal:342` (k_n); `float_add_same_exp:370` (k_n); `float_add_less_than_exp:390` (k_n); `float_add_diff_exp:410` (k_n); `float_add_internal:423` (k_n); `float_sub_internal:432` (k_n) |
| `Classify.lean` | `float_classify:233` (k_ex481015_) |
| `DecBits.lean` | `dec_bits_forwards:202` (k_n); `dec_bits_forwards_matches:206` (k_n) |
| `Eq.lean` | `float_is_eq:200` (k_n) |
| `Ge.lean` | `float_is_ge:200` (k_n) |
| `GeQuiet.lean` | `float_is_ge_quiet:200` (k_n) |
| `Gt.lean` | `float_is_gt:200` (k_n) |
| `GtQuiet.lean` | `float_is_gt_quiet:200` (k_n) |
| `Inf.lean` | `float_is_inf:198` (k_ex480923_) |
| `Le.lean` | `float_is_le:200` (k_n) |
| `LeQuiet.lean` | `float_is_le_quiet:200` (k_n) |
| `Lt.lean` | `float_is_lt:200` (k_n) |
| `LtQuiet.lean` | `float_is_lt_quiet:200` (k_n) |
| `Nan.lean` | `float_is_nan:198` (k_ex480917_); `float_is_snan:203` (k_ex480919_); `float_is_qnan:208` (k_ex480921_) |
| `Ne.lean` | `float_is_ne:200` (k_n) |
| `Normal.lean` | `float_is_normal:198` (k_ex480931_); `float_is_subnormal:203` (k_ex480933_) |
| `Option.lean` | `is_none:202` (k_a); `is_some:208` (k_a) |
| `Result.lean` | `is_ok:202` (k_a, k_b); `is_err:208` (k_a, k_b); `ok_option:214` (k_a, k_b); `err_option:220` (k_a, k_b); `unwrap_or:226` (k_a, k_b) |
| `Sign.lean` | `float_is_positive:198` (k_ex480925_); `float_is_negative:202` (k_ex480927_) |
| `String.lean` | `concat_str_bits:202` (k_n) |
| `Zero.lean` | `float_is_zero:198` (k_ex480929_) |

## Known effectful short-circuit defect remains

The pinned backend source was inspected read-only. It lacks `short_circuit_to_if`.
[Upstream fix commit 3c03fced](https://github.com/zeldovich/sail/commit/3c03fced20edb79f9c0d9fd4cfa16862f58f0464)
adds precisely that rewrite for effectful Boolean `&` / `|` right operands. The commit and patch
were downloaded as data; no compiler source build or patch was run.

A tiny user-written Sail probe exposed the backend's `false && (← side ())` and
`true || (← side ())` output forms. That probe also produced an unrelated malformed helper,
so its entire generated module is **not** claimed to compile. An independent Lean 4.35 StateM
test of those exact Boolean forms returns `(false, 1)` and `(true, 1)`: the RHS effect executes.
This confirms the relevant target-language eager-effect behavior; it is not a claim that a specific
reachable RISC-V instruction path was proved incorrect. The known compiler fix remains unapplied.

WS11 therefore establishes reproducible byte identity and supported strict compilation, while
recording both dormant-module compatibility limits and this unresolved backend correctness issue.
Any future compiler-fix regeneration must produce a new candidate, diff, pin, and proof review.

## Retained artifacts

All scratch artifacts are under `/home/agent/asm-ffi-ws9-ws11`:

- `downloads/`: verified release archive/binaries, pinned Sail-riscv tree, primary-source metadata.
- `candidate/`, `candidate-normalized/`, `candidate-build/`: raw output, compared output, fresh oleans.
- `logs/regeneration.log`, `candidate-manifest.sha256`, `candidate-diff.txt`.
- `logs/candidate-root-build.{log,json}`, `candidate-strict-equivalence.log`, `candidate-swap-smoke.log`.
- `logs/strict-inventory.json`, `missing-binder-declarations.json`, per-module strict diagnostics,
  and `original-signatures.log` for all 47 affected declarations.
- `short-circuit/` and `logs/short-circuit-lean.log`: user-written semantic probes.

The companion [keypair report](REPORT-KEYPAIR.md) makes no M3 correctness claim;
[the upstream simulation audit](REPORT-SAIL-EQUIV.md) records the required WS6 evaluation.
No notes, generated model, runtime, or existing proof file is part of this report change.
