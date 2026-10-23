# WS9 / M3: keypair obligations and measured proof frontier

The M3 shape theorem and its ProbLang uniformity theorem are **not proved**. The assembly extraction,
static libc-helper linkage, parser/elaborator tests, and a small actual-Sail MUL-body proof were run.
They establish an executable input and a measured proof frontier, rather than a crypto correctness claim.
This report records the measured assembly input and proof frontier on 2026-10-23.
The durable input is now in `fixtures/keypair/` and `MetrologyAsm/Examples/Keypair/Source.lean`.

## The statement that still needs a proof

Let `Byte = Fin 256`, `Bytes32 = Fin 32 → Byte`, and let `X` and `Y` be the 32-cell logical regions
starting at the secret and public pointers. The minimal shape result chooses `f : Bytes32 → Bytes32`
before quantifying the compatible placements, raw machines, and representable callback responses.
For one permitted logical input heap `h₀`, it must prove the actual machine specification for:

```
call "randombytes" [loc x, int 32] h₀
  (fun _ h₁ => ret (int 0) (h₁[Y := f (h₁|X)]))
```

The update preserves `h₁|X` and every logical cell outside `Y`. Invalid responses must have the
canonical invalid continuation required by `AsmSemantics.Canonical`. A reusable stronger version
chooses the same `f` before all permitted logical heaps and argument locations; merely choosing a
function separately for each physical run would not meet either placement-independent specification.

Required concrete obligations are:

1. Nonvacuous compatible entry states: assembled image and constants, ABI argument registers,
   16-byte aligned stack, enough nonwrapping RAM for code/data/stack, correct byte-array encoding,
   and frame separation. The reachable static call graph needs 2,080 stack bytes below entry SP,
   excluding execution of the external import. This bound comes from assembly frame sizes, not a
   proved stack-safety invariant.
2. Execution to the first stop is exactly one call of `randombytes(x, 32)`, before keypair writes the
   secret or public regions. The call-site saves `x` in `s0`, `y` in `s1`, and `ra` on the stack.
3. For **every** allowed resumed state and byte-valued callback heap, the remaining code terminates,
   reads no uninitialized or unowned memory, preserves the secret bytes, writes all 32 public bytes,
   returns signed 32-bit zero, restores callee-saved registers and stack, and preserves the physical
   frame. The public bytes must depend only on the resumed secret bytes, not placement, unrelated
   memory, caller-saved registers, or initial public bytes.
4. Actual imported-call/resume and `wp_asm_tree` rules must connect this interaction tree to the
   ProbLang program. The actual Sail one-callback toy now has a complete evaluator/shared-WP proof.
   That specialized result does not supply a reusable arbitrary-tree callback WP rule
   or the keypair-specific resumption and machine specification.
5. A ProbLang `randombytes` implementation must write 32 independent `rand #256` results
   (the bound is exclusive) through array offsets. Its owned-array invariant and induction must establish
   `Pr[X = b] = 256⁻³²` for each `b : Bytes32`, followed by `Y = f X`. Fresh `allocN` arrays provide
   the needed separation. `Metrology/Micrometer/Examples/RandomBytes.lean` supplies the callback,
   owned-array byte safety in the base kernel, and an exact single-byte uniform law.
   The 32-byte product-distribution theorem and its transport to the FFI kernel remain unproved.

**Statement change / missing precondition:** require `Disjoint X Y`. The boundary signature alone
accepts two identical array regions (`Region.compatible` permits identical representations).
If `x = y`, writing the public key overwrites the secret buffer, so the desired postcondition cannot
say the resumed secret bytes remain unchanged. Two fresh ProbLang allocations satisfy disjointness.
This is a substantive precondition, not an instruction-proof optimization.

The proposed signature remains `[array 8 (const 32), array 8 (const 32)] → int 32`, with the import
`randombytes : [array 8 (arg 1), uint 64] → unit`. Widths are bits; each logical element is one byte.
An optional functional theorem identifies `f` with a total Lean transcription of TweetNaCl's field
arithmetic. Equality with RFC 7748 X25519 is outside the requested prototype specification.

## Follow-up: executable ProbLang callback and array safety

The new root module `Metrology/Micrometer/Examples/RandomBytes.lean` implements the callback as
`randombytesValue : Val rT`, a closed lambda for direct `FfiEnv.impls` use. Its argument is exactly
`(ptr, (len, ()))`. For positive lengths it draws `rand(#256, #())`, stores through the current
pointer, advances it with `+ₗ #1`, and decrements the length. Nonpositive lengths return unit before
sampling or accessing memory. The exclusive bound 256 includes byte 255.

`wp_fill` and `wp_randombytes` transform an initialized owned n-cell array into ownership of n
byte-valued integer cells, preserving the caller's continuation/frame. `byte_draw` identifies the
actual primitive step with the uniform measure on `[0,256)`; `byte_draw_singleton` gives each byte
mass `1/256`. All six exported proof results have only the standard three Lean axioms.
`Metrology/Micrometer/Test/RandomBytes.lean` records 80 dual-interpreter array/frame checks at
lengths 0, 1, 4, and 32, plus three nonpositive-length empty-heap checks and axiom regression guards.

These WP rules use the **base** `wp = wpFor primStep`. Porting/transporting the ordinary sampling
and heap rules to `wpFor (primStepWith env)` is still required before using this proof inside an
actual FFI callback continuation. No such transport is assumed. Neither the 32-byte product law
nor a uniform keypair theorem follows from the single-draw and byte-range results alone; both
remain unproved. The M3 shape/curve and arbitrary-callback-tree obligations above remain open.

## Input, extraction, and static linkage

The surveyed C file is the 2014-04-27 TweetNaCl source. Its SHA-256 is
`02e65bc3013ff2168983365e55906bc783c4c7e0a60d8100f17bb303a17175c4`.
The exact surveyed `tweetnacl-Os.s` SHA-256 is
`326db09d4d8b768508f3fbd3ebc7bf5bc47e602f641d59aa57f42d9109f02dca`.
The header expands `crypto_box_keypair` to
`crypto_box_curve25519xsalsa20poly1305_tweet_keypair`.

A new data-only extraction retained the reachable assembly function bodies and `_9` / `_121665`
constants. The keypair entry calls the scalar-mult function directly; the separate nine-instruction
`crypto_scalarmult_*_base` wrapper is not reachable after this optimization.

| Reachable function | Source instructions | Frame bytes | Syntactic backedges |
|---|---:|---:|---:|
| `crypto_box_curve25519xsalsa20poly1305_tweet_keypair` | 20 | 32 | 0 |
| `crypto_scalarmult_curve25519_tweet` | 295 | 1552 | 15 |
| `M` | 63 | 304 | 3 |
| `car25519` | 32 | 0 | 1 |
| `inv25519` | 42 | 192 | 1 |
| `pack25519` | 88 | 288 | 4 |
| linked musl `memcpy` | 240 | 0 | 5 |
| linked musl `memset` | 67 | 0 | 1 |
| Total | 847 | maximum live sum 2080 | 30 |

The two musl C files were individually compiled with the installed Zig 0.13.0 / LLVM 18.1.6 toolchain:

```
zig cc -target riscv64-linux-musl -mcpu=baseline_rv64-c -mno-relax \
  -fPIC -g0 -fno-asynchronous-unwind-tables -fno-stack-protector \
  -fno-builtin -Os -S memcpy.c -o memcpy-Os.s
```

The analogous memset command was also run. Neither output calls itself or another libc function.
Compilation took 0.09s and 0.05s respectively. No downloaded build system or script was run.
Local `.L...` labels were consistently alpha-renamed per libc file to prevent cross-file collisions;
function instructions were otherwise retained. Functions were aligned to four bytes and the two
read-only objects to eight bytes. The only remaining external symbol is `randombytes`.

## Checks that completed

All artifacts and logs are under `/home/agent/asm-ffi-ws9-ws11`.

| Check | Result | Measured wall time |
|---|---|---:|
| Data-only call graph/frame/backedge extraction | eight functions, one import | 0.06s |
| LLVM assembly of linked closure | exit 0, `keypair.o` produced | 0.03s |
| Lean parser + assembler | exit 0, 882 emitted instructions | 3.11s |
| Actual `riscv_asm!` quotation and kernel elaboration | exit 0 | 4.51s |
| Actual generated Sail MUL body control proof | exit 0; standard three axioms | 3.11s process wall |

The Lean image has 3,528 text bytes, read-only data at 3,528, entry offset zero, and a single
`randombytes` address slot at 3,688. There are 160 constant bytes and 30 emitted base mnemonics.
The image SHA-256 is `34f006b0b944ab3dbc653df2654252ac67ac44cc6e1d65c3f8278e3298e70385`;
the extracted assembly SHA-256 is
`747626b938c4a387551c517ca8ba7a531927b1ac3293ef220aab20b12d3e527c`.
LLVM accepting the source is not an all-byte comparison with Lean: external call stubs and large
literal expansions need an explicit linked-image comparison before making that stronger claim.

The MUL-body benchmark unfolds the **actual** `execute_MUL` and proves that successful register reads
and its exact generated arithmetic/write operation give retirement success. It leaves
`mult_to_bits_half` explicit. Its theorem elaboration took 5.75ms and kernel type checking 5.19ms;
`#print axioms` returned only `propext`, `Classical.choice`, and `Quot.sound`.
It is a leaf-control result, not a field-multiplication or full fetch/decode/execute theorem.
A separate simple-`simp` arithmetic attempt reduced low multiplication to
`extractLsb' 0 64 (BitVec.ofInt 129 (a.toInt * b.toInt)) = a * b` and did not close it.
That diagnostic file failed elaboration and is **not** a claimed theorem. It identifies a needed
truncation/modular-arithmetic lemma, not evidence that this one lemma is intrinsically expensive.

## Why a shape theorem still needs a substantial proof

The final prototype has full Sail try_step proofs for the exchange's LD/SD/JALR forms and
reusable ADDI/AUIPC/JALR/stack-slot rules used by the actual callback toy. The universal one-call
tree/evaluator/shared-WP chain is complete for that empty-footprint toy. The generated Sail model contains definitions for the remaining emitted mnemonic families;
what is missing is their reusable end-to-end proof interface, plus byte/word data access rules,
stack and internal-call composition, and loop invariants. Parsing all those instructions does not
supply those proofs. The 2,080-byte stack footprint and array initialization are also semantic proof
obligations, not consequences of the static scanner.

The source ladder executes 255 iterations with ten `M` calls per iteration. Inversion adds 254
squares and 252 other multiplications, and the post-inversion multiply adds one: 3,057 `M` calls,
or 782,592 limb products. The inner assembly `M` loop spans eight instructions. Thus this loop alone
accounts for 6,260,736 machine instruction executions if naively unrolled. These are source/assembly
counts, not a certified dynamic instruction counter.

Useful invariants are concrete: ladder counter decreases from 254; sixteen-limb loops stay in their
allocated stack arrays; the 16×16 accumulation accesses only 31 limbs; carry loops stay in 16 limbs;
inversion decreases from 253 with its two fixed skipped multiplies; packing writes exactly 32 bytes.
`memcpy` and `memset` additionally require functional contracts for every alignment branch, since
placement changes those branches. Even an existential `f` must exclude layout- or frame-dependent
output; a per-placement choice of `f` would evade the goal.

A purely illustrative unrolling projection at the measured roughly 11ms MUL-body elaboration plus
kernel checking per execution would exceed nineteen CPU hours for the inner loop alone, before full
Sail fetch/decode, other instructions, memory, or proof-term growth. This is **not** a runtime benchmark
or a reliable total proof-time estimate. It explains why bounded-loop and procedure contracts are
needed instead of a multi-million-step proof term. A planning estimate is multiple developer-weeks
for that reusable layer and this example; elapsed human effort cannot be inferred from the leaf timing.

No keypair loop invariant, field-operation contract, keypair callback WP proof, or M3 correctness
theorem is claimed complete here. The extracted fragment and measurements make those remaining
obligations specific and reproducible.

The required upstream alternative was evaluated in [REPORT-SAIL-EQUIV.md](REPORT-SAIL-EQUIV.md).
Its 51 instruction equivalences and bounded-loop logic are useful proof material, but its run theorem
uses a supplied decoded instruction stream and a Machine-mode invariant. It does not provide the
missing actual `try_step` simulation for this User-mode boundary.

## Reproduction artifacts

The committed input is in `fixtures/keypair/`: linked GNU source, separately compiled helper
assembly, source hashes/compiler arguments in `provenance.json`, original static `metrics.json`,
and the complete available notices. `generate.py` preserves the source characters in the multiline
`riscv_asm!` quotation in `MetrologyAsm/Examples/Keypair/Source.lean`. The module declares the signature, measured
stack bound and planned two-`allocN` game; it supplies no RVSpec or game proof.

From the Metrology repository root:

```
python3 -I fixtures/keypair/generate.py --check
lake build MetrologyAsm.Examples.Keypair.Source
lake env lean Tests/Keypair.lean
```

The last command checks the expected image metadata using compiler evaluation. It is a diagnostic,
not kernel evidence of assembly or execution correctness. An attempted full closed-image kernel
reduction exceeded a 180-second experiment cap, so no such theorem is retained. The cheap declared
stack-bound equality is proved by `rfl`; it does not certify stack safety. Large lines inside the
quotation retain the original GNU source data verbatim.

The original scratch run remains under `/home/agent/asm-ffi-ws9-ws11`: `keypair/assess-keypair.py`,
`keypair/keypair.bin`, `keypair/keypair.o`, `keypair/KeypairParseFixture.lean`,
`keypair/KeypairMulBodyBench.lean`, assessment/assembly/quotation/MUL-body logs, and explicitly
failing arithmetic-attempt logs. These measurements are distinct from the committed executable
metadata regression. Run Python readers with `python3 -I`. No notes or generated architectural
source was changed.
