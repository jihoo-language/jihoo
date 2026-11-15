# Rootless dependent-kernel verification

Verified on 2026-11-15, on Linux x86_64, at commit
`e0756b03a30cb2578af35eb63de077979825d700`.
The final documentation commit does not change the verified code.
`compiler/core.jh` SHA-256:
`32c8dc168e7270e2bbafe241142bb5c042c6970f9641ee2171bc277d6a94df89`.

## Environment

- Launcher: `/workspace/.local/bin/nix-rootless`, installed with the rootless
  Nix skill using nix-portable v012 and working bubblewrap user namespaces.
- Nix: 2.20.6. Both `--version` and
  `eval --expr 'builtins.add 20 22'` passed; the latter returned `42`.
- Private store: `/home/agent/.nix-portable`, exposed as `/nix` inside the
  portable runtime. The checks used this repository's actual `.#proofs` shell.
- Lean 4.34.1, Lake 5.0.0-src, LLVM/clang 21.1.8, bundled Jihoo seed 0.5.0.
  The seed built the current compiler, which reported `jihoo 0.6.0` and ran
  `examples/hello.jh`, producing `Hello, jihoo!`.
- `flake.lock` is unchanged. Both supported Linux architectures evaluated;
  compiler execution and proof checking ran on x86_64.

This container rejects Nix build-sandbox domain setup, so development-shell
creation used `--option sandbox false` for that invocation. User systemd and
delegated cgroups were unavailable. The proof guard serialized the entire
verification process tree, retained Lean's 4 GiB allocation limit, used one
Lean thread and one Jihoo code generation unit, and monitored aggregate RSS at
6 GiB. Its inherited 64 GiB virtual address-space allowance accommodates Lean
runtime reservations. RSS enforcement is sampled, not a cgroup hard cap.
The complete proof/compiler/correspondence run observed a sampled peak tree
RSS of **3623.4 MiB**.

## Results

All commands passed:

| Check | Result |
| --- | --- |
| Project development shell | Correct tool versions and checkout `JIHOO_PATH` |
| Container proof guard | 3 tests: inherited limit/nesting/exit status, aggregate RSS termination, detached-child cleanup |
| Nix source isolation | 12 mutations across x86_64-linux and aarch64-linux |
| `nix flake check --offline --no-build --all-systems` | All outputs evaluated; this command does not execute the flake's build/test derivations |
| `bash proofs/check.sh` through the guard | 865 Lake build jobs, 8,586 axiom-audit entries, 12 generated-fixture comparisons |
| Bounded `CheckNativeLoanProgram.lean` IO adapter | Elaborated with warnings as errors |
| Current compiler build and hello | Passed |

The aggregate audit found no dependencies outside `propext`, `Classical.choice`
and `Quot.sound`; in particular, no `sorryAx` was accepted. Every generated
fixture and finite-model generator matched its checked-in source.

The following tests used the freshly built `out/jihoo` and retained actual
native exporter bytes:

| Correspondence suite | Source fixtures | Exact-byte checks |
| --- | ---: | ---: |
| Sequential loan-aware globals | 16 | 17 |
| Single-declaration loan typing | 9 | 9 |
| Loan quantities | 12 | 13 |
| Unified native families/resources | 49 | 41 |
| Historical Raw kernel | 26 | 35 |
| Full native syntax kernel | 89 | 95 |
| **Total** | **201** | **210** |

Counts include overlapping cases across suites. Byte checks include retained
accepted-native snapshots, documented subset gaps and synthetic rejection
mutations. The full-native suite additionally matched all **54 constructors**,
**162 constructor/vector wire cases**, four binder cases, and **660 actual Core
binding transformations** against the Lean definitions.

Local logs are under `out/logs/`; sources, snapshot bytes, hashes, observed
outcomes and manifests are under `out/kernel-verification/`. These generated
artifacts are ignored by Git; this report records their aggregate results.

## Added guarantee and boundary

[NativeLoanGlobalInput.lean](Jihoo/NativeLoanGlobalInput.lean) connects exact
canonical version-6 bytes to the existing sequential loan-aware global checker.
Acceptance constructs the actual ordered checking history, graph meanings,
transparent well-formed environment and exact declaration count. The decoder's
aggregate bounds are retained. A general theorem rejects any appended byte;
kernel-checked examples additionally reject self/forward references, unbound
variables, missing roots, malformed unused nodes, family tables and exhausted
fuel. Five general theorems and eleven example theorems join the aggregate
axiom audit. The new IO adapter and native correspondence suite run in the
existing `graph-certificates` flake check.

This is a global typing interface with an empty family table. It does not
establish runtime quantity admission for those programs. The complete native
`compiler/core.jh` implementation has not been proved equivalent to the Lean
checker. General heap/loan execution safety, full operational soundness and
whole-compiler correctness remain open; see
[Native kernel scope](NATIVE_KERNEL_SCOPE.md) and
[Executable kernel scope](KERNEL_CHECKER_SCOPE.md).

## Reproduction

Enter the actual project shell from the checkout:

```sh
cd /workspace/jihoo
/workspace/.local/bin/nix-rootless --option sandbox false develop .#proofs
mkdir -p out
scripts/proof-limits.sh bash proofs/check.sh >out/lean-proofs.log 2>&1
scripts/proof-limits.sh bash -c 'cd proofs && lake env lean -M 4096 -j 1 -DwarningAsError=true CheckNativeLoanProgram.lean'
scripts/proof-limits.sh jihoo build -O2 compiler/main.jh -o out/jihoo
scripts/proof-limits.sh out/jihoo run examples/hello.jh
scripts/proof-limits.sh python3 tests/core_native_loan_program_correspondence.py --compiler "$PWD/out/jihoo" --output out/kernel-verification/loan-program
scripts/proof-limits.sh python3 tests/core_native_loan_typing_correspondence.py --compiler "$PWD/out/jihoo" --output out/kernel-verification/loan-typing
scripts/proof-limits.sh python3 tests/core_native_loan_quantity_correspondence.py --compiler "$PWD/out/jihoo" --output out/kernel-verification/loan-quantity
scripts/proof-limits.sh python3 tests/core_native_unified_correspondence.py --compiler "$PWD/out/jihoo" --output out/kernel-verification/unified
scripts/proof-limits.sh python3 tests/core_kernel_correspondence.py --compiler "$PWD/out/jihoo" --output out/kernel-verification/raw
scripts/proof-limits.sh python3 tests/core_native_kernel_correspondence.py --compiler "$PWD/out/jihoo" --output out/kernel-verification/native
```

The verification run reused the new suite's exporter for the other loan and
unified suites via their `--exporter` option. The commands above also work by
building each suite's exporter separately. From the ordinary host shell:

```sh
cd /workspace/jihoo
python3 tests/proof_limits.py -v
python3 scripts/check_nix_sources.py --nix /workspace/.local/bin/nix-rootless --offline
/workspace/.local/bin/nix-rootless flake check --offline --no-build --all-systems
```
