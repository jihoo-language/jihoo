# Active whole-kernel verification work

The user's active goal is to continue implementing and checking proofs until
the entire Jihoo dependent-type kernel is formally verified, committing and
pushing intermediate results. **The goal is not complete.** Passing fixture or
theorem counts are not a completion percentage.

## Completion obligations

Retain the original specified-rule goal in `docs/internals/roadmap.md` and
`docs/internals/0.6-proof-status.md`: general logical consistency (including no
closed `Lt(0,0)` evidence), type preservation for the specified pure model, and
runtime quantity/borrow soundness from the same complete typing judgment.
Track the stronger native implementation-refinement obligation recorded in
`NATIVE_KERNEL_SCOPE.md` separately and explicitly; a Lean port, interface audit
or finite correspondence suite does not establish native implementation
correctness. Do not silently weaken either claim or remove constructors to
declare completion.

The remaining core obligations include:

1. A general universe-aware interpretation/consistency theorem reconstructed
   from actual typing, without callers supplying arbitrary interpretation
   candidates or output-realization certificates.
2. Preservation for the remaining specified computation and representation
   rules. Raw Lend macro intermediates and arbitrary CODE beta substitution
   must not be confused with the proved safe source evaluation relation.
3. A full typing-to-runtime ownership/borrow theorem: derive heap operation
   preconditions and exact resource accounting from accepted source typing and
   quantities, across arbitrary dependent functions, closures, families,
   recursion and nested readers. A guarded heap invariant alone is insufficient.
4. Native implementation refinement where the stronger full-native claim is
   made, including actual graph operations, comparison/normalization, inference
   and mixed declaration checking. LLVM/backend verification is a separate task.

## Current concrete progress

- `NativeLoanMixedProgram` checks declarations and inductive families in the
  actual earlier prefix, using Loan64 typing and that checker's own recursive
  resource projection. `NativeLoanMixedAdmission` binds the history to exact
  canonical version-6 graph bytes. It retains independent scope/shape checks.
- `NativeScopedProgramHistory` extracts the closed transparent global store
  and authentic checked family telescopes from both the earlier and Loan64
  mixed histories.
- Loan family metadata and Case/Elim/recursive View/contextual preservation
  now use that common history. `NativeLoanMixedPreservation` connects actual
  Loan64 mixed-program histories to exact-original-type ghost preservation.
- The concrete preservation example contains an active named-owner CODE Borrow
  which the earlier program checker rejects. The new checker accepts its mixed
  history, and a real family contraction preserves its original result type.
- The aggregate proof check currently audits 8,625 declarations. The mixed
  native regression suite passes 62 source fixtures and 49 exact-byte checks.
  These counts are validation evidence, not a whole-kernel soundness claim.

## Next semantic work

Prioritize the common typing-to-runtime gap over adding another independent
byte adapter or finite fixture. The existing binding-retaining runtime is in
`NativeBindingMachine`, `NativeBindingMachineHeap` and
`NativeBindingMachineTyping`. It retains original source bodies and captured
ghost origin stores, but currently executes only a fragment (calls, scalars,
branches, Strict, Alloc/Free) and reports unsupported syntax for Lend/reads and
other constructors. Its source-typing bridge uses the earlier judgment.

Connect that runtime to the complete Loan64/resource mixed history, add actual
Lend reader/continuation and read semantics with explicit lease lifetimes, and
prove that source permission and runtime-state invariants supply access guards.
Retain computed callees, erased arguments and exact dependent result origins;
do not replace binding execution with generally invalid CODE beta substitution.
The current heap is uniform-fill/read-only `SizedBufferHeap`; Store and general
data layouts require an appropriate runtime heap interpretation as well.

## Working procedure

Use `/workspace/jihoo` and branch `codex/rootless-kernel-verification` of
`https://github.com/jihoolang/jihoo`. Preserve existing edits and never force-push.
Read `AGENTS.md` and the source theorems before changing them. Continue useful
work without asking again for already authorized commits, pushes or memory
configuration. The user explicitly permits choosing memory ceilings to avoid
OOMs; keep heavy compiler/checker jobs serialized.

The actual project toolchain is available through:

```sh
cd /workspace/jihoo
/workspace/.local/bin/nix-rootless --option sandbox false develop .#proofs
```

Run compiler/checker work through `scripts/proof-limits.sh`. Standalone Lean
uses `-M 4096 -j 1`; build modules with `lake build --wfail`. Add public theorem
audits to `proofs/Audit.lean`, update its exact count in `proofs/check.sh`, and
run the aggregate check after changing a proof interface. Only standard logical
axioms (`propext`, `Classical.choice`, `Quot.sound`) are allowed: no `sorry`,
new axioms or output-typing oracles. Keep large logs in `out/logs/`.

The current native regression command is:

```sh
scripts/proof-limits.sh python3 tests/core_native_loan_mixed_correspondence.py --compiler "$PWD/out/jihoo" --output out/kernel-verification/loan-mixed
```

Update this work record when obligations or the next proof dependency change.
Commit and push meaningful checked increments. Keep reporting whole-kernel
verification as unfinished until the actual completion obligations are proved.
