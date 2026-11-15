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
- `NativeBindingMachine` now executes actual Lend reader/continuation closures,
  named Borrow and borrowed-buffer Index, with distinct lease identities and
  closing before continuation entry. Its general heap-prefix theorem covers
  the new actions, including faults and exhausted fuel. Existing call/erasure
  regressions remain intact.
- `NativeBindingMachineLoans.typed_borrow_executes` uses the full Loan64 source
  permission and independent owner-slot/reader-frame invariants to construct
  the actual Borrow result and derive that its owner is live. Local reader
  begin/body/finish lemmas preserve lease correspondence and derive the close
  guard. This is not yet an invariant-preservation theorem for every typed
  runtime transition.
- Resource-checked execution examples now include two simultaneously active
  readers (the inner reader borrows the outer named owner), and a fresh owned
  reader result followed by separate release of both resources. They retain
  actual values and exact event streams. Escaping references are rejected by
  the type checker and untyped post-close reads fault.
- The aggregate proof check currently audits 8,648 declarations. The mixed
  native regression suite passes 64 source fixtures and 51 exact-byte checks.
  These counts are validation evidence, not a whole-kernel soundness claim.

## Next semantic work

Prioritize the common typing-to-runtime gap over adding another independent
byte adapter or finite fixture. The existing binding-retaining runtime is in
`NativeBindingMachine`, `NativeBindingMachineHeap` and
`NativeBindingMachineTyping` and `NativeBindingMachineLoans`. It retains
original source bodies and captured ghost origin stores. Lend/Borrow/Index
execution is present; do not reimplement those operators as a new fragment.
The earlier source-typing bridge still uses the sixty-rule judgment, while the
new Borrow execution theorem uses Loan64 directly.

Next derive and preserve `LoanSlots` and `ReadersLive` (with distinct active
tokens) across all reachable typed machine states, rather than supplying them
independently at each Borrow. Connect captured source code/origin stores and
actual runtime values to the complete Loan64/resource mixed history. The
local reader transition lemmas are available, but a common runtime-value,
context and control-stack interpretation and its fundamental theorem are not.
Derive Index bounds from interpreted typed evidence and exact heap lengths;
the existing runtime bound check alone does not discharge that obligation.
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
