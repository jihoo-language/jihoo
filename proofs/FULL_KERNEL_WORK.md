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
- `NativeBindingMachineReaderState` now derives an exact, distinct-token
  inventory between concrete reader frames and all active heap leases across
  every reachable machine prefix, including faults/fuel exhaustion. Reader
  return supplies its close guard and retains every outer reader. An empty
  final stack has no outstanding leases; allocated-owner accounting remains
  separate. Reachable Borrow now needs only source typing and `LoanSlots`,
  not a caller-supplied heap-validity or reader-liveness invariant.
- `NativeBindingMachineLoanTyping` connects actual Loan64/resource mixed
  declarations to original code and exact closing origin stores. Ordinary
  closure activation retains the source CODE body/type and owner-slot alignment
  across binders; new named-reader entry supplies its new slot permission.
  These local source/slot lemmas do not yet give a full control-stack/value
  interpretation or derive the raw body typing of a specialized Lend callback.
- Actual reader activation now saves the entered body's exact origin, rather
  than a raw callback application. `NativeBindingMachineLendOrigins` derives
  the closed reader origin and final continuation body at the original ghost
  type from the input Loan64 Lend judgment, including specialized callbacks.
  Reachable named reader entry combines that input derivation, actual lease
  liveness and preservation of named owner slots. This is source provenance,
  not a semantic runtime-value typing or whole-machine fundamental theorem.
- The erased-owner-equality regression requires source specialization:
  standalone callback checking rejects it, while Lend admission and actual
  runtime execution succeed. Native and Loan64 mixed checking agree. The saved
  continuation argument is the checked reader body origin. No arbitrary-input
  callback typing or post-result typing is supplied to the general theorems.
- `NativeBindingMachineIndexBounds` derives Decide numeral bounds from the
  complete Loan64 judgment, including normalized-operand Decide and type
  conversions. Index input inversion covers both array and borrowed-buffer
  rules. For literal Decide, named Borrow and a concrete allocation state,
  source typing, owner-slot identity and the reader inventory construct the
  actual five-transition Index execution and exact read event; callers do not
  supply a numerical read guard, successful execution or output typing.
  The initial allocation-state/owner-slot association and source/control
  alignment remain explicit local premises, not a full-program theorem.
- `NativeBindingMachineAlignment` now proves the mutually defined structural
  value/captured-slot invariant across every evaluate, return, heap, fault and
  fuel transition. All reachable original code and closures retain aligned
  erasure flags and recursively aligned captured values. Full Loan64 variable
  typing constructs the next actual value/step with no caller-supplied `Ready`
  or slot-success premise. This is structural alignment, not heap typing,
  source-typing preservation, loan authority or allocation accounting.
- `NativeBindingMachineDynamicIndex` now connects the full IfLt/Index source
  rules to actual dynamic scalar slots and an erased branch hypothesis. The
  selected comparison constructs ten transitions and the exact read event;
  the else branch takes five transitions without a read. No caller numerical
  bound or successful-execution certificate is assumed. General allocation/
  slot association remains an explicit local entry invariant.
- The same checked dynamic-buffer function is proved for every bounded U64
  count/index with representable allocation size, directly from an empty
  machine: actual allocation, Lend, comparison, optional read, close and Free.
  It returns 7 in bounds and 0 otherwise and has the exact allocation/lease
  trace. Its full source/resource check and all-input source typing use Loan64.
  This parameterized function result does not replace the full-language goal.
- `NativeBindingMachineNumeric` now preserves numeric values, recursively
  captured slots, pending arithmetic/count frames, every heap payload and
  representable allocation length across every actual prefix, including faults
  and fuel exhaustion. It constructs I64 literal typing from actual heap data;
  callers do not supply returned-value typing or numeric realization.
- `NativeBindingMachineIndexValues` combines these bounds with full Loan64
  source inversion and the actual mixed history to type Index integers at the
  exact original closed requested type. It also covers IfLt with an Index yes
  arm and a real pending reader read. General bounds faults remain an explicit
  alternative; this is output preservation, not full typed progress or the
  missing source/control/heap fundamental theorem.
- `NativeBindingMachineLendValues` now reconstructs the checked reader type
  from the full input Lend rule and places actual heap-read integers at that
  type, including specialized callbacks without generic callback typing.
  Actual scalar values close the original continuation body at the original
  Lend result type; paired binding equations retain the real CODE body and
  owner/result slots. This is a valid ghost scalar closing and local runtime
  boundary, not the full value/heap/control-stack fundamental theorem.
- `NativeBindingMachineIndexExecution` now constructs literal/comparison-
  guarded reads together with exact original-type integers from actual initial
  execution prefixes. Heap validity, reader inventory and numeric bounds are
  all derived, rather than supplied. The false comparison arm enters a body
  with the same original source type. Local source/control typing, allocation
  identity/layout and `LoanSlots` association remain explicit inputs.
- The aggregate proof check currently audits 8,789 declarations. The mixed
  native regression suite passes 67 source fixtures and 53 exact-byte checks.
  These counts are validation evidence, not a whole-kernel soundness claim.

## Next semantic work

Prioritize the common typing-to-runtime gap over adding another independent
byte adapter or finite fixture. The existing binding-retaining runtime is in
`NativeBindingMachine`, `NativeBindingMachineHeap` and
`NativeBindingMachineTyping` and `NativeBindingMachineLoans`. It retains
original source bodies and captured ghost origin stores. Lend/Borrow/Index
execution is present; do not reimplement those operators as a new fragment.
The earlier sixty-rule source-typing bridge is retained; its new Loan64
counterpart uses the actual mixed-program history.

`ReadersLive`, exact lease coverage and token distinctness now follow from
initial execution without typing assumptions. Next derive and preserve
`LoanSlots` across the full typed control stack, rather than supplying it
independently at each Borrow. Ordinary binder and reader-entry slot lemmas
are available. Connect captured source code/origin stores and
actual runtime values to the complete Loan64/resource mixed history. The
local reader, structural erasure and numeric value/heap components are
available, but a common source-type/resource interpretation for every runtime
value, context and control stack and its fundamental theorem are not.
Dynamic IfLt hypothesis reads now supplement the literal-Decide bridge.
Extend this to all Lt proof forms and arbitrary computed index/count terms.
Derive exact heap lengths and the association between the owner slot and
allocation from the common runtime interpretation, instead of the
current explicit local allocation-state/slot premises. The runtime bound
check alone does not discharge those obligations.
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

## Latest checked increment (2026-11-15)

The all-prefix reader inventory and Loan64 ordinary-call/source-slot bridge
passed `proofs/check.sh`: 875 Lake jobs, 8,676 audited declarations and the
existing generated-fixture comparisons. The sampled peak tree RSS was
3,575.1 MiB. Only the three allowed logical axioms occurred. No production
compiler behavior was changed in this increment. Full verification remains
unfinished; in particular source permission/owner-value preservation and
Index evidence interpretation still require the common fundamental theorem.

The second increment corrects reader-result provenance and proves actual
explicit-reader/final-continuation entry origin typing from the source Lend
judgment. `proofs/check.sh` passed 876 Lake jobs and 8,693 audits; the native
mixed suite passed 66 source fixtures and 52 exact-byte checks. The sampled
aggregate peak RSS was 3,582.1 MiB. This does not discharge general runtime
value/context/stack typing, Index bound interpretation or owner accounting.

The third increment derives literal-Decide Index bounds from complete source
typing, preserves exact lengths from a concrete allocation state across all
machine prefixes, and constructs a pending read plus the full named-Index
five-step execution. The aggregate check passed 877 Lake jobs, 8,701 unique
public axiom audits and the generated-fixture comparisons (peak sampled RSS
3,583.4 MiB). No additional native implementation changed after the successful
66-source/52-byte regression run. General evidence interpretation, source/slot
fundamental preservation and the original whole-kernel obligations remain open.

The next increment derives recursive closure/context/stack erasure alignment
for all machine prefixes and removes `Ready` from reachable Loan64 variable
execution. `proofs/check.sh` passed 878 Lake jobs, 8,725 unique public audits
and the generated comparisons; peak sampled tree RSS was 3,593.8 MiB. No
native executable behavior changed. The common fundamental theorem still
needs semantic value/heap interpretation and source typing at all control
points, including full `LoanSlots` preservation and dynamic proof bounds.

The latest unit adds the full source IfLt inversion, dynamic named-reader
execution and a parameterized checked Buffer function. Runtime projection
algebra keeps actual state/observation/event execution compositional. Full
source/resource checking, all-bounded-input typing, actual return values,
exact alloc/begin/read/close/free traces and final empty live-object/lease
inventories are derived for that function, without output typing or run-success
oracles. The aggregate check covers 881 Lake jobs and 8,742 unique audits;
native mixed correspondence passes 67 sources and 53 exact-byte checks.
General source/control/value/heap fundamental preservation, all `LoanSlots`
transitions, arbitrary evidence/computed sizes, ownership, universe consistency
and native implementation refinement remain open.

The current increment proves unconditional all-prefix numeric/capture/heap
width preservation and original-source-type interpretation of actual Index
integers. The complete aggregate passed 883 Lake jobs, 8,777 unique public
axiom audits and generated comparisons (sampled peak tree RSS 3,616.6 MiB).
No runtime or production compiler behavior changed. General source-derived
heap/layout/permission invariants and exclusion of bounds/value faults remain
open, alongside all original whole-kernel completion obligations.

The Lend value increment derives actual scalar reader typing and an actual-
scalar closing of the original continuation body from source Lend typing.
The entire check passed 884 Lake jobs, 8,783 unique audits and generated
comparisons (peak sampled tree RSS 3,620.6 MiB). No generic callback or output-
value typing certificate is an input. Full source/control association, general
`LoanSlots`/resource interpretation, bounds-fault exclusion and all original
whole-kernel obligations remain unfinished.

The final increment connects actual prefix executions to original source
result types for literal and dynamic reads and preserves the original type on
else entry. New state-validity forms derive all heap/reader/numeric invariants
from reachability; previous public entry points remain compatible wrappers.
The aggregate passed 885 Lake jobs, 8,789 unique audits and generated-fixture
comparisons (peak sampled tree RSS 3,621.7 MiB). No compiler/runtime code or
native fixture changed in this unit; the existing 67-source/53-byte native
regression evidence is unchanged, not a new implementation-refinement result.
The reused `/workspace/.local/bin/nix-rootless` reports Nix 2.20.6, evaluates
`builtins.add 20 22` to 42, and runs the actual `.#proofs` shell with Lean
4.34.1/Lake 5.0.0-src. Toolchain lock/store contents were not changed.

The next core dependency is the common source/control and resource/value
interpretation: obtain input code typing, exact allocation/owner-slot association
and all `LoanSlots` obligations from the actual Loan64/resource mixed history
through every capture, call, Lend and continuation. Connect resource projection
to real owner/lease identities; preserve source-dependent heap lengths; then
extend bound interpretation to arbitrary proofs/computations. The numerical
and scalar-closing results do not by themselves establish those obligations,
full ownership/borrow soundness, universe consistency or native refinement.
