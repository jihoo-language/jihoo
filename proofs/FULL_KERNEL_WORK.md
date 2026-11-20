# Active whole-kernel verification work

The full dependent-kernel verification goal is active. This record tracks
checked increments and the obligations still needed for kernel-wide claims.

## Handoff on 2026-11-20

The preceding handoff was on `codex/kernel-pure-and-array`, merged by PR #220.
Issue #218 was closed by PR #219. Work continues from `main` at `c092595`.
Version 0.7.0 is gated on the complete verification obligations below.

| Remaining obligation | Starting point |
| --- | --- |
| General consistency and typed normalization | `NativeLoanOpenDependentTransport.lean` opens the checked declaration's written affine telescope. It normalizes selected beta-hidden equality evidence and transports the arithmetic payload at the original instantiated annotation. General dependent telescopes, family values and arbitrary checked ghost derivations still need the fundamental theorem. |
| Whole-language preservation | `NativeCoreExpandedFamilies.lean` composes recursive global lookup, dependent operand conversion and typed Case, Elim, Borrow, Deref and View reentry in the same arena. The Strict arena rewrite preserves raw typing for scrutinee-independent motives and pure typing at a formed annotation for arbitrary dependent motives. Compose the pure result through the remaining traversal, specialized Lend, wider View shapes and effect rules. |
| Ownership, borrowing and continuations | `NativeBindingMachineMutableLoanedArithmeticProgress.lean` derives either typed restoration or an exact signed overflow prefix for an ordered reader tree containing fresh and captured live references. Closed arithmetic evidence at the original index and the physical allocation length prove the computed unsigned sum fits. General execution across arbitrary closures and dependent runtime forms remains open. |
| Production refinement | `NativeCoreGhostSpineInference.lean` covers ghost Pi and lambda binders, application spines, local and global heads, universe and scalar heads, primitive operators with fixed operand types, Decide, Strict, ZeroLe, USub, conditional branches, refinements and equality transport. Successful inference gives a type convertible to the admitted declaration type when comparisons retain all positions. Continue with the remaining constructors, code checking, and full implementation refinement. |

Run the aggregate proof check from the checkout with the declared resource
limits. It checks Lake compilation, the exact axiom audit, and the generated
fixtures.

```sh
nix develop -L .#proofs -c scripts/proof-limits.sh bash proofs/check.sh
```

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
- Canonical owner aliases now resolve Borrow through a scoped same-object
  reader while retaining exact-name priority. Canonical source typing and
  physical owner-size/loan contexts construct Borrow and literal/dynamic Index
  steps without alias-key equality. These remain explicit local associations,
  not an all-control or all-value lifetime fundamental theorem.
- An earlier checkpoint audited 9,156 declarations and passed 67 mixed native
  source fixtures and 53 exact-byte checks. Later counts appear with their
  checked increments below.

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
canonical source/control, resource/value and scoped owner authority across
the full typed control stack. `OwnerLoanSlots` now transports ordinary
binders, noninjective alias rebasing, reader entry/body and captured IfLt
else entry without requiring every runtime alias to share a lexical key.
Source-to-reader lifetime association must additionally identify which reader
survives closing; same-object reader existence alone is insufficient.
Indexed execution now preserves reader-entry capture bounds in both active
and suspended frames. The canonical variable return uses those bounds and
the original Lend typing to exclude the retired token from the resumed state.
Derive the corresponding value and resource interpretation for computed
reader results.
Connect captured source code/origin stores and
actual runtime values to the complete Loan64/resource mixed history. The
local reader, structural erasure and numeric value/heap components are
available, but a common source-type/resource interpretation for every runtime
value, context and control stack and its fundamental theorem are not.
Dynamic IfLt hypothesis reads now supplement the literal-Decide bridge.
Extend this to all Lt proof forms and arbitrary computed index/count terms.
Derive exact heap lengths and the association between the owner slot and
allocation from the common runtime interpretation, instead of the
current explicit local source/slot/size entry premises. The runtime bound
check alone does not discharge those obligations.
Retain computed callees, erased arguments and exact dependent result origins;
do not replace binding execution with generally invalid CODE beta substitution.
The indexed heap tracks writes to individual Buffer cells. The common runtime
interpretation needs to cover their contents and general data layouts.

## Working procedure

The user's explicit continuation instruction on 2026-11-16 is to keep working
until Codex usage is exhausted, the user asks to stop, or the full dependent
kernel proof obligations are actually completed. An active goal records that
instruction. Checked increments and pushes do not complete or pause the goal.
The subsequent explicit user pause request overrides that instruction: finish
the current checked checkpoint, commit and push it, then pause the active goal.
Do not begin another proof task until the user resumes work.

The user resumed full-kernel work on 2026-11-20 and explicitly requested
continuation until they ask to stop. The active goal records the complete
proof obligations and the conditional 0.7.0 release. Continue checked
increments on the verification branch.

The user requested a handoff on 2026-11-20 to continue the remaining work
later. The final checked increment and the handoff above record the current
state.

Use the checkout of `https://github.com/jihoolang/jihoo` at
`/home/user/jihoo`. Work resumed on 2026-11-20 on
`codex/kernel-pure-and-array`, following the merge of
`codex/alias-reborrow-verification` into main. Preserve existing edits and never
force-push.
Read `AGENTS.md` and the source theorems before changing them. Continue useful
work without asking again for already authorized commits, pushes or memory
configuration. The user explicitly permits choosing memory ceilings to avoid
OOMs; keep heavy compiler/checker jobs serialized.

The actual project toolchain is available through:

```sh
cd /home/user/jihoo
nix develop .#proofs
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

The Lend resource handoff now connects the dependent checker's actual reader
and restored-continuation projections to the binding-retaining machine. Both
the returned owner and the old captured owner slot refer to the same concrete
object; their complete slot map and ghost closing agree with the checked alias
substitution. Actual reader return constructs close followed by both real
continuation activations, preserving every outer `LoanSlots` permission through
the two retained binders. The current lease supplies owner liveness, and the
remaining exact reader inventory characterizes Free's guard, including nested
readers of the same object.

For a continuation beginning with Free of either owner alias, the actual
eight-step execution closes, activates and releases the same object, or reports
an explicit outer-reader conflict. The source Lend derivation supplies the
remaining code's original ghost result type, and its actual resource projection
supplies zero residual owner demand on every abstract tail prefix. No output
typing, successful execution, heap-validity, liveness or Free-guard oracle is
an input. These are local theorems: input code typing/projection, source-owner
slot association and current reader-frame/control association are still inputs.
The next fundamental theorem must derive those associations from mixed-history
admission, exclude outer-reader conflicts in legal consuming continuations,
and associate arbitrary tail-machine executions with the zero-demand resource
prefixes. Ghost origin typing is not semantic typing of arbitrary returned
values. All original completion gates remain open.

Validation of this increment: `proofs/check.sh` passed 886 Lake jobs, 8,800
unique public axiom audits and all generated-fixture comparisons; sampled peak
tree RSS was 3,623.7 MiB. Only `propext`, `Classical.choice` and `Quot.sound`
occurred. No native executable behavior, compiler source or fixture changed.

The nested-reader resumption unit recovers a continuation's outer Borrow
permission from that actual dependent resource check's specialized body, then
derives its concrete captured owner from the pre-existing `LoanSlots`. At the
actual inner reader return, the old reader inventory supplies a distinct outer
token that survives close and still denotes a live owner. Eight constructed
machine transitions close the inner lease, install the two retained bindings,
execute the authorized outer Borrow, discard its result through Strict and
enter the continuation tail with all outer permissions and the original ghost
result type. No post-close slot/lease/liveness or returned-value certificate is
an input. Source checking also rejects reborrowing the just-restored owner
through either alias when it has no remaining outer source loan.

Input code typing, exact local resource projection and the original captured
loan-slot/frame association remain local premises. The common fundamental
theorem must derive them from actual closed mixed-history admission and carry
them through every machine control transition. General ownership authority,
heap layout/bound-proof interpretation, all specified computation preservation,
universe consistency and native implementation refinement remain unfinished.

The resumption increment passed the complete `proofs/check.sh`: 887 Lake jobs,
8,806 unique public axiom audits and all generated-fixture comparisons. Only
the three allowed logical axioms occurred; sampled peak tree RSS was
3,624.2 MiB. Compiler/runtime/native fixtures remain unchanged. This run reused
the existing rootless `.#proofs` shell with Lean 4.34.1/Lake 5.0.0-src and the
serialized proof guard, without changing dependency locks or memory ceilings.

The fresh owned-reader unit derives scalar literal widths and a reader's
declared first-result conversion from the actual Loan64/resource check. Buffer
normalization preserves its rigid head even for computed dependent sizes, so
the first-result linear mode and its exact-once obligation are reconstructed,
alongside the separate original-owner obligation; no `firstOwned` oracle is
required. `BufferValue` interprets an actual owner as a live heap object with
the length required by its closed source type modulo Loan64 conversion. It
deliberately does not assert exclusive authority over all retained aliases.

Actual reachable reader allocation constructs this interpretation and the
five machine transitions. Its fresh result cannot alias the currently leased
owner, no old lease refers to the new object, and its Free guard is derived.
Caller-provided output typing, fresh owner slots, heap validity and allocation
success are not premises. The byte-size overflow branch remains explicit:
source U64 typing alone permits sizes that overflow the allocator's byte bound.
The current source/control/reader association is still a local input, and
general value/resource/heap fundamental preservation remains unfinished.

Validation: `proofs/check.sh` passed 888 Lake jobs, 8,816 unique public axiom
audits and all generated-fixture comparisons, with only the three allowed
logical axioms. Sampled peak tree RSS was 3,630.0 MiB. No compiler/runtime
implementation or native fixture changed. The existing rootless project shell
reports Nix 2.20.6 (evaluation smoke check 42), Lean 4.34.1 and Lake 5.0.0-src.

The owned-reader execution unit connects that fresh Buffer interpretation and
the actual separate resource obligations to sixteen real machine transitions:
allocate, close, install both retained owner bindings, Free the fresh first
result, and Free the original owner. The final tail keeps the original ghost
result type and has zero residual source demand for both distinct capabilities.
No fresh-result lookup, output typing, allocation success or heap guard is an
input. A byte-size overflow stops explicitly after five steps. A remaining
outer reader of the original object stops its release after the fresh result
has been freed; its absence is characterized by the actual reader inventory.
General source admission must still exclude such conflicts in legal consuming
continuations and relate arbitrary tail execution to its zero-demand projection.
The original owner's source length/slot/control association and general runtime
exclusive authority remain part of the open common fundamental theorem.

The complete check passed 889 Lake jobs, 8,819 unique public axiom audits and
generated-fixture comparisons (sampled peak tree RSS 3,632.5 MiB). Dependencies
use only the three allowed logical axioms. Native executable behavior and
fixtures were not changed by this execution proof.

The owner-provenance invariant now covers every actual machine transition and
prefix from the empty heap, including faults/fuel exhaustion, computed calls,
all saved frames and recursively captured closures. Every retained owner ID is
strictly below the current allocation counter. Thus the next allocation cannot
alias any old captured owner, including owners already released, rather than
only being distinct from the currently leased object.

Captured and returned owners are connected to an actual earlier allocation
event with its exact count/payload; their present length and payload agree with
that event throughout this read-only uniform-fill heap. These results derive
runtime identity and layout provenance without a caller-provided allocation
snapshot, heap invariant or provenance certificate. They do not imply that an
owner is still live or exclusively usable: old aliases intentionally remain
captured after consumption. Source-dependent count interpretation and resource
authority must still select which retained aliases may be used.

The next semantic dependency is the common source/control/value/resource
fundamental theorem: interpret the closed Loan64 source type of each permitted
owner slot at the allocation length now reconstructed from execution, preserve
that interpretation through arbitrary calls and specialized continuations, and
connect source resource prefixes to actual permitted owner uses. Fresh literal
allocating readers now compose with source-typed Index and cleanup below;
generalize that association to arbitrary reader computations, runtime-dependent
allocation counts and dependent bound evidence.
General consistency, full specified computation preservation, ownership/borrow
soundness and native implementation refinement remain open; no completion gate
or source constructor was removed.

The final aggregate passed `proofs/check.sh`: 890 Lake jobs, 8,846 unique
public axiom audits and every generated-fixture comparison. Only `propext`,
`Classical.choice` and `Quot.sound` occurred. Sampled peak tree RSS was
3,642.1 MiB. The provenance module shares the established runtime split
auxiliaries so the full aggregate imports without duplicate generated matcher
declarations. No native compiler/runtime source or fixture changed in this run.

The returned-Buffer read unit composes actual allocating-reader return with a
second Lend and a named Borrow/Index of that retained first result. The same
Loan64 input supplies literal widths, the strict Index bound, the exact reader
origin typing and actual integer typing at that reader type, including source-
specialized callbacks and result conversions. Its own resource check supplies
the declared closed Buffer interpretation. No allocation snapshot, returned
owner-slot lookup, heap length, read success or output typing is an input.

Twenty actual transitions construct allocation, old lease close, both outer
continuation bindings, the fresh lease, its named Borrow and the read. The
old token is closed and the distinct new token authorizes this actual object;
the returned payload is the original signed fill. Allocation byte overflow
remains explicit after five steps. Both runtime code and closure captures are
retained; the closed allocation expression is ghost provenance, never CODE
substitution/re-execution. This composes a fresh owned value with source-typed
Index; arbitrary computations, dependent evidence and the full closed-admission
source/control/value/resource fundamental theorem remain open.

The complete aggregate passed 891 Lake jobs, 8,849 unique public axiom audits
and generated-fixture comparisons (sampled peak tree RSS 3,641.8 MiB), using
only the three allowed logical axioms. No native runtime/compiler or fixture
changed. The existing real-project rootless shell remains Nix 2.20.6 (smoke
evaluation 42), Lean 4.34.1 and Lake 5.0.0-src; dependency locks are unchanged.

The returned-Buffer completion unit derives the actual final integer at the
original outer Lend result type, through the same specialized source rules and
arbitrary result conversions. It then composes the constructed twenty-step
read prefix with inner close, both inner continuation bindings, separate Free
of the fresh result/original owner and scalar return: thirty-two actual steps.
All-prefix owner provenance rules out a fresh object in the old reader stack;
the actual reader inventory therefore supplies the fresh Free guard after its
lease closes. There is no caller-provided liveness/guard/output/success oracle.

An outer reader of the old object still gives an explicit thirty-one-step
borrowed-owner fault; byte overflow gives the explicit five-step fault even
when thirty-two steps are requested. Unconditional run composition also covers
already stopped states. Source/control/frame association at the entry point
remains local. The common admission-to-runtime fundamental theorem must still
derive it and rule out old-owner conflicts for all legal consuming contexts,
interpret arbitrary dependent evidence/computations and simulate resource use.
The original whole-kernel consistency/preservation/ownership/native refinement
obligations remain open; these are not narrowed completion gates.

A closed application now checks actual Loan64/resource admission and its
original captured context/projection, constructs the fourteen-step caller
entry, and instantiates the general completion theorem to derive scalar 7
after forty-six total steps. The scalar result is obtained from the general
proof, not an input output/success certificate or an independent CBV evaluation
of the final program. This demonstrates a real admitted instance of the local
theorem; it is not a general proof of every closed-admission entry invariant.

Final validation: `proofs/check.sh` passed 893 Lake jobs, 8,856 unique public
axiom audits and all generated-fixture comparisons. Only the three allowed
logical axioms occurred; sampled peak tree RSS was 3,651.7 MiB. No production
compiler/runtime behavior or native fixture changed in this unit.

Next reconstruct input source/closing/resource/slot association from actual
mixed admission through arbitrary captured/computed calls, then interpret
runtime-dependent allocation sizes and general evidence. Effectful source
origins must be related to runtime scalar values semantically; do not assume
conversion to their observed numeral or accept an output-typing/denotation
oracle. Exclude old-owner reader conflicts from source resource authority and
carry arbitrary continuation tails through that same interpretation. General
universe consistency, all specified computation preservation, whole ownership/
borrow soundness and native implementation refinement remain unfinished.

The scalar-closing bridge separates the actual value closing from retained
runtime provenance. The same Loan64 source judgment/ghost input substitution
now types arbitrary original function bodies after a natural argument is
bound to its observed canonical value. The result type is instantiated at that
actual numeral, while `Code.origins` still saves the original argument term.
No conversion of effectful Strict/Free origins to their observed numeral is
assumed. The checked mixed declaration supplies the initial empty closing and
its original resource evidence; no semantic candidate is chosen by a caller.

At a reachable natural closure-entry point, numeric bounds come from the
unconditional runtime invariant. The actual step retains the closure body and
captures, extends direct scalar-slot agreement and preserves old named loans.
No argument/output typing certificate or successful-evaluation oracle is an
input. The input closure typing/value-closing and captured-slot/loan invariants
remain local premises. This is not the general control-stack preservation
theorem or an interpretation of every captured heap/function value.

The aggregate passed 894 Lake jobs, 8,866 unique public axiom audits and the
generated-fixture comparisons. Only the three allowed logical axioms occurred.
Native compiler/runtime behavior and fixtures were not changed.

The computed-allocation unit uses an actual natural closure-call boundary and
a dependent `U64 -> Buffer` signature. Its original allocation body reads the
retained argument variable; no source count literal or caller-provided slot
lookup is supplied. Source typing closes the body at the actual numeric value
and derives fill width. Six actual transitions bind that value and allocate a
live Buffer whose heap length matches the semantic instance of the signature.
The original effectful argument origin remains in machine metadata. Global
owner provenance also excludes the new object from all earlier recursive
captures, including dead aliases. Byte-size overflow is an explicit six-step
fault. The local input function/context typing is still a premise: general
admission/control/closure/resource preservation and the interpretation of
arbitrary source result annotations remain unfinished.

The same value-closing construction now supports arbitrary I64 function
bodies as well. A first U64 call reconstructs the actual captured second
closure's dependent input type; a later computed I64 argument supplies the
fill. Six actual transitions read both retained slots and construct the
Buffer at the observed count and signed fill. Both original argument origins
are retained, with no source-origin-to-literal conversion premise.

Two closed actual Loan64/resource admissions instantiate these general
theorems. Free/addition computes the size in a twenty-one-step program. A
curried call captures that size, later computes its signed fill with another
Free/arithmetic effect, and returns an interpreted Buffer of length two and
signed fill -5 (stored as `encodeInteger(-5)`) after thirty-seven steps. Entry prefixes are checked; allocation
and output interpretation follow from the generic six-step theorem, not an
output/success certificate. Admission's source type retains the original
effectful count expression; the Buffer interpretation uses the source Pi
signature's instance at the actual value. These are distinct statements, not
a claimed raw conversion between their annotations.

The final aggregate passed 896 Lake jobs, 8,875 unique public axiom audits and
all generated-fixture comparisons. Dependencies use only `propext`,
`Classical.choice` and `Quot.sound`; sampled peak tree RSS was 3,664.8 MiB.
The existing `/workspace/.local/bin/nix-rootless` was reused (Nix 2.20.6,
evaluation smoke check 42, actual project `.#proofs` Lean 4.34.1/Lake 5.0.0-src).
No dependency lock, native compiler/runtime behavior or native fixture changed.

Next preserve a complete typed control/continuation stack and captured value
interpretation from mixed admission across every call and closure creation.
`ScalarSlots` only maps observed direct numeric slots to their canonical
meanings; it does not classify arbitrary nonnumeric values or prove all
type-directed captured lookups. Relate general effectful source annotations
and computed branch/evidence operands to their actual-value instances with a
genuine expression/heap interpretation, not conversion-to-numeral or caller
output realization assumptions. Integrate source resource authority and exclude
old-owner loan conflicts. General universe consistency, all specified
computation preservation, full ownership/borrow soundness and native
implementation refinement remain unfinished.


## 2026-11-15: type-directed captured values and general slot allocation

`NativeBindingMachineValueKinds` adds a representation-head interpretation
and a value-context invariant stronger than the one-way `ScalarSlots`.
Raw-Lend rigid-head disjointness proves that U64/I64 types select actual
natural/integer representations. The authentic mixed declaration constructs
its initial context, and arbitrary full-source U64/I64 function entry preserves
it at actual argument values while retaining the original provenance map.
Reachability supplies argument widths and captured-slot readiness. A source-
typed variable now constructs its stored numeric value, canonical meaning,
width, typing and actual next transition; no selected value or output typing
certificate is an input.

`NativeBindingMachineCapturedAllocation` uses that context and the full Loan64
allocation derivation at any reachable allocation boundary. Size and fill may
occupy arbitrary captured indices. Their representations, source-derived widths
and canonical meanings are outputs. Five constructed actual transitions either
return a live Buffer at the SAME closed source allocation result type, with
its actual size/fill, or report byte-size overflow. This generalizes the prior
fixed first/second-binder allocation schemas without assuming stored numbers,
allocation success or post-result typing.

The aggregate passed 898 Lake jobs, 8,890 unique public axiom audits and all
generated-fixture comparisons (`out/logs/value-context-allocation-full-1.log`);
sampled peak tree RSS was 3,670.8 MiB. Only `propext`, `Classical.choice` and
`Quot.sound` occur. Rootless Nix 2.20.6 and the existing proof shell were reused.
No native implementation or native fixture changed.

The value-head relation is intentionally partial semantic information: closure
bodies, heap liveness/exclusive authority and reference leases are NOT proved
by it. Its input-context premise must still be established across all control
frames, closure creation and reader/resource transitions. Next construct erased
comparison evidence and branch value contexts from actual scalar comparison,
without typing arbitrary effectful origin metadata as canonical evidence.
General effectful annotation semantics, universe consistency, all specified
computation preservation, whole ownership/borrow soundness and native
implementation refinement remain unfinished.


## 2026-11-15: canonical comparison evidence and surviving reader Borrow

`NativeBindingMachineCapturedBranch` derives both runtime U64 operands from
full source input typing and the constructed value context. Five actual
transitions select an arbitrary original yes/no body at the same closed result
type. The true branch constructs canonical erased Decide evidence from the
observed comparison, extends its ghost substitution and preserves the complete
value context. Original branch provenance remains untouched; its possibly
effectful origin evidence is never assumed to be well typed or convertible to
canonical numerals.

Erased entry preserves named-owner slots and lexical reader keys. A true
comparison with a source-authorized Borrow constructs six actual transitions
to a reference whose lease and owner are live. Validity and reader liveness
come from unconditional actual-prefix invariants, including nested reader
stacks. No selected number, comparison proof, token, live-owner certificate,
output typing or successful Borrow is supplied. General input control/value/
loan-context construction is still required; this does not establish arbitrary
Index heap-size association or complete resource authority.

The aggregate passed 899 Lake jobs, 8,893 unique public audits and all generated
fixture comparisons (`out/logs/captured-branch-full.log`), with only the three
allowed logical axioms and 3,671.4 MiB sampled peak RSS. Next connect a derived
fresh allocation to an actual owner function binding and construct its value
context from the source allocation, rather than requiring a caller's typed
runtime owner. General consistency, specified computation preservation,
ownership/borrow soundness and native implementation refinement remain open.


## 2026-11-15: derived allocated-owner entry and named Lend start

`NativeBindingMachineAllocatedArgument` connects a source-typed allocation
at arbitrary captured size/fill slots to the actual pending function closure.
The original input allocation judgment reconstructs a canonical ghost
allocation from its observed numeric meanings. Function inversion then
constructs the retained owner binder's ghost substitution, representation
agreement and arbitrary dependent body typing. Six actual transitions allocate
and enter the original body, with both the alloc and activation events. The
Buffer interpretation uses the same input allocation type; the body signature
is instantiated at the canonical ghost allocation while original argument
provenance remains untouched. No runtime-argument/output typing or successful
allocation/call certificate is an input. Byte overflow remains a five-step
fault before function entry.

For an original body beginning with named Lend of that argument, nine actual
transitions allocate, bind the owner and open its lease. The heap derives
owner liveness and the correct Buffer length, the reader code retains the
constructed value context, and the post-state has the exact complete reader
inventory, including every nested outer reader. The lease token and Lend
guard are constructed from actual allocation/reachability, with no allocation
snapshot, stored owner, live-owner witness or successful-Lend oracle.

The final aggregate passed 900 Lake jobs, 8,895 unique public axiom audits and
all generated-fixture comparisons (`out/logs/allocated-argument-full-final.log`).
All 20 public theorems added in this run are audited exactly once. Dependencies
use only `propext`, `Classical.choice` and `Quot.sound`; sampled peak tree RSS
was 3,671.6 MiB. The existing rootless Nix proof shell and resource wrapper were
reused. No production compiler/runtime behavior or native fixture changed.

Next derive the full source/control/value/loan-context invariant from mixed
admission across every frame and closure creation, extending the proved empty,
scalar, allocated-owner and comparison entries. Reader activation must retain
the authentic specialized checked-read derivation: specialized dependent Lend
checks `Lending.read owner body`, not an arbitrary-argument callback, so do NOT
assume that callback typing to recover a convenient generic body context.
Connect actual reference entry and captured dependent lengths to heap/lease
interpretation for arbitrary Index and nested reader lifetimes, and connect
resource authority to live aliases rather than every captured owner. General
effectful source-result semantics, universe consistency, all specified
computation preservation, full ownership/borrow soundness and native
implementation refinement remain unfinished. The whole-kernel goal is NOT
complete; continue the existing automation.


## 2026-11-15: authentic specialized reader reference closing

`NativeBindingMachineReaderClosing` derives the actual reader-domain
conversion and specialized checked-read typing from all full Loan64 Lend
origins. Generic callbacks use their real lambda inversion and beta proof;
specialized rules retain their checked read. No arbitrary-argument callback
judgment is added. Actual reference entry constructs its ghost substitution,
all captured value-head interpretations and canonical closed original-body
typing, independently of the runtime provenance map. Named activation also
preserves source loan slots and derives concrete lease/owner liveness from the
actual reader inventory, including nested outer readers.

The aggregate passed 901 Lake jobs, 8,898 unique public axiom audits and all
generated-fixture comparisons (`out/logs/reader-closing-full.log`); only the
three allowed logical axioms occur and sampled peak RSS was 3,674.6 MiB.
Rootless Nix 2.20.6/evaluation 42 and actual proof-shell Lean 4.34.1/Lake
5.0.0-src were verified through the resource guard. No native implementation
or native fixture changed.

The original reader body is proved at its canonical closed ghost instance;
this does NOT invent a false-mode original callback derivation for specialized
rules. General configuration/control preservation must retain that authentic
source read. Next associate captured owner types with immutable actual heap
lengths, preserving released aliases without assigning them live/exclusive
capabilities, and derive dynamic named Index preconditions from those sizes.
General admission/control/resource interpretation and all whole-kernel
consistency, computation-preservation and native-refinement gates remain open.


## 2026-11-15: immutable owner sizes and source-derived dynamic Index

`NativeBindingMachineOwnerSizes` interprets each captured owner's source
Buffer type at its actual allocated identity/length. It deliberately retains
released aliases without granting liveness or exclusive ownership. Heap-event
induction preserves this information through every actual execution suffix,
including Free, nested reader actions, faults and exhausted fuel. Empty,
scalar, reference and erased-comparison contexts preserve it. The original
source allocation and pending function construct the new owner's size context
at the six-step actual entry, preserving old captured owner lengths as well.
No caller supplies the resulting owner's heap/type interpretation.

`NativeBindingMachineSizedIndex` removes the previous dynamic-read theorem's
allocation-snapshot and selected numeric/owner-slot premises. Full source
Index inversion excludes the Array case for Borrow and exposes the actual
owner's Buffer type. The erased comparison evidence identifies that type's
closed length with the observed right operand. The constructed owner-size
context then identifies the actual heap length; source Borrow permission,
loan slots and the actual reader inventory construct the owner and live lease.
Ten real transitions return an I64 at the SAME closed input result type. A
false comparison instead enters the original-type else body in five steps.
No strict-bound, physical-length, successful-read or output-typing certificate
is requested. These remain local source/value/size/loan-context statements,
not a closed-admission fundamental theorem.

`NativeBindingMachineSizedBorrow` separately constructs a live reference at
its exact closed source type, including the real Buffer allocation length.
Its owner, token, lease, bound/type witnesses and actual next transition all
follow from the source judgment, constructed size context, source loan slots
and actual reachability. It requires no stored-owner or returned-reference
realization certificate. This reference interpretation is not a deallocation
capability.

The aggregate passed 904 Lake jobs, 8,916 unique public audits and all generated
fixture comparisons (`out/logs/owner-sizes-index-full.log`). All 21 new public
proofs in this run are audited, with only `propext`, `Classical.choice` and
`Quot.sound`; sampled peak tree RSS was 3,679.6 MiB. No native compiler/runtime
or native fixture changed, and no dependency/store pin changed.

Next derive the common source/control/value/owner-size/loan/resource invariant
from actual mixed admission across every saved frame and closure creation.
Compose the newly constructed allocation/size and authentic specialized-reader
entry contexts across whole actual reader histories; reader reference entry
must retain the checked specialized read rather than invent arbitrary callback
typing. Interpret arbitrary evidence/computed source annotations and general
Index forms, connect quantity authority to live aliases, and exclude old-owner
conflicts before Free. All-universe consistency, all specified computation
preservation, full ownership/borrow soundness and native implementation
refinement remain unfinished. The whole-kernel goal is NOT complete; keep the
existing automation active.


## 2026-11-15: source-derived read through the actual reader reference

`NativeBindingMachineReferenceIndex` connects the actual reference argument
of an explicit reader to its input full Loan64 Lend judgment. Generic and
specialized sources retain their authentic checked read. Source bound evidence
and the captured owner-size interpretation derive the literal index width,
strict bound and exact physical Buffer length; the reader annotation agrees
with that actual sized reference. Six constructed transitions activate the
reader, read its retained reference slot and perform Index. The I64 result
has the source-derived reader result type; the post-state retains the complete
reader inventory, value/owner-size contexts and named source loan slots.

No allocation snapshot, selected numeric value, successful read, arbitrary
callback judgment or returned-value typing is supplied. The owner-slot and
source/control/frame associations remain explicit local inputs. This closes
the earlier explicit bounds-failure branch for this reference-reader schema;
it does not interpret arbitrary evidence or establish all closed admissions.
`HasType.named_index_owner` is strengthened to all modes so that this uses the
actual checked ghost read rather than assuming an original false-mode reader
callback.

The aggregate passed 905 Lake jobs, 8,919 unique public axiom audits and all
generated-fixture comparisons (`out/logs/reference-index-full.log`), with only
the three allowed logical axioms and 3,681.4 MiB sampled peak tree RSS. The
existing rootless Nix 2.20.6 proof shell, Lean 4.34.1/Lake 5.0.0-src and shared
resource guard were reused; no native implementation or fixture changed.

Next close that reader and construct both actual continuation bindings at
canonical scalar/owner meanings while retaining original provenance, source
resource projection and remaining outer readers. Then derive the common
admission/control/value/size/loan/resource invariant and general evidence/
effectful result semantics. Whole-kernel consistency, all specified computation
preservation, full ownership/borrow soundness and native refinement remain open.


## 2026-11-15: actual scalar/owner handoff and eleven-step reader composition

`NativeBindingMachineValueHandoff` extracts both actual continuation annotation
conversions from all full Loan64 Lend origins. Generic cases use real lambda/
Pi inversion; specialized cases retain their checked read/restore premises.
The observed integer's width comes from actual reachability. It constructs
both retained bindings at canonical integer/owner meanings, while preserving
all original runtime provenance. The same source Lend reconstructs the
continuation body's exact closed original result type and its complete value
and immutable-owner-size contexts; no arbitrary callback or returned-value
typing is supplied. Five actual transitions close the reader before either
binding, preserve old source loan slots and the exact remaining outer-reader
inventory, and relate the actual owner aliases to the same resource
projection's zero reader demand and single continuation demand. The Free guard
is characterized by remaining concrete readers, not assumed.

`NativeBindingMachineReferenceReaderCompletion` composes the proved six-step
reference read with that five-step handoff. The intermediate actual prefix,
read integer, heap and continuation frame are constructed using run composition,
not checked as a supplied output. Eleven actual transitions reach the original
continuation body with canonical value/heap-size contexts, original closed
result typing, restored source loans, exact owner-alias/resource correspondence
and remaining reader inventory. It works with arbitrary original continuation
bodies and nested outer reader stacks under the explicit local entry contexts.
This is not execution/progress of every later continuation body.

The aggregate passed 907 Lake jobs, 8,922 unique public audits and every
fixture comparison (`out/logs/reference-reader-completion-full.log`). All six
public theorems added in this run are audited exactly once, with only
`propext`, `Classical.choice` and `Quot.sound`; sampled peak tree RSS was
3,684.6 MiB. The source-only proofs preserve the existing native implementation,
fixtures and dependency lock; the rootless Nix/resource-guard environment was
reused.

Next derive the all-control source/value/size/loan/resource invariant from
actual mixed admission, using authentic specialized checked reads/restores
rather than inventing false-mode original callback/body derivations. In
particular carry the enclosing reader's zero-owner-demand authority through
all actual frames to exclude consumption/re-lending of its leased owner and
derive absence of remaining owner readers before Free. The local old-owner
Free characterization is still conditional until that common invariant is
proved. General higher-order/context association, arbitrary evidence and
effectful result semantics, all-universe consistency, all specified computation
preservation, complete ownership/borrow soundness and native implementation
refinement remain unfinished. The whole-kernel goal is NOT complete; keep the
existing automation active.


## 2026-11-15: authentic checked dynamic reference reader

`NativeBindingMachineCheckedDynamicReader` starts from the actual full resource
projection of the original Lend. Its checker receipt reconstructs the original
Loan64 source judgment, specialized false-mode checked read, exact recursive
resource projections and zero/one owner contract. It does not assume typing
of the original reader callback at arbitrary arguments. Actual closure capture
alignment and the constructed value context determine both captured U64
operands; immutable owner sizes and the source comparison evidence determine
the physical Buffer length. Removing the erased binder uses only substitution
of proved conversion equations, never an invented typed comparison proof.

The real reference binder then executes either eleven transitions to a source-
typed I64 read or six transitions to the original else body at the checked
reader type. Runtime provenance remains unchanged. Both paths retain exact
nested reader inventory and the reference value/owner-size contexts. Neither
selected numeric operands, an allocation snapshot, a strict-bound certificate,
a generic callback nor successful execution/output typing is an input.
The owner-slot and source/control/frame association are still local entry
invariants, not reconstructed for every closed mixed admission.

The aggregate passed 908 Lake jobs, 8,925 unique public audits and all generated
fixture comparisons (`out/logs/checked-dynamic-reader-full.log`); only the
three allowed logical axioms occur, with 3,686.6 MiB sampled peak RSS. The
existing rootless Nix 2.20.6 proof shell (Lean 4.34.1/Lake 5.0.0-src), smoke
evaluation 42 and shared resource guard were reused. No native implementation,
fixture, lock or Nix store pin changed.

Next extend canonical continuation binding to guarded scalar readers using
source-derived scalar conversion, compose the actual dynamic read with close
and resource handoff, and carry the zero-owner-demand authority through all
runtime frames. General all-control mixed-admission/resource interpretation,
arbitrary evidence and result semantics, universe consistency, all specified
computation preservation and native refinement remain unfinished.


## 2026-11-15: guarded scalar handoff and sixteen-step checked composition

`NativeBindingMachineScalarReaderShape` proves source-derived scalar conversion
for Index and comparison-guarded Index under substitution and specialized read.
It is an auxiliary local classification; the complete Loan64 judgment, source
grammar and completion criteria are unchanged. Generic and specialized Lend
cases reconstruct the actual scalar finish without callback/output typing
premises. `NativeBindingMachineValueHandoff` now constructs canonical integer/
owner bindings, original closed result typing, heap-size and loan contexts and
the same zero/one resource correspondence for both cases. The previous direct-
Index public entry remains as a specialization.

`NativeBindingMachineDynamicReaderCompletion` starts from the actual resource
receipt and constructs sixteen transitions from the returned original reader
closure through captured-number comparison, physical reference read, close and
both continuation bindings. The intermediate global prefix and observed read
value are derived by run composition. The final body retains its exact closed
inferred source result type, canonical contexts, owner aliases, source loans
and outer reader inventory. The Free guard is characterized by those outer
readers, rather than assumed. A false comparison retains six-step original-
type else entry with the reference and reader inventory intact. No arbitrary
callback, numeric/output typing or intermediate-success certificate is supplied.

The aggregate passed 910 Lake jobs, 8,931 unique public audits and all fixture
comparisons (`out/logs/dynamic-reader-completion-full.log`), with the three
allowed logical axioms only and 3,690.2 MiB sampled peak RSS. No native
implementation, native fixture or dependency pin changed.

Next derive Free's guard for actual fresh-argument histories using allocation
provenance, then extend the common mixed-admission/control/resource invariant
to arbitrary captured owners and enclosing zero-demand readers. The reader
boundary's source/control/frame and owner-slot/size contexts still require
that global construction. Arbitrary evidence and result interpretation,
all-universe consistency, all specified computation preservation, complete
ownership/borrow soundness and native implementation refinement remain open.


## 2026-11-15: fresh checked dynamic reader release without a Free oracle

`NativeBindingMachineFreshDynamicRelease` derives the previously conditional
Free guard for an actual fresh-argument history. The reader owner is identified
with `nextObject` at an earlier actual call prefix with the same residual caller
stack. All-prefix saved-frame owner provenance proves that no frame in that
old stack can read the fresh identity, including dead captured aliases. The
constructed close/handoff inventory therefore excludes every remaining lease
of this owner. No no-reader, Unborrowed, Free guard or success certificate is
supplied by the caller.

For a true comparison, twenty actual transitions activate the captured-number
reference reader, perform the physical read, close it, bind both continuation
arguments, release through either the returned-owner slot or its old captured
alias, and return the observed I64 at the original closed inferred source type.
The owner is dead afterward; heap validity, outer reader inventory and all old
captured size interpretations are retained. The same original resource check
has zero residual owner demand on every remaining abstract resource prefix.
A false comparison still preserves six-step original-type else entry. The
explicit earlier birth/current-frame and source/value/size/loan associations
remain local inputs; they are not yet reconstructed for all mixed admissions.

The final aggregate passed 911 Lake jobs, 8,933 unique public axiom audits and
all generated-fixture comparisons (`out/logs/fresh-dynamic-release-full.log`).
All eleven new public proofs in this run are audited exactly once; dependencies
use only `propext`, `Classical.choice` and `Quot.sound`, with sampled peak RSS
3,689.8 MiB. No production compiler/runtime behavior, native fixture, dependency
lock or Nix store pin changed.

Next construct the all-control mixed-admission/resource authority invariant,
including the actual birth/current-frame and owner-slot associations used here.
For arbitrary pre-existing owners, transport each enclosing reader's zero-owner
budget across calls, closures, branches and restored aliases to exclude
consumption/re-lending and derive the general Free guard. The new fresh case
alone does not settle that general borrowed-owner conflict. General arbitrary
evidence/result semantics, all-universe consistency, all specified computation
preservation, full ownership/borrow soundness and native implementation
refinement remain unfinished. The whole-kernel goal is NOT complete; leave the
existing automation active.


## 2026-11-15: internal body resource receipts from original function checking

`NativeLoanRawResourceOrigins` recovers the exact internal body query from an
original full lambda resource projection. Internal Lend receipts retain original
read/restore scopes, full checker-derived source judgments and zero/one owner
contracts. The residual owner-demand proof is reconstructed from that same
internal receipt. These are internal query results, NOT a replacement admission
gate; mixed checking, scope/context guards and the complete source grammar
remain unchanged.

The checked dynamic reference reader, scalar handoff, dynamic completion and
fresh release proofs now have reusable internal-receipt variants. Their previous
full-query APIs remain specializations through the actual projector's origin
lemma. This lets the original function projection supply its body evidence;
a caller no longer needs to rerun or assume a separately successful full body
projection before composing allocation and reader entry. No output typing,
execution-success or arbitrary callback certificate is added.

The aggregate passed 912 Lake jobs, 8,941 unique public audits and all generated
fixture comparisons (`out/logs/function-resource-receipts-full.log`), with only
the three allowed logical axioms and 3,696.1 MiB sampled peak RSS. Rootless Nix
2.20.6, smoke evaluation 42 and the actual proof shell (Lean 4.34.1/Lake
5.0.0-src) were verified and reused under the shared guard. No native behavior,
fixture, dependency lock or store pin changed.

Next construct allocation, argument binding, Lend and reader-closure entry from
the actual pre-allocation prefix, deriving the birth/current-frame, owner-slot
and value/size/loan associations currently supplied at the reader boundary.
Then extend all-control authority to arbitrary old owners and enclosing readers.
The whole-kernel consistency, preservation, ownership/borrow and native-refinement
obligations remain unfinished.


## 2026-11-15: original function/allocation to dynamic reader release

`NativeBindingMachineAllocatedDynamicRelease` removes the previously supplied
body-recheck, birth/current-reader, owner-slot and reader-frame associations
for this actual fresh-call path. The original full function resource query
supplies its exact body receipt. The source allocation and pending function
judgments construct the owner binder and canonical value/size contexts. Ten
actual transitions allocate, bind, open named Lend and create the original
reader closure. Run composition constructs the real global prefix; source
loans, owner slot, fresh identity and precise continuation frame are all
outputs of that entry proof, not supplied post-state certificates.

Source bound evidence identifies the reader's captured length with the actual
allocation count. Thirty transitions then perform guarded reference read,
close, both continuation bindings, alias release and return the actual signed
fill. The integer has the original function signature's dependent instance at
the canonical allocation. Original argument provenance is retained and is NOT
assumed raw-convertible to that canonical value instance. False comparisons
have source-typed sixteen-step else entry; byte-size overflow has a five-step
fault. No selected numbers, successful allocation/read/Free, live-owner,
allocation snapshot or output-typing oracle is supplied.

`NativeBindingMachineAllocatedDynamicExamples` checks a closed complete Loan64/
resource admission with three scalar parameters and a genuinely dependent
Buffer/reader type. Initial scalar value/size contexts are constructed by the
proved entry rules. The actual eighteen-step caller prefix is computed; the
generic thirty-step proof derives the forty-eight-step release/return of I64
7. Final execution is not a supplied or directly computed output certificate.

The final aggregate passed 914 Lake jobs, 8,944 unique public audits and all
generated-fixture comparisons (`out/logs/allocated-dynamic-composition-full-final.log`).
All eleven public proofs added in this run are audited exactly once, using only
`propext`, `Classical.choice` and `Quot.sound`; sampled peak RSS was 3,701.7 MiB.
No native implementation, native fixture, dependency lock or store pin changed.

The source allocation/function typing and captured value/size/loan contexts at
the pending-call boundary are still local inputs. Next recover that boundary
and its exact function/body resource receipts from a single original call or
mixed-admission derivation, and carry authority across all saved frames and
closures. Arbitrary else/tail execution is not yet proved by this local path.
For pre-existing owners, transport enclosing zero-demand reader budgets to
exclude borrowed-owner consumption and derive the general Free guard. General
evidence/effectful result semantics, all-universe consistency, all specified
computation preservation, complete ownership/borrow soundness and native
implementation refinement remain unfinished. The whole-kernel goal is NOT
complete; leave the existing automation active.


## 2026-11-15: one original call judgment to actual fresh reader release

`NativeBindingMachineCallDynamicRelease` moves the entry boundary before call
preparation. Full Loan64 call inversion recovers the actual non-erased lambda,
its argument typing and the original dependent result conversion. The original
call's resource query supplies the exact function-body receipt through
`projectRaw_single_lambda_call_body`; neither a separate function query nor
independent function/argument typing is an input. The old full-function API
remains a specialization of the new internal-body variant.

Three constructed transitions evaluate the call head and install its actual
argument frame. Composition with allocation/binding/Lend/reader/release proves
thirty-three transitions to the actual fill, typed at the EXACT original closed
call type. It retains the fresh owner's dead state, valid heap, enclosing
reader inventory and alloc/beginLease/read/close/free heap trace. False
comparisons have source-typed nineteen-step else entry and byte-size overflow
has an eight-step fault. No pending-call frame, selected operands, successful
execution, output typing or raw conversion of effectful provenance is assumed.

The existing closed dependent example now uses a fifteen-step scalar-entry
prefix and this thirty-three-step semantic theorem. Its separate allocation
and owner-function checks and computed pending-call frame were removed. The
final forty-eight-step result remains derived, rather than computed directly.
Its whole closed admission and scalar entry checks are still separate local
proofs; this is not yet a general admission-to-execution simulation.

The final aggregate passed 915 Lake jobs, 8,948 unique public audits and all
generated-fixture comparisons (`out/logs/original-call-dynamic-release-full-final.log`).
All four added public proofs are audited exactly once, with only `propext`,
`Classical.choice` and `Quot.sound`; sampled peak tree RSS was 3,706.1 MiB.
The existing rootless Nix 2.20.6 proof shell (Lean 4.34.1/Lake 5.0.0-src) was
verified and reused under the shared guard. No native implementation, fixture,
dependency lock or store pin changed.

The call-boundary value/size/loan contexts, entered-loan invariant and source
call shape remain local inputs. Next derive these together with the original
call typing/resource receipt from a single complete mixed admission and carry
them through arbitrary saved frames and closures. The current result permits
arbitrary enclosing reader stacks but does not prove resource authority for
all old owners. Arbitrary else/tail execution, general evidence/effectful result
semantics, universe consistency, all specified computation preservation,
complete ownership/borrow soundness and native implementation refinement remain
unfinished. The whole-kernel goal is NOT complete; keep the automation active.


## 2026-11-15: original mixed admission constructs the complete scalar/call entry

`NativeBindingMachineMixedScalarEntry` retains the exact expanded-declaration
check and quantity fuel from the authentic `MixedProgram.checkDeclaration`.
For the existing three-scalar signature, its computational mode is computed by
the original checker. The original function judgment constructs all three
scalar closings, value/size contexts, empty source-loan associations and the
entered-loan invariant. Fifteen actual transitions install the bindings and
preserve the empty heap; the original lambda projections supply the exact
internal call resource receipt. The body remains arbitrary original syntax.
No independent scalar-entry or call check/context is supplied.

`NativeBindingMachineMixedDynamicRelease` composes this entry with the actual
allocation/read/close/alias-Free proof. One earlier mixed history and its real
next declaration check now derive the forty-eight-step signed-fill return at
I64, a dead fresh owner, closed lease, valid heap, reader inventory and the
alloc/beginLease/read/close/free trace. Literal argument ranges are explicit;
byte-size fit and index comparison remain alternatives, not success premises.
A false comparison reaches the original typed else code at thirty-four steps,
with a live owner, live lease and its exact reader inventory. Byte overflow
faults after twenty-three steps with the empty heap and no heap events.

The closed dependent example now uses this same mixed declaration admission;
its independent function typing, scalar context proofs and call recheck are
removed. The previous call API is retained through a raw internal-receipt
variant. The general theorem is parameterized by scalar values, source types,
reader/else syntax, physical owner alias, environment and authentic earlier
mixed history; it is not a directly computed output fixture.

The aggregate passed 917 Lake jobs, 8,953 unique public audits and all generated
fixture comparisons (`out/logs/mixed-admission-dynamic-release-full-1.log`). All
five added public proofs are audited exactly once with only `propext`,
`Classical.choice` and `Quot.sound`; sampled peak tree RSS was 3,707.2 MiB.
The existing rootless Nix 2.20.6 / Lean 4.34.1 / Lake 5.0.0-src proof shell was
verified and reused. No native implementation, fixture, dependency lock or
store pin changed.

This constructs admission-to-execution associations for this scalar/dependent
call path, not arbitrary controls. The declared three-scalar I64 signature is
a local theorem case, not a reduced grammar or completion criterion. General
mixed-admission authority across arbitrary saved frames, closures, dependent
functions/families/recursion, old-owner conflict exclusion, arbitrary else/tail
execution, evidence/effectful result semantics, universe consistency, full
preservation and native implementation refinement remain unfinished. Keep the
whole-kernel automation active. A useful next semantic step is finishing the
live-lease else path, followed by general all-control resource authority.


## 2026-11-15: original literal else closes its lease and releases the fresh owner

`NativeBindingMachineLiteralElseRelease` completes both outcomes of the
original guarded fresh reference reader when its else body is an integer
literal. The failed comparison's source judgment derives the literal's signed
range. Six transitions enter that original else code, one evaluates the
literal, five close the lease and bind the continuation, and four release
either physical owner alias and return the literal at the original inferred
Lend result type. The true branch retains its twenty-step actual payload read.
Both outcomes preserve valid heap and exact enclosing reader inventory and
prove the fresh owner dead. The original source/resource receipt and earlier
actual frame provenance derive the Free guard; no literal bound, selected
branch, no-reader premise or successful suffix is supplied by the caller.

The aggregate passed 918 Lake jobs, 8,955 unique public audits and all generated
fixture comparisons (`out/logs/fresh-literal-else-release-full.log`), with only
the three allowed logical axioms and 3,707.6 MiB sampled peak RSS. The shared
four-step alias-release lemma is now public for composition and audited; the
new both-outcome theorem is audited too. No native code, fixture, dependency
lock or store pin changed.

The literal-else result is currently at the reachable fresh reader boundary,
whose associations are constructed by the existing allocation/call proofs.
Next compose this both-outcome suffix through those entries to remove the
remaining live-lease else entry for mixed-admitted literal-fallback calls.
Arbitrary else bodies, old-owner reader conflict exclusion, all-control mixed
resource authority, universe consistency, full preservation and native
implementation refinement remain open. The whole-kernel goal is NOT complete.


## 2026-11-15: mixed-admitted literal fallback completes both index outcomes

`NativeBindingMachineAllocatedLiteralRelease` and
`NativeBindingMachineCallLiteralRelease` compose the both-outcome reader suffix
through the actual allocation and original full call. The allocation boundary
now has thirty-step read/return or twenty-six-step literal/return; the original
call has thirty-three or twenty-nine steps. Both release the fresh owner,
retain enclosing reader inventory, prove heap validity and derive the actual
value at the original signature instance/full call type. The shared call and
Lend entry lemmas are public and audited; no successful intermediate suffix or
output typing is supplied.

`ScalarCalls.admitted_program_typed` reconstructs the complete original Loan64
runtime judgment for the actual closed caller from the same admitted function
and literal scalar arguments. `ScalarCalls.admitted_literal_release` includes
this input judgment and composes every entry/suffix. One authentic earlier
mixed history and its next declaration check derive an I64 runtime-typed
return after forty-eight steps when the index is in range, or after forty-four
steps for the original fallback literal when it is out of range. The fallback's
range is derived from source typing, not a premise. Both prove the fresh owner
dead, lease closed, valid heap, no remaining reader inventory and exact heap
trace, with a read event only on the successful comparison. Byte overflow
retains its twenty-three-step fault with the empty heap and no heap events.
No comparison outcome, byte fit, context, local call check, bound/allocation
snapshot, fallback bound, output typing or execution-success oracle is supplied.

The existing closed dependent example now instantiates this both-outcome mixed
admission theorem. Its returned value remains derived rather than directly
computed. The final aggregate passed 921 Lake jobs, 8,961 unique public audits
and all generated-fixture comparisons
(`out/logs/mixed-literal-release-full-final-3.log`), with only `propext`,
`Classical.choice` and `Quot.sound`; sampled peak tree RSS was 3,711.3 MiB.
All six newly public proofs in this composition are audited exactly once.
No native implementation, native fixture, dependency lock or store pin changed.

This completes the literal-fallback branch for the local parameterized scalar/
dependent-call path. It does not complete the kernel's grammar or whole-kernel
obligations. Next transport the same admission/resource authority through
arbitrary saved frames and closures, extend old-owner conflicts using enclosing
zero-demand budgets, and handle arbitrary else/tail computation. Full ownership/
borrow soundness from the same complete judgment, evidence/effectful result
semantics, all-universe consistency, all specified computation preservation and
native implementation refinement remain unfinished. Keep the automation active.


## 2026-11-15: enclosing-reader budgets derive old-owner release guards

`NativeLoanBorrowedBudget` defines zero ownership demand for every active
source loan. The authentic original Lend receipt derives its owner's one-use
demand and therefore excludes lending an already active owner under that
budget. It constructs budgets for the entered reader and restored continuation,
including every enclosing loan. Budgets pass through sequences, either branch,
ordinary scopes and original single-lambda call opening. A checked variable
Free is inactive under the same budget. After either restored physical owner
alias is consumed, the actual recursive tail receipt retains all enclosing
zero budgets and the consumed owner's zero residual demand.

`NativeBindingMachineLoanCoverage` supplies the converse of the existing
`LoanSlots`: a retained owner with an actual enclosing reader has a source loan.
It is an association invariant, not a Free guard or success certificate. Empty
stacks, non-owner bindings, same-reader administrative frames and fresh owner
entry construct it. Actual allocation provenance constructs owner-slot
separation; distinct owner slots permit named reader entry. The converse is
not yet preserved for every arbitrary call or unused duplicate alias.

`NativeBindingMachineBudgetedRelease` combines those original source budgets
with the converse association. Nine actual transitions close the lease, bind
both aliases, Free an arbitrary OLD owner and return the actual scalar at the
original source result type. Liveness comes from the reachable reader inventory;
quantity inactivity and physical/source coverage exclude all outer readers of
that owner. No fresh identity, birth prefix, no-reader/Free-success premise or
output typing is supplied. Value-size information, both loan directions, valid
heap, exact outer inventory and all enclosing source tail budgets are retained.

`NativeBindingMachineBudgetedReaders` constructs the read itself before that
suffix. Actual source/resource typing derives captured numbers, physical size,
Index bounds and the returned value. Both guarded outcomes now take twenty
read/close/Free or sixteen literal/close/Free transitions for an arbitrary old
owner under those entry invariants; literal range is derived. This generalizes
the fresh-only guard argument. `checked_mixed_loan_authority` initializes the
source/value/size/loan associations, distinct owner slots and exact full resource
receipt from the same actual mixed declaration admission, for the full syntax.

The aggregate passed 926 Lake jobs, 8,985 unique public audits and all generated
fixture comparisons (`out/logs/borrowed-reader-authority-full.log`). All 24 new
public proofs are audited exactly once with only `propext`, `Classical.choice`
and `Quot.sound`; sampled peak tree RSS was 3,717.3 MiB. Rootless Nix 2.20.6 and
the actual Lean 4.34.1/Lake 5.0.0-src proof shell were verified and reused under
the unchanged shared guard. No native implementation, fixture, dependency lock
or store pin changed.

This is a conditional generalization of operation preconditions, not a completed
mixed-admission fundamental theorem. LoanBudget and LoanCoverage are constructed
initially and through the proved entry cases, but their association with every
later original control/frame remains open. In particular, LoanCoverage over ALL
retained owner aliases is too strong after some aliasing reborrows: canonical
resource-index substitution must account for unused aliases rather than assume
physical slot injectivity universally. Next transport resource-aware reader
budgets through those alias maps and arbitrary saved closures/frames. General
else/tail execution, complete ownership/borrow soundness, all-universe
consistency, full specified preservation and native implementation refinement
remain unfinished. The whole-kernel goal is NOT complete; keep the automation.


## 2026-11-15: canonical retained aliases and original continuation CODE authority

The cloud machine was replaced during this run, losing the checkout, Nix store
and build cache. The pushed `625af6f` branch was cloned from GitHub and the
rootless-Nix skill installer restored `/workspace/.local/bin/nix-rootless`.
Nix 2.20.6 / smoke evaluation 42 and the actual pinned Lean 4.34.1 / Lake
5.0.0-src proof shell were verified. The original flake lock was retained.

`NativeBindingMachineCanonicalView` connects actual retained code to canonical
source code with a possibly non-injective index map. It preserves exact origins
and stored values, composes earlier alias layers, lifts through binders, and
constructs both owner aliases' `openOwner` view from the actual bindings. This
is source-variable identification, not conversion of effectful provenance to a
runtime value. Canonical source authority derives the physical Free guard of
an actual alias without separate source loans for all duplicated runtime slots.

`NativeBindingMachineCanonicalHandoff` constructs the canonical continuation's
CODE judgment at the ORIGINAL input result type, value/size/loan contexts and
exact recursive resource budget from one original Lend query. Five actual
transitions close and install the two runtime bindings. The source view retains
one scalar-result binder, and its coverage/loan budget is constructed from the
old source context. No current loan permission for every unused runtime alias,
rechecked canonical body or caller-provided continuation/output typing is used.
The original checked restore supplies local CODE typing; actual scalar range
comes from the reachable prefix, and type uniqueness retains the input type.

`NativeLoanScalarFreeAliases` derives which returned-owner alias is consumed
from the original restored one-use quantity contract. It removes the previously
supplied alias-selection premise for this scalar-return shape.
`NativeBindingMachineCanonicalRelease` uses the constructed canonical authority
at the real Free boundary. Nine transitions close/bind/Free/return at the original
runtime result type, preserving valid heap, outer inventory, canonical source
tail CODE typing, alias view and all old zero budgets plus zero residual owner
demand. Neither an alias choice, Free-success/no-reader certificate nor output
typing is supplied. Physical liveness comes from the actual closing reader.

The new target build passed 309 Lake jobs with warnings as errors
(`out/logs/canonical-release-local-5.log`, 1,103.1 MiB sampled peak RSS).
The subsequent cold aggregate passed 930 Lake jobs, 8,996 unique public audits
and all generated-fixture comparisons (`out/logs/canonical-authority-full-final.log`),
with only the three allowed logical axioms and 3,828.2 MiB sampled peak RSS.
No native implementation, native fixture, dependency lock or store pin changed.

This removes the duplicated-slot coverage requirement at the canonical
continuation boundary; it is not an all-control fundamental theorem. General
preservation of canonical views and resource authority across arbitrary saved
closures, computed calls, reader entry and dependent computation remains open,
as do general else/tail execution, complete ownership/borrow soundness,
all-universe consistency, full specified preservation and native implementation
refinement. Keep the automation active; the whole-kernel goal is NOT complete.


## 2026-11-15: canonical variable steps and a confirmed alias-reborrow blocker

`NativeBindingMachineCanonicalVariables` constructs canonical single-binder
slot readiness from the actual saved reader-continuation frame. Original
canonical CODE variable typing and value context then select an actual stored
runtime value through any composed alias map. Actual integer/natural lookups,
canonical meanings, source-derived numeric ranges and runtime-mode literal
typing are outputs; no stored value, successful lookup or output-typing oracle
is supplied. This is a source-to-actual-machine variable step, not a claim of
reference lifetime or general heap/value realization.

A concrete NEW BLOCKER is now proved in
`NativeBindingMachineAliasReborrowBoundary`. `source_admitted` proves that the
closed I64 program is accepted by the authentic complete
`MixedProgram.checkDeclaration 256 512` in the empty earlier environment.
`runtime_alias_fault` proves that the actual binding-retaining run observes
`inactiveBorrow`. The program allocates one Buffer, reads/closes a first Lend,
then lends the returned owner alias and reads via Borrow of the older captured
alias. Source restore correctly identifies the owner slots. The runtime instead
records the second reader under lexical key 3 and looks up Borrow of the older
alias under key 1; the earlier reader is already closed. This is a current
Lean runtime-model progress/precondition blocker, NOT evidence of a native
compiler failure or logical inconsistency.

The final aggregate passed 932 Lake jobs, 9,002 unique public audits and all
generated-fixture comparisons
(`out/logs/canonical-lookups-boundary-full-final.log`), using only `propext`,
`Classical.choice` and `Quot.sound`; sampled peak tree RSS was 3,858.3 MiB.
The six additional public proofs, including both counterexample facts, are
audited exactly once. The complete lost build cache was reconstructed under
the shared guard. No native implementation, fixture, dependency lock or store
pin changed. Passing this aggregate does NOT discharge the blocker.

NEXT PRIORITY: repair the binding-retaining Borrow/reader-name correspondence
for returned owner aliases. Inspect `NativeBindingMachine.evaluateAction`'s
Borrow key, `execute`/`activeLease`, and the source alias map/loan-slot invariant.
Preserve this accepted program and its admission proof; after a justified
semantic repair, replace the fault fact with a proved successful scalar return.
Do not reject the source program, add a guard/output oracle, or weaken the
completion criterion to avoid it. Recheck reader inventory, numeric/provenance
invariants and all existing source/runtime compositions when the model changes.
Then continue general canonical control/frame/closure preservation, arbitrary
else/tail computation, complete ownership/borrow soundness, universe consistency,
full specified preservation and native implementation refinement. The whole-
kernel goal is NOT complete; keep the automation active.

## 2026-11-16: repair scoped owner-alias reborrowing

The accepted `AliasReborrowBoundary` program retains its complete mixed
admission. Its runtime fact now proves scalar return 7 instead of
`inactiveBorrow`, with exact alloc/read/close/free events, the released owner
and no outstanding leases. The binding machine preserves the existing
exact-name lookup first, then resolves a retained alias through an enclosing
named reader of the same concrete object. It does not consult heap-global
leases or anonymous readers for this fallback.

`NativeBindingMachineAliasLoans` proves lookup soundness/completeness, exact
lexical-token preference and rejection without an enclosing named reader.
Actual reachable owner slots plus an enclosing reader under any lexical name
construct the next Borrow step and derive the live lease and owner liveness.
No successful execution or returned-value interpretation is an input.

The local builds passed with warnings as errors (308 Lake jobs in each
dependency closure), including the repaired admission/execution regression
and the existing canonical variable path. All 15 declarations in the new
lookup module and repaired regression passed an elaborated dependency audit
using only the allowed standard logical axioms. Logs are
`out/logs/alias-baseline.log`, `out/logs/alias-repair-local.log` and
`out/logs/alias-repair-audit.log`. The aggregate audit target is now 9,015;
the full aggregate recheck remains pending at this checkpoint.

The pinned Nix proof shell runs directly on `/home/user/jihoo` with Lean
4.34.1. Every compiler/check ran through `scripts/proof-limits.sh` with the
unchanged memory limits and single-thread configuration. No native compiler,
fixture, dependency pin or runtime heap representation changed.

This resolves the concrete immediate-Borrow model blocker, not general
lifetime preservation. Source Lend's Outlived gate rejects reader results
that are references or closures; the semantic theorem excluding the closing
token from every returned value/capture is still missing. Next connect
canonical source loans to physical scoped owner slots through aliases,
binders and reader entry, and recheck the entire aggregate. General
source/control/resource/value preservation and all original whole-kernel
completion obligations remain open.

## 2026-11-16: canonical source loans and physical reader authority

`NativeBindingMachineCanonicalBorrow` introduces `OwnerLoanSlots`, associating
each active source owner with its actual stored object and an enclosing named
reader without equating canonical and runtime lexical keys. Existing LoanSlots
construct it. Initial code, child code, ordinary erased/runtime binders,
noninjective alias rebasing and reader entry/body transport it. In particular,
a new reader's runtime name may differ from its canonical source owner's key.

Canonical source Borrow typing now constructs the actual slot, live lease and
next machine step through an arbitrary CanonicalView. Canonical immutable owner
sizes additionally construct ReferenceSize at the ORIGINAL closed requested
type. No actual lexical LoanSlots, name-equality, selected owner/token, successful
lookup or output interpretation certificate is an input. The nine new public
theorems passed a 310-job local target build with warnings as errors in
`out/logs/canonical-borrow-local-2.log`.

This remains a local association, not full stack preservation. In particular
arbitrary captured closures, computed calls, reader returns and resource/size
contexts still need a common semantic interpretation. Existence of some
same-object reader does not by itself identify the source reader that must
survive a later close. Preserve the source Outlived restriction and prove the
missing all-value/all-control lifetime bridge rather than assuming it.

The complete aggregate recheck passed 934 Lake jobs, 9,024 distinct public
axiom audits and all generated-fixture comparisons in
`out/logs/alias-canonical-full.log`. Only `propext`, `Classical.choice` and
`Quot.sound` occur. This also completes the full recheck pending at the first
alias-repair checkpoint. No production compiler or native fixture changed;
the existing native correspondence evidence is unchanged, not a new native
implementation-refinement result.

## 2026-11-16: canonical alias Index execution from source evidence

`NativeBindingMachineCanonicalIndex.reachable_canonical_index` derives an
actual five-transition read through an arbitrary retained owner alias from
the complete source Index judgment, canonical owner sizes and OwnerLoanSlots.
Source literal-Decide evidence supplies both U64 bounds, the strict comparison
and the exact physical allocation length. Reachability derives the selected
lease's liveness and actual heap payload width. The resulting integer has the
ORIGINAL requested closed type in runtime mode. No selected owner/token,
alias-key equality, allocation snapshot, numerical read guard, successful run
or output typing is an input. Noninjective alias maps are supported.

The target passed 311 Lake jobs with warnings as errors in
`out/logs/canonical-index-local-2.log`. The original helper's rewriting of the
pending Index frame needed normalization of Code.child before simplification;
no memory limits, runtime behavior or theorem premises were changed to fix it.
General computed index/evidence interpretation and all-control preservation of
source, sizes, resources and scoped owner authority remain unfinished.

The complete aggregate passed 935 Lake jobs, 9,025 distinct public axiom audits
and all generated-fixture comparisons in `out/logs/canonical-index-full.log`.
Only the three allowed standard logical axioms occur. No native implementation
or native fixture changed. This extends the local canonical typing-to-runtime
bridge; it does not complete general ownership/borrow soundness, universe
consistency, specified preservation or native refinement.

## 2026-11-16: captured dynamic canonical Index and typed else entry

`NativeBindingMachineCanonicalDynamicIndex.reachable_canonical_dynamic_index`
extends canonical owner-alias execution to actual captured IfLt index/length
comparisons. Complete source CODE typing, source slot alignment and value
meanings construct the actual scalar slots and widths. A true comparison
constructs the erased source proof, identifies physical owner length from
canonical size realization, selects an enclosing same-object live reader and
performs ten transitions with the exact read event. The resulting integer has
the ORIGINAL requested closed type in runtime mode. The false comparison
performs five transitions into the original actual else body and retains its
canonical original-type judgment, value/size/loan contexts, alignment and alias
view. Noninjective index maps and differing source/runtime keys are supported.
No numerical guard, selected scalar/owner/token, actual-code LoanSlots,
successful run or output-typing certificate is supplied.

The target passed 312 Lake jobs on its first build with warnings as errors
(`out/logs/canonical-dynamic-index-local.log`). The complete aggregate then
passed 936 Lake jobs, 9,026 distinct public audits and every generated-fixture
comparison (`out/logs/canonical-dynamic-index-full.log`). Only the three
allowed logical axioms occur. All compiler/checker jobs used the unchanged
shared resource wrapper and pinned Nix proof shell. No production compiler,
native fixture, dependency pin or memory limit changed.

This is local progress from canonical source entry invariants, not a general
closed-admission/control-stack fundamental theorem. Next carry the source
owner/value/size/resource and reader-lifetime associations through arbitrary
saved closures, computed calls and reader returns, and cover arbitrary
computed index/count terms and Lt evidence. General else/tail evaluation,
complete ownership/borrow soundness, all-universe consistency, full specified
preservation and native implementation refinement remain open. The whole-
kernel verification goal is NOT complete.

## 2026-11-16: ordered reader authority and source-derived nonescaping close

`NativeBindingMachineLoanScope` pairs SOURCE LOAN OCCURRENCES positionally with
concrete ordered reader identities. Equal source frames and noninjective alias
rebasing retain distinct occurrences. Initial, child, binder, reader entry/body
and canonical transport construct the association. Pop/finish remove source and
runtime heads together and derive outer authority, distinct surviving tokens and
their live leases from the actual reader inventory. This projects to the older
OwnerLoanSlots interface without requiring a post-close authority certificate.

`NativeBindingMachineReferenceProvenance` proves strict reference-token bounds
through actual values, recursively captured closures, source Code, every frame
and control state across ALL execution prefixes, including faults/fuel. Reader
and Index descriptor tokens are included. Fresh reader tokens cannot occur in
previously captured values or saved outer frames. This is provenance, not
current reference liveness. The module imports ReaderState so its generated
Lean evaluateAction case helpers share the established dependency chain.

`NativeBindingMachineReaderCaptures` preserves a stronger birth snapshot for
each reader: its saved continuation and complete stack tail retain reference
tokens strictly older than its own token. These bounds hold unconditionally
at every reachable prefix. They exclude the closing token from saved captures,
but deliberately say nothing about the current reader result by themselves.

`NativeBindingMachineOutlivedValues` proves that the current ValueKind relation
cannot realize Outlived with a reference, closure or type code. The full
original Lend judgment derives Outlived for the actual first continuation
domain after source value closing. `NativeBindingMachineOutlivedReferences`
then uses canonical source VARIABLE typing to select a real result and perform
the actual two-transition return/close. The token is closed in the heap and
absent from the entire resulting runtime control and stack, including every
recursive capture. No supplied result value/kind, successful close, post-state
interpretation or no-token oracle is an input to this source-to-execution result.

All five target modules passed with warnings as errors. The complete aggregate
passed 941 Lake jobs, 9,109 distinct public audits and every generated-fixture
comparison (`out/logs/loan-lifetime-foundations-full.log`). All 83 additional
public theorems are audited exactly once with only `propext`, `Classical.choice`
and `Quot.sound`. Every compiler/check used the unchanged resource wrapper,
single-thread settings and pinned Nix proof shell. No production compiler,
fixture, dependency pin or memory limit changed.

This does not supply the common all-control semantic interpretation: source
LoanScope/value/size/resource authority through arbitrary saved closures/calls
and arbitrary reader results is still open. The no-escape result currently
constructs the final VARIABLE return; it does not assume and then claim that
ValueKind is preserved for every reader computation. Next generalize original-
type continuation entry beyond the existing scalar-only handoff using actual
source-variable results, then connect these relations through full captured
closures and arbitrary source computation. All original consistency,
specified preservation, complete ownership/borrow soundness and native
refinement obligations remain unfinished. Keep the active goal running.

## 2026-11-16: arbitrary interpreted variable-result continuation entry

`NativeBindingMachineVariableHandoff.reachable_canonical_variable_handoff`
constructs the actual six-step variable return, close and two retained
continuation bindings from the full original Lend/resource query. It preserves
canonical CODE at the ORIGINAL requested Lend result type, actual value/size
contexts, ordered outer LoanScope, reader inventory and absence of the closed
token from the complete resulting runtime state. The private ghost finish
proof accepts the source variable's derived checked meaning: observed scalars
retain their numeral, while owners retain their checked source expression and
physical allocation size. No physical-owner literal, returned-value typing,
successful run or injected alias choice is supplied.

The target passed 316 Lake jobs on its first build with warnings as errors.
The aggregate passed 942 jobs, 9,110 distinct audits and all generated fixture
comparisons (`out/logs/variable-handoff-full.log`), with only the three allowed
logical axioms and unchanged resource limits. No production/native fixture
or dependency pin changed.

Owned-result converse LoanCoverage/exclusive accounting is still missing;
an added owned binder may physically alias an outer borrowed object unless
the actual returned source slot is connected to resource/control preservation.
Do not silently assume it fresh or use enter_nonowner for that binder. The
current head-only ValueKind also cannot model rigid Refine, Back, Array or
family result heads: a richer value/heap interpretation is needed for those
accepted constructors, not a restriction of the source language.

Next compose existing canonical source views through ACTUAL saved Lend frames:
the current handoff still identifies its original Code with the actual saved
snapshot, which prevents direct use after arbitrary earlier alias layers.
Keep the active goal running. All original completion obligations remain open.

## 2026-11-16: compose canonical views through actual saved Lend frames

`NativeBindingMachineCanonicalFrameHandoff` removes the original-Code-equals-
actual-snapshot restriction. The actual saved continuation has an arbitrary
prior CanonicalView into its source snapshot. Both real bindings lift that
view, and source owner restoration composes the resulting index map; neither
layer is required to be injective. Actual raw lambda annotations, bodies and
captured values drive all six transitions, while original source Lend/resource
typing constructs original-type canonical CODE and value/size/ordered-loan
contexts. No actual-snapshot source typing, reader-key equality, selected
result, successful run or output interpretation is supplied. Closed-token
absence follows from the actual reader snapshot and source-derived result.

The target passed 317 Lake jobs after normalizing the source owner provenance
in the two view witnesses. The complete aggregate passed 943 jobs, 9,112
distinct public audits and all generated fixtures
(`out/logs/canonical-frame-handoff-full.log`), using only the standard allowed
axioms and unchanged resource guard. No native implementation or fixture changed.

The next reader-entry bridge must distinguish the runtime/reference-binder
source view from the specialized original-context read typed by the checker.
Do not assert generic CODE typing of a raw callback body: admitted specialized
readers can depend on the actual Borrow argument. General owned-result
coverage/exclusivity, full control/value interpretation and all original
whole-kernel completion obligations remain open. Keep the active goal running.

## 2026-11-16: reconstruct higher-kind codes from actual Loan64 admission

`NativeLoanHigherKindSource` reuses the ENTIRE existing HigherKinds.Recognized
grammar, intrinsic Expression and concrete finite denotation. It reconstructs
them from the authentic LoanTyping.HasType judgment using genuine RawLend
conversion, rather than asking for an earlier Environment.HasType derivation
or an old-conversion witness. Raw kind validity/injectivity/classification
support source principal reconstruction under arbitrary loan stacks and source
prefix frames. Mixed histories and actual checkDeclaration acceptance supply
closed derivations at the exact expanded annotation. No semantic candidate,
normal form or output-realization certificate is supplied.

The native source universe rule requires n < 32 (compiler/core.jh and the full
Loan64 univ rule agree). Existing finite levels include the required
administrative successors; the remaining consistency gap is source-to-model
reconstruction for arbitrary annotations/computation, not an absent infinite
universe hierarchy. Recognized is deliberately still an explicit premise.

The target passed 229 jobs after adapting the mutually defined Loan64 recursor
arity and using its full PrincipalView for Pi formation. The complete aggregate
passed 944 Lake jobs, 9,124 distinct audits and all generated fixture comparisons
(`out/logs/loan-higher-kind-full.log`), using only the three standard logical
axioms under unchanged resource limits. No native implementation, fixture or
dependency pin changed.

Next reconstruct the semantic substitution itself from an actual Loan64 ghost
substitution on this source grammar, with syntax/denotation coherence, rather
than accepting an arbitrary semantic substitution certificate. General
dependent annotation interpretation/coherence, arbitrary proof consistency,
full specified preservation, runtime fundamental preservation and native
refinement remain open. Keep the active goal running.

## 2026-11-16: completed reference-world and typed-substitution checkpoint

The user requested completing only the current work and pausing. This
checkpoint finishes five modules and records the remaining obligations for
resumption; it does not complete the whole-kernel proof.

`NativeBindingMachineCanonicalReaderEntry` constructs actual reader activation
under distinct actual and canonical snapshots. It retains the reference-binder
ghost view and the specialized original-context CODE read as separate source
judgments. Raw specialized callback bodies need not have generic CODE typing.

`NativeBindingMachineCanonicalCaptures` strengthens CanonicalView with an
ordered sublist of actual retained captures. Recursive reference bounds then
transport to the canonical snapshot, including after composed owner restoration.
A proved counterexample shows why a plain alias view alone cannot transport
all source capture bounds: unused phantom source slots may lie outside its map.

`NativeBindingMachineReferenceSizes` relates every stored Buffer reference to
its live physical lease, length and original closed source type. Actual reader
entry constructs that relation and the stronger captured view from the original
Lend judgment, source owner sizes and actual reader inventory. Close transport
uses actual saved snapshots rather than a caller-supplied source token bound.

`NativeBindingMachineReaderLeaseWorld` proves that an enclosing reader protects
older lease slots through arbitrary actual execution intervals, including nested
readers and partial/fault prefixes. Fresh-token monotonicity and expiration
exclude closing and reopening the enclosing reader. The saved-reference interval
theorem derives endpoint reference liveness, length and post-close reference
contexts from entry relations and actual frame shapes.

`NativeLoanHigherKindSubstitution` reconstructs intrinsic replacements from an
actual Loan64 ghost substitution over the existing complete Recognized grammar.
Its valuation map is induced by those replacements. The source theorem supplies
exact substituted syntax, denotation coherence, genuine substituted HasType and
original-kind conversion, without a semantic substitution certificate.

The final aggregate passed 949 Lake jobs, 9,156 distinct public declaration
audits and all generated fixture comparisons
(`out/logs/reader-world-and-substitution-full.log`). The five modules add 32
audited public theorems. Only the three allowed logical axioms occur. All checks
used the unchanged resource wrapper, Lean memory/thread limits and Nix shell.
No native implementation, native fixture, dependency pin or resource limit changed.

After committing and pushing this checkpoint, pause the active goal as requested.
On resumption, connect richer source/control specialization through saved frames
and use the interval theorem where endpoint liveness was previously supplied.
Derive owned-result coverage and exclusive resources from actual source receipts.
A richer value/heap relation must interpret accepted Refine, Back, Array and
family values. Arbitrary dependent annotation interpretation, general logical
consistency, complete specified preservation, runtime fundamental preservation
and native implementation refinement all remain open.

## 2026-11-18: preserve saved references through canonical variable handoff

`reachable_reader_finish_snapshot` derives the saved continuation and exact
outer stack at the finish from a reader entry and finish with the same token.
Fresh-token monotonicity and lease expiration ensure that intermediate steps
preserve the snapshot.

`NativeBindingMachineReferenceHandoff` composes the reader interval with the
six actual transitions that close a reader and enter its continuation with a
variable result and the restored owner. The saved owner sizes and Buffer
reference context come from reader entry. The live reference context, capture
coverage, original-type CODE typing, and remaining loan scope follow for the
resulting canonical continuation. Source `Outlived` excludes a reference in the
new result slot.

The local aggregate passed 950 Lake jobs, 9,158 axiom checks and all generated
fixture comparisons under the resource wrapper. The native mixed-program suite
passed 68 source fixtures and 54 exact-byte checks, including the returned-owner
alias reborrow.

## 2026-11-18: Loan64 computation, captured-owner transfer, and machine boundaries

`NativeLoanComputationPreservation` preserves the original Loan64 type across
all `ACU.Computes` roots and arithmetic equations, and composes them with typed
family and Lend reduction. It also proves the five pure value-contraction roots
and the dependent Take/Give endpoint. The pure value and Take/Give endpoints are
root theorems. The contextual relation uses the reduction rules that supply a
raw conversion.

`NativeLoanProofConsistency` reconstructs truth from authentic Loan64 typing
and mixed-history global declarations for its recognized proof syntax. For
that syntax, a closed derivation of `Lt(0,0)` is impossible even with genuine
raw conversion. General proof elimination and iteration are still open.

`NativeBindingMachineCapturedOwnerHandoff` derives the seven real transitions
for a named reader returning a captured Buffer variable. The original source
receipt transfers the unit of demand to the continuation result slot,
preserves exclusive demand for the other owners, and keeps older aliases at
zero demand for that allocation. It preserves converse loan coverage under
the entry coverage premise. This proof needs the saved resource and control
invariants at reader activation.

The native `Core.transform` checks widened variable shifts and binder cutoff
increments before narrowing. `NativeTransformMachine` proves the scalar
variable and cutoff operations against the partial renaming model.
`NativeWireMachine` proves the fixed-width token, vector and signed integer
encoding operations, including `Int64.minValue`. Complete graph traversal,
parser and checker execution refinement are still open.

The aggregate check passed 955 Lake jobs, 9,184 axiom checks and 12 fixture
comparisons. The native kernel suite passed 89 native fixtures, 31 additional
checks, 162 exact writer comparisons and 665 actual Core transformations.

## 2026-11-18: transparent globals, affine evidence, and buffer operations

`NativeLoanEnvironmentExtension` preserves the full 64-rule Loan64 judgment
under environment extension. `NativeLoanDeltaPreservation` recovers the body
from the original mixed declaration history and composes transparent unfolding
with the typed computation rules at the original type.

`NativeLoanArithmeticProofConsistency` interprets Loan64 `ZeroLe`, `LtAdd`,
`LtCancel`, `LtLe` and `Decide` over supported affine evidence. Its checked
example unfolds a checked global and cancels through an intermediate sum of
`2^64`. Transparent global unfolding and contextual computation can connect a
checked global to its supported residual proof. Arbitrary dependent
elimination and induction still need a semantic or typed-normalization theorem.

`NativeBindingMachineBufferStore` specifies executable indexed-heap writes and
lease reads. A checked literal Store obtains its physical bounds from source
typing and OwnerSizes and excludes active readers through the original loan
budget and coverage. A write retains metadata and every other cell, including
all existing leased observations. The whole binding machine still needs Store
control frames. An isolated Lean check confirms that the mixed checker admits
`Free(Store(Alloc(1, 0), 0, 7, Decide(0, 1)), 0)` and the current binding machine
reports `unsupported` for it.

`NativeLoanLoadPreservation` obtains the complete Load continuation telescope
from source typing. An observed signed I64 and the unchanged owner instantiate
both binders, preserving the original type of the specialized body. Physical
load observations still need the runtime control invariant.

The aggregate check passed 960 Lake jobs, 9,206 declaration audits, and all
generated fixture comparisons under the resource wrapper. The audits report
only `propext`, `Quot.sound`, and `Classical.choice`.

## 2026-11-18: executable Store, CODE renaming, and proof evaluation

`NativeBindingMachineMutable` executes Store by evaluating its owner, index,
and value in order. The mutable heap supplies indexed contents for both
writes and leased reads. Borrow sees the enclosing frames saved while Store
evaluates an operand. Every finite prefix preserves heap validity and the
exact inventory of active readers. A named-owner literal Store with the
source typing, quantity receipt, and owner world constructs seven actual
transitions and preserves all existing lease reads. Checked examples execute
distinct writes and reads within one buffer and an outer Borrow while a
different buffer's write is pending. `NativeBindingMachineMutableCompatibility`
embeds uniform contents and proves exact agreement with every old execution
prefix that has yet to select Store, including states and events on faults.

`NativeLoanCodeBetaBoundary` gives a checked counterexample to arbitrary
raw CODE beta. Substituting an allocation for an owner variable makes the
chosen Borrow untypable in CODE. The retained binding executes the original
program. `NativeLoanCodeRenaming` preserves all Loan64 rules in their original
mode under context and loan transport, including canonical alias rebasing and
opening a binder with a matching variable.

`NativeLoanProofLoopUnrolling` constructs typed finite applications of a
checked proof Loop's base and induction step at its original dependent type.
`NativeLoanProofNormalization` runs bounded typed computation, delta, and
family elimination. A mixed admitted indexed recursive proposition is
eliminated by using its induction hypothesis and reaching actual `Decide`
evidence. `NativeLoanProofLoopObservation` normalizes the unrolling at the
original dependent type, including a computed count and actual erased
induction hypothesis. The residual truth theorems require supported outcomes.
`NativeLoanProofObservation` checks that residual syntax in the executable
observer. Its successful observation of a stored global supplies all of the
reduction, typing, and arithmetic recognition needed to rule out `Lt(_,0)`.
General typed normalization and consistency remain open.

`NativeCoreGraph` models the native arena cap, first failing ordered reference,
and cached suffix check. The snapshot writer and `Core.extend` now use the
same `Core.children` extraction. `NativeCoreGraphWire` proves that parsing
those version-6 writer words preserves the graph scan result at any prefix
position. A successful exact-byte Loan64 check implies the observed reference
scan passes. Validated prefix immutability, generated nodes, and the actual
native scan and inference execution still need refinement.

The aggregate passed 970 Lake jobs, 9,269 declaration audits, and all generated
fixture comparisons under the resource wrapper. Native checks matched 162
writer rows with distinct high `UInt32` references, 665 Core transformations,
89 source fixtures, and 31 additional checks.

A direct production Core API probe checked a one-node arena, replaced the
public node with a self-reference, then ran both check paths. `Core.extend`
accepted the changed cached prefix. `Core.check` rejected it. The actual
implementation must enforce immutability of the cached prefix and account for
nodes generated during inference before using the proved suffix-scan rule.

## 2026-11-18: incremental Core cache, indexed Load, and nested proof observation

The production Core stores the node, definition, and family vectors privately.
Read APIs return detached terms and declarations or scalar metadata. A change
to constructors of a checked family invalidates the declaration cursors.
`Core.extend` checks both the input suffix and the suffix created by inference,
uses pure conversion, and commits all cursors only after both scans and
declaration checking succeed. On failure it restores visible counts and
trims temporary signature and representation rows to the committed prefix.
Regression tests exercise generated nodes, retry after a failed declaration,
and isolation of exported copies. External compiler checks reject mutable
access to each of the three private vectors.

`NativeCoreGraphState` models the two ordered scans and cursor commit and
proves exact frame preservation for earlier decoded definition and constructor
roots under append-only inference. `NativeCoreDeclarationCache` proves that
the rollback loop retains exactly the committed signature and representation
rows and restores visibility. These proofs use an abstract inference callback.
The actual native inference implementation still needs refinement.

`NativeBindingMachineMutable` executes indexed Load by evaluating the owner
and offset, reading the guarded cell, and entering the callback with the I64
and original owner. Its numeric invariant proves the width of every indexed
cell for all reachable states. The typed named-owner literal Load theorem
derives the physical read guard, executes nine transitions through both
callback binders, and proves the original Loan64 result type. The checked
Store-then-Load regression reads 17 from the changed cell. This local theorem
uses canonical alignment, owner liveness and size, and loan coverage.

`NativeLoanProofTreeObservation` finds nested computed Loop evidence, including
inside `LtAdd`, and checks the resulting residual at its exact source type.
`NativeLoanProofNormalForms` proves uniqueness, replay stability, and absence
of visited redexes for successful bounded normalization. General termination,
canonical proof coverage, and universe-aware consistency remain open.

The aggregate passed 976 Lake jobs, 9,301 declaration audits, and every
generated fixture comparison under the resource wrapper. The audits report
only `propext`, `Quot.sound`, and `Classical.choice`. The rebuilt compiler
passed 64 Core unit tests, 89 native kernel fixtures and 31 additional
correspondence checks, 68 mixed source fixtures and 54 exact-byte checks.
Typed beta replay accepted 12 inputs, rejected 24, and gated two handoffs.
The transform and canonical replay suites passed 18 native snapshots and
25 graph/root handoffs. Both now require native rejection at the `UInt32`
shift limit and test Lean rejection of a forged wrapping result.

## 2026-11-18: mixed checker replay and reachable Load callback typing

`NativeLoanMixedIncremental` proves exact equivalence between reusing a
checked Loan64 declaration environment and running the complete Lean mixed
checker with the same typing and quantity fuel. Appended families start at or
after the prior global count. Families at the checkpoint follow older families
in table order. Invalid suffix scheduling and checker rejection propagate
through the equivalence. A successful suffix extends both earlier tables
and constructs a checked combined history.

`NativeBindingMachineMutableAlignment` preserves slot and erasure alignment
through every indexed transition, including suspended operand stacks,
captured closures, both Load callback activations and faults. A source-typed
CODE variable in any reachable machine state selects its actual retained value.
`NativeBindingMachineMutableDynamicLoad` uses the reachable alignment,
lease inventory and cell widths to derive the selected U64 slot and physical
read bound from the closed source `Decide` evidence. Nine real transitions
read the indexed cell and activate the two callback binders. The lifted
canonical view relates the actual callback to retained source CODE and its
original result type, including both observed arguments in the ghost closing.
The admitted branch example performs one read at index 1 and returns 17.

The Load theorem still uses a live owner slot and local source-to-runtime
value, size, erasure and loan correspondence. Extending this result to all
reachable typed control states is part of the outstanding runtime obligation.

`NativeLoanHigherKindObservation` decides the existing higher-kind grammar
using a bound computed from the term tree. For actual typed ghost replacement,
the recognizer supplies the grammar evidence at every index of the finite
source context and the checked substitution produces its denotational action.
The byte observer runs the Lean Loan64 mixed checker on a version-6 snapshot,
then computes a typed residual at the exact stored annotation and reconstructs
its intrinsic kind and finite semantic carrier. A checked example observes a
higher-kind identity whose definition and annotation both contain a comparison.
Successful normalization and membership of the residual in the grammar remain
conditions of the observer. Full type-to-model coverage and production checker
refinement remain open.

The aggregate passed 980 Lake jobs, 9,327 declaration audits, and all
generated fixture comparisons under the resource wrapper. The audits report
only `propext`, `Quot.sound`, and `Classical.choice`.

## 2026-11-18: Load context transport and pure conversion coverage

`NativeBindingMachineMutableLoadContexts` carries the complete local value and
buffer-size contexts and coverage of actual readers across both Load callback
binders. The heap and reader frames keep their identities. The canonical view
equates the returned owner with the original owner slot, with the same sizes
and coverage. When the owner binder has the exact captured annotation, typed
variable renaming also transports open CODE into the one-owner view. The
two-binder view retains its original CODE type when annotations only convert.

`NativeLoanProofTransportObservation` shows that an admitted closed less-than
proof can be normal for the earlier contractor and outside its supported
arithmetic syntax. In the example a literal `Strict` prefix protects `Refl`
inside `Transport`. The checked observer exposes the equality evidence and
contracts the transport at the original Loan64 result type. An actual compiler
probe reaches `Decide(0,1)` by normalizing the same checked declaration.

`NativeLoanPureFreeBoundary` proves the existing Lean conversion cannot equate
a variable with a pure `Free` returning it. The Lean mixed declaration checker
rejects the corresponding reflexivity proof at every budget. The production
compiler accepts `tests/core_preserves/pure-free-equality.jhc` and checks its
normal result at the original type. The wrapped Lean version-6 checker rejected
the exact snapshot written from that input. Projecting the annotation with
`NativeLoanValueProjection` yields ordinary reflexivity. Connecting that
projection to source typing and production conversion remains open.

`NativeCoreTransformWire` connects version-6 child references and the four
binding edges to arbitrary paths in the represented syntax tree. The selected
subtree sees exactly the lifting of renaming, signed shift and substitution
determined by the crossed binders. The model of the `UInt32` cutoff increments
rejects exactly on overflow along that path. Whole native traversal execution,
resource accounting, and the append of the new arena nodes remain separate
refinement obligations.

The aggregate passed 984 Lake jobs, 9,352 declaration audits, and all
generated fixture comparisons under the resource wrapper. The audits report
only `propext`, `Quot.sound`, and `Classical.choice`. Both Python modes of the
native pure erasure suite passed the new assertion, 18 MIR twin comparisons,
300 executed results, 60 expected runtime traps and three rejection cases.

## 2026-11-18: pure conversion algebra and signed Core arithmetic

`NativeLoanPureConversion` extends the raw relation with the shaped `Free`
and `Strict` equations. Every term has a finite path to the existing combined
Lend and value projection. In an admissible environment, the extended raw
relation is equivalent to family conversion of those projections and is
confluent. Renaming, substitution, and `Eq` and `Pi` injectivity hold. The
projection explains the native dependent reflexivity example. The existing
Loan64 typing judgment and checker still need to incorporate the extension.

`NativeCoreArithmeticMachine` models the signed arithmetic branch after Core
has normalized both operands. It proves that sign extension to `I128` and
addition, subtraction or multiplication are exact for all `I64` arguments.
The guard and narrowing agree with the old pure value contraction for every
input. A successful fold has the original Loan64 result type. The complete
native normalization traversal remains an implementation-refinement goal.

`NativeLoanProofContextualObservation` extends both prior proof observers
at identical budgets, retaining their exact successful output. It exposes a
`Transport` inside supported proof operands and follows the typed finite Loop
unrolling. The regression uses real dependent induction hypotheses under
computed equality witnesses to prove `Lt(3,4)`.

`NativeBindingMachineMutableLoadFree` composes the actual Load handoff with
the returned owner's immediate Free in twelve transitions. The original
quantity receipt, inherited loan budget, and actual reader inventory supply
the physical release guard. The source tail retains its original CODE type,
value and size contexts, and reader coverage. Both slots still identify the
same owner, and the original captured owner slot has zero remaining demand.
The theorem is local to the specified callback and its source/runtime world.

The aggregate passed 988 Lake jobs, 9,378 declaration audits, and every
generated fixture comparison. The audits report only `propext`, `Quot.sound`,
and `Classical.choice`. Typed beta replay passed 12 accepts, 24 rejections,
and two gated handoffs with both standalone Lean checkers under the project
memory and thread limits. Those limits are also the defaults for graph
certificate and canonical replay validation.

## 2026-11-18: unsigned arithmetic and source use of pure conversion

`NativeCoreArithmeticMachine` now models the unsigned constant accumulator.
At most one U64 literal is added for each successful literal tick and guarded
cancellation never increases the sum. With at most one million such visits,
the U128 accumulator agrees exactly with mathematical naturals, including
repeated visits to a shared node. The balanced `natural_sum` reconstruction
uses valid U64 literals and represents the exact sum. With that tick bound,
the unfolded result has at most 21 levels. The actual traversal and its tick
accounting still need implementation refinement.

The indexed binding machine now evaluates unsigned subtraction left to right,
skips the erased evidence, and reports arithmetic overflow on underflow.
The step preserves heap and reader invariants, numeric widths, and active and
suspended frame alignment. Source typing of literal operands and supported
evidence derives the runtime guard and original result type, including maximum
U64 minus zero. The exact event fixture checks source operand order and proof
erasure. The older runtime equivalence applies to prefixes that select none of
Store, Load, and unsigned subtraction.

`NativeLoanPureTyping` connects the expanded pure conversion to a structural
ghost judgment over authentic Loan64 derivations. It keeps the original binder
policy and checks formation of conversion targets. The Pi, lambda, and
application fragment has typed ghost substitution and beta preservation
at the original requested codomain. The earlier Free equality program has a
derivation here. Applying it to a Free-containing argument and contracting the
beta redex both give `Eq(0,0)`. This covers a fragment of the source judgment.
Extension to all constructors and executable checker admission remains open.

The full check passed 990 Lake jobs, 9,406 declaration audits, and every
generated fixture comparison under the resource wrapper. The audits report
only `propext`, `Quot.sound`, and `Classical.choice`.

## 2026-11-18: graph comparison and proof irrelevance

`NativeCoreCompareWire` proves that the version-6 node words carry the native
constructor rank, exact signed payload order and comparison child selection.
Its graph comparator follows shared references with depth and work bounds.
Every successful result on the parsed graph agrees with the structural
ordering on represented trees. A zero result is equivalent to equality after
stripping `Strict` and omitting the designated evidence of `USub`, `Pack` and
erased `Give`. The separate `Core.identical` traversal and refinement of
compiled checker execution remain open.

The full check passed 991 Lake jobs, 9,416 declaration audits, and every
generated fixture comparison under the resource wrapper. The audits report
only `propext`, `Quot.sound`, and `Classical.choice`.

## 2026-11-18: checked pure admission, identity, and refinement values

`NativeLoanPureTypingChecker` reuses Loan64 inference and independent type
formation, then proves the requested `RawValue` conversion with checked
projection and family/delta/ACU comparison. Projection enforces work and
Lend expansion bounds before materializing the tree. The checker has a sound
single-declaration version-6 entry for closed ghost code with no families.
It accepts the exact 329 bytes exported from the native pure Free equality
fixture. The original Loan64 checker rejected those bytes. Integrating the
extension throughout inference, family admission and CODE remains open.

`NativeCoreEffectAnalysis` links a bounded graph traversal of the observed
version-6 rows to `iterationMemoryFree`. It handles the skipped `Give`,
`Loop`, `Absurd`, and `Back` children and the actual boxed family flags in the
supplied checked environment. It rejects missing nodes or family entries.
With sufficient depth the graph result agrees exactly with the syntactic
test. This concerns the structural analysis, with runtime effect and compiled
implementation correspondence still to be proved.

The indexed binding machine now carries `Pack` and `Witness` using an
unsigned runtime word. It evaluates the runtime operand and erases the
predicate and evidence. The local `RefinementWord` relation retains the
source witness and its proof. The typed literal Pack and retained-slot
Witness theorems use the Loan64 source rules. A checked closure retains the
original Pack provenance and returns its captured witness, 3.

`NativeCoreIdentical` models the distinct identity path, including budget
diagnostic priority, stripping Strict, eager vector length checks, and
checking the motive before the case vector for eliminations. It charges
equal references again. Successful identity agrees with retained shape
equality and with compare-zero whenever both computations succeed. The
structural self-cost theorem counts every retained child occurrence and both
strict descents with sufficient depth and step budget. The checked
shared-reference example uses five ticks and fails with four.

The full check passed 995 Lake jobs, 9,449 declaration audits, and every
generated fixture comparison under the resource wrapper. The audits report
only `propext`, `Quot.sound`, and `Classical.choice`.

## 2026-11-18: mixed pure admission, arithmetic truth, and arrays

`NativeLoanPureMixedAdmission` uses the real declaration order and family
checker, checks the original CODE and quantity obligations, and retains a
typed history of expanded ghost definitions. Ghost aliases and dependent
applications reuse the previously accepted value at its exact stored type.
The mixed byte checker accepted 1,101 bytes from the rebuilt native compiler,
including four definitions and an intervening family. Arbitrary nested ghost
inference under the extended conversion still needs support.

`NativeLoanPureArithmetic` derives arithmetic truth from the extended ghost
typing and bounded recognition. Affine equality and order, including under
dependent U64 quantifiers, respect the new conversion and capture-avoiding
substitution. A checked application recovers the affine argument after bounded
pure projection of a Free expression. The theorem rules out false numeral
inequalities in the recognized grammar and reads actual stored types from
successful mixed version-6 admission. General universe-aware consistency and
coverage of all well-typed evidence remain open.

`NativeCoreGlobalNormal` verifies allocation-free normalization of transparent
global aliases to atomic heads. Successful mixed history bounds the chain by
the declaration count even when a global body jumps forward in the arena.
The equal model shares the native counter across left, right, and identity.
For represented admitted inputs of this form, it returns true exactly when
their expansions agree. The proof covers visibility and diagnostic precedence
within the model. Composite normalization and compiled refinement remain open.

The binding machine now retains actual immutable Array values in closures,
evaluates literal elements in source order, and reads both arrays and leased
buffers by their distinct Index paths. The proofs preserve numeric bounds and
heap, reader and binding invariants. Typed literal construction and typed
Index of a retained array derive the length and result from the source rules.
A checked example performs two allocation and release effects in order and
returns the second element, -6. General runtime interpretation of every
accepted source value remains open.

The full check passed 999 Lake jobs, 9,502 declaration audits, and every
generated fixture comparison under the resource wrapper. Only `propext`,
`Quot.sound`, and `Classical.choice` occur in the audits. Native mixed
correspondence passed 69 source fixtures and 55 raw exact-byte checks. The
suite also passed the pure admission check of the same 1,101 native bytes
that the raw checker rejected.

## 2026-11-20 kernel verification checkpoint

The mixed pure checker carries the actual local context into ghost lambdas.
It reuses the checked type of an earlier global under the binder, then checks
dependent application arguments in that context. The regression exercises a
stored proof function with a Free expression in its binder annotation and a
later lambda that applies the function to a local reflexivity proof.
The native mixed regression passes 69 source cases and 55 exact-byte checks.
The expanded checker also accepts the same 2,133-byte native snapshot.

The extended ghost judgment has unique result types up to RawValue conversion.
The finite polymorphic model reconstructs inhabitants from checked expanded
ghost typing in its recognized grammar. It also proves that the executable
checker rejects a function returning an arbitrary abstract type at each of the
32 supported universe levels, within that grammar.

The allocation-free graph path for pure Free and Drop follows their
continuations through interleaved transparent global references. Exact-byte
admission supplies the original declaration type, and a successful path to an
atomic node preserves that type and produces a forward conversion witness.
Structural normalization now composes the path across all children of a
supported parent. It shares the checking budget, reuses unchanged parents,
and appends at most one node while preserving backward references. The same
conversion theorem applies to exact admitted snapshot bytes.
The recursive version handles arbitrary nesting of supported structural
parents over atomic, Free, Drop, and alias leaves. It threads each child's
extended arena through the next child. A later failing child preserves earlier
appends and backward references. The shared-child example checks two distinct
appends and the exact arena retained when the second traversal exhausts fuel.

The zero-count Fold and dependent Loop graph paths visit the count and
initializer in native order and return the normalized initializer at the
exact original type. The count may follow transparent aliases to zero,
and the initializer may follow the allocation-free pure path. Exact
mixed admission provides the original declaration typing. The native
preservation command accepts both the existing empty-iteration fixture and
a variant whose count is a transparent global.

The binding machine now derives variable-array indexing from reachable slots
and supported closed arithmetic evidence. Its array frames retain the
original source expression and the progress through its element list. At an
integer child return, the checked source supplies the next child's type or the
original array result type, using the concrete accumulated values.

The aggregate check passed 1,004 Lake jobs, 9,533 declaration audits, and all
generated fixture comparisons. The axiom audit accepts only the standard
Lean axioms `propext`, `Quot.sound`, and `Classical.choice`.
The focused Nix graph-certificate build now includes the pure mixed
admission module imported by the version-6 validator. Both system
derivations evaluated, and the native mixed regression passed again after
building the validator's imports.

General consistency, contextual preservation across the rest of the
language, the source-to-runtime ownership invariant, and refinement of the
production compiler remain open.

### Composite delta normalization, array call entry, and proof observation

The recursive graph normalizer now reenters structural normalization after
transparent global lookup and the pure Free and Drop continuations. A
successful run retains its forward reduction under the authentic mixed
history. Arena growth is bounded by charged visits. A run entering within
budget can exceed the limit only by the final rejecting tick.

An actual final array element return can resume an argument frame and enter
its saved closure. The two-transition theorem derives the dependent result
typing and the value context from the constructed array and the original
source typing. Captured source typing remains a premise. Relating the
saved argument origin to the constructed array remains an open obligation.

Bounded observation now works directly on extended ghost derivations and
the stored bodies of exact-byte mixed admission. Typed beta, reflexive
Transport, Strict, and Free preserve the original result type. Contextual
steps cover lambda bodies and application callees. Recognized arithmetic
residuals give truth for the original accepted type and rule out a false
closed numeral inequality when observation succeeds. General termination
and coverage of all source proof terms remain open.

The aggregate check passed 1,006 Lake jobs, 9,546 declaration audits, and
all generated fixture comparisons. With the existing Lake cache, the
resource-limited aggregate check took 13.48 seconds.

### Normal forms, array calls, and dependent proof operands

A successful recursive graph normalization in the supported fragment
produces a represented normal form. Its depth and unfolded tree size are
bounded by the original depth and charged visits. Rerunning from the result
reference with the same starting counter and limits returns the same arena
and reference, charging at most the original work. Each occurrence of a
shared child still consumes its own visit. Exact-byte mixed admission
supplies the original body representation for a stored definition.

The typed array call and variable index paths now compose from a reachable
final array element return. Seven actual transitions enter the saved closure,
select its captured unsigned index, and return the integer with the original
dependent type. The bounds follow from the captured value and the supported
closed arithmetic evidence. The source typing and captured value context
remain explicit premises.

The bounded ghost proof observer can reduce a dependent application operand
when the executable Loan64 conversion relates it to the original operand.
It reconstructs the original instantiated codomain and retains prior
successful observation paths. The checked example uses a computed argument
and an annotation that requires Free conversion.

The aggregate check passed 1,006 Lake jobs, 9,554 declaration audits, and
all generated fixture comparisons. The cached, resource-limited run took
11.33 seconds.

### Live arena equality, signed normal forms, and mutable heap history

Pure structural equality now carries the arena produced by the left
normalization into the right normalization and then reads both returned
references with the shared identity evaluator. The live evaluator agrees
with aligned version-6 words, including failures and the step counter.
Successful comparison decides equality of the normalized retained shapes.
The shared limit bounds both normalizations and the final identity call,
and every appended row is charged to a visit.

Signed arithmetic normalization visits nested operands left to right and
passes exact I64 words through the widened fold. It retains overflow as an
arithmetic node. Represented results preserve the original Loan64 ghost
type, including when exact-byte admission supplies that type. In this
fragment the nonarithmetic leaf paths end in atoms.

Actual Mutable transitions project to the exact allocation and lease
history of their metadata, including when evaluation fails. This supplies
the history needed to transport captured Buffer lengths across arbitrary
reachable Store and Load suffixes and to show released owner IDs stay dead.
Indexed reads, writes, and activation leave this metadata unchanged.

Bounded ghost proof observation now replays computed proof loops and
nested arithmetic evidence through the actual stored derivations. The
mixed admission example replays a checked two-step dependent induction at
its original annotation. The general logical interpretation and
termination argument remain open.

The aggregate check passed 1,009 Lake jobs, 9,573 declaration audits, and
all generated fixture comparisons in 39.78 seconds with the warm cache.

### Comparison reflection and typed observation of computed branches

The comparison header and child arity recover the complete constructor,
including vector-length fields. For expanded inputs whose entire trees
are retained by comparison, structural normalization preserves full
retention. Successful live equality on this fragment therefore yields a
RawValue conversion of the original nodes. Equality of discarded evidence
remains a separate typed proof obligation.

The graph normalization models for Witness and Proof first normalize the
refinement structurally. They return the appropriate Pack reference with
the native step counter and model the different neutral append behavior.
Exact mixed admission supplies the declaration history for the RawValue
reduction and graph preservation theorem.

Actual Free events characterize liveness of an earlier allocated owner
through a reachable Mutable suffix. The typed literal Store theorem now
derives its current size world and reader inventory from that suffix,
using an earlier captured owner world and liveness. The resulting run
either writes the selected cell at its original Buffer type or faults on
the released owner without changing the heap.

Bounded ghost observation can select either branch of computed IfLt and
IfEq with U64 numeral operands. A true branch receives a proof at the
original operand terms, and replay preserves the exact requested type.
The mixed checker examples combine this with dependent beta and verify
true equality for distinct operand expressions.

The aggregate check passed 1,011 Lake jobs, 9,592 declaration audits, and
all generated fixture comparisons. Rebuilding the affected dependencies
and checking the aggregate took 78 seconds.

### Checked comparison evidence, transparent globals, and mutable roundtrip

For checked USub, Pack, and erased Give roots, the typing derivations
recover the proposition and typing of the evidence skipped by Core.identical.
A successful live comparison identifies the same proposition on both sides
when both retained operands are fully retained. The result supplies the
typing premise for a future irrelevance rule without inserting an untyped
equation into RawValue conversion.

An admitted transparent global can be unfolded in any local context at an
independently formed requested type using its original derivation and closed
weakening. Bounded expansion followed by structural replay retains residual
typing and supports arithmetic observation from the original source with
global references. The checked example uses a transparent call under a
binder at a type that requires Free conversion.

Pure graph normalization now handles nested Borrow and Deref. Either order
of cancellation returns the original inner reference. Neutral results
preserve an existing row or append one when the operand changes. For a
structurally normal payload, exact-byte admission also supplies the original
ghost typing at the cancellation result.

The actual mutable evaluator now has a checked execution theorem for a closed
Alloc, Store, Load, and Free program with arbitrary admitted literal lengths,
offsets, fill values, and replacements. Given a representable allocation
size, checking supplies the numeric premise for each step. The 23 transitions
write and read the same cell, release the original owner, and return the
integer at the exact original result type.

The aggregate check passed 1,015 Lake jobs, 9,610 declaration audits, and
all generated fixture comparisons in 9.27 seconds with the warm cache.

### Unsigned collection, cancellation, and wide constants

Live unsigned collection follows the addition children in evaluation order.
It records Strict prefixes and charges each occurrence of shared nodes.
An independent syntax trace accounts for both output vectors, every literal
update and the exact counter difference. The production budget implies that
the actual U128 accumulator contains the mathematical total.

Cancellation copies the pool, scans with live identity and charges every
entry shifted after a match. Completed calls agree with ordered first-match
removal on represented comparison shapes. Success accounts for one
occurrence per request and preserves the mathematical remainder for any
valuation on those shapes.

The wide-constant emitter now appends to the arena in native order, shares
equal halves and preserves the old prefix even when an append fails. The
represented result preserves the collected value, has the U64 ghost type,
and its unfolded depth is at most 21 for a collection from zero within the
production step budget.

The aggregate check passed 1,018 Lake jobs, 9,626 declaration audits, and
all generated fixture comparisons in 13.16 seconds with the warm cache.

### Canonical ordering, source assumptions, and typed continuation entry

The live and serialized structural orders share a comparison traversal.
Canonical sorting spends one tick per variable insertion comparison and uses
the live structural order for ghost nonvariables. It preserves the input
order of runtime nonvariables. The sorted references represent a permutation
of the original atoms. Canonical graph emission folds the ordered references
from the left, preserves the earlier arena, and produces a U64 term from
U64 atoms. An oversized runtime constant returns the native fallback signal
before sorting or appending.

An actual ghost checker derivation in a mixed local context can now be
closed with typed substitutions constructed from a U64 valuation and
true erased Lt and Eq assumptions. The wide variant handles affine
expressions whose operands exceed U64 by constructing Loan64 evidence
from mathematical arithmetic. Successful proof observation derives truth
at the original instantiated proposition.

Pure variable-body applications use the native identity shift and binder
decrement. The graph result is reached by raw reduction of the original
admitted term. The original ghost type is recovered in the identity case
with structurally normal operands, and the model tracks the traversal
counter across the application.

The executable mixed checker supplies the typed entry of an arbitrary
explicit two-binder Load callback after 19 actual allocation, store, read,
and activation steps. Its captured scalar has the written value and the
restored owner has its original live physical Buffer and size. The checked
resource projection supplies the one-unit owner budget. For an admitted
callback whose body starts by freeing that owner, 22 actual steps reach the
remaining body with dependent typing and no residual demand for the
released slot. Full control-stack preservation continues beyond this entry.

The aggregate check passed 1,026 Lake jobs, 9,666 declaration audits, and
all generated fixture comparisons in 9.20 seconds with the warm cache.

### Binder transformations, typed sums, and physical owner demand

The live graph transformation now covers all 54 constructors for signed
shift, binder-removing substitution, and rewrite without binder removal.
Successful runs give the independent capture-avoiding tree meaning while
preserving earlier rows and backward references. Visit accounting charges
each source occurrence and each shifted replacement occurrence. A worked
failure retains the earlier child's committed append.

The two operand collections of Core.sum share depth, clock, atom pool,
and the widened accumulator. Ghost sum construction preserves the exact
original checked type and raw conversion when the collected pool has no
root subtraction to cancel. It returns the sorted, canonically emitted
result after reattaching every Strict prefix in the native wrapping order.
The remaining cancellation rounds require a typed symbolic subtraction
equation and the complete guarded branch.

The open arithmetic proof fragment now derives finite successful replay
from an actual typing derivation and the source grammar. It supports nested
erased assumptions and arbitrary head chains of Strict, Free, and reflexive
Transport. Its normalization gives the original proposition's arithmetic
truth and rules out closed Lt(0,0) derivations in that grammar.

Positive demand in the retained owner context entails a single live
physical owner with no other demanded alias. Free derives liveness from
this world and preserves the remaining world. An actual variable Load
transfers the single unit to the restored binding, leaves older aliases of
that owner at zero demand, and preserves unrelated live owner units. Both
operations retain the original dependent continuation typing.

The aggregate check passed 1,032 Lake jobs, 9,702 declaration audits, and
all generated fixture comparisons in 70.92 seconds while rebuilding the
affected dependencies.

### Compound beta, evaluation analysis, and named reader entry

Pure application normalization now composes the exact graph substitution
with operand and result normalization for a represented lambda body of
any shape supported by the successful walks. With structurally normal
operands the substituted body remains in the same fragment, and the exact
declared dependent type and cost follow from the original typing and the
native visit accounting.

Core.may_trap and Core.reads have live-arena and syntax models with
matching results at every depth. The graph walk terminates along the
backward application spine. The models preserve erased Pack and Give
positions, the runtime variable-call guard, and the distinction between
View motives returning functions and those reading scalar results.

A complete owner demand receipt can be split for sequential execution.
Each positive physical owner unit belongs to only one side, even through
retained aliases. Named reader entry uses this demand world to derive live
ownership and opens the actual fresh lease and token. Its specialized
reader retains the original ghost type and zero owner demand for the
borrowed slot. Demand totality on the physical owner slots also carries
through the existing Free and Load handoffs.

The aggregate check passed 1,037 Lake jobs, 9,720 declaration audits, and
all generated fixture comparisons in 9.34 seconds with the warm cache.

### Final checked increment

The recursive pure graph model now handles structural nodes, beta and
Transport together. It preserves the original Loan64 type of definitions
admitted from exact version-6 bytes, with no need for their operands to
start in normal form. One example reduces a nested call to reflexivity
under an erased binder and completes Transport after 22 ticks.

Arithmetic proof replay now follows prior transparent definitions and
beta at U64 binders with a derived sufficient fuel threshold. All larger
fuel bounds produce the same typed residual in the supported grammar.
The example checks a prior source alias through actual mixed admission.

Guarded USub cancellation preserves the source type, original residual
references and mathematical subtraction value in every interpretation of
the retained comparison shapes. It reattaches potentially trapping
operands and has a typed neutral fallback retaining the proof reference.
This covers the subtraction branch after operand normalization. The
separate cancellation rounds for UAdd and general typed conversion for
symbolic subtraction remain open.

The named direct-Index reader path now derives the read, the exact lease
close, the restored bindings and the continuation owner world from the
original entry. The composed 18-step path releases the owner through
either its returned slot or its older alias, preserves outer leases, and
enters the checked tail with its original type and complete owner demand.

The aggregate check passed 1,042 Lake jobs, 9,751 declaration audits, and
all generated fixture comparisons in 11.11 seconds with the warm cache.

### Reader provenance and non-escape with indexed buffers

Every reachable indexed machine state bounds its retained reference tokens by
the current lease counter. This includes nested closure captures, suspended
buffer operands, and the ordinary frames saved with those operands. A reader
also retains its entry-time bound for its own continuation and every enclosing
frame. The bound survives suspension and resumption of stack segments.

For a canonical variable return, the original Lend judgment supplies the
Outlived policy and the typed value context selects the actual result. Two
transitions return that value and close its reader. The closing token is
absent from the resulting control, active frames, and suspended frames. The
indexed cells and other leases are preserved. The heap lifecycle keeps an
expired lease closed in every later execution suffix.

The closed regression exercises a reader that returns a local variable inside
a Store value operand while its enclosing reader is suspended. Extending the
result to computed reader bodies requires deriving the same value and resource
interpretation from arbitrary typed execution.

The aggregate check passed 1,047 Lake jobs, 9,770 declaration audits, and all
generated fixture comparisons under the project resource guard.

### Conditional normalization, computed readers, and unsigned rounds

The pure graph walk for IfLt and IfEq normalizes the operands in order. A
known comparison visits only its selected arm. The true path appends actual
Decide or Refl evidence, then shares the counter across substitution and
recursive reentry. The unchanged arm, evidence append before budget failure,
and an admitted equality declaration are checked by executable fixtures.

The global proof normalizer now derives sufficient fuel for both comparison
outcomes with bounded literal or scalar-slot operands. The selected source
arm retains its original type after substituting the original Decide or Refl
term. A checked global exercises below, equal and above inputs, including a
Transport that uses the inserted equality.

A named reader can compute a signed expression from the actual indexed
cell. Its original Lend judgment supplies the literal Index and operand
bounds. The indexed machine's fitting result is typed at the original reader
annotation, closes exactly its own lease, and excludes the retired token from
the entire retained state. On overflow the real machine stops with its lease
active. Checked examples exercise an updated cell and the overflow path.

The unsigned sum cancellation loop now follows the production scan order,
matches multiset occurrences through live identity, preserves denominator
traps, and shares the checking counter over up to 64 rounds. Completed rounds
produce a linked retained-syntax trace and exact residual value equations.
The tested two-round trace succeeds at ten ticks and rejects on the same
tenth visit with a budget of nine.

The aggregate check passed 1,049 Lake jobs, 9,788 declaration audits, and all
generated fixture comparisons under the project resource guard.

### Recursive branch and refinement walks, arithmetic trees, and sum emission

The pure graph normalizer now reenters the same driver for comparisons after
beta substitution and under ordinary structural nodes. It also normalizes a
refinement-producing expression before taking its Witness or Proof field.
Successful walks retain the original admitted type, old arena prefix, and
backward references. The byte-admitted examples expose a comparison and a
Pack after beta and verify the reused field reference and exact visit counts.

The checked global proof observer derives both an operand value and sufficient
fuel for bounded affine comparisons. An older erased bound can justify a
nonzero addition to a scalar slot. Substituting the original Decide or Refl
keeps the requested dependent type. The checked example derives `x + 1 < 5`
from `x < 4` and returns evidence retaining the addition.

The indexed machine executes arbitrary signed arithmetic trees of checked
buffer reads and literals in left-to-right order. The original Lend typing
supplies the index bounds and result type. Success closes the reader with the
whole-state token exclusion. The first overflow retains its fault stack and
lease and skips the remaining operands.

After operand normalization, the UAdd model composes both collections, the
cancellation rounds, canonical emission, and the original-order Strict
wrappers. Every successful output retains the original checked type in ghost
mode and preserves the arena prefix. A wide runtime constant appends UAdd of
the original normalized operands before canonical sorting. The matching ghost
case emits a shared literal tree.

The aggregate check passed 1,052 Lake jobs, 9,804 declaration audits, and all
generated fixture comparisons under the project resource guard.

### Transparent alias entry, computed owner handoff, and dependent codes

The recursive pure graph walk now preserves typing in both raw syntax and its
transparent interpretation. Exact byte admission supplies typing for a branch
that skips a global in its unselected arm. A visible chain of initial aliases
enters composite beta and conditional reduction with the original clock and
type, while a reference before visibility rejects on its own tick.

After computed reader evaluation, the original checked continuation restores
both bindings, the canonical dependent type, the value/size/loan contexts,
and one exclusive owner unit. An immediate Free through the returned slot or
an older retained alias consumes that same unit, enters the checked tail,
and leaves every alias of the released object at zero demand.

An admitted symbolic `(x - y) + y` demonstrates a production equation absent
from RawValue conversion. A checked affine cancellation relation preserves
the original type and every satisfying natural valuation. With U64-bounded
numerators it also derives conversion after the actual typed closing. This
identifies the additional open equation that production refinement needs.

The finite universe interpretation reconstructs recognized dependent Pi codes
over native classifiers, including code-level application and Type32 values.
The exact mixed byte checker supplies the stored annotation. The interpreted
code of a mixed universe prefix ending in Lt(0,0) has an empty carrier. General
proof consistency still needs the fundamental theorem for proof inhabitants.

The aggregate check passed 1,056 Lake jobs, 9,838 declaration audits, and all
generated fixture comparisons under the project resource guard.

### Checked quantified proofs, production cancellation, and rejecting visits

Actual expanded ghost typing now constructs semantic inhabitants for the
recognized proof grammar under mixed universe binders. It covers affine
proofs, typed universe-code application, erased arguments validated by the
checker, and authenticated earlier globals. At the exact mixed snapshot
boundary, no admitted declaration in this grammar proves a mixed universe
prefix ending in Lt(0,0).

The checked affine cancellation relation now connects to an exact successful
Core.sum graph run. For `(x - y[p]) + Strict(t, y)` with the shared
denominator reference, seven ticks produce `Strict(t, x)` using the original
prefix reference. Source admission supplies the erased bound. The result
retains the exact type and arithmetic truth under all satisfying valuations.

Every graph transform and covered pure normalization visit preserves the
existing arena prefix, including on rejection. From an in-budget start,
success stays within the limit and a failing traversal uses at most the one
additional rejecting tick. This includes work shared by alias visits,
evidence appends, substitution, and normalization reentry.

The native mixed correspondence suite passed 69 source fixtures and 55
exact-byte checks. The pure checker accepted the original extended-ghost
snapshot bytes.

Guarded reader execution now uses CODE-typed captured U64 slots and derives
the selected bound from the actual comparison. The resulting erased Lt
hypothesis authorizes the selected indexed read. After close, both original
continuation bindings, their dependent type, and the exclusive owner receipt
are recovered. The checked fixture skips the first captured offset and reads
the second before releasing the original owner.

The aggregate check passed 1,059 Lake jobs, 9,861 declaration audits, and all
generated fixture comparisons under the project resource guard.

### Constructor elimination, retained owned calls, and erased implication

The checked constructor derivation now proves the exact field count. A
remaining Pi cannot convert to the terminal Ind, and an extra argument
cannot open that Ind as a Pi. Generated branch types and the branch typing
proof determine the case vector's length. These facts give executable
contraction at the original type for known-constructor Case, Prop and data
Elim, and recursive or one-level borrowed View. Checked View branch
generation also supplies the exact field borrowing plan.

The graph Case path normalizes the motive, cases and scrutinee in native
order, skips the leading parameters, and appends the selected arm's
application spine. The same clock continues into reentry. A byte-admitted
regression exposes the constructor by beta, retains the requested converted
Buffer index, and checks the emitted spine on reentry exhaustion. The
neutral Case and Strict scrutinee paths still need graph refinement.

An actual checked retained closure call transfers a named Buffer from its
source slot to the parameter at the original dependent type. The original
resource projection separates argument use from the body receipt. The
body retains the value and size context, outer loan authority, and the
unique unit of owner demand, with old aliases at zero. A mixed-checker
regression reads a previously written cell after nested call entry and frees
the original object.

The semantic proof grammar now supports erased affine implication in mixed
universe contexts. Typed application uses the actual guarded premise, while
an unsatisfiable premise supplies an empty semantic argument domain. The
admitted-byte exclusion for mixed-quantified Lt(0,0) holds for the expanded
grammar. Arbitrary checked ghost derivations still need the fundamental
theorem.

The aggregate check passed 1,063 Lake jobs, 9,897 declaration audits, and all
generated fixture comparisons under the project resource guard. The next
graph obligations include neutral Case, the Strict scrutinee's reentry and
the ordered recursive hypotheses of Elim.

### Neutral and strict Case, supported family proof replay, and owned returns

The pure Case entry preserves the original dependent type when the
scrutinee remains neutral. It keeps the original row when the normalized
references match, and appends a replacement when a child changes. The
checked neutral regression exercises both paths, including beta exposing
the open scrutinee.

The post-operand Strict path appends the inner Case, normalizes it with
the shared counter, and appends the original prefix around the result.
Inversion of the outer typed Case gives the same generated arms at the
inner scrutinee. The changed motive application is related by RawValue
conversion, which preserves the independently formed requested type in
PureTyping. Checked reentry retains the prefix around the contracted
constructor result. The budget regression retains the emitted inner
Case on rejection. The enclosing recursive driver still needs to
dispatch the retained Strict operand and establish runtime effect
preservation.

Known-constructor Elim emits the ordinary field applications after
skipping fixed data parameters, then emits each recursive hypothesis and
its application in signature order. Checked history supplies the actual
signature, case and field counts, and dependent result type. Capacity
failure retains exactly the rows that fit and consumes no ticks before
reentry. The recursive regression verifies the full emitted spine and
its type. A leaf regression verifies reentry at the shared clock. The
recursive normalization driver still needs to visit the emitted Elim
hypotheses.

Checked constructor-headed Case and Elim now feed the finite semantic
replay for proposition codes. Actual mixed history supplies the family
metadata, and head beta uses the checked branch argument. The checked
regression eliminates an indexed proposition twice recursively under
Type31. The exact-byte exclusion for mixed-quantified Lt(0,0) extends to
this grammar. A fundamental theorem for arbitrary proof derivations and
native proposition-family carriers remains open.

A checked Buffer variable returns its live physical allocation and exact
dependent size. The use receipt proves the active reader is absent and
retires other aliases. A saved closure binds that returned value with
its checked body receipt and preserves the instantiated dependent
codomain. The mixed regression returns the only allocation into a saved
call, reads the earlier write, and frees it. General computed callees
still need reconstruction of the capture and body receipts.

The aggregate check passed 1,067 Lake jobs, 9,934 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Recursive Elim, indexed proposition carriers, and checked computed callees

The recursive pure driver now visits Elim operands and its emitted
application spine in native order with one arena and counter. The same
visitor normalizes the induction hypotheses, including through beta and
under existing structural nodes. Successful runs give native Loan64
preservation for the raw term and its transparent expansion. An exact
admitted snapshot visits two recursive eliminations and returns the
original base proof at the converted declaration type. Rejecting the
first reentry visit keeps the complete outer spine.

The indexed proposition model uses the actual native constructor table
to interpret unary U64 indices. Its least carrier covers nullary,
scalar, and single erased recursive fields with supported affine
indices. Source typing recovers the instantiated recursive field type
and the result conversion. The mixed-checked even family has an
inhabitant at 2, and the induction invariant excludes 1 in this carrier.
General telescopes, elimination over these carriers, and the fundamental
theorem for all checked proofs remain open.

Borrowed View walks the raw constructor telescope, skips its fixed
parameters, and visits the remaining domains with the shared counter.
When those visits produce the checked canonical fields, their native
flags agree with the independent plan. The append phase gives each
recursive hypothesis a fresh Borrow and keeps the original result type
through reentry. The boxed recursive regression verifies ten emitted
rows. A checked scalar fixture executes the original constructor Pi,
appends one application, and returns the original word at step 11.
Deriving canonical domain visits directly from general mixed history and
normalizing recursive View hypotheses remain open.

The original application projection supplies the ordered receipts for
an effectful Strict callee and its Buffer argument. The actual saved
argument frame retains the checked closure body and zero demand for
captured owners. The regression frees a temporary while finding the
callee, then reads the original written Buffer and releases it.
Preserving capture and argument liveness through arbitrary callee
effects remains open.

The aggregate check passed 1,072 Lake jobs, 9,979 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Joint Case and Elim reentry, Strict decisions, and separated callee effects

Case joins Elim and the ordinary pure operations in the same recursive
walker. With a constructor scrutinee, checked typing supplies each
signature lookup and count needed to build the native arm's application
spine. The exact-byte regression normalizes a neutral Case under a
lambda, substitutes the constructor, and reduces the new Case to the
original Buffer with its converted declaration type. Step exhaustion
at reentry preserves the just-appended Case.

Pure Strict root normalization classifies the already normalized prefix.
It drops a lambda value or a nontrapping prefix, and keeps other prefixes
with their refreshed result. Successful visits preserve the exact Loan64
type. The regression keeps an allocation prefix when its result changes by
beta and discards a lambda whose body contains an allocation. The
post-operand movement of Strict out of Case now reenters the joint family
walker. Arbitrary nested Strict contexts still need a typing bridge for
the extended conversion.

The View shape proof obtains each field conversion and erasure flag from
the checked constructor telescope. Confluence identifies rigid live
domain results with the stored fields. The exact mixed fixture uses a
global alias to a beta redex in the raw domain and shares the clock from
that domain visit through the final branch application. General
non-rigid canonicalization and recursive View reentry remain open.

Realization of an indexed proposition carrier produces a closed native
constructor and its exact dependent type. Prop Elim uses actual checked
case types, and finite replay derives the type of its selected branch.
The semantic theorem supports affine motives depending on the family
index and retains the syntax-only replay condition for interpreting the
result. The checked Even at 2 fixture uses the motive `0 < n + 1`,
which has different instances at the recursive and result indices.
Interpreting arbitrary proof derivations and recursive evidence under
all proof constructors remains open.

The original checked application splits callee and pending argument
demands at the level of physical Buffer identities. A finite chain of
checked named releases excludes all owners still demanded by the
argument. The actual Free events prove these owners live on entry to the
saved closure, with the original types and receipts. The mixed fixture
releases two other Buffers before reading the pending argument.
Deriving this exclusion for arbitrary checked effects remains open.

The aggregate check passed 1,077 Lake jobs, 10,031 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Recursive View and borrowed operands, iteration roots, and arithmetic induction

The joint pure walker now handles Borrow and Deref cancellation and
known-owner View. It visits the original constructor telescope, validates
the live flags against the checked signature, and reenters the same
walker for each generated recursive hypothesis. All shape and spine
visits share the budget. The bounded representation check succeeds on
the original constructor roots after append-only extension of an admitted
snapshot. Rigid-domain shape alignment is supplied by the existing
checked-telescope proof. The exact-byte recursive View fixture emits two
spines and returns the leaf word to the enclosing equality in 80 steps.
View through a Strict owner and arbitrary shape normalization remain open.

The Fold and Loop root walk visits the count then the initializer, returns
the initializer at zero, and otherwise visits the motive for Loop and the
body. Changed nonzero rows keep the original type. Loop's budget fixture
identifies the first rejected motive visit. Nested iteration and runtime
lowering remain open.

The indexed arithmetic observer replays recursive family evidence beneath
LtAdd, LtCancel, LtLe and the other supported proof nodes. It preserves
the original operands and their type. The checked Even at 4 fixture uses
two generated induction hypotheses to derive `4 < 5`. The semantic
result still needs a successful bounded replay into the supported
arithmetic grammar.

The checked Store followed by Free takes nine real machine steps. From
the original source type and resource receipt, it derives the exact cell
write, released owner and retained continuation type. A physically
separated sibling receipt keeps all demanded cells, sizes and loans.
A mixed regression writes and releases one capture while the pending
argument reads its original value. Arbitrary indices and general
effectful prefixes still need the runtime fundamental theorem.

The aggregate check passed 1,081 Lake jobs, 10,074 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Early Lend and Drop, typed Take reentry, and branching inductive proofs

The joint pure walker can dispatch a rule before visiting its operands.
Drop enters the continuation directly. The exact-byte regression leaves a
Strict owner unvisited and charges a rejecting tick at the continuation when
the budget is exhausted. Lend appends the borrow and the three applications
in native order. Its raw reentry theorem covers explicit callback shapes and
preserves the graph prefix and forward equation. The joint type-preserving
walk uses the generic rule when both literal and transparently expanded
callbacks are nonspecialized. The admitted quantified regression executes
that path in 27 ticks. A checked explicit example reaches the independently
typed specialized finish through the same four appends and recursive visitor.
General typed preservation for the explicit native reentry remains open.

The pure Take root visits the packed value first. A known Give emits two
applications before reentry. A neutral Take then visits its continuation
and applies normal row reuse. The mixed-checked owned regression returns
the original allocation at the converted dependent Buffer type in 61
ticks. Its budget regression keeps both emitted rows. A rigid-head lemma
shows why the typed operational rule supplies preservation for this path
under the current conversion equations.

A native indexed proposition can now have any finite number of erased
recursive fields after a leading U64 scalar. Each field has its own unary
affine predecessor expression. The original checked arguments recover
their native types and carrier evidence, and reification rebuilds the
typed constructor for the actual eliminator. The mixed regression at
`P(2)` uses induction hypotheses at distinct indices 0 and 1 as two
operands of LtLe. General index arity and arbitrary dependent telescopes
remain open.

The checked Store-to-Free path evaluates a captured U64 index and a
signed expression over actual captured scalars. The source-typed
Decide-shaped evidence provides the physical bound. After the write and
release it recovers the original continuation type and resource receipt.
Under physical separation, every cell of the sibling Buffer is retained
along with its owner, length and loan receipts. The closed regression
writes 46 at a dynamic index and reads the original 7 from the other
Buffer. The theorem uses successful numeric interpretation and
separation of sibling demand.

The aggregate check passed 1,085 Lake jobs, 10,129 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Joint iteration, vector-indexed induction, and captured Load

The ordered Fold and Loop visits now share the recursive budget and arena
with family elimination, View, Drop and generic Lend. The child walker
retains counted iterations in ordinary contexts and reuses the original
row when the operands are unchanged. The typed root takes the zero branch
after normalizing the count and initializer. It recovers the original
Loan64 type for both raw and transparently expanded terms. A mixed-checked
fixture rebuilds a Loop nested under Eq after visiting a Drop initializer
in 18 ticks. Its zero Fold returns the initializer in four ticks without
visiting the body. Rigid-head lemmas exhibit signed zero-iteration results
outside the current raw conversion equations.

Array and Buffer formation preserve the original universe through their
typed U64 length visit. Both formations reduce a zero Loop length to 2
in four ticks in the same admitted snapshot, and unchanged literal
lengths reuse the original graph rows. Other dependent contexts still
need a compatible conversion or preservation rule.

The indexed proposition carrier now ties every index vector to the
authenticated family's arity. Each erased recursive field has its own
vector of affine expressions over the leading U64 scalar. Carrier
extraction reads the original Arguments derivation and reification
rebuilds the native constructor and its checked Elim. The two-index
fixture admits witnesses at `P(0,1)` and `P(1,2)`, then observes the
eliminator using both induction hypotheses to prove the motive of
`P(2,3)`. General dependent index expressions and ghost derivations
remain open.

The captured Load derives the physical owner, liveness, and exclusive
demand from the complete projected source world. It evaluates the named
owner and index, reads the exact cell, and transports the original type,
callback receipt, loans, and total ownership interpretation through the
two native callback bindings. A following Free releases that owner and
preserves the remaining world. The accepted Store–Load–Free regression
writes and reads 46 at the same indexed cell and then releases the
allocation. The general handoff theorem uses a canonical alias view and
closed Decide-shaped evidence.

Signed normalization now verifies the native bounded fold after recursive
operand visits. A beta-produced operand yields either a literal product
of 42 or a rebuilt addition with overflowing operands, with the original
I64 typing in both paths. The checked literal-array fixture retains a
typed Index in the native walk. The independently proved abstract array
equation selects 7 from those normalized operands.

The aggregate check passed 1,090 Lake jobs, 10,184 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Recursive typed value contexts, computed Load, and scalar-prefix induction

The shared operand traversal now preserves any relation proved by its
single-operand visitor. The typed value traversal uses this result for
arbitrarily nested Strict and signed arithmetic, as well as Array, Buffer,
Eq, Lt, Elements and Refine. It extracts the actual operand premises of
each constructor, preserving the exact type of the raw and expanded
source. Elements keeps its declared cardinality. The ordinary joint
family walker still handles the covered dependent positions that require
conversion. A checked Elements fixture reduces a product nested around
Strict and two signed sums to 42 in 11 ticks. If the budget runs out on
the next element, the committed arithmetic rows remain. A checked
Buffer length keeps the overflowing Strict prefix and drops a zero Loop
to its initializer in eight ticks.

The native pure Free branch selects its continuation before any owner
visit. The retained Load branch visits buffer, index, evidence and
callback in order, then reuses or rebuilds the typed row. In an admitted
program the direct Load and Load reached through Free select the same
typed result with 22 and 23 ticks respectively. The shared callback uses
a boxed constructor and pure Drop, and the rejecting tick confirms that
the first evidence visit precedes the callback. The Free step is tracked
by its immediate value equation and independently typed child change.

The runtime Load index can now be an arbitrary tree of literals,
captured U64 values and checked additions, provided its unsigned
evaluation succeeds. The numeric derivation gives the actual machine
trace, zero additional Buffer demand, and a conversion for the index.
The original closed Decide-shaped evidence yields the physical bound.
The callback and immediate Free preserve the remaining loan and demand
world. The admitted example reads the stored 46 at computed index 2,
then frees the same allocation.

For vector-indexed propositions, the actual checked Arguments
derivation now peels any finite prefix of ordinary U64 scalars. Closed
affine arguments are substituted simultaneously into the recursive
fields and result, and reification rebuilds the native constructor.
An admitted example passes both 1 and the original addition 2+3. Its two
recursive fields are `P(1,2)` and `P(5,6)`, and the checked Elim uses both
induction hypotheses to prove `6 < 7` at `P(6,7)`. General dependent
telescope interpretation remains open.

The aggregate check passed 1,095 Lake jobs, 10,245 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Dependent binders, transparent aliases, and computed Store–Load–Free

The recursive value visitor now enters Pi and Lam bodies under the exact
original binder. A raw conversion for the normalized annotation gives
the context conversion for the rebuilt body. Applications normalize the
function with the typed visitor and the operand with the raw visitor.
The operand conversion instantiates the original dependent codomain.
The shared beta branch substitutes actual graph references and reenters
the same visitor. A normalized Strict function appends and visits the
inner application, then puts the original effect back around its result.
Exact-byte admission covers a dependent application whose result type
still contains the original argument redex, an overflowing Strict
function, and a Pi whose domain and body both change. Their native
schedules take 22, 32, and 15 ticks respectively. The rejecting application
visit keeps the substituted body in the arena. Conditional callees and
wider dependent operand conversions need further rules.

The initial global dispatch records each arena reference and earlier
definition index. Admitted alias chains strictly descend the definition
table, consume one tick and one depth level per alias, and pass the
terminal reference to the chosen visitor. Its expanded typing theorem
uses actual checked global entries. The three-alias arithmetic fixture
returns `42 : I64` in eight ticks and tests visibility, depth and budget
failures. The binder visitor also runs through the same alias dispatch.
Its admitted endpoint fixture enters the dependent application in 23
ticks, including one alias tick. Aliases inside later subterms still need
recursive dispatch in those visitors.

The runtime Store path evaluates nested U64 addition and signed
arithmetic under the actual pending frames. Its original erased
comparison yields the physical index bound. The returned owner enters
the actual saved checked Buffer lambda. The same interpreted index and
erased proof are transported under that binder for Load, which reads
exactly the cell just written. Free releases the same owner, and the
dependent tail type, untouched cells, remaining owner demand and both
loan invariants follow through the original resource receipts. The
handoff uses successful scalar evaluations, closed Decide-shaped
evidence, and the initial complete runtime world.

The proposition carrier now follows an arbitrary interleaving of U64
scalars and erased self-recursive fields in the original Arguments
derivation. It grounds recursive vectors using only previously checked
scalar slots, even when another proof binder occurs between scalars.
The admitted scalar/proof/scalar/proof example checks its original
constructor and replays the actual Elim using both recursive hypotheses
to prove `7 < 8`.

The aggregate check passed 1,100 Lake jobs, 10,298 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Recursive global dispatch, universe replay, and computed borrowed Index

The recursive pure graph driver separates execution from the relation
used to interpret its endpoints. Its expanded normalization relation
interprets exact checked stored definitions and is closed under the existing
computation and ordinary-node rules. An authenticated initial arena remains
a prefix through operand visits, true-arm opening, substitution and beta
reentry. A nested global follows the actual raw value reference of the
earlier definition while preserving transparent expansion. The admitted
application visits globals in its callee, lambda annotation, conditional
discriminant and argument. An invisible callee alias rejects before the
argument visit. The wider typed value and family visitors still need this
recursive dispatch at their own dependent boundaries.

The neutral conditional application rule shifts the true-arm argument
under the evidence binder, appends both applications in order, appends the
rebuilt conditional, and reenters at child depth. A typed derivation
reconstructs the original dependent codomain by instantiation under the
evidence binder. A mixed program and a rejecting-budget fixture check the
same native schedule and its committed graph rows.

The universe-family replay theorem interprets supported dependent
proposition codes from the real typing of a reified recursive family
elimination. It opens written universe binders, substitutes checked type
codes, and interprets compositional arithmetic proof terms with recursive
hypotheses. The admitted example uses its hypothesis in LtAdd beneath
Type0 and applies the resulting proof to U64. Unsupported proof syntax
and general universe-family semantics remain open.

The runtime borrowing proof follows an authentic named Lend through
its pending Index with a fresh leased reference and a successful U64
index expression over older captures. The original erased comparison
supplies the bound and the actual heap supplies the cell content. The
reference is closed before the restored callback, whose source typing
and resource receipts preserve the remaining loans and ownership through
Free. The admitted regression writes 46, reads 46 at computed index 2,
closes the loan and frees the same Buffer.

The aggregate check passed 1,104 Lake jobs, 10,346 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Recursive delta in typed reentry, erased application, and nested loans

The recursive value visitor now shares its exact tick and append schedule
between raw-and-expanded typing and expanded typing. The latter is the
typing judgment supplied by mixed admission. Its typed function positions
visit the authentic earlier global graph rows, and its dependent arguments
and binder annotations use the independent raw conversion visitor with the
same recursive global lookup. Arena prefix witnesses carry the original
definition table through each append, scope extension and beta reentry.
An admitted fixture uses globals in a Strict prefix, an arithmetic lambda
body, a binder type, and a separately visited argument alias. It returns
`40 : I64` in 25 ticks. Budget and visibility errors keep exactly the
rows committed before the rejecting visit.

The comparison adapter runs left normalization, right normalization and
identity at the same depth using one live arena and clock. Checked-byte
admission recovers each selected definition's independent original type.
A successful native identity test coincides with equality of the two
projected represented outputs, with full syntax equality when both
projections retain every position. Exact fixtures cover comparison and
normalization failures with their committed arena prefixes. The paired
admission theorem instantiates the recursive delta visitor for both
passes. On the final live references, a successful structural order
comparison reports order zero exactly when identity reports equality.

The erased application theorem recovers the original checked premise
argument and the instantiated result conversion under arbitrary written
universe binders in the supported code grammar. The replay uses actual
erased beta and recursive Elim evidence. An admitted fixture beneath
Type31 and Type0 consumes an Elim proof of `2 < 3` to establish `3 < 4`.
The quantified-false exclusion is derived for the same replay grammar.

The runtime proof composes the actual computed Store, checked Buffer
closure entry, borrowed read, close, and Free. The same computed U64
index and erased evidence are carried through the argument and reference
binders. It proves the exact bytes and buffer identity, nonescape of the
inner loan, unchanged cells elsewhere, and every older lease's read
observation. An admitted nested example reads 5 from the outer loan both
before and after the inner allocation is written, borrowed and released.
The complete run returns 56 and releases both allocations.

The aggregate check passed 1,108 Lake jobs, 10,383 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Family reentry with recursive delta, equality Transport, and multi-loan readers

The constructor fast paths share one prefix-anchored refinement with the
ordinary and expanded typing visitors. Case and Elim visit their original
motive, arms and scrutinee in order. The original dependent positions
carry expanded conversion, and constructor selection with the authenticated
signature witnesses the actual iota rule. The emitted application spine
reenters the typed visitor. An induction hypothesis passed to another
branch can enter the conversion visitor, which also supports recursive
family computation and visible globals. Borrow and Deref share their
ordinary cancellation, and View carries the same prefix through each
constructor telescope visit and its generated borrowed hypotheses.
The paired comparison theorem uses this joint family visitor for both roots.

Three exact-byte admitted fixtures cover the shared paths. Case visits
earlier globals in the motive, branch annotation, and owned scrutinee,
then returns an allocation at its original Buffer type in 33 ticks.
Recursive Elim uses an earlier global base proof and returns the original
converted equality result. A recursive View uses a global arm and
returns the expected equality in 81 ticks. Existing metadata and constructor
shape guards remain part of the successful fragment.

The Transport theorem reconstructs the native Eq typing premises and
uses the reflected affine equality of the original endpoints to derive
kernel conversion. It transports a checked vector-indexed family carrier
from the written expression `1+1` to `2`. A separate admitted proof
under Type31 and Type0 replays an erased beta in the equality argument
before exposing the proof of `2 < 3`.

A scoped runtime reader can now evaluate signed arithmetic across
multiple actual reads from the fresh reference and from older live
references it captures. Checked projection identifies the original
operand receipts, and the reference size interpretation and erased
evidence give each index bound. The replay and actual machine agree on
the current cells, read order and scalar result. Closing the fresh loan
restores the original typed owner and callback while preserving every
older lease's indexed observation. An admitted nested fixture reads
31 from the new loan and 8 from an older loan in the same reader, then
reads the old value again after the inner close and returns 47.

The aggregate check passed 1,111 Lake jobs, 10,423 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Ghost application inference, Strict scrutinees, open Transport, and reader progress

Ghost inference now shares the graph and step counter with type weakening,
Pi exposure, argument-type normalization, identity, and capture-avoiding
codomain substitution. Local variable lookup derives the exact weakening
from the pre-binder context. Global lookup uses the original declaration
type root from the admitted graph. Each argument check normalizes both types
before identity. The codomain is instantiated with the original argument
reference. When the compared types retain every position, identity supplies
kernel conversion. The established Loan64 uniqueness theorem then relates
the represented inferred type to the original checked declaration type.
The same proof accepts the recursive family visitor for both normalization
phases. The executable fragment covers variables, globals, applications and
scalar and universe heads in ghost mode.

The admitted two-application fixture infers `Eq(7,7)` in 59 ticks, including
substitution under an erased binder. It also checks prefix retention when
the final substitution exceeds the work budget, and weakening of an older
erased binder in an open context. A direct Jihoo `Core.infer` run on the
same source nodes and checked prefix returned the same represented type
and appended the same four nodes in order, with references relative to the
arena after prefix checking.

The typed family visitor now handles the native Strict scrutinee branch for
Case and data Elim on data families whose indices are all parameters. If the
expanded lambda motive has a closed body, actual beta conversion preserves
the exact result type as Strict moves outside the family operation. In the
admitted Buffer examples, a signed overflow remains the Strict prefix.
Both graph traces append the inner elimination, branch application and
outer Strict in 45 ticks. A step budget of 17 retains the newly appended
elimination when its next child visit fails.

The open Transport proof obtains the body derivation from the actual
byte-admitted declaration and instantiates its written affine telescope.
Erased beta may hide an equality assumption. The source spine computes
the fuel to expose it, and the satisfying valuation supplies the closed
Refl witness. The typed residual has the original instantiated annotation
when the checker supplies its formation. A canonical byte fixture
transports a strict inequality from one bound word to a distinct
equality-related bound word. Its proof works for every satisfying
valuation, including the largest U64 values, where the affine result
indices exceed the word range.

For a supported checked reader, the machine theorem now derives the
successful read operands and reports either a typed restoration after
closing or the exact signed overflow prefix with the lease still open.
Captured indices obtain their scalar width from the originating typing.
Computed word sums require a fitting mathematical result, and captured
reads require a checked Buffer reference in the original context. The
admitted overflow example reads through the fresh lease and faults before
the older captured read. It keeps both leases in the terminal state.

The aggregate check passed 1,115 Lake jobs, 10,467 distinct declaration
audits, and all generated fixture comparisons under the project resource
guard. The audit found only Lean's three standard axioms.

### Primitive ghost inference

Array and Buffer formation, Eq, Lt, Refl, UAdd, and signed arithmetic share
an ordered operand checker. The graph model appends a single expected scalar
type, infers and compares each operand at child depth, and appends the raw
result type after the checks. The soundness proof derives Loan64 typing for
each operand from the actual comparison trace and uses the original operand
references for the dependent result of Refl. Retention of the compared terms
remains a hypothesis of the general inference theorem.

The version-6 admission example infers `Eq(7+1,7+1)` at its original sum
reference in 13 ticks. The mismatch example stops at the first `Eq` operand
in five ticks after appending the expected U64 and the inferred I64. The three
new declarations join the project axiom audit. The native kernel correspondence
suite checks both traces against `Core.infer` using the shared work limit and
the actual graph rows.

### Dependent binder inference

Pi and lambda first infer and expose the domain sort. For erased type domains,
the graph visitor checks a normalized U64 or consults the declared data-family
flag. Context representation then extends with the original domain at its
pre-binder scope. Lambda returns a Pi using the body type directly. Pi exposes
the codomain sort and computes the product sort, including the impredicative
Prop case. The soundness theorem carries the context representation through
allocation and derives the binder and body judgments used by Loan64 typing.

The admitted erased U64 lambda uses the new variable in a Refl result in ten
ticks. The admitted product over Type31 returns Prop in 13 ticks, with Type32
used for the intermediate sort query. Native `Core.infer` matches both traces
under the same work limits, and nine new declarations join the axiom audit.

### Decidable inequalities and Strict inference

Decide checks both operands against a shared U64 type before normalizing the
original inputs. An accepted graph result exposes two in-range numerals in
strict order. The proof obtains conversion from each written operand to its
numeral and constructs the Loan64 decision judgment at the written inequality.
Strict infers both terms in order and returns the second term's original type.

An admitted Strict prefix followed by Decide returns `Lt(1,2)` in 13 ticks.
The descending comparison stops in 11 ticks and retains its completed
operand-check rows. The native schedule probe checks both against `Core.infer`.

### Unsigned bounds and subtraction inference

ZeroLe uses the original U64 operand in the generated successor and inequality.
USub constructs `Lt(b,a+1)`, checks the original evidence at that type, and
emits U64 after the check. The theorem reflects comparison of the bound
against the inferred proof type and retains the graph through rejection.

The exact-byte ZeroLe example keeps the successor of the largest U64 as a
ghost sum. The subtraction example exhausts its budget at the first tick of
the bound comparison, with both proposition graphs committed. Native
`Core.infer` checks the same arena and work boundaries.

### Open motives for Strict family scrutinees

The Case and data Elim guard lowers the expanded motive body across the
scrutinee binder. Successful lowering reweakens to the original body, so
beta substitution with either scrutinee yields the same type in the
enclosing context. This connects the existing Strict visitor to motives
such as `Buffer(n)` where `n` belongs to an older binder.

The Lean regression checks that this open motive satisfies the preservation
guard and that a separate motive that uses the scrutinee is rejected. The
existing exact-byte Case and data Elim examples also pass.

### Conditional inference and erased assumptions

The shared IfLt and IfEq path checks both operands, appends the appropriate
proposition, and infers the consequent under that erased binder. The
normalizer and negative shift lower the consequent type into the enclosing
scope. The soundness proof recovers its exact reweakening and checks the
alternative there. The resulting Loan64 judgment retains both branch types
and the original comparison operands.

An admitted IfLt has a consequent that returns its erased assumption and an
alternative that supplies a checked Decide. Lean and native `Core.infer`
return the same inequality row and append the same graph in 39 ticks.

### Computed index bounds from checked reader evidence

The reader proof closes its original index using the typed captured words
and reconstructs its affine expression. Inverting the original Decide
derivation and comparing the affine conversion yields the mathematical
sum strictly below the represented length and its U64 width. Nonnegative
subexpressions inherit the bound, so the actual word computation has the
value used for the indexed read. The reader progress theorem uses this
derivation for fresh and captured Buffer references.

The nested-reader example still reaches the signed overflow after its first
read, with both leases present. The two new bound and value theorems join the
axiom audit.

### Aggregate check of the reader-width checkpoint

At `8a084d9`, the rootless Nix proof shell completed all 1,116 Lake jobs,
the generated fixture comparisons and the exact audit of 10,487 declarations.
Of these, 526 require no axioms. The remaining declarations use only
`propext`, `Quot.sound`, and `Classical.choice`. The proof guard measured
4,763.2 MiB peak sampled RSS across the process tree.

The compiler rebuilt from the checkout reported Jihoo 0.6.0. Its kernel
correspondence suite passed 89 native fixtures and 31 additional checks.
Mixed declaration checking passed 69 source fixtures and 55 exact-byte
checks, including pure admission of the native snapshot.

### Reader index bounds from closed arithmetic proofs

The checked reader tree accepts closed evidence built from arithmetic proof
operators, including LtAdd, LtCancel, LtLe, and ZeroLe. The original Index
judgment supplies the proof type. The live reference identifies the actual
buffer, and the sized heap translates the written upper endpoint to its
physical length. Numeric reachability supplies the width of that length.
Arithmetic interpretation then gives the exact unsigned operand and
constructs the read without an independent numerical guard.

The nested example uses LtAdd over ZeroLe as its read evidence. It reads the
fresh lease at index 1 and faults on signed overflow before reading the
captured outer lease. Both leases remain live at the fault. The focused
Lake build passed all 422 jobs.

### Indexed motives for Strict family scrutinees

The Strict visitor now follows the nonparameter index binders before
checking the final scrutinee binder. Lowering and reweakening prove that
the motive's body remains independent of that binder under every
substitution for the earlier indices. Case and data Elim keep their
original checked branch types and reconstruct the original result type
using the authenticated family arity.

The exact-byte fixture uses `Box(n)` with a `Buffer(n)` field. Both
eliminators keep the overflowing prefix and give the selected allocation
type `Buffer(2)`. The rebuilt native compiler independently admits both
definitions, checks their original-type preservation and returns the
same Strict graph shape.

### Refinement inference and dependent evidence

Refine and Pack check their predicate at the synthesized `U64 → Prop`
type. Pack applies that predicate to the original witness before checking
the evidence. Witness and Proof expose the inferred refinement type, and
Proof constructs the dependent result by applying its predicate to a
Witness of the original subject. Successful inference retains the
checked operand types in the Loan64 derivation.

The rebuilt compiler matches the Refine arena and 24-tick schedule. It
also matches the Pack failure at tick 29 with the required dependent
application already present. The admitted Lean example for Proof keeps
the original global subject. The focused build passed 329 jobs and a
32-declaration axiom audit.

### Dependent entry into a saved erased closure

The indexed machine keeps the closure's original body and capture context.
Its erased argument supplies a checked ghost substitution from the caller's
context and occupies no runtime slot. The actual entry step has the
instantiated dependent result type and preserves the captured ownership
demands and active loan associations. The resource checker supplies the
erased body scope for a single leading lambda.

The admitted regression places overflowing arithmetic inside the erased
evidence. The machine enters the body directly, returns 7 and emits only
the closure activation. The focused build passed 407 jobs and the four
new theorems use only standard Lean axioms.

### Erased entry into a leading lambda telescope

The saved erased closure enters its original body at the closed dependent
result type even when that body begins with another lambda. Reintroducing
the inner closure boundary preserves zero demand for captured owners and
active loans. The body keeps its original projection under the erased binder.

The admitted example skips an overflowing erased operand, closes the inner
lambda, and returns the relevant input `11`. The focused build passed 407
jobs. The three audited declarations use only standard Lean axioms.

### Inequality inference with a shared offset

The metered ghost checker builds both sums and both inequalities before
checking the original proof. `LtAdd` returns the shifted inequality and
`LtCancel` returns the original. The source derivation uses the Loan64
arithmetic evidence rule corresponding to the native operator.

Lean and the rebuilt compiler agree on exhaustion at tick 14 with both
inequality nodes retained. The native regression also checks both successful
directions. The focused build passed 329 jobs and the 34-declaration audit
used only standard Lean axioms.

### Metered transitive inequality inference

`LtLe` builds the upper endpoint's successor and the two ordered bounds
before visiting either proof. The metered inference proof uses the original
five operands and constructs the Loan64 transitivity judgment once the
normalizer accepts both evidence types. Lean and the rebuilt compiler agree
on the prefix at tick 14. The first checkpoint checked the complete native
call and the Lean prefix before the upper bound's addition.

The recursive ghost traversal now normalizes sums of two literal operands
whose result fits a U64. This path agrees with the established Core.sum
model on both collection visits, the graph append or graph error and the
shared counter. The exact-byte inference theorem uses the new traversal.
On the closed `LtLe` fixture, Lean and the rebuilt compiler both spend 57
ticks and place the final inequality at row 26 of a 27-row arena. The
focused build passed 427 jobs and its nine-declaration audit used only
standard Lean axioms.

The same ghost traversal also handles sums of two U64 literals whose total
exceeds a word. Arithmetic reduction constructs the balanced result before
lifting that reduction through the typed computation relation. The native
sum model and Lean agree on the shared half in `U64.max + 1` and all five
ticks. The focused rebuild passed 427 jobs and the audit used only
standard Lean axioms.

### Metered array and allocation inference

`Elements` checks each signed value before emitting the array length, and
`Alloc` checks the unsigned count before its signed fill. The inferred
`Buffer` retains the original count reference. Lean and the rebuilt compiler
agree on the nine-tick successful paths and on the array prefix at tick 6.
The focused build passed 427 jobs and its four-declaration audit used only
standard Lean axioms.

### Metered store and release inference

`Store` exposes the checked buffer length, checks its index and signed value
in order, and builds the original dependent inequality before visiting the
proof. `Free` checks the owned operand and returns the original checked tail
type. Lean and the rebuilt compiler agree on the retained inequality at
tick 21 and on the successful 40-tick store and 44-tick release paths.
The focused build passed 427 jobs and the three-declaration audit used only
standard Lean axioms.

### Ghost inference of an impossible case

`Absurd` checks the requested type's sort, exposes the evidence's original
inequality and normalizes its upper endpoint to zero. It returns the written
target reference. Lean and the rebuilt compiler agree on the 11-tick path
under an erased impossible hypothesis. The focused inference build and
three-declaration standard-axiom audit passed.

### Relevant closure entry with returned non-owner values

The actual pending argument frame opens the saved closure at the dependent
result type instantiated by the returned value's source representative.
The event still records the original argument expression. The proof
constructs the updated value and size contexts and preserves both directions
of the active-loan association. The shared resource lemma recovers the body
receipt through a leading telescope for both relevant and erased entry.

The focused build passed 407 jobs. Both entry theorems use only standard
Lean axioms.

### Aggregate check of inequality inference and closure entry

At `18e09eb`, the proof shell completed 1,117 Lake jobs, the generated
fixture comparisons and the exact audit of 10,523 declarations. The audit
found 526 axiom-free declarations and only standard axioms elsewhere.

The rebuilt Jihoo 0.6.0 passed 89 kernel fixtures and 31 additional checks,
with the offset inference assertions in the native schedule. Mixed checking
passed 69 source fixtures and 55 exact-byte checks, including pure mixed
admission of the native snapshot. The proof guard reported a peak sampled
tree RSS of 4,762.9 MiB for the combined run.

### Closing the complete application telescope

Loan-aware resource projection exposes the original application replay,
the ordered runtime operand receipts and the receipt of the body after
consuming the leading source lambdas. Each replayed argument closes the
original dependent domain under the store built by the preceding arguments.
The theorem retains the original CODE body derivation, the exact closed
result at that boundary and the remaining application replay. It permits
different caller and capture contexts and uses no CODE substitution rule.

The same projected application carries the enclosing loan budget through
every relevant operand and through all consumed local scopes. Each active
loan has zero owner demand in the original body at the depth of the opened
telescope. The focused build passed 274 jobs and the seven-declaration
audit used only standard Lean axioms.

At the exact slot of any consumed linear or erased binder, the body receipt
records respectively one or zero uses. The checked application supplies these
counts in the original source order through any mixture of binder modes.
Every finite body prefix obeys the bound and every completed body has the
exact count. The focused build and two-declaration audit passed.

### Dependent semantics of equality transport

The equality relation combines agreement of the represented natural values
with raw conversion of the evidence to canonical Refl. Agreement transports
the semantic payload between dependent proposition fibers, and the native
Refl equation preserves its raw realization in the destination fiber.
Original typing and a typed delta or contextual computation exposing Refl
construct the equality realization for closed endpoints with known numeric
meanings. The two modules passed their focused build and eight-declaration
standard-axiom audit.

### Proof irrelevance in dependent type comparison

Two closed Type1 annotations apply the same bound type family to
`Pack` values with the same witness and different proofs of `Lt(0,1)`.
The rebuilt compiler checks both annotations and accepts their equality.
The corresponding Lean graph identity succeeds. The raw conversion
classes are distinct by constructor injectivity, neutral application
injectivity and the separation of ZeroLe and Decide. Native refinement
therefore needs typed proof irrelevance at ignored fields.

The focused build passed 290 jobs. The separation theorem uses only the
three standard Lean axioms.

### Reader bounds after typed proof replay

The same reader proof accepts arithmetic evidence reached by bounded
Loan64 proof normalization in the actual mixed declaration history. Typed
preservation gives the residual the original inequality. The index proof
then uses that inequality and the physical allocation length to compute the
word and construct the read.

The nested reader fixture wraps its arithmetic bound in an erased beta
redex. The focused build passed 423 jobs, including evidence replay and
the same overflow prefix, and its 10-declaration audit used only standard
Lean axioms.

### Equality transport inference

Transport first checks its predicate at `U64 → Prop`, then exposes the
checked equality proof's endpoints. The payload is checked at the source
fiber, and the graph returns the original predicate applied to the
destination endpoint. The soundness proof retains both checked operands
and uses the Loan64 transport rule.

Lean and the rebuilt compiler agree on exhaustion at tick 33 when
entering the payload, with its required source fiber already committed.
The native Proof projection separately confirms that the emitted Witness
uses the original local subject and consumes 14 ticks. The focused build
and 33-declaration axiom audit passed.

### Dependent semantics of refinement values

The finite semantic model interprets `Refine(P)` in Type0 as a natural
number paired with evidence in the proposition carrier for that number.
Pack builds the pair in any dependent valuation context. Witness and
Proof realize the two projections using the original raw equations.

Convertible witnesses determine the same semantic refinement value.
Every semantic family therefore assigns the same fiber to packs of the
same word with different proofs of the predicate. These local semantic
rules compose with the existing dependent relation. Reconstructing the
relation from arbitrary checked terms remains open. The focused build
passed 100 jobs and a six-declaration axiom audit.

### Aggregate check of the refinement and transport checkpoint

At `7e5b05a`, the proof shell completed 1,117 Lake jobs, generated fixture
comparisons and the exact audit of 10,508 declarations. The 526
axiom-free declarations and the remaining dependencies all met the
standard-axiom check.

Jihoo 0.6.0 passed 89 native kernel fixtures and 31 additional checks
with the expanded inference schedule and indexed Strict regression.
Mixed declaration checking also passed 69 source fixtures and 55
exact-byte checks. The proof guard reported 4,783.9 MiB peak sampled
RSS for the combined run.

### Checked lambda creation retains the original capture

For any accepted lambda projection, the checker exposes the resolved binder
mode and the original body receipt, including a leading telescope. The
indexed machine's actual closure creation keeps the capture, the original
dependent body derivation and its closed Pi type. The checked closure
receipt gives zero demand for each captured owner.

The admitted higher-order example returns a closure with both source
binders intact. The focused Lake build and the audit of the three new
theorems passed.

### Pure preservation for scrutinee-dependent Strict motives

The Case and data Elim arena rewrite shares one graph proof for both
typing interpretations. Pure typing keeps the original independently
formed result annotation even when the motive uses the scrutinee. The
shaped Strict conversion relates the two motive applications, and the
original checked arms and effect derivation are reused.

The dependent fixture computes a buffer's result length from a field in
the scrutinized value. Lean derives the original written type after
moving Strict. The native regression checks both eliminators and the
retained overflow prefix. The focused build passed 326 jobs and the
three new audited theorems use only standard Lean axioms.

### Pure conversion for identity with nested Strict

Graph identity can skip Strict effects at any retained position. When
the compared portions retain all evidence fields, the shaped Strict
equation relates each input to a fully retained tree. Structural identity
of those trees yields pure conversion between the original inputs.
The exact graph fixture compares two equality propositions in four ticks.
The focused build passed 290 jobs and its three audited theorems use only
standard Lean axioms.

### Reconstructing checked literal refinement values

For a checked Pack guarded by a literal upper bound, the original word
projection supplies its U64 width. Typed proof extraction and arithmetic
interpretation derive the predicate's truth from the source evidence.
These facts construct the concrete value in the dependent relation.
Two checked packs of the same literal with supported proofs of that bound
share one interpretation. The focused build passed 384 jobs and both
new theorems use only standard Lean axioms.

### Refinement semantics after typed operand computation

The original checked Pack retains its type while its witness and evidence
take typed steps under the same mixed declaration history. The computed word
and arithmetic evidence then construct the dependent value. Raw conversion
transports this realization back to the original Pack. An admitted fixture
hides both operands behind beta applications and realizes the word `3` in
the original refinement fiber. The focused check passed 384 jobs, and both
theorems use only standard Lean axioms.

### Computed refinement values in calls and comparison

The pending machine frame for a Pack restores the saved continuation with
the returned word. Typed replay constructs the corresponding Pack at the
original requested type and retains its dependent evidence.

Two checked Packs whose witnesses compute to the same word give a realized
dependent function one semantic argument. Its two source applications
realize one result in the same fiber. At an ignored evidence field, raw
conversion of the two retained operands transports both proofs to a common
formed proposition. The focused builds and four-declaration audit passed.

A saved relevant closure now binds the actual refinement word in its
runtime slot and uses the checked Pack representative to close the original
dependent result. The checked body retains its captured owners and active
loans. A Witness of the new slot returns the same word at that original
result type in four machine steps, with the original activation event and
saved continuation. The focused build passed 410 jobs and the three new
theorems use only standard Lean axioms.

### Aggregate check of call telescopes and literal arithmetic

At `62b0f7b`, 1,120 Lake jobs and the generated fixture comparisons passed.
The exact audit covered 10,543 declarations, with 526 axiom-free and only
standard Lean axioms in the others. The native kernel suite passed 89
fixtures and 31 additional checks. Mixed checking passed 69 source fixtures
and 55 exact-byte checks, including the pure admission of the native
snapshot. Peak sampled process-tree RSS was 4,761.0 MiB.

### Aggregate check of refinement closure entry and buffer effects

At `8368935`, 1,120 Lake jobs and the generated fixture comparisons passed.
The exact audit covered 10,557 declarations, with 526 axiom-free and only
standard Lean axioms in the others. The rebuilt compiler passed 89 native
kernel fixtures and 31 additional checks. Mixed checking passed 69 source
fixtures and 55 exact-byte checks, including the pure admission of the
native snapshot. Peak sampled process-tree RSS was 4,764.8 MiB.

### Comparison paths and ownership after entering a full call

Successful native graph identity now relates the original retained occurrences
in order at every depth. For well-formed terms it preserves the full opcode,
including the arity hidden by field omission, and records where Strict nodes
were stripped. A pair of checked dependent types illustrates the retained Pack
position under a family application. Source inversion of the original Pi and
application derivations types the two skipped proofs at the same formed
proposition when the retained operands are convertible. A general typed
comparison interpretation under arbitrary binders is still open.

The final entered call telescope gives a demand of one for each installed live
linear owner. Existing aliases of those owners retain zero demand, and all
other captured slots retain their original exact demand. The theorem uses the
actual slot ordering and local checked-scope conditions. Installation and
retirement still need to be derived across arbitrary machine call sequences.
The focused build passed 421 jobs and the five new declarations use only
standard Lean axioms.

### Metered array and borrowed-buffer indexing

Ghost Index inference now follows the native split after normalizing the
subject's type. The array branch uses the emitted array length. The borrow
branch normalizes the inner type separately, exposing the original buffer
length. Both branches check the U64 index and its evidence in that original
bound and return I64. The admitted examples agree with the rebuilt compiler
at 36 ticks for the array and 34 for the borrow, including the exact bound
and result roots. The focused build passed 427 jobs and the new theorem
uses only standard Lean axioms.

### Inequality evidence in open dependent contexts

The concrete dependent relation now interprets Lt, ZeroLe, shifting and
cancelling strict bounds, transitivity and Absurd. A checked Decide recovers
the original literal comparisons from its actual Loan64 derivation and proves
the order of the two interpreted words at every realized valuation. In an
empty context this constructs the proposition's semantic proof.

Bounded subtraction uses the proof of the original `b < a + 1` fiber and
the word bound only at realized valuations. Different valid evidence terms
produce the same subtraction value and the same result when passed to any
interpreted dependent family. The theorem uses literal source contraction
after realizing the operands. General gluing for wide subtraction and the
interpretation of all source derivations remain open. The focused build passed
202 jobs and the nine new declarations use only standard Lean axioms.

### Metered dependent Load callback inference

Ghost Load checks the original buffer length, index and bound, then infers
the actual successive value and owner binders. It shifts the open length
once before comparing the owner domain and removes both binders from the
normalized result. The source rule is reconstructed from the two checked
domains and the exact lowering. The admitted fixture and the rebuilt
compiler agree on the initial proof bound, the shifted owner domain and the
original I64 result at 67 ticks, including the budget failure at the final
lowering. The focused build passed 427 jobs and the new theorem uses only
standard Lean axioms.

### Actual call entry and dependent arithmetic branches

The mutable machine now has a call-entry theorem for the original checked
application spine. It pushes the actual function frames, runs each relevant
operand in its saved argument frame, skips each erased operand, and produces
one activation and one runtime slot per consumed binder. Unconsumed
arguments remain on the stack. The resulting code retains the original
dependent body and closing substitution, and the final slot list gives its
ownership demand when the local liveness, alias and retirement conditions
hold. Arbitrary operand success and owner retirement still need to follow
from the full source execution invariant.

The gluing model uses the actual IfLt branch rule with the erased Decide
term in the true arm and the unchanged valuation in the false arm. Native
ghost cancellation on checked literal sum trees realizes the exact
mathematical difference, including values wider than one word. The output
retains its original type and possible Strict prefixes. The focused build
passed 520 jobs and all seven new declarations use only standard Lean
axioms.

### Aggregate check of call entry and dependent arithmetic

At `76ca5c2`, 1,126 Lake jobs and the generated fixture comparisons passed.
The exact audit covered 10,580 declarations, with 526 axiom-free and only
standard Lean axioms in the others. The rebuilt compiler passed 89 native
kernel fixtures and 31 additional checks. Mixed checking passed 69 source
fixtures and 55 exact-byte checks, including the pure admission of the
native snapshot. Peak sampled process-tree RSS was 4,769.9 MiB.

### Metered ghost references and admitted family ownership

Ghost Ref now checks the inferred sort and the actual owned head. Borrow
uses the normalized head for the ownership check and retains the original
inferred owner type in Ref. Deref exposes that Ref and returns the exact
target root. Boxed-family metadata comes from the admitted program. An
accepted recursive family permits Borrow, and a flat family rejects it.

The rebuilt compiler agrees with the Lean examples at 9 ticks for Ref, 12
for Borrow, 16 for the borrowed buffer's Deref and 7 for a boxed family
borrow and Deref. The flat family rejection adds no rows. The focused
build passed 428 jobs and all six new declarations use standard Lean axioms.

### Erased returned ownership and equality branch semantics

The dependent Back relation now interprets an owner returned with erased
evidence as a subtype of its original owner at Type0. The source candidate
retains the actual Give constructor and evidence. The two original checked
Give derivations reconstruct the common formed proposition, and either
proof supplies the same semantic owner to a dependent family.

IfEq now realizes the original dependent result in both branches. The
true branch extends the valuation with the actual Refl term, which meets
the canonical equality premise used by Transport. The false branch uses
the original valuation. The result uses the literal rule after related
operands fit a physical word. The focused build passed 390 jobs and the
four new declarations use only standard Lean axioms.

### Metered inductive family formation

Ghost family formation reads the declared index arity and sort from the
checked table. A successful query checks every index as U64. The index
checker uses native depth 128 and the original cumulative work counter,
even when the enclosing type visit starts with depth one. The recursive
driver now distinguishes its visit allowance from that depth parameter.

The Lean and native fixtures agree on the exact graph and five ticks for
both Prop and Type0 results. The native test also rejects an unchecked
family and checks arity before any graph append. The focused build passed
428 jobs and the four new declarations use standard Lean axioms.

### Earlier family tables and checked constructor field walks

At any checked definition, filtering the final immutable signature table
by declaration position gives exactly the family entries in its actual
earlier mixed history. This includes families checked at that position and
excludes families declared after the definition.

The metered constructor field walk checks the actual inferred operand
against the live Pi domain, substitutes the original graph argument into
the codomain, and finishes at the normalized inductive result. It produces
the complete Loan64 Arguments derivation at the starting telescope.
Connecting that telescope to production constructor lookup and the initial
signature shift is the next part of constructor inference.

The original typing of an occurrence can now be recovered along any path of
Pi and lambda domains or bodies, applications and retained Strict tails.
With converted binder contexts, the two proof fields at aligned positions
still inhabit the same formed dependent proposition when their retained
operands are convertible. The focused build passed 436 jobs and the six new
declarations use only standard Lean axioms.

### Authentic metered constructor signature and field checking

The original version-6 family row and the mixed admission history now select
the written constructor graph and its corresponding checked telescope. The
checked field and index conversions relate the two telescopes in the actual
earlier environment. The constructor inference branch shifts the written
signature at the caller depth, checks its fields and derives the original
family result. A successful dependent substitution keeps that family head.

The native fixture and Lean branch agree at 54 ticks including the entry
tick, with the same instantiated evidence type and final index root. Both
reject the incomplete field list. The focused build passed 432 jobs and
the nine new declarations use only standard Lean axioms. This branch is
available separately from the recursive inference dispatch.

### Aggregate check of family and constructor inference

At `62a6e12`, 1,135 Lake jobs and the generated fixture comparisons passed.
The exact audit covered 10,609 declarations, with 527 axiom-free and only
standard Lean axioms in the others. The rebuilt compiler passed 89 native
kernel fixtures and 31 additional checks. Mixed checking passed 69 source
fixtures and 55 exact-byte checks, including the pure admission of the
native snapshot. Peak sampled process-tree RSS was 4,780.5 MiB.

### Constructor dispatch in recursive ghost inference

The recursive graph driver now retrieves the constructor from the checked
family graph visible at the current declaration. It shifts the written
signature by the source context length and calls the metered field checker
with the same recursive inference function used for other operands. Its
soundness theorem therefore produces the typed constructor result for
nested calls as well as for the outer expression.

The recursive fixture reproduces the native graph and all 54 ticks from
the initial state. The focused build passed 434 jobs and the four new
audited declarations use only standard Lean axioms.

### Enclosing readers across argument evaluation

Actual mutable call entry preserves the exact token-to-owner lease map of
all enclosing reader frames. Relevant arguments may execute heap operations
and open and close their own temporary readers. The resulting invariant and
heap lifecycle trace come from the same argument run and identify the
original reader inventory at the entered body. The focused build passed
414 jobs. The new theorem uses `propext` and `Quot.sound`.

### Declaration annotations select the body checking mode

The native-shaped annotation check infers the original graph root and
normalizes its answer to a sort on the same meter. Exact mixed admission
supplies the actual written annotation and its source expansion. Sort
rigidity and typing uniqueness identify the mode with the one in the
checked declaration history and recover the original body at that type.

The native and Lean checks agree at ten ticks for an equality annotation
selecting ghost mode and two for a word annotation selecting code mode.
The focused build passed 434 jobs and the four new audited declarations
use only standard Lean axioms.

### Applying an erased owner-return continuation

Given an original checked `Take` and a related owner, evidence and
continuation, applying the actual two-binder continuation realizes the
original caller's type. The first application substitutes the owner into
the evidence fiber. The second uses evidence at that instantiated fiber.
The typing conclusion uses the genuine checked `Take`/`Give` preservation
rule. The focused build and the new theorem's axiom audit passed.

### Checking a proof declaration at its original annotation

When the annotation's inferred sort selects evidence mode, the declaration
checker infers the original body and compares its inferred type with the
original annotation. Successful checking derives both formation and ghost
body typing at that annotation. The graph and meter run continuously from
annotation inference to the last identity visit.

The Lean and native fixtures spend exactly 24 ticks. With 23 allowed,
the final comparison fails with the same committed graph prefix. The native
fixture also exercises `Core.extend`. The focused build passed 435 jobs and
the three new audited declarations use only standard Lean axioms.

### Captured owner demand across the actual call trace

At call entry, the capture store's earlier ownership world survives exactly
when the actual argument trace releases none of its demanded allocations.
This derives capture liveness for the entered telescope from its initial
world and the release trace. New slots still require checked facts about
their mode, liveness, exclusivity and retired aliases. The focused build
passed 414 jobs and the three new declarations use standard Lean axioms.

### Aggregate check of constructor dispatch, declarations and call entry

At `f1983c6`, 1,141 Lake jobs and the generated fixture comparisons passed.
The audit covered 10,625 declarations, with 527 axiom-free and only
standard Lean axioms in the others. The rebuilt compiler passed 89 native
kernel fixtures and 31 additional checks. Mixed checking passed 69 source
fixtures and 55 exact-byte checks, including the pure admission of the
native snapshot. Peak sampled process-tree RSS was 4,794.2 MiB.

### Boxed Drop inference

Recursive ghost inference checks that the visible family is boxed before
visiting the owner. It exposes the owner's inferred inductive type, checks
the exact family identity, and retains the checked tail's original type.

The native and Lean fixtures produce the same signed tail type in five
ticks and reject the flat family in one tick with no graph append. The
focused build passed 433 jobs. The new fixture and the updated recursive
soundness theorem use only standard Lean axioms.

### Code inference for local and scalar heads

The code-mode head checker rejects an erased local after its entry tick.
A relevant local shifts the original graph domain under its exact caller
depth and produces the corresponding code typing derivation. Native and
Lean agree on three ticks and two new rows for a dependent local domain,
and one tick with no new rows for the erased access.

The declaration driver now checks both modes with sound body visitors at
the selected sort. Its word declaration uses the actual code-mode head
checker and spends six ticks across the two original roots and comparison.
The native exhaustion fixture also compares every committed proof check row.
The focused build passed 439 jobs and the eight new audited declarations
use only standard Lean axioms.

### Owner-return type and result inference

The ghost `Back` and `Give` branches use the native motive check. The
inferred motive exposes a relevant owner argument and a sort selected by
erasure. Relevant results pass the representation check. `Give` checks
the result against an application of the written motive to the original
owner expression. Its output retains that motive and the owner's type.

The native and Lean fixtures agree on 32 ticks for relevant `Back`, 36
for erased `Back`, and 48 for `Give`, and reject a borrowed result type.
The focused build passed 439 jobs and the seven new declarations use only
standard Lean axioms. These two branches are checked independently of
dispatch in the full recursive driver.

### Dependent realizations across exact graph normalization

The raw family-aware normalizer in the authentic mixed history retains the
original caller annotation and the realization of each semantic value at
every related valuation. The theorem identifies the actual selected arena
row, transports source typing to that residual and proves realization
equivalence in the same dependent type. The focused build and the new
theorem's standard-axiom audit passed.

### Native Fold and Loop callback telescopes

The graph builders for both iteration forms use the original count below
the index binder. `Fold` weakens the same open accumulator type by two
binders for its domain and three for its result. `Loop` instead applies
the correctly weakened motive at the current and next index. Its proof
flag determines accumulator erasure. The output graph represents the
specified three-binder type and retains all existing rows.

Open native and Lean fixtures agree on the callback edges and five ticks
for `Fold` and three for `Loop`. The focused build passed 329 jobs and all
five new declarations use standard Lean axioms.

### Aggregate check of code mode and iteration telescope construction

At `0d4dd1f`, 1,147 Lake jobs and the generated fixture comparisons passed.
The audit covered 10,647 declarations, with 527 axiom-free and only
standard Lean axioms in the others. The rebuilt compiler passed 89 native
kernel fixtures and 31 additional checks. Mixed checking passed 69 source
fixtures and 55 exact-byte checks, including the pure admission of the
native snapshot. Peak sampled process-tree RSS was 4,798.5 MiB.
