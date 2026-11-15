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
