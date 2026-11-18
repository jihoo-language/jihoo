# Active whole-kernel verification work

The whole-kernel verification work has resumed. Verified checkpoints are
committed and pushed as the work progresses. The completion obligations below
remain open.

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
- The aggregate proof check currently audits 9,156 declarations. The mixed
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
canonical source/control, resource/value and scoped owner authority across
the full typed control stack. `OwnerLoanSlots` now transports ordinary
binders, noninjective alias rebasing, reader entry/body and captured IfLt
else entry without requiring every runtime alias to share a lexical key.
Source-to-reader lifetime association must additionally identify which reader
survives closing; same-object reader existence alone is insufficient.
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
The current heap is uniform-fill/read-only `SizedBufferHeap`; Store and general
data layouts require an appropriate runtime heap interpretation as well.

## Working procedure

The user's explicit continuation instruction on 2026-11-16 is to keep working
until Codex usage is exhausted, the user asks to stop, or the full dependent
kernel proof obligations are actually completed. An active goal records that
instruction. Checked increments and pushes do not complete or pause the goal.
The subsequent explicit user pause request overrides that instruction: finish
the current checked checkpoint, commit and push it, then pause the active goal.
Do not begin another proof task until the user resumes work.

Use the current checkout of `https://github.com/jihoolang/jihoo`; the current
workstation path is `/home/user/jihoo` and the active continuation branch is
`codex/alias-reborrow-verification`. The earlier verification branch was merged
into main. Preserve existing edits and never force-push.
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
