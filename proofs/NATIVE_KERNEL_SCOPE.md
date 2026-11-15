# Full native syntax and the remaining kernel proof

The native work uses one shared `Jihoo.NativeKernel` syntax for every one of
`compiler/core.jh`'s **54** `Term` constructors. This extends beyond the older
universe-free `CoreBridge.Raw` checker. Complete syntax coverage is distinct
from complete typing-rule coverage and native implementation refinement.

## Mechanized results

`NativeSyntax` records all scalar payloads, vector lengths, child order and
implicit binding edges. `NativeSubstitution` proves simultaneous renaming and
substitution algebra, identity/composition, both interchange laws, dependent
instantiation and finite-scope/arity preservation for this entire vocabulary.
Pi/Lam bind in their second child; IfLt/IfEq bind evidence only in their true
branch. Functions stored in other fields contain explicit lambda binders.

`NativeArena` defines an independent graph representation relation and a
fuel-bounded decoder. It proves decoder soundness, eventual completeness and
uniqueness, preservation of existing meanings under arena extension, fresh
allocation, tree emission, backward references and capture-avoiding arena
renaming/substitution. The arena transformation currently decodes, transforms
the tree and emits the result. Its allocation order and work budget are not
asserted equal to the native mutable implementation.

`NativePartialRenaming` and `NativeArenaPartial` add checked removal of arbitrary
variable blocks, inverse reweakening, scope/arity preservation and native-style
no-removal rewrite. References into removed blocks explicitly fail; replacement
terms are shifted only under actual binding edges. Direct native mutable
execution and machine-cast behavior remain separate obligations.

`NativeTransform` and `NativeReplacementTransform` also traverse arena references
directly, without decoding into a tree or calling the emitter. Their successful
shift/substitute/rewrite results have the proved tree meaning and preserve every
existing node. Depth, visit and allocation budgets, u32 result bounds and signed
arithmetic side conditions are explicit. Failure-state equivalence and exact
native allocation-order/source execution remain separate obligations.

`NativeTyping` independently specifies the supported pure dependent rules with
universes, Prop, ghost/code positions and pre-binder context annotations.
`NativeCheckerSoundness` proves acceptance soundness of the actual executable
`NativeChecker`, including independent checking of type sorts. Supported rules
include:

- Universe levels below 32, Prop/U64/I64 sorts, dependent type abstraction,
  maximum universe levels for Pi and impredicative Prop codomains.
- Erased U64 indices and proposition binders, and rejection of erased variables
  in code. The earlier erased-U64 Raw discrepancy has positive native-syntax
  regressions.
- All older Raw pure operations, signed arithmetic and Strict, arithmetic
  evidence combinators, proposition-only transport and refinements.
- Verified conversion at comparisons and type-head exposure, normalized Decide
  operands, and the conservative native first-order gate for code type arguments.
  Unknown inductive-family representation is rejected by that gate.
- Evidence-binding IfLt/IfEq branches and Absurd. The true branch's inferred
  result is lowered with checked binder removal, so evidence cannot escape its
  scope. Executable code Absurd enforces the native non-function result
  restriction; code neutral application heads remain conservatively rejected.
  Ghost function results are admitted and remain stable under type substitution.
- I64 Fold and dependent Loop with Prop or Type0 motives, including scalar and
  refinement accumulators and genuine Nat induction using its induction
  hypothesis. The exact three-binder telescopes have proved renaming/substitution
  laws. Code admission conservatively rejects explicit memory/family operations
  in the body and owned accumulators; it does not certify their resource use.

`NativeConversion` proves renaming/substitution closure and soundness of the
bounded executable converter. It traverses every native child, even when that
operator has no typing rule yet. Root computation covers beta, bounded
addition/subtraction, local reads, refinement and borrow/deref projections,
literal IfLt/IfEq selection with evidence substitution, and Transport along
reflexivity. `NativeNormalization` independently defines forward computation
and proves the exact computed result is reachable. Bounded residuals need not
be normal forms, and a failed comparison is inconclusive.

`NativeModeSafety` proves mode promotion to ghost, exclusion of erased runtime
variables, constructor arity and finite-context scope of every typed term.
`NativeGhostMetatheory` proves typed renaming, weakening, simultaneous
substitution and genuine dependent instantiation for every currently supported
rule, including universe type arguments. Results are in ghost mode; this is
not an unconditional code-substitution theorem.

`NativeConfluence` proves parallel reduction's diamond property and Church–Rosser
for the selected complete-syntax conversion relation, including overlapping
borrow/deref projections. Pi, sort, equality, array and refinement injectivity
and rigid-constructor separation follow. `NativeTypeUniqueness` proves uniqueness
modulo this conversion for every current rule, even across code/ghost modes,
and derives universe limits and rejection of Type-in-Type.

`NativeContextConversion`, `NativeInversion` and `NativeRootPreservation` supply
lookup-based context transport, conversion-aware inversion and each executable
root's preservation. `NativePreservation` proves contextual ghost preservation
at the exact original type, finite-step preservation and preservation by the
actual `Conversion.normalize` implementation. This applies to all current
pure typing rules; it is not a runtime ownership preservation theorem.
Fold/Loop remain neutral computations, as in native conversion; preservation
covers reductions in their count, motive, initial value and body. In particular,
changing a dependent count preserves the original result type by conversion.

`NativeSchema` / `NativeWire` provide a canonical version-4 full-graph envelope.
Round-trip, encoding injectivity and exact-byte decoding are proved. Whole-graph
validation checks unused nodes too, with proved backward-reference, payload,
arity and graph-count consequences. A measurement pass precedes root expansion
and caps expanded tree size/depth separately from graph size.

`NativeAdmission` checks raw snapshot bytes without derivation certificates.
Acceptance implies exact input re-encoding, whole-graph validity, graph meaning
and well-formed arities for both roots, closed typing in the recorded mode, and
independent ghost typing of the requested type at an inferred sort.

`NativeDefinitions` derives a closed declaration's body mode from its type's
inferred sort, independently of the snapshot's observation-mode flag. Its pure
checker and exact-byte admission prove formation and body typing in that derived
mode. A synthetic erased data identity is accepted as a ghost observation but
rejected as an executable declaration; forging its mode flag cannot authorize
runtime access to its erased parameter.

`NativeGlobalEnvironment` checks ordered whole programs through an independent
transparent-global expansion relation. Both annotation and body expand against
the previously checked prefix, then pass the same sort-derived declaration
checker. Every interpreted entry is typed, locally closed, arity-correct and
global-free; raw references precede their declaration, earlier entries retain
their interpretation, and checked global bodies have unique types modulo
conversion. Expansion precharges repeated body occurrences and bounds output
size/depth. This conservative interpretation can reject opaque code uses of
ghost globals that native inference accepts; it is not a proof of the native
Global inference branch.

`NativeProgramWire` and `NativeProgramAdmission` bind that checked environment
to a canonical version-5 envelope containing all declaration roots and the full
shared graph. Modes are absent from the format. Acceptance proves exact bytes,
graph meanings, declaration formation/body typing, local closure, and exclusion
of forward/self references. Aggregate root expansion is checked before decoding
any declaration, with separate declaration/node/expanded-occurrence bounds.

`NativeAffineSum` implements native-shaped affine canonicalization for the
full-syntax Var/Natural/UAdd profile: sorted variable occurrences, one natural
constant and balanced oversized ghost constants with valid U64 leaves. Equality
is sound and complete for all U64-valued valuations over mathematical naturals;
the U128 collector bound, renaming/substitution compatibility and idempotence are
proved. `NativeAffineTyping` proves exact-original-type preservation in the same
input mode. Its equations now embed into full `ACU.Conv`, which is used by the unified
environment checker. The earlier pure checker retains its selected converter. Runtime folding refusal for oversized constants is explicit;
the typing theorem does not establish runtime overflow or evaluation behavior.

`NativeIrrelevanceBoundary` proves why native proof-irrelevant comparison cannot
be inserted as an unconditional untyped Pack equation: together with Proof
congruence and projection it would equate all raw terms. A faithful integration
requires formation-aware irrelevance.

`NativeFamilyEnvironment` independently checks raw constructor telescopes and
computes their signatures and layouts. Its soundness includes strict positivity,
closed and well-formed telescopes, checked U64 indices, normalized domain/result
formation, unchanged leading parameters, and recursive-field erasure policy.
The mixed program checker interleaves families at their recorded global boundary;
each accepted family has an actual earlier checked program history. It scans
original Pi/Ind structure before normalization. Earlier-family fields, buffers
and family term introduction/elimination are handled by the unified layer below.

`NativeFamilyWire` / `NativeFamilyAdmission` bind those results to exact version-6
bytes containing all definition roots, raw constructor roots, metadata and the
complete shared graph. No external signatures or computed layout bits enter
admission. All definition and constructor occurrences share the pre-expansion
budget. Acceptance derives the independent mixed program judgment and positivity,
closure and arity of every stored raw constructor type.

`NativeQuantity` projects the complete constructor vocabulary into the proved
resource-control semantics. It enforces balanced branches, exact local linear
use, erased locals, closure restrictions, repeat-body capture restrictions and
once-only continuations. Known syntactic lambda spines visit relevant arguments
once outside the consumed scopes and the body under its complete telescope.
Successful checks imply exact completed use, at-most-once prefix use and erased
unreachability in projected traces. Full-native renaming and Var/Borrow(Var)
substitution commute with the concrete projection, including dependent-reader
opening and continuation aliasing. A fresh query checks local scopes even when
the outer owner list is empty. The standalone projection takes outer owner/erased lists; `NativeOwnership`
and the unified admission layer derive them from actual types and checked family
metadata. Unknown call signatures, unresolved binder domains and alias-sensitive
Lend remain rejected. Native heap execution and u32 counter equivalence remain
separate obligations.

`NativeACU` explicitly extends conversion by UAdd associativity, commutativity
and zero, with full binding-aware renaming/substitution. `NativeACUAffine` derives
affine canonical forms through actual finite ACU and bounded literal-add
equations, without oversized invalid literals or semantic-reflection assumptions.
The separate pure `Theory` has a genuine full-syntax bag characterization,
rigid/Pi injectivity and forward Church–Rosser. Its forward reduction eliminates
zero without arbitrary unit insertion. This does not yet prove Church–Rosser or
injectivity for the combined relation at that stage. `NativeACUFullConfluence` and
`NativeACUForwardConfluence` now prove full `ACU.Conv` injectivity and an actual
common finite forward `MixedRed` reduct, including beta and every legacy
observing contraction. Zero is only eliminated; no reverse legacy contraction
is introduced. The original pure checker retains its established converter;
the unified checker uses the concrete bounded full-ACU normalizer/comparator in
all conversion, head-exposure and representation-policy slots.
The arithmetic extension additionally has a proved bag characterization,
natural/rigid/Pi injectivity and independent forward Church–Rosser. Valid literal
addition is included, while invalid oversized literals remain distinct atoms.
The proof-only unit expansion is handled symbolically; it is not the executable
native normalizer. Full beta/observation transport and contextual composition are supplied by the
subsequent transport, parallel and forward-confluence modules.
`NativeACULegacyTransport` now constructs forward mixed reductions transporting
every non-add legacy root across arithmetic equivalence, including hidden
lambda/elements/pack/borrow/reflexivity heads and dependent branch substitution.
This supplies root transport; full contextual parallel rewriting and actual combined
Church–Rosser are supplied by the subsequent full and forward confluence modules.

`NativeResourceSyntax` proves the actual Buffer/ref operation telescopes commute
with binding transformations, including checked Load-result binder removal.
`NativeOwnership` derives owner and erased positions from the concrete context,
proves agreement with weakened lookup annotations, and connects checks directly
to lookup-based trace accounting. Closed checking uses depth zero and empty
outer position lists. This removes caller-supplied resource lists at that gate;
resource typing and closed declaration admission are supplied by the unified layer.

## Actual native correspondence tests

The exhaustive writer `compiler/core_native_snapshot.jh` calls the actual native
parser/checker/inference and serializes all 54 constructors. It performs no
additional Core call during serialization. The version-4 CLI runs the same pure
admission function whose soundness is proved, after bounded input scanning.

`tests/native_kernel_schema.py` compares the Lean metadata with the actual native
Term declaration and four binder-sensitive transform cases. An exhaustive native
writer fixture also matches the proved Lean encoder for all constructors at
vector lengths 0, 1 and 3: **162 exact byte comparisons**.

`tests/core_native_kernel_correspondence.py` retains actual sources, full
snapshots, hashes and labelled synthetic mutations. Its native cases include
universes, high impredicative Prop, polymorphism in both modes, erased indices,
transport/refinement projections, evidence-binding branches, absurdity,
arithmetic evidence, scalar iteration, refinement iteration and Nat induction.
There are 89 source fixtures and 31 additional checks. This legacy pure path
retains owned/effectful-iteration gaps; the unified gate below now checks those
forms with authentic representation and quantity conditions.
Native code rejection of erased proof variables is also checked.

The production shift/substitute/rewrite routines are also exercised directly
on every constructor, three vector lengths and four operations, with an extra
free-variable case: **660 actual Core calls**. Independent before/after snapshots
preserve old-prefix comparisons; expected results come from the proved Lean
binding transformations, including explicit negative-shift rejection.

These comparisons are regression evidence. Native parser/exporter behavior,
source execution, process association and IO are outside the pure theorems.

The whole-program suite also checks 15 actual source programs, one constructed
Core API opaque-proof case and 14 labelled mutations. The affine suite compares
90 actual Core.normal results across variable/literal counts and three tree
groupings, including oversized constants; five mutations check rejection of
wrong results, prefix changes, unsupported atoms and incomplete coverage.

The family suite checks 20 actual source programs and 18 labelled mutations.
Quantity observations retain each complete arena, context references/erasure
flags and queried variable: 32 count/rejection agreements, seven deliberately
stricter invalid-local-scope checks and one unknown-callee boundary. Six
mutations test its comparison adapter. Bare native runtime_uses does not itself
validate all local scopes, so the stricter cases are not equivalence claims.

## Completion obligations

The full native kernel is verified only when the following remaining obligations
are discharged, rather than replaced with more passing fixtures:

1. Extend the proved contextual ghost preservation and typed substitution to the
   remaining typing/computation rules. Code substitution additionally needs
   preservation of mode and representation restrictions.
2. A consistency/normalization argument for the universe-aware judgment, beyond
   forward reachability of a bounded untyped simplifier.
3. The remaining typing rules: Lend and active-loan runtime Borrow,
   together with exact native opaque-global behavior. Owned/effectful iteration,
   checked families, dependent constructors, proposition/data elimination,
   Case/Drop, borrowed View, owned Ref and Back/Give/Take already share the unified judgment.
   Family Elim/Case/View/Drop computation is integrated; loan computation and
   the remaining native equations still require integration.
4. Runtime ownership, quantities, borrow/continuation boundaries and first-order
   representation, connected to the same complete native judgment. Existing
   restricted resource proofs do not automatically supply this connection.
5. The remaining native conversion equations and formation-aware
   proof-irrelevant comparison, and refinement of native graph operations,
   normalization/comparison, inference,
   family declaration and whole-program checking by their actual implementation
   semantics. A Lean port or syntactic interface audit alone does not discharge it.

The existing top-level proof goal remains active until these native-kernel
obligations are actually completed. LLVM/compiler backend verification is a
separate task.

## Reproduction

With Lean 4.34.1 and the native development toolchain:

```sh
cd proofs
bash check.sh
../scripts/proof-limits.sh lake env lean -M 4096 -j 1 -DwarningAsError=true CheckNativeInference.lean
cd ..
scripts/proof-limits.sh python3 tests/core_native_kernel_correspondence.py --output out/native-kernel-correspondence
scripts/proof-limits.sh python3 tests/core_native_program_correspondence.py --output out/native-program-correspondence
scripts/proof-limits.sh python3 tests/core_native_affine_correspondence.py --output out/native-affine-correspondence
scripts/proof-limits.sh python3 tests/core_native_family_correspondence.py --output out/native-family-correspondence
scripts/proof-limits.sh python3 tests/core_native_quantity_correspondence.py --output out/native-quantity-correspondence
scripts/proof-limits.sh python3 tests/core_native_ownership_correspondence.py --output out/native-ownership-correspondence
scripts/proof-limits.sh python3 tests/core_native_unified_correspondence.py --output out/native-unified-correspondence
scripts/proof-limits.sh python3 tests/core_native_back_correspondence.py --output out/native-back-correspondence
scripts/proof-limits.sh python3 tests/core_native_acu_normalizer_correspondence.py --output out/native-acu-normalizer-correspondence
scripts/proof-limits.sh python3 tests/core_native_delta_correspondence.py --output out/native-delta-correspondence
scripts/proof-limits.sh python3 tests/core_native_data_correspondence.py --output out/native-data-correspondence
scripts/proof-limits.sh python3 tests/core_native_owned_loop_correspondence.py --output out/native-owned-loop-correspondence
```

The aggregate imports the native modules and examples; every public theorem is
included in the exact-count axiom audit. The graph-certificates flake check
builds the admission dependencies and runs the actual native correspondence
suite, including the exhaustive schema/serialization checks.


## Unified typed environments and resource admission

`NativeKernelEnvironment` holds syntax-only global/family records shared by
signature checking and the environment-indexed kernel. `NativeEnvironmentTyping`
and its concrete checker use one mutual judgment for all earlier pure rules,
Global, Ind, dependent Con, proposition Elim, Buffer allocation/store/free/load,
Ref formation, ghost Borrow/Deref, borrowed Index and Back/Give/Take. Acceptance soundness,
actual-term arity/scope and environment-extension transport are proved. This is
a genuine extension of the earlier calculus; its old metatheorems are not
silently asserted for the added rules.

`NativeOwnershipAdmission` derives declaration mode from the inferred sort and
requires the closed quantity gate for code, independent of the observation flag.
All leading function lambdas share one telescope, matching Core.uses_function;
callbacks open the exact prefix and reclose any remaining function. This admits
owner-before-index functions while preserving real closure-capture rejection.
The source suite checks 22 programs and 21 exact-byte comparisons/mutations.

`NativeUnifiedFamilies`, `NativeUnifiedProgram` and `NativeUnifiedAdmission`
remove the earlier pure-prefix restriction. Ordinary fields, earlier families,
dependent Buffer fields and family/resource-valued globals use the same unified
checker. Independent history, recomputed positivity/parameters/layout, exact
bytes, authenticated resource projection and environment/formal-signature scope
invariants are proved. Native Lend/active-loan rules, runtime substitution
and universe consistency remain completion work. Ghost substitution, type uniqueness and exact-original-type forward
preservation are proved for every rule in this checkpoint.
The integrated source suite checks 49 mixed programs and 41 exact-byte checks,
including dependent Buffer fields, earlier flat/boxed families, constructor-valued
globals, resource leaks/duplication and malformed unused graph nodes.

`NativeACUBoundedNormalizer` supplies a concrete full-Term NormalizerKit, with
compact arbitrary-atom collection/sorting and balanced valid constant leaves.
Both actual ACU conversion soundness and exact finite forward output reachability
are proved. It preserves Option failure at fuel/work/depth limits and retains
all proof and Strict children. Of 204 actual Core.normal comparisons, 202 match
exactly; selected array-read and proof-slot-ordering boundaries are explicit,
and all outputs pass the proved comparator. Eight mutations reject.

The native runtime-only function-result guards had a real ghost preservation
bug: both added ghost Load/Absurd fixtures checked successfully but their beta
normal forms were rejected. Core now applies those capture guards only to code;
the model's executable ghost policies agree. Actual Core unit tests and all 18
preservation fixtures pass after the fix. This does not by itself discharge the
remaining source-semantics refinement or full-calculus consistency obligations.

`NativeEnvironmentConversion` connects every unified conversion and head-exposure
slot to actual `ACU.Conv` and `ACU.Bounded.kit`. Its code representation gates
conservatively reject unresolved Global aliases; ghost embedding of the earlier
pure judgment is proved without casting code policies from a smaller conversion
relation. Back/Give/Take include owned and erased results, dependent motives,
checked two-binder result removal and metadata-derived ownership. Their suite
checks 37 actual source fixtures and 28 exact-byte checks. The aggregate axiom
audit currently covers 5,670 declarations using only Lean's standard logical
axioms, with warnings treated as errors.

`NativeEnvironmentOperationalRoots` proves original-type ghost preservation for
additional pure value equations: signed literal arithmetic within I64 bounds,
Strict's result, pure Free and empty Fold/Loop. Its bounded root-only evaluator
has exact finite reachability, decreasing node count and eventual root normality;
overflow remains uncontracted. These equations are not silently inserted into
`ACU.Conv`: contextual preservation/confluence of the combined theory remains
open. The three new source fixtures bring actual Core preservation regressions
to 21, including both signed bounds, overflow and unused trapping loop bodies.

`NativeEnvironmentGhostMetatheory` and `NativeEnvironmentContextConversion`
establish mode promotion, typed ghost renaming/weakening, simultaneous
substitution, dependent instantiation and context conversion for the current
unified judgment, now comprising 60 HasType constructors plus Binder formation
and five mutual judgments. The required environment premise contains
closed global types and scoped formal constructor signatures; mixed checked
history proves that premise. It is not an arbitrary well-formed-environment
assumption supplied by a certificate. Binding algebra covers captured motives,
recursive proposition cases and two-binder Load/Take removal. These are ghost
results; runtime substitution remains a separate obligation. Full contextual
ghost preservation for the current ACU relation is supplied below.

`NativeEnvironmentInversion`, `NativeEnvironmentTypeUniqueness` and
`NativeEnvironmentContextualPreservation` now establish principal inversion,
cross-mode type uniqueness and exact-original-type ghost preservation for every
current unified rule under actual full ACU conversion. The forward theorem
covers the actual `MixedRed` relation and concrete bounded normalizer, with
environment closure supplied by checked history. It handles dependent
constructor fields, captured proposition motives, Ref/Buffer shapes and the
actual leading-lambda shape of Take. No preservation under arbitrary symmetric
untyped conversion is assumed.

`NativeEnvironmentDelta` derives closed/global-free interpreted entries from
the same mixed history and proves binding-natural, idempotent global expansion.
`NativeEnvironmentDeltaConversion` combines it with actual ACU: delta and node
congruence, substitution, Pi/sort injectivity, genuine finite forward confluence
and conversion iff forward join. `NativeEnvironmentDeltaBounded` precharges
repeated bodies against a shared allowance before ACU normalization, propagates
unknown/malformed-global and budget failure, and proves exact forward results,
sound comparison and output bounds. The delta root preserves the original type
in the existing unified judgment using its actual stored body typing.
`NativeEnvironmentConversionBasis` now installs an environment-indexed
inductive delta/ACU relation into the same typing constructors and executable
checker. The executable normalizer, comparison, inferred-head exposure and
runtime domain checks use the actual environment. Acceptance soundness does
not assume admissibility: every successful bounded operation yields an actual
finite forward derivation in the inductive relation. Admissibility is used
where needed for confluence and rigid/Pi/sort injectivity, and closed stored
bodies are used for renaming and substitution. Mixed checked history derives
both invariants; callers do not supply a validity oracle.

Full contextual delta preservation now uses actual checked history to obtain
the stored body's typing. `GhostTransform` carries the actual combined
`EnvironmentDelta.Forward` path; its child theorem retains the original type
under every existing binding/resource/elimination rule. Successful concrete
normalization therefore retains an independently derived original type,
including a type which still contains global aliases. The ACU-only forward
preservation theorem continues to need only the closed/transparent world.
No preservation of arbitrary symmetric conversion representatives is asserted.

The delta source suite checks 19 actual programs and 22 exact-byte comparisons
and mutations, binding checked version-6 metadata and before/after arenas to the
same original root and unchanged prefix. Generic identity now passes the same
unified gate through authenticated context kinds and signature replay.
Parser/export/IO execution refinement, the full code closing/substitution
fundamental theorem, all native equations and universe consistency remain open.

Owned Fold/Loop, data Elim/Case/Drop and generic owned Ref/Borrow/Deref now
extend that same checker and all its ghost metatheory. The exact iteration
telescope retains the original bound; Buffer and boxed accumulators permit
memory under their three leading callback lambdas. Other function expressions
retain the native effect gate. Data branches are generated from checked
parameters, fields, recursive hypotheses and actual motive; positivity,
scoping and binding/motive naturality are proved. The five mutual judgments
have cross-mode uniqueness and original-type forward normalization preservation.
Case quantities enforce equal branch use and zero recursive outer captures;
closed admission computes metadata and normalizes binder annotations itself.

The joint tests pass 23 native data programs/22 byte checks, 28 owned iteration
programs/26 byte checks, and all prior Back/ownership/mixed-program regressions.
Thirty-five data, 24 iteration and seven expanded-metatheory Lean regressions
also pass. The installed enlarged converter now admits the ghost Drop equality
through its genuine family computation rule. Existing
proved Borrow/Deref inverse equations are retained. These results do not prove
native heap execution, active-loan semantics or machine counter fidelity.

`NativeViewSyntax` derives borrowed View branch telescopes from the same checked
constructor signatures. Its field plan is computed before parameter substitution;
recursive boxed fields receive borrowed arguments and runtime recursive results.
Dependent field reads preserve every binder and dereference earlier borrowed
fields. Scoping, arbitrary outer substitution/renaming, prefix extension and
motive conversion are proved for the concrete successful builder. Unknown field
layouts reject. Dependent code motives enforce the native fixed representation gate;
ghost motives remain closed under typed substitution.

View now shares the environment-indexed delta checker and all 60-rule ghost,
context, uniqueness and actual forward-preservation proofs. Forty typing,
resource, program and direct-global regressions and 17 telescope regressions
pass. The native suite covers 33 source programs and 28 exact-byte checks,
including typed recursive-result leaks/duplication and code dereference mutations.
The installed enlarged converter now computes View iota, including recursive
borrowed results. Neither active loans nor runtime heap preservation is assumed.

`NativeClosedTerm` now supplies generic closed-term algebra independently of
typing. Delta algebra/conversion/bounded search use only that lower layer;
`NativeEnvironmentDeltaChecked` authenticates it from mixed history afterward.
This permits installation of delta into typing without import cycles. Prefix
metadata (`NativeEnvironmentPrefix`) is also independent of typing. The code
nonfunction condition is now a positive conversion-to-head witness, so adding
a later definition preserves an earlier certificate. Its exclusion of Pi uses
the authenticated world. The raw declarative application policy permits
conversion representatives; only actual executable application checking
provides a computed normal form for runtime kind safety.

`NativeEnvironmentPlainSeparation` proves that an actually plain type cannot
convert under the installed family-iota/delta/ACU theory to Buffer, Ref, Pi, Back
or a boxed family.
The proof uses raw Boolean forward invariants and genuine Church–Rosser; it
does not assume symmetric preservation of plainness or typing. Seven regressions
include the explicit failure of reverse-beta plainness invariance. The context
interpretation below additionally handles authenticated abstract kinds and
representations with arbitrary genuinely typed U64 indices.


`NativeEnvironmentDeltaCAPIExamples` exercises the installed same-judgment
checker with global type aliases, global functions, aliases in binders,
global/beta normalization, exact-original-alias-type preservation, and
unknown/malformed-alias refusal. `NativeEnvironmentConversionBoundary`
mechanically demonstrates why closed stored bodies matter: a raw table whose
body is an open variable collapses delta/beta conversion between all terms.
Such a table cannot satisfy the world invariant derived from checked history.
The native delta adapter also checks original source bodies and observed normal
outputs with this installed typing checker, in addition to exact graph/prefix
and combined-conversion checks. Native parser/export/IO refinement remains open.


`NativeFiniteUniverses`, `NativeFinitePi`, and the contextual universe model/code
modules construct a finite Tarski hierarchy, dependent Pi closure, contextual
substitution, and concrete encode/decode equations for the native universe range
and administrative top. Three text generators reproduce the checked modules
exactly; they supply no logical axioms. This host model is not a total
interpretation of all native typing derivations.

`NativeFunctionFundamental` now reconstructs a concrete U64/nondependent-function
expression from actual unified `HasType` and syntax-only recognition. Its
contextual realization is derived for every realizing closing substitution;
source membership or normalization is not an input. Arbitrary raw result
conversions remain allowed. `NativeTypeFormationBoundary` verifies that raw
result-type regularity fails: a natural value may be assigned `UAdd U64 0`, even
though that type has no sort. `NativeQuotientTypingBoundary` separately verifies
that symmetric arithmetic quotient steps need not preserve term typing. Neither
false property is used by the semantic development.

`NativeNumeralForward` proves that conversion to a valid numeral in an
admissible world gives a genuine finite delta/ACU forward path to that numeral.
Forward descendants of literals remain numeric trees; symbolic contraction
handles arbitrary valid totals without allocating unary expansions of large
constants. `NativeFunctionNormalization` applies this to actual recognized
U64/function source typing, retaining the original independently checked type
under real checked history and proving unique numeral results. This establishes
weak normalization of that fragment, including arbitrary-depth identity chains;
it does not assert termination of commutative reduction or completeness of the
bounded executable search.

The candidate/atomic observation modules additionally derive truth for their
explicit supported proof trace. Actual checked global reflexivity is supported
after delta unfolding; opaque Load stays conservatively rejected. Full dependent
universe/family/resource/iteration fundamental lemmas, full consistency, source
execution refinement, and native loan obligations remain open.


`NativeDependentFormulaSemantics` and `NativeDependentProofFundamental` extend
actual source reconstruction to Refl, U64 lambdas and applications with
variable/literal indices and genuinely dependent proposition codomains. The
semantic families include equality, order and impredicative U64 Pi; substitution
and conversion coherence hold for every natural assignment. Actual `HasType`
and syntax-only recognition derive truth of the raw result conversion class,
including authentic global aliases and unformed raw proposition representatives.
False closed equality and order atoms are excluded throughout that grammar.
This is a dependent source fundamental theorem for the stated grammar, not a
fundamental lemma for arbitrary universe-polymorphic terms or native resources.


The default `NativeEnvironmentQuantity.check` now uses `NativeContextQuantity`
inside the existing unified program admission path. Binders are reconstructed
by the same checker from the empty context; normalized lookup types determine
first-order kinds and resource modes. Calls replay their actual dependent Pi
signatures, argument checks, erasures and result substitutions. Runtime arguments
execute once outside consumed leading-lambda scopes; computed callee syntax is
retained and accounted once. Owner-consuming partial calls require a rigid
nonfunction result or an authenticated abstract type spine such as `A` or `F n`.
An unclassified variable is never assumed to have a scalar representation.

`PlainIndices` retains exact lambda/branch contexts and arbitrary ghost-typed
U64 holes. Actual delta/ACU forward preservation, checked-world common reducts
and typed inversion separate these representations from ownership/reference/Pi
heads. There is no arbitrary quotient-step typing or valid-literal canonicity
assumption. Kind arguments passing the real closed checker/application gate
realize their kind, including neutral/computed families. Under the explicit
checked closing interpretation, unrestricted binders stay nonowning and emitted
abstract call results are Pi-separated in every later checked world.

The resource certificate retains its actual checked origin environment, finite
control/local-scope evidence, and family-table validity in the current prefix.
Prefix transport uses those facts rather than assuming that rerunning a bounded
checker is complete or monotone. These theorems concern projected Control
execution/demand. Uniformly deriving the complete closing interpretation from
all dependent runtime calls, full code/resource substitution, native heap and
loan lifetime semantics, and actual source execution refinement remain open.
The updated delta and owned-loop source suites now admit generic identity and
unknown owned-step callees through that same boundary while retaining their
source negatives and synthetic mutation checks.


`NativeUniverseContext` and `NativeUniverseFundamental` reconstruct actual
source bodies under an abstract Type0 parameter, with U64, higher-order function
values and mixed value contexts. A conversion-saturated partial source code
interpretation supplies coherent meanings for the supported type-code grammar.
The closed theorem constructs a genuine dependent Pi over the concrete finite
universe, rather than accepting realization of the original source as an input.

`NativeFiniteUniverseValues`, `NativeUniverseLevelModel`, and
`NativeUniverseLevelSource` generalize this source reconstruction to each native
universe input 0 through 31, with actual noncumulative Pi sorts and administrative
Type32. The added text generator is reproduced by the aggregate check.
`NativeUniverseLevelRealization` derives contextual simultaneous-substitution
realizations and universal parametric applications at every supported level,
using actual delta conversion and checked-history invariants. The source grammar
has no recognized inhabitant of `Pi A:Type(k), A` at any allowed input level.
These are fragment results: arbitrary type-code interpretation/coherence,
general dependent universe/value contexts, all family/resource constructs,
and full kernel consistency remain open.

`NativeLoanScope` models the native reader's saved context depth and owner
index. Active loans have scoped indices; entering and exiting readers, ordinary
binder weakening and arbitrary variable rebasing preserve the stated permissions.
The weakening theorem requires that all saved frames have already been entered:
a future-depth snapshot supplies a checked counterexample without that premise.

`NativeLendSyntax` models the exact dependent reader specialization to
`Borrow(owner)` and continuation specialization to the returned original owner.
Renaming and simultaneous substitution commute with these constructions. The
source dependent-path selector requires a named variable, so its substitution
theorem explicitly requires the substituted owner to remain a variable.
`NativeLendPolicyExamples` verifies nested loan exit and returned-owner aliasing.
Ordinary typing permits the duplicate-free example, while the actual current
`ContextQuantity.checkClosed` rejects its duplicate owner consumption and accepts
the corresponding single-use continuation. These results add no Lend typing rule,
ambient code-borrow permission, full code-substitution or heap/lifetime theorem.

`NativeLendReduction` constructs genuine finite beta paths from the native pure
Lend expansion and its dependent specialization to the same contractum.
`NativeLendGhostChecking` derives the contractum's exact original result type
from executable inference of the specialized reader and continuation, authentic
conversion and successful partial result-binder removal. It assumes neither
callback is universally typable and supplies no output typing oracle.
`NativeLendGhostExamples` checks scalar and owner-dependent refinement results
and rejects escaping result binders. This is a sound ghost-body result checker;
complete source Lend admission, active runtime loans and heap lifetimes remain open.
`NativeLendGhostRule` supplies source-facing generic and dependent ghost rule
premises, including owner typing/ownership, native result-head lifetime policy
and the dependent returned-owner annotation. Both rule shapes construct a typed
pure-model result; the generic branch uses genuinely checked callbacks and the
dependent branch uses the actually specialized bodies. The closed value-owner
example follows the generic path. This does not install Lend into the shared
HasType judgment or claim runtime loan permission/accounting.

The `NativeFamilyIota` collection defines executable family contractions and
their genuine root equations in the installed family-iota/delta/ACU converter.
Actual checked histories derive signature scope, parameter alignment and
recursive-field metadata. `case_preserves` and `contract_case_preserves` retain
the original type for generic Case with leading parameters, dependent fields,
nonparameter indices, and context/branch/result conversions. The analogous
`view_preserves_one_level` and `contract_view_one_level_preserves` cover borrowed
boxed constructors with leading parameters, dependent owned fields and dependent
motives. `NativeFamilyIotaViewRecursivePreservation` additionally proves generic
recursive View original-type preservation and executable contractor preservation
for either recursion flag. Recursive calls and their exact IH telescope come
from actual source arguments and authenticated recursive metadata. The concrete
two-self-field regression retains a converted leading parameter and dependent
original result. `NativeFamilyIotaDataElimPreservation` and
`NativeFamilyIotaPropElimPreservation` cover general indexed recursive data and
proposition elimination. `NativeFamilyIotaPreservation.Root.preserves` and
`contract_preserves` combine every selected Elim/Case/View/Drop root and its
executable contraction under actual checked history. The raw syntax layer sits
below typing, avoiding circular dependencies. Binding-aware parallel residuals
prove confluence and Church–Rosser through actual finite Forward paths for all
legacy, delta and family roots, including arbitrary family metadata. Rigid
injectivity and separation use that enlarged relation. The same relation now
underlies all 60 shared typing rules, checker soundness, checked histories,
ghost substitution, cross-mode uniqueness, original-type contextual preservation
and bounded normalization. Plain-index and kind interpretations, closing,
numeral reachability and finite universe models use it consistently. Bounded
success is not asserted to produce a normal form or imply completeness.

`NativeMultiUniverseSyntax`, `Model`, `Fundamental`, `Closure` and `Examples`
support any finite list of independent mixed-level universe parameters. Actual
source typing and syntax recognition reconstruct the intrinsic expression and
its conversion-saturated contextual interpretation; nested universe lambdas
construct concrete dependent Pi meanings. The example spanning input levels
0 and 31 checks at administrative Type32. The `CodeComputations` and `Computed`
modules additionally construct normal forms and authentic conversion/model
coherence for arbitrarily nested first-order type-level lambda applications,
including computed source binder annotations. No normal-form premise or
realization of the original source is assumed. General interleaved dependent
universe/value contexts and arbitrary native type codes are not yet covered.

`NativeNeutralSpines` derives free-head application injectivity and rigid-head
separation from genuine conversion confluence at every finite arity. The
`NativeFamilyCode` and `NativeFamilySource` collection uses these facts to
construct coherence, actual source reconstruction and a saturated fundamental
interpretation for finite blocks of type-to-type family variables
`G : Type(i) -> Type(j)` and independent mixed-level universe parameters. Codes
include arbitrary nested family applications such as `G(H(A))` and arrows.
Closed family/universe lambdas construct concrete iterated dependent Pi meanings
and formed native principal types; empty families exclude abstract inhabitants.
The source example `lambda G, lambda A, lambda x:G A, x` works at all native
input levels. Fully interleaved dependent contexts and arbitrary native
type-code computations/constructors remain open.

`NativeDependentFamilyModel`, `Contexts`, `Source`, `Closure` and `Examples`
add genuine value dependence: finite family declarations `B : A -> Type(j)`
with any monotype A over mixed universe parameters, including function carriers,
and finite observations `x : A`. Fibers `B x` occur in program domains/results,
and observations are also usable as ordinary values. Actual native typing
derives annotation validity and family/observation domain equality; source
recognition is syntax-only. Concrete dependent Pi meanings close finite
universe/family/observation blocks, with a closed dependent identity at every
native pair of input levels. Arbitrary interleaving, proposition-valued families,
erased proof binders, unrestricted closing codes and all native constructors
remain outside this pure contextual fundamental theorem.

The `NativeAuthenticKindArguments`, `NativeTraceInterpretation` and
`NativeClosing` collection constructs dependent closing interpretations from
actual checked-call argument traces. Converted inferred signatures are aligned
using typed ghost substitution and uniqueness. Erased arguments retain their
actual checked mode rather than being fabricated as runtime rechecks. The
general telescope theorem still requires explicit domain classification, while
`NativeSmallTelescopeClosure` removes that premise uniformly for every binder
genuinely formed at Prop or Type0, including neutral, computed and aliased
domains. Constructed closing interpretations establish unowned unrestricted
representations and Pi-separated owner-consuming results. General positive-kind
closing, full CODE/resource substitution and the operational fundamental theorem
remain open.

`NativeInferredKindArguments.InputTelescope.close_checkedCall` additionally
handles finite mixtures of fresh kind parameters and small ordinary binders.
It retains actual argument inference at the original replay fuel and the
inferred kind-spine observation; the closed domain's canonical kind and value
realization follow from those input checks, forward spine preservation and the
actual application gate. No canonical output/classification certificate is
supplied. All-positive-input kind-spine coverage and runtime value closing
interpretation still remain open. `NativeCodeBetaBoundary` checks that raw
syntactic code rechecking is stronger than the current validator's guarantee:
an admitted closed application can have a rejected raw beta substitution.
The actual native Core accepts both forms and retains the effectful argument
as a runtime binding, so this is not a native soundness counterexample.

`NativeKindValueEvaluation` transports authentic kind realization along actual
family-iota/delta/ACU forward paths and the separate Strict/Free/zero-iteration pure value
roots, retaining the original kind type and avoiding CODE rechecks.
`NativeInferredKindCoverageBoundary` records concrete raw-environment fuel
behavior: the enlarged search rejects the old low-fuel residual example and
returns a displayed kind at sufficient fuel. This finite regression does not
establish all-input kind-spine coverage.
`NativeExactClosing` fixes the final substitution to `pushValues` of the actual
argument list and proves the exact argument/slot correspondence. Evaluated
closing and resource-mode transport along actual Forward use typed ghost
preservation and pointwise substitution conversion, with no final interpretation
or type-coherence flag supplied. Strict/Free roots outside the installed Conv
still require heterogeneous model coherence for general dependent annotations;
heap execution and the full operational fundamental theorem remain open.

`NativeLoanTyping` is a separate loan-indexed extension of the complete shared
typing rules, with stacks as judgment indices. A dependent code reader enters
the named owner's saved-depth frame; its continuation returns to the outer stack.
Generic and dependent ghost Lend rules retain their actual body/owner/result
premises. `NativeLoanEmbedding` embeds all five existing mutual judgments at
any stack. `NativeLoanGhostPromotion` proves ghost promotion to any target stack.
`NativeLoanPermissions` derives active named-owner permission from every code
Borrow derivation, including result-type conversions, and excludes code Borrow
without a reader. `NativeLoanExamples` constructs an entire closed allocating
application, borrowed index reader and owner-returning continuation, and proves
permission revocation on reader exit. The default HasType/checker/admission
alias is unchanged. `NativeLoanPolicyNaturality`, `NativeLoanRenaming` and
`NativeLoanSubstitution` prove policy naturality, ghost renaming/weakening and
simultaneous substitution across every one of its 64 rules and five mutual
judgments. Dependent ghost Lend permits arbitrary owners, so substituting an
allocated value for a named owner retains typing without a fabricated variable
premise. The examples check that instantiation and weakening. The full
`NativeLoanPrincipalInversion` and `NativeLoanTypeUniqueness` collection proves
type uniqueness modulo its genuine raw Lend/family/delta/ACU relation across every rule,
different loan stacks and code/ghost modes. Strong source-substitution induction
handles overlapping generic/dependent Lend paths and their larger specialized
bodies; the final theorem requires only actual typing and environment well
formedness. Binder/sort uniqueness are consequences. `NativeLoanConversion`
and its algebra facade place the loan judgment, old-rule embedding, ghost
binding, inversion, uniqueness, atomic evaluation and checker soundness in that
same genuine relation. Loan-local representation policies carry raw witnesses,
with positive conversion congruence and binding transport; the original default
60-rule policies remain unchanged. The bounded raw search includes Lend,
family, delta and ACU computation with genuine finite forward soundness and
explicit depth/occurrence/duplication limits. Successful bounded output is not
assumed normal or independently typed. Default mixed-program admission and the
native heap/loan fundamental theorem remain open.

`NativeLoanCheckerPolicy`, `NativeLoanLendChecking`, `NativeLoanChecker` and
their soundness modules implement full recursive inference/binder/check/sort
checking with the actual loan stack threaded through every shared constructor.
Code Borrow requires an active named owner. Dependent readers use the entered
stack and continuations the original stack; generic callbacks are checked at
their independent signatures. Acceptance derives the full loan-indexed judgment
without typing certificates or recursive soundness supplied by callers.
`NativeLoanTypingInput` binds type formation and body typing of one closed native
declaration to canonical version-6 graph bytes. `NativeScopeCheck` also validates
all actual binder edges, independently of typing and conversion, and returns
complete type/body scope proofs. Even unbound variables hidden in beta-erased
annotation arguments reject. `CheckNativeLoanTyping.lean` bounds
the IO adapter. The native suite checks nine source fixtures and nine exact-byte
cases, including scope/erasure mutations and exhausted fuel. This entry point
does not perform whole-program quantity admission or prove heap/loan execution.

The separate `NativeLoanQuantity` collection threads the same full checker and
loan stacks through recursive resource projection. From the same successful
named-dependent check it derives actual specialized reader/body typing and
scope, zero reader demand for the owner, one restored-owner demand, and linear
use of an owned first result. Both owner names are identified before counting,
so duplicate consumption rejects. Computed and generic callback forms retain
their source contracts; their general dynamic closure/resource fundamental
theorem remains open. The exact-byte quantity adapter has twelve native source
fixtures and thirteen byte checks. It does not prove heap lifetime safety.

`NativeTermShapeCheck` validates all native payloads/arity independently of
typing. `NativeLoanGlobalChecking` expands declarations against the actual
earlier prefix, checks stored typing/scope/shape, and derives a transparent
well-formed global environment with strictly earlier references. Its examples
include a Lend function called by a later declaration and rejection of forward
references and discarded malformed annotations. This globals-only layer checks
types; mixed-family quantity admission is separate.

`NativeLoanGlobalInput` binds that sequential checker to exact canonical
version-6 bytes with an empty family table. Acceptance constructs the actual
ordered checking history, complete backward graph representation, transparent
well-formed environment, and exact declaration count. The existing aggregate
decoder bounds still apply. Kernel-checked examples include a dependent Lend
function called by a later declaration and rejection of self/forward references,
unbound variables, missing roots, malformed unused nodes, family tables,
trailing bytes and exhausted checker fuel. `CheckNativeLoanProgram.lean` is a
bounded IO adapter; `tests/core_native_loan_program_correspondence.py` compares
retained native exporter bytes with that proved function. This is global type
checking, not a runtime quantity or heap-safety theorem; native parser/exporter
refinement is not claimed.

`NativeLoanMixedProgram` and `NativeLoanMixedAdmission` now check complete
mixed declaration streams with the Loan64 checker and its actual recursive
resource projector. The same history records checked family signatures and
each global's original expansion, scope/shape checks, sort-derived body mode,
typing and runtime quantity evidence in the real earlier prefix. Exact-byte
acceptance constructs that history and a transparent well-formed environment.
Kernel examples distinguish a well-typed double consumption from resource-safe
admission and reject incorrect family placement, unscoped source annotations
and exhausted resource fuel. The new native suite checks 62 source fixtures
and 49 exact-byte cases, including families interleaved with dependent Lend
functions and an explicit code Borrow of the active named owner. This closes
the earlier separate mixed-family quantity interface.

`NativeScopedProgramHistory` extracts the closed transparent global storage
and actual checked family telescopes needed by family-iota metatheory. Both
the earlier history and the full Loan64/resource mixed history construct this
common history. Loan family metadata, Case/Elim/recursive View preservation
and contextual family evaluation now use it. `NativeLoanMixedPreservation`
derives exact-original-type ghost preservation directly from the new mixed
history, with no legacy global-typing premise. A checked example has an active
owner Borrow declaration rejected by the older program checker, yet its actual
family contraction retains its original type under the new history. General
typing-to-runtime ownership and universe consistency remain open.

`NativeCallResourceContracts` extracts exact original application typing,
actual runtime argument code typing/resource safety, and the opened source
lambda's body contract from the same successful resource check.
`NativeCodePolicyRenaming` and `NativeCodeRenaming` prove mode-preserving
renaming/weakening for all shared rules. `NativeRetainedCallBodies` derives
formation of the opened source context and code typing of its original body.
These retain source bindings; they do not assume raw code beta rechecking,
arbitrary resource renaming or dynamic closure/heap simulation.

`NativeCallBindingStores` reconstructs the source telescope from actual
opened-head typing, splits the same inferred call replay at its source prefix,
and constructs the exact argument substitution with ghost typing for every
source lookup. Original CODE body typing, body/resource contracts, actual
remaining replay and dependent result coherence are retained together.
`NativeCallStorePermissions` aligns every source erasure flag, actual slot value
and closed lookup type with the replay entry; only nonerased entries gain CODE
variable access and actual argument CODE/resource evidence. These type-only
stores cover all binder sorts without kind classification or canonicality
premises. They do not establish universal output realization or heap execution.

`NativeLendRawSyntax`, `Projection`, `Conversion`, `Binding`, `Injectivity`,
`Policies` and `API` add the genuine unconditional raw Lend macro equation to
family-iota/delta/ACU. Total capture-avoiding macro projection proves enlarged
Church–Rosser and actual finite common reducts, even when owner occurrences
duplicate. Renaming, substitution, environment extension and rigid type
injectivity are proved. `NativeLendRawTypedEndpoints` connects actual generic
or specialized ghost checks to a genuinely reached typed result. This raw
relation is separate from the installed family converter; raw macro intermediate
typing is not asserted.

`NativeLoanFunctionInversion`, `NativeLoanBetaPreservation` and
`NativeLoanLendPreservation` derive lambda/application inversion, beta
preservation and exact original-type Lend finish from the full 64-rule
loan-indexed derivation. Both generic and specialized rules participate;
the conclusion also survives result-type conversions. `NativeLoanAtomicEvaluation`
uses those results for finite pure beta/explicit-Lend atomic steps, with genuine
raw forward paths and original-type ghost preservation. This relation does not
substitute arbitrary computations into CODE derivations or model heap events.
The safe contextual evaluator additionally closes these steps beneath every
non-Lend node, handling binders and dependent annotation changes. A Lend root
contracts before descent into its source-specialized callbacks. The Loan64
family collection covers parameterized Case, recursive Prop/data elimination
and recursive borrowed View at the exact original type, using authentic checked
family history. Its family evaluation relation composes those roots with the
safe atomic/contextual evaluator, without an output-typing oracle. General raw
macro-intermediate preservation is not asserted.

Raw forward reduction also preserves explicitly supplied scope across legacy,
ACU, delta, all family roots and Lend, with closed stored globals. Actual family
and loan normalization preserve the executable scope flag. Symmetric conversion
is excluded from this claim because reverse beta can insert unbound arguments.

`NativeGhostValueErasure` defines a total raw projection dropping Strict/Free's
first operand, commuting with capture-avoiding renaming and substitution. Its
legacy theorem is explicitly pinned to the old Basis relation.
`NativeFamilyIotaValueMaps` and `NativeGhostValueIotaErasure` extend projection
coherence to every genuine family root and the full installed conversion.
This relates projected terms; it does not assert conversion of a source term to
its erasure, formation of arbitrary erased types, or runtime heap correctness.

`NativeProjectedContextCoherence` transports arbitrary raw dependent
annotations through projected closing substitutions, consuming the actual
source-slot alignment above. `NativeDependentCodeFrames` preserves genuine
universe/family/observation lookup slots beneath arbitrary raw binder prefixes.
`NativeEffectfulCodeInterpretation` recovers finite-code validity and its exact
native universe from actual typing of nested Pi/Strict/Free annotations, then
constructs the existing concrete finite universe interpretation. Checked
conversion and projected coherence preserve that meaning. The all-level
value-dependent family example has Strict in its Pi domain and Free(Alloc0)
in its codomain. General native code interpretation and heap semantics remain
open.

`NativeLoanValueProjection` and `NativeLoanCodeCoherence` compose genuine raw
Lend expansion with ghost value projection, preserving dependent closing
alignment and concrete finite-code meaning even through raw macro paths.
`NativeDependentLogicalRelation`, `NativeDependentRelationalContexts`,
`NativeDependentNumericCoherence` and `NativeDependentRelationExamples` extend
the existing concrete finite CwF with arbitrary dependent Pi fibers, semantic
context extension/interleaving, RawLend conversion saturation and genuine beta
lambda/application clauses. Concrete natural realizers use valid additive trees
for arbitrary mathematical naturals, avoiding a false result word bound.
Generic dependent identity has actual source typing and a constructed relational
meaning. Interpretation candidates remain parameters; reconstructing every
native annotation and universe candidate is still open.

`NativeBindingMachine` retains original terms/contexts, captured origin
substitutions and runtime slots in real closures. It evaluates callees and
runtime arguments once, skips erased arguments, and executes scalar values,
conditions, Strict, Alloc and Free. It now executes Lend reader/continuation
closures, named code Borrow and borrowed-buffer Index with explicit lease
identities. The owner is evaluated once; the reader receives a reference and
the continuation receives its actual result and the original owner after the
lease closes. Nested readers retain the outer reader's authority. Its heap
module connects every observed
prefix, including fault/fuel results, to the existing sized heap steps and
validity invariant without a successful-run premise. Entry typing preserves
the original CODE body and ghost origin; ready variable lookup excludes missing
and erased faults. Execution examples include exact single allocation/release,
computed closures, erased ghost-borrow arguments and an explicit double-free
fault with a valid prefix. New Loan64/resource-checked examples cover explicit
named-owner reads, two simultaneously active readers and a fresh owned reader
result whose identity is distinct from the original owner. Their actual event
streams include reads, closes and exactly the expected releases. An untyped
escaped reference faults when read after its lease closes.

`NativeBindingMachineLoans.typed_borrow_executes` derives a live lease and an
actual successful Borrow action from the full Loan64 permission derivation,
owner-slot alignment and real reader-frame/heap invariants. These invariants
do not assume Borrow guard success or output typing. Local begin/body/finish
lemmas preserve reader correspondence using fresh or distinct lease tokens;
the close guard follows from the finished reader frame. Closed leases cannot
be read, and continuation frames grant no reader authority. General runtime
value typing and preservation of slot/frame alignment across all typed
transitions remain open. So do exclusion of all invalid value/ownership/index
faults for admitted programs, general no-leak, Store and the remaining runtime
constructors, and native evaluator refinement.


`NativeBindingMachineReaderState` now proves an exact inventory of heap leases
and concrete reader frames, with distinct tokens, across every actual finite
machine prefix from the empty initial heap. The proof analyzes all evaluation,
return and heap-action cases, including fault/fuel results. Reader return derives
the close guard, closing preserves remaining readers, and an empty stack has no
outstanding leases. This discharges the global reader-frame/lease invariant;
it is not an allocated-object no-leak or whole-typing progress theorem.
Reachable code Borrow derives its actual step from Loan64 typing and `LoanSlots`
without externally supplied heap validity or `ReadersLive`.

`NativeBindingMachineLoanTyping` supplies the Loan64 counterpart of the earlier
ordinary-call source bridge using the actual resource-checked mixed history.
It retains the exact CODE body, captured origin store, dependent result origin,
and ordinary binder slot permissions, with separate erased argument handling.
Named reader entry installs the corresponding new permission. A common typed
control-stack/value invariant, specialized Lend callback entry, all source-derived
heap/Index preconditions and native implementation refinement remain open.


Reader-result provenance now records the exact body activated with the concrete
reference and captured origin store, instead of a raw callback application.
`NativeBindingMachineLendOrigins` proves that explicit-reader entry closes to
`Lending.read` and that both continuation binders close to `Lending.finish`.
The input Loan64 Lend derivation and its actual mixed history derive closed
reader typing and the final continuation's original requested ghost type,
without assuming callback typing at arbitrary arguments or output-value typing.
Reachable named-reader activation combines that source provenance, real lease
liveness and local owner-slot preservation. The erased equality example is
accepted only after Lend specialization, computes 7, and retains the proved
body origin; the native mixed checker agrees.

These entry lemmas do not interpret arbitrary returned runtime values or prove
source/slot preservation across all computation, capture and continuation
steps. In particular `LoanSlots` is still an input at the pending source-frame
boundary, reference lengths/evidence need an interpretation, and source-derived
Index/no-fault and general ownership accounting remain open.


`NativeBindingMachineIndexBounds` inverts both Index source rules in the full
Loan64 judgment and derives Decide's numeral conversions, widths and strict
order from its actual typing constructors. Literal Decide thus supplies the
read bound without a caller truth certificate. Exact lengths from a concrete
allocation state survive every machine prefix. The named-Borrow Index theorem
uses those facts, source slot permissions and the reader inventory to construct
all five actual transitions and the exact read event, including erasure of the
proof field. It assumes the entry heap's concrete allocation shape, its owner
slot identity and source/control alignment. Their general typing-derived
preservation, dynamic indices and arbitrary proof forms remain open; this is
not the full Index progress or no-leak theorem.


`NativeBindingMachineAlignment` defines recursive runtime value/capture alignment,
original-context erasure-slot alignment and concrete control/frame alignment.
Every evaluation, return and heap action preserves them, so they hold at every
prefix from any source term in the empty initial context, even at faults or fuel
exhaustion. This includes computed closures, skipped erased arguments, branch
proof slots and nested Lend reader/continuation frames. Reachable Loan64 variable
input typing then constructs its next actual returned value without a supplied
`Ready` premise. This discharges structural slot/erasure preservation. It does
not yet establish that runtime values inhabit source types, source typing is
preserved at every control point, or ownership/loan/length interpretations are
preserved through arbitrary closures and effects.


`NativeBindingMachineDynamicIndex` extends the literal bridge to dynamic scalar
slots and the actual IfLt hypothesis binder. Full source typing supplies the
named Borrow permission; actual comparison selects ten read transitions or
five transitions into the else body. No caller-provided index bound or
successful-run predicate is used. The general local theorem still assumes the
entry allocation/slot association and source/control alignment.

`NativeBindingMachineDynamicIndexExamples` connects a whole checked function
with dynamic Buffer allocation and a Lend reader to the existing machine from
its empty initial state, quantified over all bounded U64 count/index values
whose allocation size fits the machine guard. It derives source typing,
actual in-bounds result 7/out-of-bounds result 0, the exact single allocation,
lease, optional read, close and Free trace, and final empty live-object/lease
inventories. The source/resource checker is Loan64; the native mixed checker
agrees on the source function. This function theorem eliminates local heap/slot
premises for that composition, not arbitrary source functions or the full
language. General runtime value/heap/source-stack interpretation, computed
sizes and arbitrary proof terms, ownership and native refinement remain open.


`NativeBindingMachineNumeric` supplies a numeric runtime-value/capture/control-
stack and heap interpretation, preserved by every actual transition and prefix
from the empty initial heap. U64/I64 values and saved arithmetic/count operands
stay in range; uniform heap payloads and allocation byte lengths remain bounded,
including released identities. I64 typing of actual decoded heap contents is
constructed from that invariant, not an output-typing or realization premise.

`NativeBindingMachineIndexValues` uses the full Loan64 input derivation and
actual mixed history to place these integers at the exact original closed
Index result type, including arbitrary result conversion and IfLt Index arms.
Actual pending-reader authority follows from the all-prefix reader inventory;
the read step either returns a constructed original-type integer or explicitly
faults on bounds. General source/control association, heap layout/slot semantics
and proof interpretation must still exclude that alternative for arbitrary
admitted programs. Numeric preservation alone is not type preservation for
arbitrary runtime values, ownership soundness or native refinement.


`NativeBindingMachineLendValues` reconstructs explicit Index-reader result
formation/type from the full source Lend rule and its mixed history. Reachable
heap integers inhabit that checked reader type without assuming generic callback
typing or returned-value realization. The actual scalar can close the original
continuation body at the original Lend result type, and concrete binding
equations retain the actual CODE body and owner/result value slots. This is a
ghost scalar closing derived from actual data, not a claim that the machine
performs CODE beta substitution or that all captured runtime values satisfy
their source-dependent heap types. The general source/control/slot/resource
fundamental theorem, bounds-fault exclusion and native refinement remain open.


`NativeBindingMachineIndexExecution` combines the existing constructed literal
and comparison-guarded Index paths with actual prefix numeric interpretation
and full Loan64 original-type conversion. Its caller supplies no heap-validity,
reader-inventory, numeric-realization or post-result typing certificate: these
are derived from the actual initial execution. Returned integers have the exact
input closed type, and false comparison enters an else body with the same
original source type. Earlier entry points remain compatibility wrappers.
The source/control judgment and allocation/owner-slot/loan association are still
local inputs. The full fundamental theorem must construct them from admitted
mixed-program typing/resources, including all captures/effects and arbitrary
bound proofs. This increment does not close general ownership, consistency,
full source computation preservation or native implementation refinement.

`NativeBindingMachineLendResources` connects the same dependent Lend resource
projection to actual close and two retained continuation bindings. Its slot map
identifies the restored-owner alias with the captured original owner, while
preserving all outer named-loan slots. For Free at either alias, it constructs
the eight actual transitions and derives the guard from the remaining concrete
reader inventory. A still-active outer reader of that object gives a specified
borrowed-owner fault; absence gives release, without caller-provided liveness
or guard evidence. The remaining code retains the original ghost result type,
and the recursive source projection has zero residual owner demand.

This does not prove absence of that conflict from arbitrary admitted programs.
The local input code typing/resource projection, original owner slot and actual
reader-frame/control association still need the common fundamental theorem.
Abstract zero-demand tail prefixes are not yet associated with all concrete tail
executions. The theorem executes retained source code, not a substituted CODE
macro, and neither claims general value realization nor native refinement.

`NativeBindingMachineReaderResume` derives an outer Borrow's source permission
from the actual specialized checked continuation. Pre-existing captured loan
slots identify its owner; reachability derives a distinct outer lease that
survives closing the inner reader. It constructs all eight real transitions
through both continuation bindings, the authorized Borrow and Strict tail
entry, preserving outer slots and the original ghost result type. Both owner
aliases are rejected for reborrow when no outer source permission remains.
No caller supplies post-close heap/slot safety or execution success. Current
input source/control/resource and captured-slot association are still local
premises, not yet a closed-admission fundamental theorem or native refinement.

`NativeBindingMachineOwnedReader` reconstructs Buffer first-result linear mode
from successful actual normalization and derives its separate exact-once source
contract. The same checked reader supplies literal widths and its declared
first-result conversion. A live concrete owner and its actual heap length give
the limited `BufferValue` interpretation; exclusivity is a separate obligation.
Reachable reader allocation constructs that interpretation, a fresh identity
distinct from the leased original owner, absence of old leases to the new
object, its Free guard, and the actual five steps. Byte-size overflow is an
explicit outcome, not an assumed allocation success. Source/control/reader
association, general resource authority and the full fundamental theorem still
remain open. This source-machine result does not refine native allocation.

`NativeBindingMachineOwnedReaderExecution` constructs the allocating reader
and two-owner continuation together: sixteen actual transitions and exact
allocation/close/activation/two-Free events, with original ghost tail typing
and zero residual demand for both source resources. The fresh first result is
interpreted at its declared closed Buffer type. Fresh identity/guard evidence
is derived, not an input. Byte overflow and a still-active outer reader of the
old owner remain explicit outcomes; general admitted-program exclusion of the
latter and arbitrary tail resource simulation are still unproved.

`NativeBindingMachineOwnerProvenance` gives an unconditional all-prefix
runtime owner-identity interpretation. Current values, every saved frame and
all nested closure captures have owner IDs below the actual allocation counter.
The next allocation cannot alias any of those old captures, even dead owners.
Each captured/returned owner has an earlier actual allocation event, and its
current length/payload equal that event's count/payload in this read-only
uniform-fill heap. No allocation snapshot or provenance oracle is an input.

This is provenance, not live/exclusive ownership: retained dead aliases remain
possible, and source resource authority must determine which slots may be used.
The actual allocation length still needs interpretation at arbitrary dependent
source types, through all calls and continuation control. Unsupported syntax
continues to fault in this source machine; no native allocator, Store/write,
general progress or full-kernel correctness claim follows from the invariant.

`NativeBindingMachineReturnedBufferRead` composes an allocating reader with
its retained continuation, a second Lend and named Borrow/Index on the fresh
returned owner. Twenty real transitions and exact events are constructed from
the source Loan64 judgment/resource check and the actual reader entry. Literal
widths/bounds, fresh owner slot, allocation length, lease guards and the actual
integer at the reconstructed reader's exact ghost type are derived. The first
lease is closed before the distinct new lease is opened. Byte overflow remains
an explicit outcome; ghost allocation origins are not re-executed as CODE.
Current input source/control/frame association is still local, and the read
endpoint retains its inner reader frame. General completion, arbitrary bound
interpretation/resource simulation and native implementation refinement remain
open.

`NativeBindingMachineReturnedBufferCompletion` closes the fresh-result reader
and executes both owner releases and scalar return in thirty-two real steps.
The actual scalar has the original outer source result type; its proof uses
input typing and actual fill bounds rather than an output certificate. The
fresh Free guard follows from all-prefix owner provenance plus the concrete
reader inventory. A still-active outer reader of the old owner gives a specified
thirty-one-step fault; byte overflow stops after five. General admission/control
association and old-owner conflict exclusion remain open, as do arbitrary source
computations/resource simulation and native implementation refinement.

`NativeBindingMachineReturnedBufferCompletionExamples` checks one actual
closed Loan64/resource admission and contextual reader entry, then applies the
general thirty-two-step proof after the fourteen-step caller prefix. The
forty-six-step scalar result is derived through that theorem, not assumed as an
output certificate. This concrete instantiation does not establish the general
admission/control fundamental theorem or native checker/evaluator refinement.

`NativeBindingMachineScalarClosing` retains the complete Loan64 body typing
with a value closing independent of the machine's source-origin map. Actual
natural closure entry instantiates dependent result types at the observed
numeral, preserving source code/captures/provenance, direct numeric-slot
agreement and earlier named loans. Mixed declaration checking reconstructs the
initial empty closing and resource evidence. Runtime bounds are derived, not
an argument/output typing input; effectful origin-to-numeral conversion is never
assumed. Input closure/capture invariants still need the common all-control
fundamental theorem, including general value kinds and heap/resource authority.

`NativeBindingMachineComputedAllocation` derives the value-closed dependent
body type and fill width, then constructs six actual transitions from a
computed-natural call boundary through retained-variable allocation. The
resulting live Buffer has the heap length of the source signature instantiated
at the actual argument. No source numeral, returned slot lookup, guard or output
typing certificate is an input. Byte overflow remains an explicit fault, and
the fresh object is absent from every earlier recursive capture. This is a
semantic signature instance, not an assertion that an arbitrary effectful
origin converts to a numeral. General function/control/context association and
the full source-result/resource fundamental theorem remain open.

Integer closing and captured second-call typing also reconstruct actual I64
fill binding while preserving the earlier U64 size. Both argument source
origins remain in the real closure environments. The generic six-step
two-scalar allocation theorem is instantiated by a closed curried program:
size and fill are computed separately with Free/arithmetic effects, and the
typed Buffer interpretation/result payload follow after thirty-seven steps.
The single-count closed instance takes twenty-one steps. These examples have
actual Loan64/resource admission, but neither equate the effectful source
result annotation with a numeral by raw conversion nor prove arbitrary
admission/control/context preservation or native implementation correctness.


`NativeBindingMachineValueKinds` now constructs numeric representation-head
agreement at typed captured lookups, using actual-prefix slot readiness and
source variable inversion. Mixed entry and actual U64/I64 entry construct and
preserve this stronger context. `NativeBindingMachineCapturedAllocation`
then reads arbitrary captured size/fill indices and constructs five actual
allocation steps at the SAME value-closed source result type, or explicit
byte overflow. No stored-number, successful-run or output-typing certificate
is supplied. Representation heads alone do not establish closure bodies,
heap liveness, exclusive authority or reference leases; general control-stack
context construction and original effectful annotation semantics remain open.


`NativeBindingMachineCapturedBranch` constructs canonical erased evidence from
actual captured-number comparisons, preserves arbitrary original branch-body
types and value contexts, and retains named-reader loan slots. A true branch
can execute source-authorized Borrow in six steps using a live lease derived
from the actual nested reader inventory. Original provenance evidence is not
used as a canonical proof. The input source/control/value/loan association and
general Index heap-size/resource interpretation remain unfinished.


`NativeBindingMachineAllocatedArgument` now constructs a retained owner value
context and dependent body typing from the original source allocation and
pending function judgments, with six actual allocation/call transitions.
Canonical ghost allocation and original runtime provenance remain distinct.
A named Lend of that fresh argument then has nine constructed transitions,
a live correctly sized Buffer, its new concrete lease and the exact complete
reader inventory including outer readers. Byte overflow is explicit. No
runtime argument/output typing, allocation snapshot, stored owner, live-owner
or successful-execution certificate is supplied. Source/control/value contexts
are still local preconditions, and representation-head interpretation alone
is not heap/resource authority. Specialized dependent reader activation must
retain its actual checked read, not assume arbitrary callback typing. General
reference/Index interpretation, all-control fundamental soundness and native
implementation refinement remain unfinished.


`NativeBindingMachineReaderClosing` reconstructs the reference binder and
canonical closed reader-body typing from the authentic full Lend input. It
covers generic and specialized checked reads without assuming an arbitrary-
argument callback derivation, and connects actual activation to source loan
slots and the reachable nested reader inventory. Canonical value meanings and
runtime provenance remain distinct. General control/source association, heap
size interpretation and exclusive resource authority remain open.


`NativeBindingMachineOwnerSizes` now constructs captured source/heap length
agreement at allocation argument entry and preserves old captured identities'
lengths through arbitrary actual heap-event suffixes, including released aliases.
It gives size/provenance information without assigning live/exclusive authority
to every capture. `NativeBindingMachineSizedIndex` combines this with full bound
evidence, source named-Borrow permission and the actual reader inventory to
construct dynamic ten-step reads at the same closed input type. Allocation
snapshots, selected numeric/owner slots, strict-bound and read-success premises
are removed from this local theorem. A false comparison has original-type
five-step else entry. `NativeBindingMachineSizedBorrow` similarly constructs a
live reference with the actual dependent Buffer length at its exact source
type. The common admission/control/value/size/loan/resource invariant, arbitrary
evidence and source-result semantics, complete ownership safety and native
implementation refinement remain unfinished.


`NativeBindingMachineReferenceIndex` constructs six actual activation/read
transitions through a reader's retained reference argument. The authentic full
Lend read, bound evidence and captured owner sizes determine the actual physical
length and strict bound; the input annotation describes the actual live sized
reference. Reader inventory, canonical value contexts and old owner sizes are
retained. No allocation snapshot, arbitrary callback or success/output-typing
certificate is supplied. Source/control/frame and owner-slot association remain
local preconditions; arbitrary evidence and the whole fundamental theorem are
still open.


`NativeBindingMachineValueHandoff` now constructs the canonical scalar/owner
continuation bindings, value/size contexts and exact closed original result
type from the authentic full Lend input. Five actual transitions close before
binding, retain outer reader inventory and source loans, and connect both
physical owner aliases to the same zero/one resource projection. No callback/
output typing is assumed. `NativeBindingMachineReferenceReaderCompletion`
constructs the entire eleven-step actual reference-read/close/handoff path and
its intermediate prefix from those proofs. Arbitrary continuation bodies are
retained, but their later execution, the all-control mixed-admission invariant,
enclosing-reader consumption exclusion and native refinement remain open.


`NativeBindingMachineCheckedDynamicReader` reconstructs the original Loan64
source judgment and specialized CODE read directly from the actual resource
projection. Its zero/one owner contract accompanies actual captured numeric
lookup and physical-size interpretation. The reference argument executes an
eleven-step guarded read or six-step original-type else entry, preserving
nested reader inventory and canonical value/size contexts. No original generic
callback, selected numeric operands, bound/allocation snapshot or output/success
certificate is assumed. Source/control/frame and owner-slot association and
all-control resource authority remain open.


Guarded reference readers now have a sixteen-step authentic-checker composition
through read, close and canonical continuation bindings, with original closed
inferred result typing, owner-alias/resource agreement and outer reader
inventory. False comparisons keep original-type six-step else entry. The
scalar-shape helper only classifies local proof cases and leaves the full
source grammar/Loan64 judgment unchanged. The old direct-Index API remains.
No callback/output or intermediate-execution certificate is assumed. All-
control mixed-admission/resource authority and general Free conflict exclusion
remain unfinished.


`NativeBindingMachineFreshDynamicRelease` derives absence of remaining owner
readers from all-prefix frame provenance at an earlier actual call/birth prefix,
then derives Free's guard from the constructed close inventory. Twenty actual
transitions read, close, bind, release through either physical owner alias and
return the observed I64 at the original inferred source type. The owner is dead,
the heap/outer reader inventory remain valid and source residual owner demand
is zero. No no-reader/Unborrowed/Free-success oracle is an input. The local
birth/current-frame and source/context associations remain explicit; arbitrary
old-owner conflicts and the all-control mixed-admission authority theorem are
still unfinished.


Original full lambda resource projection now yields its exact internal body
receipt. Internal Lend source judgments, read/restore scopes and zero/one owner
contracts feed the actual reader/handoff/release proofs; previous full-query
APIs remain specializations. These internal-query lemmas do not replace mixed
admission, source/context guards or the full grammar. Allocation-to-reader
association and the all-control authority theorem are still to be constructed.


`NativeBindingMachineAllocatedDynamicRelease` now constructs actual allocation,
owner binding, named Lend and original reader-closure entry from the pending
call's source judgments and original function resource receipt. The body query,
birth/current-frame and owner-slot associations are derived. Thirty transitions
read the captured index, close, bind, release and return the actual signed fill
at the source signature's canonical argument instance. Original provenance is
retained without a raw-conversion premise. False comparisons have typed else
entry at sixteen steps; byte overflow faults at five. A closed full-checker/
resource admission instantiates the theorem to an actual forty-eight-step
release/return. Pending-call value/size/loan/source contexts and general
admission/control authority remain open, as do arbitrary else/tail execution,
old-owner conflict exclusion and native implementation refinement.


`NativeBindingMachineCallDynamicRelease` starts at the original full call,
recovering its lambda/argument typing and exact internal body resource receipt.
The actual three-transition call prefix constructs the pending frame; composing
allocation, reader activation, guarded read, close and alias Free gives a
thirty-three-step return at the EXACT original closed call type. The heap trace
and enclosing reader inventory are retained. False comparisons give typed
nineteen-step else entry; allocation-size overflow faults after eight steps.
The closed dependent example now uses this theorem after scalar entry, without
separate function/argument checks or a supplied pending frame. Value/size/loan
contexts at the original call, global mixed-admission authority, arbitrary
else/tail execution and old-owner conflict exclusion remain open. This does not
establish general progress, universe consistency or native implementation
refinement.
