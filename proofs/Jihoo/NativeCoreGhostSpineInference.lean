import Jihoo.NativeCoreTypedEqual
import Jihoo.NativeCoreGhostSort
import Jihoo.NativeLoanTypeUniqueness

/-! Ghost Core.infer on local and global heads, dependent application spines,
and primitive forms with fixed operand types. A successful checker records
which pairs of normalized type roots identity accepted. The trace has no
effect on graph allocation or work. -/
namespace Jihoo.NativeKernel.NativeCoreGhostSpineInference

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreCaseStrict (append append_progress append_refines)
open NativeCoreCompare (FullyRetained)
open NativeCoreBinderTraversal (VisitsFrom)
open EnvironmentDelta (expand expandArgs)
open NativeCoreGhostSort (DataFamilies)

structure GraphBinding where
  typeRoot : Nat
  erased : Bool
  deriving Repr

structure Inferred where
  typeRoot : Nat
  compared : List (Nat × Nat)
  deriving Repr

abbrev Visit := State → Nat → Outcome Nat
abbrev Infer := State → Nat → Outcome Inferred
abbrev NormalAt := Nat → Visit

private structure InferredBinder where
  sort : SortTag
  compared : List (Nat × Nat)

private def inferBinder (infer : Infer) (normal : Visit) (isData : Nat → Bool)
    (state : State) (domain : Nat) (erased : Bool) : Outcome InferredBinder :=
  (infer state domain).next fun afterDomain domainType =>
    (NativeCoreGhostSort.sort normal afterDomain domainType.typeRoot).next fun afterSort selected =>
      (NativeCoreGhostSort.policy normal isData afterSort domain erased selected).next fun after _ =>
        ⟨after, .ok ⟨selected, domainType.compared⟩⟩

private def sortOp : SortTag → Op
  | .prop => .prop
  | .type level => .universe level

private theorem sortOp_arity (sort : SortTag) : (sortOp sort).arity = 0 := by cases sort <;> rfl

private theorem sortOp_expanded (sort : SortTag) : expand env (.node (sortOp sort) []) = sort.term := by
  cases sort <;> simp [sortOp, SortTag.term, Term.prop, Term.univ, expand, expandArgs]

private def finishBinding (normal : Visit) (state : State) (product erased : Bool)
    (domain rangeRoot : Nat) (domainSort : SortTag) : Outcome Nat :=
  if product then
    (NativeCoreGhostSort.sort normal state rangeRoot).next fun after rangeSort =>
      append after (sortOp (domainSort.pi rangeSort)) []
  else append state (.pi erased) [domain, rangeRoot]

private def inferBinding (inferDomain inferBody : Infer) (normal : Visit) (isData : Nat → Bool)
    (state : State) (product erased : Bool) (domain body : Nat) : Outcome Inferred :=
  (inferBinder inferDomain normal isData state domain erased).next fun afterDomain checked =>
    (inferBody afterDomain body).next fun afterBody inferred =>
      (finishBinding normal afterBody product erased domain inferred.typeRoot checked.sort).next fun after root =>
        ⟨after, .ok ⟨root, checked.compared ++ inferred.compared⟩⟩

private def liftTransform (result : NativeCoreTransformExact.Outcome Nat) : Outcome Nat :=
  ⟨result.state, result.result.mapError .substitution⟩

private theorem liftTransform_success (success : (liftTransform result).result = .ok selected) :
    result.result = .ok selected := by
  cases found : result.result <;> simp [liftTransform, found, Except.mapError] at success ⊢
  exact success

private theorem liftTransform_progress (progress : NativeCoreTransformExact.Progress limit state result) :
    Progress limit state (liftTransform result) :=
  ⟨progress.kept, progress.monotone, progress.bounded, fun room selected found =>
    progress.accepted room selected (liftTransform_success found)⟩

private def shiftType (limit depth : Nat) (state : State) (root amount : Nat) : Outcome Nat :=
  liftTransform (NativeCoreTransformExact.run limit depth state root (.shift amount) 0)

private def lowerType (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  liftTransform (NativeCoreTransformExact.run limit depth state root (.shift (-1)) 0)

private def instantiate (limit depth : Nat) (state : State) (result argument : Nat) : Outcome Nat :=
  liftTransform (NativeCoreTransformExact.substitute limit depth state result argument)

private theorem shiftType_progress (limit depth : Nat) (state : State) (root amount : Nat) :
    Progress limit state (shiftType limit depth state root amount) :=
  liftTransform_progress (NativeCoreTransformExact.run_progress limit depth state root (.shift amount) 0)

private theorem lowerType_progress (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (lowerType limit depth state root) :=
  liftTransform_progress (NativeCoreTransformExact.run_progress limit depth state root (.shift (-1)) 0)

private theorem instantiate_progress (limit depth : Nat) (state : State) (result argument : Nat) :
    Progress limit state (instantiate limit depth state result argument) :=
  liftTransform_progress (NativeCoreTransformExact.substitute_progress limit depth state result argument)

private def plain (root : Nat) : Inferred := ⟨root, []⟩

private def discard (state : State) (root : Nat) : Outcome α :=
  ⟨state, .error (.outsideFragment root)⟩

private def emit (state : State) (op : Op) : Outcome Inferred :=
  let result := append state op []
  ⟨result.state, result.result.map plain⟩

private def shiftInferred (limit depth : Nat) (state : State) (root amount : Nat) : Outcome Inferred :=
  let shifted := shiftType limit depth state root amount
  ⟨shifted.state, shifted.result.map plain⟩

private def tick (limit depth : Nat) (state : State) (root : Nat)
    (entered : State → Outcome Inferred) : Outcome Inferred :=
  let (paid, steps) := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let state := {state with steps}
  match paid with
  | .error reason => ⟨state, .error (.tick reason)⟩
  | .ok () => entered state

/-- Core.require normalizes the inferred argument type, then the expected
domain, and uses identity on their live roots. The original argument
reference, not either type root, is later substituted into the codomain. -/
def requireTypes (normal : Visit) (limit depth : Nat) (state : State)
    (actual expected argument : Nat) : Outcome (Nat × Nat) :=
  (normal state actual).next fun afterLeft left =>
    (normal afterLeft expected).next fun afterRight right =>
      (NativeCoreTypedEqual.identify limit depth afterRight left right).next fun afterIdentity same =>
        if same then ⟨afterIdentity, .ok (left, right)⟩ else discard afterIdentity argument

/-- Check each operand before visiting the next one. All operands share the
single expected type node just emitted by the native inference branch. -/
private def requireOperands (infer : Infer) (normal : Visit) (limit depth expected : Nat) :
    State → List Nat → Outcome (List (Nat × Nat))
  | state, [] => ⟨state, .ok []⟩
  | state, root :: rest =>
      (infer state root).next fun inferred type =>
        (requireTypes normal limit depth inferred type.typeRoot expected root).next fun checked pair =>
          (requireOperands infer normal limit depth expected checked rest).next fun after comparisons =>
            ⟨after, .ok (type.compared ++ pair :: comparisons)⟩

/-- Native primitive branches synthesize the expected type and check each
operand at child depth. -/
private def checkFixed (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (operand : Op) (args : List Nat) : Outcome (List (Nat × Nat)) :=
  (append state operand []).next fun emitted expected =>
    requireOperands infer normal limit depth expected emitted args

private def inferFixed (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (operand : Op) (args : List Nat) (output : Op) (refs : List Nat) : Outcome Inferred :=
  (checkFixed infer normal limit depth state operand args).next fun checked comparisons =>
    (append checked output refs).next fun after root => ⟨after, .ok ⟨root, comparisons⟩⟩

private def finishDecide (normal : Visit) (state : State) (root first second : Nat) : Outcome Nat :=
  (normal state first).next fun afterFirst left =>
    (normal afterFirst second).next fun afterSecond right =>
      match afterSecond.arena[left]?, afterSecond.arena[right]? with
      | some (.node (.natural a) []), some (.node (.natural b) []) =>
          if a < 2^64 ∧ b < 2^64 ∧ a < b then append afterSecond .lt [first, second]
          else discard afterSecond root
      | _, _ => discard afterSecond root

private def inferDecide (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (root first second : Nat) : Outcome Inferred :=
  (checkFixed infer normal limit depth state .u64 [first, second]).next fun checked comparisons =>
    (finishDecide normal checked root first second).next fun after result =>
      ⟨after, .ok ⟨result, comparisons⟩⟩

private def inferStrict (infer : Infer) (state : State) (effect result : Nat) : Outcome Inferred :=
  (infer state effect).next fun afterEffect first =>
    (infer afterEffect result).next fun afterResult second =>
      ⟨afterResult, .ok ⟨second.typeRoot, first.compared ++ second.compared⟩⟩

private def addOne (state : State) (word : Nat) : Outcome Nat :=
  (append state (.natural 1) []).next fun after one => append after .uadd [word, one]

private def subtractBound (state : State) (numerator denominator : Nat) : Outcome Nat :=
  (addOne state numerator).next fun after successor => append after .lt [denominator, successor]

private def zeroBound (state : State) (word : Nat) : Outcome Nat :=
  (append state (.natural 0) []).next fun afterZero zeroRef => subtractBound afterZero word zeroRef

private def inferZeroLe (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (word : Nat) : Outcome Inferred :=
  (checkFixed infer normal limit depth state .u64 [word]).next fun checked comparisons =>
    (zeroBound checked word).next fun after result => ⟨after, .ok ⟨result, comparisons⟩⟩

private def checkSubtract (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (numerator denominator proof : Nat) : Outcome (List (Nat × Nat)) :=
  (subtractBound state numerator denominator).next fun assembled expected =>
    requireOperands infer normal limit depth expected assembled [proof]

private def inferSubtract (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (numerator denominator proof : Nat) : Outcome Inferred :=
  (checkFixed infer normal limit depth state .u64 [numerator, denominator]).next fun checked comparisons =>
    (checkSubtract infer normal limit depth checked numerator denominator proof).next fun afterProof proofComparisons =>
      (append afterProof .u64 []).next fun after result =>
        ⟨after, .ok ⟨result, comparisons ++ proofComparisons⟩⟩

private def offsetBounds (state : State) (left right delta : Nat) : Outcome (Nat × Nat) :=
  (append state .uadd [left, delta]).next fun afterLeft shiftedLeft =>
    (append afterLeft .uadd [right, delta]).next fun afterRight shiftedRight =>
      (append afterRight .lt [left, right]).next fun afterPlain plain =>
        (append afterPlain .lt [shiftedLeft, shiftedRight]).next fun afterShift shifted =>
          ⟨afterShift, .ok (plain, shifted)⟩

private def inferOffsetProof (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (forward : Bool) (left right delta proof : Nat) : Outcome Inferred :=
  (checkFixed infer normal limit depth state .u64 [left, right, delta]).next fun checked operands =>
    (offsetBounds checked left right delta).next fun assembled bounds =>
      (requireOperands infer normal limit depth (if forward then bounds.1 else bounds.2) assembled [proof]).next
        fun after compared =>
          ⟨after, .ok ⟨if forward then bounds.2 else bounds.1, operands ++ compared⟩⟩


private def transitiveBounds (state : State) (left middle right : Nat) : Outcome (Nat × Nat) :=
  (addOne state right).next fun afterSuccessor successor =>
    (append afterSuccessor .lt [left, middle]).next fun afterLower lower =>
      (append afterLower .lt [middle, successor]).next fun afterUpper upper =>
        ⟨afterUpper, .ok (lower, upper)⟩

private def inferTransitiveProof (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (left middle right lower upper : Nat) : Outcome Inferred :=
  (checkFixed infer normal limit depth state .u64 [left, middle, right]).next fun checked operands =>
    (transitiveBounds checked left middle right).next fun assembled bounds =>
      (requireOperands infer normal limit depth bounds.1 assembled [lower]).next fun checkedLower lowerPairs =>
        (requireOperands infer normal limit depth bounds.2 checkedLower [upper]).next fun checkedUpper upperPairs =>
          (append checkedUpper .lt [left, right]).next fun after result =>
            ⟨after, .ok ⟨result, operands ++ (lowerPairs ++ upperPairs)⟩⟩

private def conditionOp (equality : Bool) : Op := if equality then .eq else .lt

private def conditionalOp (equality : Bool) : Op := if equality then .ifEq else .ifLt

private def finishConditional (inferAlternative : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (thenType alternative : Nat) : Outcome Inferred :=
  (normal state thenType).next fun afterNormal normalized =>
    (lowerType limit depth afterNormal normalized).next fun afterLowering result =>
      (requireOperands inferAlternative normal limit depth result afterLowering [alternative]).next fun after compared =>
        ⟨after, .ok ⟨result, compared⟩⟩

private def inferConditional (infer : Infer) (inferThen : Nat → Infer) (normal : Visit)
    (limit depth : Nat) (state : State) (equality : Bool) (left right yes no : Nat) : Outcome Inferred :=
  (checkFixed infer normal limit depth state .u64 [left, right]).next fun checked compared =>
    (append checked (conditionOp equality) [left, right]).next fun entered assumption =>
      (inferThen assumption entered yes).next fun afterThen inferred =>
        (finishConditional infer normal limit depth afterThen inferred.typeRoot no).next fun after finished =>
          ⟨after, .ok ⟨finished.typeRoot, compared ++ inferred.compared ++ finished.compared⟩⟩

private def predicateType (state : State) : Outcome Nat :=
  (append state .u64 []).next fun afterWord word =>
    (append afterWord .prop []).next fun afterProp prop => append afterProp (.pi false) [word, prop]

private def checkPredicate (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (predicate : Nat) : Outcome (List (Nat × Nat)) :=
  (predicateType state).next fun after expected => requireOperands infer normal limit depth expected after [predicate]

private def inferRefine (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (predicate : Nat) : Outcome Inferred :=
  (checkPredicate infer normal limit depth state predicate).next fun checked comparisons =>
    (append checked (.universe 0) []).next fun after result => ⟨after, .ok ⟨result, comparisons⟩⟩

private def checkPredicateEvidence (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (predicate word evidence : Nat) : Outcome (List (Nat × Nat)) :=
  (append state .app [predicate, word]).next fun applied expected =>
    requireOperands infer normal limit depth expected applied [evidence]

private def inferPack (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (predicate word evidence : Nat) : Outcome Inferred :=
  (checkPredicate infer normal limit depth state predicate).next fun predicateState predicatePairs =>
    (checkFixed infer normal limit depth predicateState .u64 [word]).next fun wordState wordPairs =>
      (checkPredicateEvidence infer normal limit depth wordState predicate word evidence).next fun proofState proofPairs =>
        (append proofState .refine [predicate]).next fun after root =>
          ⟨after, .ok ⟨root, predicatePairs ++ wordPairs ++ proofPairs⟩⟩

private def refinementProjectionType (state : State) (evidence : Bool) (predicate subject : Nat) : Outcome Nat :=
  if evidence then
    (append state .witness [subject]).next fun after witness => append after .app [predicate, witness]
  else append state .u64 []

private def inferRefinementProjection (infer : Infer) (normal : Visit) (state : State)
    (evidence : Bool) (subject : Nat) : Outcome Inferred :=
  (infer state subject).next fun inferred sourceType =>
    (normal inferred sourceType.typeRoot).next fun exposed typeRoot =>
      match exposed.arena[typeRoot]? with
      | some (.node .refine [predicate]) =>
          (refinementProjectionType exposed evidence predicate subject).next fun after root =>
            ⟨after, .ok ⟨root, sourceType.compared⟩⟩
      | _ => discard exposed subject

private def inferTransport (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (predicate equality payload : Nat) : Outcome Inferred :=
  (checkPredicate infer normal limit depth state predicate).next fun afterPredicate predicatePairs =>
    (infer afterPredicate equality).next fun afterEquality inferred =>
      (normal afterEquality inferred.typeRoot).next fun exposed typeRoot =>
        match exposed.arena[typeRoot]? with
        | some (.node .eq [left, right]) =>
            (checkPredicateEvidence infer normal limit depth exposed predicate left payload).next fun checked proofPairs =>
              (append checked .app [predicate, right]).next fun after root =>
                ⟨after, .ok ⟨root, predicatePairs ++ inferred.compared ++ proofPairs⟩⟩
        | _ => discard exposed equality

/-- Post-tick App inference in ghost mode. Every recursive call here uses
the same child depth. The inferred codomain is returned immediately. -/
def inferApp (infer : Infer) (normal : Visit) (limit childDepth : Nat) (state : State)
    (function argument : Nat) : Outcome Inferred :=
  (infer state function).next fun afterFunction functionType =>
    (normal afterFunction functionType.typeRoot).next fun afterExpose functionRoot =>
      match afterExpose.arena[functionRoot]? with
      | some (.node (.pi _) [domain, result]) =>
          (infer afterExpose argument).next fun afterArgument argumentType =>
            (requireTypes normal limit childDepth afterArgument argumentType.typeRoot domain argument).next
              fun afterCheck pair =>
                (instantiate limit childDepth afterCheck result argument).next fun afterSubstitution output =>
                  ⟨afterSubstitution, .ok ⟨output, functionType.compared ++ argumentType.compared ++ [pair]⟩⟩
      | _ => discard afterExpose function

/-- The list reverses the compiler's physical list of bindings so that
de Bruijn index zero looks up the newest binding. Visibility is shared
by inference and all type normalization visits. -/
def runWithData (normal : NormalAt) (roots : List Roots) (visible limit : Nat) (isData : Nat → Bool) :
    Nat → List GraphBinding → Infer
  | 0, _, state, root => tick limit 0 state root (fun entered => discard entered root)
  | depth + 1, ctx, state, root =>
      tick limit (depth + 1) state root fun entered =>
        match entered.arena[root]? with
        | some (.var index) =>
            match ctx[index]? with
            | some binding => shiftInferred limit depth entered binding.typeRoot (index + 1)
            | none => discard entered root
        | some (.node (.global index) []) =>
            if index < visible then
              match roots[index]? with
              | some declaration => shiftInferred limit depth entered declaration.typeRoot ctx.length
              | none => discard entered root
            else ⟨entered, .error (.invisibleGlobal root)⟩
        | some (.node (.universe level) []) =>
            if level < 32 then emit entered (.universe (level + 1)) else discard entered root
        | some (.node .prop []) | some (.node .u64 []) | some (.node .i64 []) =>
            emit entered (.universe 0)
        | some (.node (.natural value) []) =>
            if value < 2^64 then emit entered .u64 else discard entered root
        | some (.node (.integer value) []) =>
            if -(2^63 : Int) ≤ value ∧ value < (2^63 : Int) then emit entered .i64 else discard entered root
        | some (.node .array [n]) | some (.node .buffer [n]) =>
            inferFixed (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              .u64 [n] (.universe 0) []
        | some (.node .eq [a, b]) | some (.node .lt [a, b]) =>
            inferFixed (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              .u64 [a, b] .prop []
        | some (.node .refl [a]) =>
            inferFixed (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              .u64 [a] .eq [a, a]
        | some (.node .uadd [a, b]) =>
            inferFixed (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              .u64 [a, b] .u64 []
        | some (.node (.arith _) [a, b]) =>
            inferFixed (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              .i64 [a, b] .i64 []
        | some (.node .decide [a, b]) =>
            inferDecide (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              root a b
        | some (.node .strict [a, b]) =>
            inferStrict (runWithData normal roots visible limit isData depth ctx) entered a b
        | some (.node .zeroLe [a]) =>
            inferZeroLe (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered a
        | some (.node .usub [a, b, proof]) =>
            inferSubtract (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              a b proof
        | some (.node .ltAdd [a, b, delta, proof]) =>
            inferOffsetProof (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              true a b delta proof
        | some (.node .ltCancel [a, b, delta, proof]) =>
            inferOffsetProof (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              false a b delta proof
        | some (.node .ltLe [a, b, c, lower, upper]) =>
            inferTransitiveProof (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              a b c lower upper
        | some (.node .ifEq [a, b, yes, no]) =>
            inferConditional (runWithData normal roots visible limit isData depth ctx)
              (fun assumption => runWithData normal roots visible limit isData depth (⟨assumption, true⟩ :: ctx))
              (normal depth) limit depth entered true a b yes no
        | some (.node .ifLt [a, b, yes, no]) =>
            inferConditional (runWithData normal roots visible limit isData depth ctx)
              (fun assumption => runWithData normal roots visible limit isData depth (⟨assumption, true⟩ :: ctx))
              (normal depth) limit depth entered false a b yes no
        | some (.node .refine [predicate]) =>
            inferRefine (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered predicate
        | some (.node .pack [predicate, word, evidence]) =>
            inferPack (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              predicate word evidence
        | some (.node .transport [predicate, equality, payload]) =>
            inferTransport (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered
              predicate equality payload
        | some (.node .witness [subject]) =>
            inferRefinementProjection (runWithData normal roots visible limit isData depth ctx) (normal depth) entered false subject
        | some (.node .proof [subject]) =>
            inferRefinementProjection (runWithData normal roots visible limit isData depth ctx) (normal depth) entered true subject
        | some (.node (.pi erased) [a, b]) =>
            inferBinding (runWithData normal roots visible limit isData depth ctx)
              (runWithData normal roots visible limit isData depth (⟨a, erased⟩ :: ctx))
              (normal depth) isData entered true erased a b
        | some (.node (.lam erased) [a, b]) =>
            inferBinding (runWithData normal roots visible limit isData depth ctx)
              (runWithData normal roots visible limit isData depth (⟨a, erased⟩ :: ctx))
              (normal depth) isData entered false erased a b
        | some (.node .app [f, a]) =>
            inferApp (runWithData normal roots visible limit isData depth ctx) (normal depth) limit depth entered f a
        | _ => discard entered root

def runWith (normal : NormalAt) (roots : List Roots) (visible limit : Nat) : Nat → List GraphBinding → Infer :=
  runWithData normal roots visible limit (fun _ => false)

def run (roots : List Roots) (visible limit : Nat) : Nat → List GraphBinding → Infer :=
  runWith (NativeCoreNestedAliases.run roots visible limit) roots visible limit

private theorem next_progress {before : Outcome α} {later : State → α → Outcome β}
    (prior : Progress limit state before) (room : state.steps ≤ limit)
    (following : ∀ value, before.result = .ok value → before.state.steps ≤ limit →
      Progress limit before.state (later before.state value)) :
    Progress limit state (before.next later) := by
  cases found : before.result with
  | error reason =>
      simp only [Outcome.next, found]
      exact ⟨prior.kept, prior.monotone, prior.bounded, fun _ _ impossible => by cases impossible⟩
  | ok value =>
      have within := prior.accepted room value found
      have after := following value found within
      simp only [Outcome.next, found]
      exact ⟨prior.kept.trans after.kept, Nat.le_trans prior.monotone after.monotone,
        fun _ => after.bounded within, fun _ output done => after.accepted within output done⟩

private theorem identify_progress (room : state.steps ≤ limit) :
    Progress limit state (NativeCoreTypedEqual.identify limit depth state left right) := by
  have bounds := NativeCoreIdentical.runArena_step_bounds (arena := state.arena)
    (depth := depth) (a := left) (b := right) room
  generalize found : NativeCoreIdentical.runArena state.arena limit depth state.steps left right = outcome at bounds ⊢
  rcases outcome with ⟨result, spent⟩
  simp only [NativeCoreTypedEqual.identify, found]
  refine ⟨.refl _, bounds.1, fun _ => bounds.2.1, fun _ value success => ?_⟩
  cases result with
  | error reason => simp [Except.mapError] at success
  | ok answer =>
      have found : answer = value := Except.ok.inj (by simpa only [Except.mapError] using success)
      exact bounds.2.2 value (congrArg Except.ok found)

theorem requireTypes_progress
    (metered : ∀ state root, state.steps ≤ limit → Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (requireTypes normal limit depth state actual expected argument) := by
  apply next_progress (metered _ _ room) room
  intro left _ leftRoom
  apply next_progress (metered _ _ leftRoom) leftRoom
  intro right _ rightRoom
  apply next_progress (identify_progress rightRoom) rightRoom
  intro same _ _
  cases same <;> exact Progress.atState _ _

private theorem requireOperands_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, state.steps ≤ limit → Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (requireOperands infer normal limit depth expected state args) := by
  induction args generalizing state with
  | nil => exact Progress.atState _ _
  | cons root rest ih =>
      apply next_progress (infers _ _ room) room
      intro type _ inferredRoom
      apply next_progress (requireTypes_progress normalizes inferredRoom) inferredRoom
      intro pair _ checkedRoom
      exact (ih checkedRoom).next (fun _ => Progress.atState _ _)

private theorem checkFixed_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, state.steps ≤ limit → Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (checkFixed infer normal limit depth state operand args) := by
  apply next_progress (append_progress _ _ _) room
  intro expected _ emittedRoom
  exact requireOperands_progress infers normalizes emittedRoom

private theorem inferFixed_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, state.steps ≤ limit → Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferFixed infer normal limit depth state operand args output refs) := by
  apply next_progress (checkFixed_progress infers normalizes room) room
  intro comparisons _ _
  exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)

private theorem finishDecide_progress
    (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (finishDecide normal state root first second) := by
  unfold finishDecide
  apply (normalizes _ _).next
  intro left
  apply (normalizes _ _).next
  intro right
  split
  · split
    · exact append_progress _ _ _
    · exact Progress.atState _ _
  · exact Progress.atState _ _

private theorem inferDecide_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferDecide infer normal limit depth state root first second) := by
  apply next_progress (checkFixed_progress infers (fun state root _ => normalizes state root) room) room
  intro comparisons _ _
  exact (finishDecide_progress normalizes).next (fun _ => Progress.atState _ _)

private theorem inferStrict_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferStrict infer state effect result) := by
  apply next_progress (infers _ _ room) room
  intro type _ effectRoom
  exact (infers _ _ effectRoom).next (fun _ => Progress.atState _ _)

private theorem addOne_progress (state : State) (word : Nat) : Progress limit state (addOne state word) :=
  (append_progress _ _ _).next (fun _ => append_progress _ _ _)

private theorem subtractBound_progress (state : State) (numerator denominator : Nat) :
    Progress limit state (subtractBound state numerator denominator) :=
  (addOne_progress _ _).next (fun _ => append_progress _ _ _)

private theorem zeroBound_progress (state : State) (word : Nat) : Progress limit state (zeroBound state word) :=
  (append_progress _ _ _).next (fun _ => subtractBound_progress _ _ _)

private theorem inferZeroLe_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferZeroLe infer normal limit depth state word) := by
  apply next_progress (checkFixed_progress infers (fun state root _ => normalizes state root) room) room
  intro comparisons _ _
  exact (zeroBound_progress _ _).next (fun _ => Progress.atState _ _)

private theorem checkSubtract_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (checkSubtract infer normal limit depth state numerator denominator proof) := by
  apply next_progress (subtractBound_progress _ _ _) room
  intro expected _ after
  exact requireOperands_progress infers (fun state root _ => normalizes state root) after

private theorem inferSubtract_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferSubtract infer normal limit depth state numerator denominator proof) := by
  apply next_progress (checkFixed_progress infers (fun state root _ => normalizes state root) room) room
  intro comparisons _ operandsRoom
  apply next_progress (checkSubtract_progress infers normalizes operandsRoom) operandsRoom
  intro proofComparisons _ _
  exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)

private theorem offsetBounds_progress (state : State) (left right delta : Nat) :
    Progress limit state (offsetBounds state left right delta) :=
  (append_progress _ _ _).next (fun _ => (append_progress _ _ _).next (fun _ =>
    (append_progress _ _ _).next (fun _ => (append_progress _ _ _).next (fun _ => Progress.atState _ _))))

private theorem inferOffsetProof_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferOffsetProof infer normal limit depth state forward left right delta proof) := by
  apply next_progress (checkFixed_progress infers (fun state root _ => normalizes state root) room) room
  intro operands _ operandRoom
  apply next_progress (offsetBounds_progress _ _ _ _) operandRoom
  intro bounds _ boundRoom
  apply next_progress (requireOperands_progress infers (fun state root _ => normalizes state root) boundRoom) boundRoom
  intro compared _ _
  exact Progress.atState _ _


private theorem transitiveBounds_progress (state : State) (left middle right : Nat) :
    Progress limit state (transitiveBounds state left middle right) :=
  (addOne_progress _ _).next (fun _ => (append_progress _ _ _).next (fun _ =>
    (append_progress _ _ _).next (fun _ => Progress.atState _ _)))

private theorem inferTransitiveProof_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferTransitiveProof infer normal limit depth state left middle right lower upper) := by
  apply next_progress (checkFixed_progress infers (fun state root _ => normalizes state root) room) room
  intro _ _ operandsRoom
  apply next_progress (transitiveBounds_progress _ _ _ _) operandsRoom
  intro _ _ boundsRoom
  apply next_progress (requireOperands_progress infers (fun state root _ => normalizes state root) boundsRoom) boundsRoom
  intro _ _ lowerRoom
  apply next_progress (requireOperands_progress infers (fun state root _ => normalizes state root) lowerRoom) lowerRoom
  intro _ _ _
  exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)

private theorem finishConditional_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (inferAlternative state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (finishConditional inferAlternative normal limit depth state thenType alternative) := by
  apply next_progress (normalizes _ _) room
  intro normalized _ normalRoom
  apply next_progress (lowerType_progress _ _ _ _) normalRoom
  intro result _ lowerRoom
  apply next_progress (requireOperands_progress infers (fun state root _ => normalizes state root) lowerRoom) lowerRoom
  intro compared _ _
  exact Progress.atState _ _

private theorem inferConditional_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (infersThen : ∀ assumption state root, state.steps ≤ limit → Progress limit state (inferThen assumption state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferConditional infer inferThen normal limit depth state equality left right yes no) := by
  apply next_progress (checkFixed_progress infers (fun state root _ => normalizes state root) room) room
  intro compared _ checkedRoom
  apply next_progress (append_progress _ _ _) checkedRoom
  intro assumption _ openedRoom
  apply next_progress (infersThen assumption _ _ openedRoom) openedRoom
  intro inferred _ thenRoom
  apply next_progress (finishConditional_progress infers normalizes thenRoom) thenRoom
  intro result _ _
  exact Progress.atState _ _

private theorem predicateType_progress (state : State) : Progress limit state (predicateType state) :=
  (append_progress _ _ _).next (fun _ => (append_progress _ _ _).next (fun _ => append_progress _ _ _))

private theorem checkPredicate_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (checkPredicate infer normal limit depth state predicate) := by
  apply next_progress (predicateType_progress _) room
  intro expected _ expectedRoom
  exact requireOperands_progress infers (fun state root _ => normalizes state root) expectedRoom

private theorem inferRefine_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferRefine infer normal limit depth state predicate) := by
  apply next_progress (checkPredicate_progress infers normalizes room) room
  intro comparisons _ _
  exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)

private theorem checkPredicateEvidence_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (checkPredicateEvidence infer normal limit depth state predicate word evidence) := by
  apply next_progress (append_progress _ _ _) room
  intro expected _ expectedRoom
  exact requireOperands_progress infers (fun state root _ => normalizes state root) expectedRoom

private theorem inferPack_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferPack infer normal limit depth state predicate word evidence) := by
  apply next_progress (checkPredicate_progress infers normalizes room) room
  intro predicatePairs _ predicateRoom
  apply next_progress (checkFixed_progress infers (fun state root _ => normalizes state root) predicateRoom) predicateRoom
  intro wordPairs _ wordRoom
  apply next_progress (checkPredicateEvidence_progress infers normalizes wordRoom) wordRoom
  intro proofPairs _ _
  exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)

private theorem refinementProjectionType_progress (state : State) (evidence : Bool) (predicate subject : Nat) :
    Progress limit state (refinementProjectionType state evidence predicate subject) := by
  cases evidence
  · exact append_progress _ _ _
  · simp only [refinementProjectionType, ite_true]
    exact (append_progress _ _ _).next (fun _ => append_progress _ _ _)

private theorem inferRefinementProjection_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferRefinementProjection infer normal state evidence subject) := by
  apply next_progress (infers _ _ room) room
  intro sourceType _ sourceRoom
  apply (normalizes _ _).next
  intro typeRoot
  split
  · exact (refinementProjectionType_progress _ _ _ _).next (fun _ => Progress.atState _ _)
  · exact Progress.atState _ _

private theorem inferTransport_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferTransport infer normal limit depth state predicate equality payload) := by
  apply next_progress (checkPredicate_progress infers normalizes room) room
  intro predicatePairs _ predicateRoom
  apply next_progress (infers _ _ predicateRoom) predicateRoom
  intro inferred _ equalityRoom
  apply next_progress (normalizes _ _) equalityRoom
  intro typeRoot _ typeRoom
  split
  · apply next_progress (checkPredicateEvidence_progress infers normalizes typeRoom) typeRoom
    intro proofPairs _ _
    exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)
  · exact Progress.atState _ _

private theorem inferBinder_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferBinder infer normal isData state domain erased) := by
  apply next_progress (infers _ _ room) room
  intro inferred _ _
  exact (NativeCoreGhostSort.sort_progress normalizes).next (fun _ =>
    (NativeCoreGhostSort.policy_progress normalizes).next (fun _ => Progress.atState _ _))

private theorem finishBinding_progress
    (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (finishBinding normal state product erased domain rangeRoot domainSort) := by
  cases product
  · exact append_progress _ _ _
  · simp only [finishBinding, ite_true]
    exact (NativeCoreGhostSort.sort_progress normalizes).next (fun _ => append_progress _ _ _)

private theorem inferBinding_progress
    (infersDomain : ∀ state root, state.steps ≤ limit → Progress limit state (inferDomain state root))
    (infersBody : ∀ state root, state.steps ≤ limit → Progress limit state (inferBody state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferBinding inferDomain inferBody normal isData state product erased domain body) := by
  apply next_progress (inferBinder_progress infersDomain normalizes room) room
  intro checked _ binderRoom
  apply next_progress (infersBody _ _ binderRoom) binderRoom
  intro inferred _ _
  exact (finishBinding_progress normalizes).next (fun _ => Progress.atState _ _)

theorem inferApp_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, state.steps ≤ limit → Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferApp infer normal limit childDepth state function argument) := by
  apply next_progress (infers _ _ room) room
  intro functionType _ functionRoom
  apply next_progress (normalizes _ _ functionRoom) functionRoom
  intro functionRoot _ exposedRoom
  split
  · apply next_progress (infers _ _ exposedRoom) exposedRoom
    intro argumentType _ argumentRoom
    apply next_progress (requireTypes_progress normalizes argumentRoom) argumentRoom
    intro pair _ _
    exact (instantiate_progress _ _ _ _ _).next (fun _ => Progress.atState _ _)
  · exact Progress.atState _ _

private theorem tick_progress
    (after : ∀ entered, entered.steps ≤ limit → Progress limit entered (visit entered)) :
    Progress limit state (tick limit depth state root visit) := by
  have rejected (why : NativeCoreIdentical.Error) :
      Progress limit state (⟨{state with steps := state.steps + 1}, .error (.tick why)⟩ : Outcome Inferred) :=
    ⟨.refl _, Nat.le_succ _, Nat.succ_le_succ, fun _ _ impossible => by cases impossible⟩
  by_cases outside : limit < state.steps + 1
  · simpa only [tick, NativeCoreUnsignedCancellation.tick, ite_eq_left outside] using rejected (.stepLimit root)
  by_cases tooDeep : depth = 0
  · simpa only [tick, NativeCoreUnsignedCancellation.tick, ite_eq_right outside, ite_eq_left tooDeep] using
      rejected (.depthLimit root)
  by_cases missing : state.arena.size ≤ root
  · simpa only [tick, NativeCoreUnsignedCancellation.tick, ite_eq_right outside, ite_eq_right tooDeep,
      ite_eq_left missing] using
      rejected (.invalidReference root)
  have room : state.steps + 1 ≤ limit := by omega
  have continued := after {state with steps := state.steps + 1} room
  simp only [tick, NativeCoreUnsignedCancellation.tick, ite_eq_right outside, ite_eq_right tooDeep, ite_eq_right missing]
  exact ⟨continued.kept, Nat.le_trans (Nat.le_succ _) continued.monotone,
    fun _ => continued.bounded room, fun _ => continued.accepted room⟩

/-- Progress is a statement about the executable graph path, including
rejected steps and failures before the eventual type has been instantiated. -/
theorem runWithData_progress {normal : NormalAt} {roots : List Roots} {bindings : List GraphBinding}
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runWithData normal roots visible limit isData depth bindings state root) := by
  induction depth generalizing state root bindings with
  | zero => exact tick_progress (fun _ _ => Progress.atState _ _)
  | succ depth ih =>
      simp only [runWithData]
      apply tick_progress
      intro entered within
      split
      · split
        · exact (shiftType_progress _ _ _ _ _).map plain
        · exact Progress.atState _ _
      · split
        · split
          · exact (shiftType_progress _ _ _ _ _).map plain
          · exact Progress.atState _ _
        · exact Progress.atState _ _
      · split
        · exact (append_progress _ _ _).map plain
        · exact Progress.atState _ _
      · exact (append_progress _ _ _).map plain
      · exact (append_progress _ _ _).map plain
      · exact (append_progress _ _ _).map plain
      · split
        · exact (append_progress _ _ _).map plain
        · exact Progress.atState _ _
      · split
        · exact (append_progress _ _ _).map plain
        · exact Progress.atState _ _
      all_goals with_reducible first
        | exact inferFixed_progress (fun _ _ room => ih room)
            (fun state ref _ => normalProgress depth state ref) within
        | exact inferDecide_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferStrict_progress (fun _ _ room => ih room) within
        | exact inferZeroLe_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferSubtract_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferOffsetProof_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferTransitiveProof_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferConditional_progress (fun _ _ room => ih room) (fun _ _ _ room => ih room)
            (normalProgress depth) within
        | exact inferRefine_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferPack_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferTransport_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferRefinementProjection_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferBinding_progress (fun _ _ room => ih room) (fun _ _ room => ih room)
            (normalProgress depth) within
        | exact inferApp_progress (fun _ _ room => ih room)
            (fun state ref _ => normalProgress depth state ref) within
        | simpa only [discard] using (Progress.atState (limit := limit) entered
            (.error (.outsideFragment root) : Except NativeCorePureComputationNormal.Error Inferred))

theorem runWith_progress {normal : NormalAt} {roots : List Roots} {bindings : List GraphBinding}
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runWith normal roots visible limit depth bindings state root) :=
  runWithData_progress normalProgress room

theorem run_progress {roots : List Roots} {bindings : List GraphBinding}
    (room : state.steps ≤ limit) :
    Progress limit state (run roots visible limit depth bindings state root) :=
  runWith_progress (NativeCoreNestedAliases.run_progress roots visible limit) room

/-- Each graph row records the written domain in pre-binder scope. -/
def BindingRep (env : Environment) (arena : Arena) (row : GraphBinding) (binding : Binding) : Prop :=
  ∃ term, Represents arena row.typeRoot term ∧ binding.ty = expand env term ∧ binding.erased = row.erased

inductive ContextRep (env : Environment) (arena : Arena) : List GraphBinding → Context → Prop where
  | nil : ContextRep env arena [] []
  | cons : BindingRep env arena row binding → ContextRep env arena rows ctx →
      ContextRep env arena (row :: rows) (binding :: ctx)

theorem ContextRep.frame (represented : ContextRep env arena rows ctx) (kept : Prefix arena after) :
    ContextRep env after rows ctx := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih =>
      obtain ⟨term, source, ty, flag⟩ := head
      exact .cons ⟨term, source.frame kept, ty, flag⟩ ih

theorem ContextRep.lookup_type (represented : ContextRep env arena rows ctx)
    {index : Nat} (found : rows[index]? = some row) :
    ∃ term, Represents arena row.typeRoot term ∧
      lookup ctx index = some ⟨(expand env term).rename (fun x => x + (index + 1)), row.erased⟩ := by
  induction represented generalizing index with
  | nil => simp at found
  | cons headRep tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst row
          obtain ⟨term, source, ty, flag⟩ := headRep
          exact ⟨term, source, by simp only [lookup, ty, flag]⟩
      | succ k =>
          obtain ⟨term, source, atIndex⟩ := ih (by simpa using found)
          refine ⟨term, source, ?_⟩
          simp only [lookup, atIndex, Option.map_some, Term.rename_comp, Nat.succ_eq_add_one, Nat.add_assoc]

private theorem represented_at {index : Nat} (aligned : RepresentsDefinitions arena roots definitions)
    (found : roots[index]? = some row) :
    ∃ source, definitions[index]? = some source ∧ RepresentsDefinition arena row source := by
  induction aligned generalizing index with
  | nil => simp at found
  | @cons _ source _ _ head _ tail =>
      cases index with
      | zero => cases found; exact ⟨source, rfl, head⟩
      | succ index => exact tail found

private theorem type_expansion_at {index : Nat} (history : LoanTyping.MixedProgram.History definitions declarations env)
    (found : definitions[index]? = some source) :
    ∃ entry, env.globals[index]? = some entry ∧ GlobalEnvironment.Expansion env.globals source.type entry.type := by
  induction history with
  | empty => simp at found
  | @definition definitions declarations env raw entry history checked ih =>
      by_cases earlier : index < definitions.length
      · rw [List.getElem?_append_left earlier] at found
        obtain ⟨previous, previousFound, expanded⟩ := ih found
        have inside : index < env.globals.size := history.globalLength.symm ▸ earlier
        refine ⟨previous, ?_, expanded.extend entry⟩
        rw [Array.getElem?_eq_getElem inside] at previousFound
        exact (Array.getElem?_push_lt (x := entry) inside).trans previousFound
      · have bound := (List.getElem?_eq_some_iff.mp found).1
        have atEnd : index = definitions.length := by simp only [List.length_append, List.length_singleton] at bound; omega
        subst index
        have same : raw = source := by simpa using found
        subst source
        exact ⟨entry, by rw [← history.globalLength, Array.getElem?_push_size], checked.typeExpansion.extend entry⟩
  | family _ _ ih => exact ih found

private theorem checked_type_at {index : Nat} (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions arena roots definitions) (found : roots[index]? = some row) :
    ∃ entry written, env.globals[index]? = some entry ∧ Represents arena row.typeRoot written ∧
      expand env written = entry.type := by
  obtain ⟨source, sourceFound, represented⟩ := represented_at aligned found
  obtain ⟨entry, recorded, expanded⟩ := type_expansion_at history sourceFound
  exact ⟨entry, source.type, recorded, represented.1, EnvironmentDelta.expansion_eq_expand expanded⟩

private theorem plain_success {original : Outcome Nat} (success : (original.result.map plain) = .ok answer) :
    ∃ selected, original.result = .ok selected ∧ answer = plain selected := by
  cases found : original.result with
  | error reason => simp [found, Except.map] at success
  | ok selected =>
      exact ⟨selected, rfl, (Except.ok.inj (by simpa only [found, Except.map] using success)).symm⟩

private theorem shiftType_refines (source : Represents state.arena root written)
    (success : (shiftType limit depth state root amount).result = .ok selected) :
    let output := shiftType limit depth state root amount
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      Represents output.state.arena selected (written.rename (fun x => x + amount)) := by
  obtain ⟨kept, backward, residual, expected, held⟩ :=
    (NativeCoreTransformExact.run_refines (mode := .shift amount) (binders := 0) (value := written)
      source trivial (liftTransform_success success)).1
  change PartialRenaming.shift amount 0 written = some residual at expected
  rw [PartialRenaming.shift_nonnegative (by omega)] at expected
  have shape : PartialRenaming.raiseIndex 0 ((amount : Int).toNat) = fun x => x + amount := by
    funext index
    simp [PartialRenaming.raiseIndex]
  rw [shape] at expected
  cases expected
  exact ⟨kept, backward, held⟩

private theorem lowerType_refines (source : Represents state.arena root written)
    (success : (lowerType limit depth state root).result = .ok selected) :
    let output := lowerType limit depth state root
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ result, Represents output.state.arena selected result ∧ result.rename Nat.succ = written := by
  obtain ⟨kept, backward, result, lowered, represented⟩ :=
    (NativeCoreTransformExact.run_refines (mode := .shift (-1)) (binders := 0) (value := written)
      source trivial (liftTransform_success success)).1
  exact ⟨kept, backward, result, represented, LoanTyping.Checker.branch_type_reweakens lowered⟩

private theorem tick_success (success : (tick limit depth state root visit).result = .ok selected) :
    tick limit depth state root visit = visit {state with steps := state.steps + 1} ∧ state.steps + 1 ≤ limit := by
  by_cases outside : limit < state.steps + 1
  · simp [tick, NativeCoreUnsignedCancellation.tick, outside] at success
  by_cases tooDeep : depth = 0
  · simp [tick, NativeCoreUnsignedCancellation.tick, outside, tooDeep] at success
  by_cases missing : state.arena.size ≤ root
  · simp [tick, NativeCoreUnsignedCancellation.tick, outside, tooDeep, missing] at success
  exact ⟨by simp [tick, NativeCoreUnsignedCancellation.tick, outside, tooDeep, missing], by omega⟩

def PairRetained (arena : Arena) (pair : Nat × Nat) : Prop :=
  ∃ first second, Represents arena pair.1 first ∧ Represents arena pair.2 second ∧
    FullyRetained first ∧ FullyRetained second

def RetainedComparisons (arena : Arena) (answer : Inferred) : Prop :=
  ∀ pair ∈ answer.compared, PairRetained arena pair

private theorem identify_true
    (left : Represents state.arena a first) (right : Represents state.arena b second)
    (success : (NativeCoreTypedEqual.identify limit depth state a b).result = .ok true) :
    (NativeCoreTypedEqual.identify limit depth state a b).state.arena = state.arena ∧
      NativeCoreCompare.project first = NativeCoreCompare.project second := by
  rcases compared : NativeCoreIdentical.runArena state.arena limit depth state.steps a b with ⟨result, steps⟩
  cases result with
  | error reason => simp [NativeCoreTypedEqual.identify, compared, Except.mapError] at success
  | ok flag =>
      simp [NativeCoreTypedEqual.identify, compared, Except.mapError] at success
      subst flag
      exact ⟨by simp [NativeCoreTypedEqual.identify, compared],
        (NativeCoreIdentical.runArena_refines left right compared).mp rfl⟩

/-- Retention is evidence about the actual two comparison outcomes.
Full syntax equality reflects their projected identity, and the normalizer
supplies conversion from each original type to its corresponding outcome. -/
theorem requireTypes_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (leftRep : Represents state.arena actual actualType) (rightRep : Represents state.arena expected expectedType)
    (success : (requireTypes normal limit depth state actual expected argument).result = .ok pair)
    (ambient : Prefix (requireTypes normal limit depth state actual expected argument).state.arena final)
    (retained : PairRetained final pair) :
    let output := requireTypes normal limit depth state actual expected argument
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      LoanTyping.Conversion.Conv env (expand env actualType) (expand env expectedType) := by
  unfold requireTypes at success ambient ⊢
  obtain ⟨a, firstOk, firstNext⟩ := Outcome.next_success success
  obtain ⟨firstKept, firstBack, first, firstRep, firstChange⟩ := normalSound onBase leftRep firstOk
  rw [firstNext] at success ambient ⊢
  obtain ⟨b, secondOk, secondNext⟩ := Outcome.next_success success
  obtain ⟨secondKept, secondBack, second, secondRep, secondChange⟩ :=
    normalSound (onBase.trans firstKept) (rightRep.frame firstKept) secondOk
  rw [secondNext] at success ambient ⊢
  obtain ⟨flag, identical, identityNext⟩ := Outcome.next_success success
  rw [identityNext] at success ambient ⊢
  cases flag with
  | false => simp [discard] at success
  | true =>
      simp at success
      subst pair
      have firstFinal := firstRep.frame secondKept
      obtain ⟨unchanged, same⟩ := identify_true firstFinal secondRep identical
      simp [unchanged] at ambient ⊢
      obtain ⟨left, right, leftRep, rightRep, leftKept, rightKept⟩ := retained
      have sameLeft := (firstFinal.frame ambient).unique leftRep
      have sameRight := (secondRep.frame ambient).unique rightRep
      have syntactic : first = second := NativeCoreCompare.project_injective_of_fully_retained
        (sameLeft.symm ▸ leftKept) (sameRight.symm ▸ rightKept) same
      refine ⟨firstKept.trans secondKept, secondBack ∘ firstBack, ?_⟩
      have converted : LoanTyping.Conversion.Conv env (expand env actualType) (expand env first) :=
        firstChange.converted
      rw [syntactic] at converted
      exact converted.trans secondChange.converted.symm

private theorem binary_read
    (represented : Represents arena root term) (read : arena[root]? = some (.node op [a, b])) :
    ∃ first second, term = .node op [first, second] ∧ Represents arena a first ∧ Represents arena b second := by
  cases represented with
  | var variableRead => rw [read] at variableRead; cases variableRead
  | node found _ children =>
      rw [read] at found
      cases found
      cases children with
      | cons first tail =>
        cases tail with
        | cons second tail =>
          cases tail
          exact ⟨_, _, rfl, first, second⟩

structure Refines (env : Environment) (arena : Arena) (ctx : Context) (source : Term)
    (outcome : Outcome Inferred) (answer : Inferred) : Prop where
  kept : Prefix arena outcome.state.arena
  backward : Backward arena → Backward outcome.state.arena
  inferred : ∃ type, Represents outcome.state.arena answer.typeRoot type ∧
    LoanTyping.HasType env [] ctx true (expand env source) (expand env type)

def InferSound (env : Environment) (base : Arena) (ctx : Context) (limit : Nat) (visit : Infer) : Prop :=
  ∀ {state root term answer final}, Prefix base state.arena → state.steps ≤ limit → Represents state.arena root term →
    (visit state root).result = .ok answer → Prefix (visit state root).state.arena final →
    RetainedComparisons final answer → Refines env state.arena ctx term (visit state root) answer

private theorem inferBinder_refines
    (metadata : DataFamilies env isData)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (domainRep : Represents state.arena domain term)
    (success : (inferBinder infer normal isData state domain erased).result = .ok answer)
    (ambient : Prefix (inferBinder infer normal isData state domain erased).state.arena final)
    (retained : ∀ pair ∈ answer.compared, PairRetained final pair) :
    let after := (inferBinder infer normal isData state domain erased).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.Binder env [] ctx erased (expand env term) answer.sort := by
  unfold inferBinder at success ambient ⊢
  obtain ⟨inferred, inferenceOk, inferredNext⟩ := Outcome.next_success success
  rw [inferredNext] at success ambient ⊢
  obtain ⟨selected, sortOk, sortNext⟩ := Outcome.next_success success
  rw [sortNext] at success ambient ⊢
  obtain ⟨⟨⟩, policyOk, policyNext⟩ := Outcome.next_success success
  rw [policyNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  have inferProgress := childProgress state domain room
  let sorted := NativeCoreGhostSort.sort normal (infer state domain).state inferred.typeRoot
  have sortProgress := NativeCoreGhostSort.sort_progress (state := (infer state domain).state)
    (typeRoot := inferred.typeRoot) normalProgress
  have policyProgress := NativeCoreGhostSort.policy_progress (state := sorted.state) (isData := isData)
    (domain := domain) (selected := selected) (erased := erased) normalProgress
  have afterSort := policyProgress.kept.trans ambient
  obtain ⟨_, inferBack, _, inferredRep, domainTyped⟩ := childSound onBase room domainRep inferenceOk
    (sortProgress.kept.trans afterSort) retained
  obtain ⟨sortedKept, sortedBack, exposed⟩ := NativeCoreGhostSort.sort_refines normalSound
    (onBase.trans inferProgress.kept) inferredRep sortOk
  have throughSort := inferProgress.kept.trans sortedKept
  obtain ⟨policyKept, policyBack, allowed⟩ := NativeCoreGhostSort.policy_refines normalSound metadata
    (onBase.trans throughSort) (domainRep.frame throughSort) policyOk
  exact ⟨throughSort.trans policyKept, policyBack ∘ sortedBack ∘ inferBack,
    .intro (domainTyped.convert exposed) allowed⟩

private theorem finishBinding_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (domainRep : Represents state.arena domain a) (rangeRep : Represents state.arena rangeRoot type)
    (binder : LoanTyping.Binder env [] ctx erased (expand env a) domainSort)
    (body : LoanTyping.HasType env [] (⟨expand env a, erased⟩ :: ctx) true (expand env b) (expand env type))
    (success : (finishBinding normal state product erased domain rangeRoot domainSort).result = .ok root) :
    let after := (finishBinding normal state product erased domain rangeRoot domainSort).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ resultType, Represents after root resultType ∧ LoanTyping.HasType env [] ctx true
        (expand env (if product then .pi erased a b else .lam erased a b)) (expand env resultType) := by
  cases product
  · obtain ⟨kept, backward, represented⟩ := append_refines (.cons domainRep (.cons rangeRep .nil)) rfl success
    refine ⟨kept, backward, _, represented, ?_⟩
    simpa only [Bool.false_eq_true, ite_false, Term.pi, Term.lam, expand, expandArgs] using
      LoanTyping.HasType.lam binder body
  · simp only [finishBinding, ite_true] at success ⊢
    obtain ⟨rangeSort, rangeOk, rangeNext⟩ := Outcome.next_success success
    rw [rangeNext] at success ⊢
    obtain ⟨sortedKept, sortedBack, converted⟩ := NativeCoreGhostSort.sort_refines normalSound onBase rangeRep rangeOk
    obtain ⟨resultKept, resultBack, represented⟩ := append_refines .nil (sortOp_arity _).symm success
    refine ⟨sortedKept.trans resultKept, resultBack ∘ sortedBack, _, represented, ?_⟩
    rw [sortOp_expanded]
    simpa only [ite_true, Term.pi, expand, expandArgs] using LoanTyping.HasType.pi binder (body.convert converted)

private theorem inferBinding_refines
    (metadata : DataFamilies env isData)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (domainSound : InferSound env base ctx limit inferDomain)
    (domainProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferDomain state root))
    (bodySound : ∀ {extended}, Prefix state.arena extended →
      InferSound env extended (⟨expand env a, erased⟩ :: ctx) limit inferBody)
    (bodyProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferBody state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (domainRep : Represents state.arena domain a) (bodyRep : Represents state.arena body b)
    (success : (inferBinding inferDomain inferBody normal isData state product erased domain body).result = .ok answer)
    (ambient : Prefix (inferBinding inferDomain inferBody normal isData state product erased domain body).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (if product then .pi erased a b else .lam erased a b)
      (inferBinding inferDomain inferBody normal isData state product erased domain body) answer := by
  unfold inferBinding at success ambient ⊢
  obtain ⟨checked, binderOk, binderNext⟩ := Outcome.next_success success
  rw [binderNext] at success ambient ⊢
  obtain ⟨inferred, inferredOk, inferredNext⟩ := Outcome.next_success success
  rw [inferredNext] at success ambient ⊢
  obtain ⟨selected, resultOk, resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let bound := inferBinder inferDomain normal isData state domain erased
  have binderRoom := (inferBinder_progress (domain := domain) (isData := isData) (erased := erased)
    domainProgress normalProgress room).accepted room checked binderOk
  have nextProgress := bodyProgress bound.state body binderRoom
  have resultProgress := finishBinding_progress (state := (inferBody bound.state body).state)
    (product := product) (erased := erased) (domain := domain) (rangeRoot := inferred.typeRoot)
    (domainSort := checked.sort) normalProgress
  have bodyFinal := resultProgress.kept.trans ambient
  obtain ⟨binderKept, binderBack, domainTyped⟩ := inferBinder_refines metadata normalSound normalProgress
    domainSound domainProgress onBase room domainRep binderOk (nextProgress.kept.trans bodyFinal)
    (fun pair found => retained pair (List.mem_append_left _ found))
  obtain ⟨bodyKept, bodyBack, _, rangeRep, bodyTyped⟩ := bodySound binderKept (.refl _) binderRoom
    (bodyRep.frame binderKept) inferredOk bodyFinal (fun pair found => retained pair (List.mem_append_right _ found))
  have throughBody := binderKept.trans bodyKept
  obtain ⟨resultKept, resultBack, _, resultRep, typed⟩ := finishBinding_refines normalSound
    (onBase.trans throughBody) (domainRep.frame throughBody) rangeRep domainTyped bodyTyped resultOk
  exact ⟨throughBody.trans resultKept, resultBack ∘ bodyBack ∘ binderBack, _, resultRep, typed⟩

private theorem requireOperands_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (operands : RepresentsList state.arena args terms) (expectedRep : Represents state.arena expected type)
    (success : (requireOperands infer normal limit depth expected state args).result = .ok comparisons)
    (ambient : Prefix (requireOperands infer normal limit depth expected state args).state.arena final)
    (retained : ∀ pair ∈ comparisons, PairRetained final pair) :
    let outcome := requireOperands infer normal limit depth expected state args
    Prefix state.arena outcome.state.arena ∧ (Backward state.arena → Backward outcome.state.arena) ∧
      ∀ term ∈ terms, LoanTyping.HasType env [] ctx true (expand env term) (expand env type) := by
  induction args generalizing state terms comparisons with
  | nil =>
      cases operands
      exact ⟨.refl _, id, by simp⟩
  | cons root rest ih =>
      cases operands with
      | @cons _ term _ tail head tailRep =>
          simp only [requireOperands] at success ambient ⊢
          obtain ⟨inferred, inferredOk, inferredNext⟩ := Outcome.next_success success
          rw [inferredNext] at success ambient ⊢
          obtain ⟨pair, checkedOk, checkedNext⟩ := Outcome.next_success success
          rw [checkedNext] at success ambient ⊢
          obtain ⟨remaining, restOk, restNext⟩ := Outcome.next_success success
          rw [restNext] at success ambient ⊢
          simp only [Except.ok.injEq] at success
          subst comparisons
          have inferredProgress := childProgress state root room
          have inferredRoom := inferredProgress.accepted room inferred inferredOk
          let checked := requireTypes normal limit depth (infer state root).state inferred.typeRoot expected root
          have checkedProgress := requireTypes_progress (expected := expected) (actual := inferred.typeRoot)
            (argument := root) (depth := depth) (fun state ref _ => normalProgress state ref) inferredRoom
          have checkedRoom := checkedProgress.accepted inferredRoom pair checkedOk
          have restProgress := requireOperands_progress (expected := expected) (depth := depth) (args := rest)
            childProgress (fun state ref _ => normalProgress state ref) checkedRoom
          have checkedFinal := restProgress.kept.trans ambient
          have inferredFinal := checkedProgress.kept.trans checkedFinal
          obtain ⟨_, inferredBack, actualType, actualRep, typed⟩ := childSound onBase room head inferredOk
            inferredFinal (fun comparison found => retained comparison (List.mem_append_left _ found))
          obtain ⟨kept, checkedBack, conversion⟩ := requireTypes_refines normalSound
            (onBase.trans inferredProgress.kept) actualRep (expectedRep.frame inferredProgress.kept)
            checkedOk checkedFinal (retained pair (List.mem_append_right _ (List.mem_cons_self)))
          have throughCheck := inferredProgress.kept.trans kept
          obtain ⟨restKept, restBack, restTyped⟩ := ih (state := checked.state)
            (onBase.trans throughCheck) checkedRoom (tailRep.frame throughCheck) (expectedRep.frame throughCheck)
            restOk ambient (fun comparison found => retained comparison
              (List.mem_append_right _ (List.mem_cons_of_mem _ found)))
          refine ⟨throughCheck.trans restKept, restBack ∘ checkedBack ∘ inferredBack, ?_⟩
          intro operand member
          rcases List.mem_cons.mp member with rfl | previous
          · exact typed.convert conversion
          · exact restTyped operand previous

private theorem checkFixed_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (operands : RepresentsList state.arena args terms) (operandArity : operand.arity = 0)
    (success : (checkFixed infer normal limit depth state operand args).result = .ok comparisons)
    (ambient : Prefix (checkFixed infer normal limit depth state operand args).state.arena final)
    (retained : ∀ pair ∈ comparisons, PairRetained final pair) :
    let after := (checkFixed infer normal limit depth state operand args).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∀ term ∈ terms, LoanTyping.HasType env [] ctx true (expand env term) (expand env (.node operand [])) := by
  unfold checkFixed at success ambient ⊢
  obtain ⟨expected, emittedOk, emittedNext⟩ := Outcome.next_success success
  rw [emittedNext] at success ambient ⊢
  obtain ⟨emittedKept, emittedBack, expectedRep⟩ := append_refines .nil operandArity.symm emittedOk
  have emittedRoom := (append_progress state operand []).accepted room expected emittedOk
  obtain ⟨checkedKept, checkedBack, typedOperands⟩ := requireOperands_refines normalSound normalProgress childSound
    childProgress (onBase.trans emittedKept) emittedRoom (operands.frame emittedKept) expectedRep success ambient retained
  exact ⟨emittedKept.trans checkedKept, checkedBack ∘ emittedBack, typedOperands⟩

private theorem inferFixed_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (operands : RepresentsList state.arena args terms) (operandArity : operand.arity = 0)
    (resultRefs : RepresentsList state.arena refs resultTerms) (resultArity : refs.length = output.arity)
    (success : (inferFixed infer normal limit depth state operand args output refs).result = .ok answer)
    (ambient : Prefix (inferFixed infer normal limit depth state operand args output refs).state.arena final)
    (retained : RetainedComparisons final answer)
    (typing : (∀ term ∈ terms, LoanTyping.HasType env [] ctx true (expand env term) (expand env (.node operand []))) →
      LoanTyping.HasType env [] ctx true (expand env source) (expand env (.node output resultTerms))) :
    Refines env state.arena ctx source (inferFixed infer normal limit depth state operand args output refs) answer := by
  unfold inferFixed at success ambient ⊢
  obtain ⟨comparisons, checkedOk, checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  obtain ⟨root, resultOk, resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checks := checkFixed infer normal limit depth state operand args
  have resultProgress := append_progress (limit := limit) checks.state output refs
  obtain ⟨checkedKept, checkedBack, typedOperands⟩ := checkFixed_refines normalSound normalProgress childSound
    childProgress onBase room operands operandArity checkedOk
    (resultProgress.kept.trans ambient) retained
  obtain ⟨resultKept, resultBack, outputRep⟩ := append_refines (resultRefs.frame checkedKept) resultArity resultOk
  exact ⟨checkedKept.trans resultKept, resultBack ∘ checkedBack, _, outputRep, typing typedOperands⟩

private theorem finishDecide_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (firstRep : Represents state.arena first a) (secondRep : Represents state.arena second b)
    (firstTyped : LoanTyping.HasType env [] ctx true (expand env a) .u64)
    (secondTyped : LoanTyping.HasType env [] ctx true (expand env b) .u64)
    (success : (finishDecide normal state root first second).result = .ok selected) :
    let after := (finishDecide normal state root first second).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after selected (.lt a b) ∧
      LoanTyping.HasType env [] ctx true (expand env (.decide a b)) (expand env (.lt a b)) := by
  unfold finishDecide at success ⊢
  obtain ⟨left, leftOk, leftNext⟩ := Outcome.next_success success
  rw [leftNext] at success ⊢
  obtain ⟨leftKept, leftBack, leftValue, leftRep, leftChange⟩ := normalSound onBase firstRep leftOk
  obtain ⟨right, rightOk, rightNext⟩ := Outcome.next_success success
  rw [rightNext] at success ⊢
  obtain ⟨rightKept, rightBack, rightValue, rightRep, rightChange⟩ :=
    normalSound (onBase.trans leftKept) (secondRep.frame leftKept) rightOk
  split at success
  · rename_i m n leftRead rightRead
    split at success
    · rename_i ordered
      simp only [ite_eq_left ordered]
      have kept := leftKept.trans rightKept
      have leftShape := (leftRep.frame rightKept).unique (Represents.node leftRead rfl .nil)
      have rightShape := rightRep.unique (Represents.node rightRead rfl .nil)
      have leftConversion : LoanTyping.Conversion.Conv env (expand env a) (.natural m) := by
        simpa only [leftShape, Term.natural, expand, expandArgs] using leftChange.converted
      have rightConversion : LoanTyping.Conversion.Conv env (expand env b) (.natural n) := by
        simpa only [rightShape, Term.natural, expand, expandArgs] using rightChange.converted
      obtain ⟨appended, appendBack, resultRep⟩ := append_refines
        (.cons (firstRep.frame kept) (.cons (secondRep.frame kept) .nil)) rfl success
      refine ⟨kept.trans appended, appendBack ∘ rightBack ∘ leftBack, resultRep, ?_⟩
      simp only [Term.decide, Term.lt, expand, expandArgs]
      exact .decideConverted firstTyped secondTyped leftConversion rightConversion ordered.1 ordered.2.1 ordered.2.2
    · simp [discard] at success
  · simp [discard] at success

private theorem inferDecide_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (firstRep : Represents state.arena first a) (secondRep : Represents state.arena second b)
    (success : (inferDecide infer normal limit depth state root first second).result = .ok answer)
    (ambient : Prefix (inferDecide infer normal limit depth state root first second).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.decide a b) (inferDecide infer normal limit depth state root first second) answer := by
  unfold inferDecide at success ambient ⊢
  obtain ⟨comparisons, checkedOk, checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  obtain ⟨selected, selectedOk, selectedNext⟩ := Outcome.next_success success
  rw [selectedNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checked := checkFixed infer normal limit depth state .u64 [first, second]
  have decision := finishDecide_progress (state := checked.state) (root := root) (first := first) (second := second) normalProgress
  obtain ⟨kept, back, typed⟩ := checkFixed_refines normalSound normalProgress childSound childProgress onBase room
    (.cons firstRep (.cons secondRep .nil)) rfl checkedOk (decision.kept.trans ambient) retained
  simp only [expand, expandArgs] at typed
  obtain ⟨finished, finishBack, resultRep, resultTyped⟩ := finishDecide_refines normalSound (onBase.trans kept)
    (firstRep.frame kept) (secondRep.frame kept) (typed _ List.mem_cons_self)
    (typed _ (List.mem_cons_of_mem _ List.mem_cons_self)) selectedOk
  exact ⟨kept.trans finished, finishBack ∘ back, _, resultRep, resultTyped⟩

private theorem inferStrict_refines
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (effectRep : Represents state.arena effect first) (valueRep : Represents state.arena value second)
    (success : (inferStrict infer state effect value).result = .ok answer)
    (ambient : Prefix (inferStrict infer state effect value).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.strict first second) (inferStrict infer state effect value) answer := by
  unfold inferStrict at success ambient ⊢
  obtain ⟨effectType, effectOk, effectNext⟩ := Outcome.next_success success
  rw [effectNext] at success ambient ⊢
  obtain ⟨valueType, valueOk, valueNext⟩ := Outcome.next_success success
  rw [valueNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  have effectProgress := childProgress state effect room
  have effectRoom := effectProgress.accepted room effectType effectOk
  have valueProgress := childProgress (infer state effect).state value effectRoom
  obtain ⟨_, effectBack, _, _, effectTyped⟩ := childSound onBase room effectRep effectOk
    (valueProgress.kept.trans ambient) (fun pair found => retained pair (List.mem_append_left _ found))
  obtain ⟨kept, valueBack, result, resultRep, valueTyped⟩ := childSound (onBase.trans effectProgress.kept) effectRoom
    (valueRep.frame effectProgress.kept) valueOk ambient (fun pair found => retained pair (List.mem_append_right _ found))
  refine ⟨effectProgress.kept.trans kept, valueBack ∘ effectBack, result, resultRep, ?_⟩
  simp only [Term.strict, expand, expandArgs]
  exact .strict effectTyped valueTyped

private theorem addOne_refines (wordRep : Represents state.arena word a)
    (success : (addOne state word).result = .ok selected) :
    let after := (addOne state word).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (.uadd a (.natural 1)) := by
  unfold addOne at success ⊢
  obtain ⟨one, oneOk, oneNext⟩ := Outcome.next_success success
  rw [oneNext] at success ⊢
  obtain ⟨firstKept, firstBack, oneRep⟩ := append_refines .nil rfl oneOk
  obtain ⟨secondKept, secondBack, sumRep⟩ := append_refines
    (.cons (wordRep.frame firstKept) (.cons oneRep .nil)) rfl success
  exact ⟨firstKept.trans secondKept, secondBack ∘ firstBack, sumRep⟩

private theorem subtractBound_refines
    (numeratorRep : Represents state.arena numerator a) (denominatorRep : Represents state.arena denominator b)
    (success : (subtractBound state numerator denominator).result = .ok selected) :
    let after := (subtractBound state numerator denominator).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (.lt b (.uadd a (.natural 1))) := by
  unfold subtractBound at success ⊢
  obtain ⟨successor, successorOk, successorNext⟩ := Outcome.next_success success
  rw [successorNext] at success ⊢
  obtain ⟨firstKept, firstBack, successorRep⟩ := addOne_refines numeratorRep successorOk
  obtain ⟨secondKept, secondBack, boundRep⟩ := append_refines
    (.cons (denominatorRep.frame firstKept) (.cons successorRep .nil)) rfl success
  exact ⟨firstKept.trans secondKept, secondBack ∘ firstBack, boundRep⟩

private theorem zeroBound_refines (wordRep : Represents state.arena word a)
    (success : (zeroBound state word).result = .ok selected) :
    let after := (zeroBound state word).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (.lt (.natural 0) (.uadd a (.natural 1))) := by
  unfold zeroBound at success ⊢
  obtain ⟨zeroRef, zeroOk, zeroNext⟩ := Outcome.next_success success
  rw [zeroNext] at success ⊢
  obtain ⟨firstKept, firstBack, zeroRep⟩ := append_refines .nil rfl zeroOk
  obtain ⟨secondKept, secondBack, boundRep⟩ := subtractBound_refines (wordRep.frame firstKept) zeroRep success
  exact ⟨firstKept.trans secondKept, secondBack ∘ firstBack, boundRep⟩

private theorem inferZeroLe_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (wordRep : Represents state.arena word a)
    (success : (inferZeroLe infer normal limit depth state word).result = .ok answer)
    (ambient : Prefix (inferZeroLe infer normal limit depth state word).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.zeroLe a) (inferZeroLe infer normal limit depth state word) answer := by
  unfold inferZeroLe at success ambient ⊢
  obtain ⟨comparisons, checkedOk, checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  obtain ⟨selected, boundOk, boundNext⟩ := Outcome.next_success success
  rw [boundNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checked := checkFixed infer normal limit depth state .u64 [word]
  have boundProgress := zeroBound_progress (limit := limit) checked.state word
  obtain ⟨checkedKept, checkedBack, typed⟩ := checkFixed_refines normalSound normalProgress childSound
    childProgress onBase room (.cons wordRep .nil) rfl checkedOk (boundProgress.kept.trans ambient) retained
  obtain ⟨boundKept, boundBack, resultRep⟩ := zeroBound_refines (wordRep.frame checkedKept) boundOk
  refine ⟨checkedKept.trans boundKept, boundBack ∘ checkedBack, _, resultRep, ?_⟩
  simp only [Term.zeroLe, Term.lt, Term.uadd, Term.natural, expand, expandArgs] at typed ⊢
  exact .zeroLe (typed _ List.mem_cons_self)

private theorem checkSubtract_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (numeratorRep : Represents state.arena numerator a) (denominatorRep : Represents state.arena denominator b)
    (proofRep : Represents state.arena proof p)
    (success : (checkSubtract infer normal limit depth state numerator denominator proof).result = .ok comparisons)
    (ambient : Prefix (checkSubtract infer normal limit depth state numerator denominator proof).state.arena final)
    (retained : ∀ pair ∈ comparisons, PairRetained final pair) :
    let after := (checkSubtract infer normal limit depth state numerator denominator proof).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] ctx true (expand env p) (expand env (.lt b (.uadd a (.natural 1)))) := by
  unfold checkSubtract at success ambient ⊢
  obtain ⟨expected, expectedOk, continued⟩ := Outcome.next_success success
  rw [continued] at success ambient ⊢
  obtain ⟨assembledKept, assembledBack, expectedRep⟩ := subtractBound_refines numeratorRep denominatorRep expectedOk
  have assembledRoom := (subtractBound_progress state numerator denominator).accepted room expected expectedOk
  obtain ⟨proofKept, proofBack, typed⟩ := requireOperands_refines normalSound normalProgress childSound childProgress
    (onBase.trans assembledKept) assembledRoom (.cons (proofRep.frame assembledKept) .nil) expectedRep success ambient retained
  exact ⟨assembledKept.trans proofKept, proofBack ∘ assembledBack, typed _ List.mem_cons_self⟩

private theorem inferSubtract_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (numeratorRep : Represents state.arena numerator a) (denominatorRep : Represents state.arena denominator b)
    (proofRep : Represents state.arena proof p)
    (success : (inferSubtract infer normal limit depth state numerator denominator proof).result = .ok answer)
    (ambient : Prefix (inferSubtract infer normal limit depth state numerator denominator proof).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.usub a b p) (inferSubtract infer normal limit depth state numerator denominator proof) answer := by
  unfold inferSubtract at success ambient ⊢
  obtain ⟨comparisons, checkedOk, checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  obtain ⟨proofComparisons, proofOk, proofNext⟩ := Outcome.next_success success
  rw [proofNext] at success ambient ⊢
  obtain ⟨selected, selectedOk, selectedNext⟩ := Outcome.next_success success
  rw [selectedNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checked := checkFixed infer normal limit depth state .u64 [numerator, denominator]
  have checkedProgress := checkFixed_progress (operand := .u64) (args := [numerator, denominator]) (depth := depth)
    childProgress (fun state root _ => normalProgress state root) room
  have checkedRoom := checkedProgress.accepted room comparisons checkedOk
  have proofProgress := checkSubtract_progress (state := checked.state) (depth := depth) (numerator := numerator)
    (denominator := denominator) (proof := proof) childProgress normalProgress checkedRoom
  let proofChecks := checkSubtract infer normal limit depth checked.state numerator denominator proof
  have proofFinal := (append_progress (limit := limit) proofChecks.state .u64 []).kept.trans ambient
  obtain ⟨checkedKept, checkedBack, typedOperands⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    onBase room (.cons numeratorRep (.cons denominatorRep .nil)) rfl checkedOk
    (proofProgress.kept.trans proofFinal) (fun pair found => retained pair (List.mem_append_left _ found))
  obtain ⟨proofKept, proofBack, typedProof⟩ := checkSubtract_refines normalSound normalProgress childSound childProgress
    (onBase.trans checkedKept) checkedRoom (numeratorRep.frame checkedKept) (denominatorRep.frame checkedKept)
    (proofRep.frame checkedKept) proofOk proofFinal (fun pair found => retained pair (List.mem_append_right _ found))
  obtain ⟨resultKept, resultBack, resultRep⟩ := append_refines .nil rfl selectedOk
  refine ⟨checkedKept.trans (proofKept.trans resultKept), resultBack ∘ proofBack ∘ checkedBack, _, resultRep, ?_⟩
  simp only [Term.lt, Term.uadd, Term.natural, expand, expandArgs] at typedProof
  simp only [expand, expandArgs] at typedOperands
  simp only [Term.usub, expand, expandArgs]
  exact .usub (typedOperands _ List.mem_cons_self)
    (typedOperands _ (List.mem_cons_of_mem _ List.mem_cons_self)) typedProof


private theorem offsetBounds_refines
    (leftRep : Represents state.arena left a) (rightRep : Represents state.arena right b)
    (deltaRep : Represents state.arena delta d)
    (success : (offsetBounds state left right delta).result = .ok bounds) :
    let after := (offsetBounds state left right delta).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after bounds.1 (.lt a b) ∧ Represents after bounds.2 (.lt (.uadd a d) (.uadd b d)) := by
  unfold offsetBounds at success ⊢
  obtain ⟨shiftedLeft, leftOk, leftNext⟩ := Outcome.next_success success
  rw [leftNext] at success ⊢
  obtain ⟨shiftedRight, rightOk, rightNext⟩ := Outcome.next_success success
  rw [rightNext] at success ⊢
  obtain ⟨plain, plainOk, plainNext⟩ := Outcome.next_success success
  rw [plainNext] at success ⊢
  obtain ⟨shifted, shiftedOk, shiftedNext⟩ := Outcome.next_success success
  rw [shiftedNext] at success ⊢
  simp only [Except.ok.injEq] at success
  subst bounds
  obtain ⟨leftKept, leftBack, firstSum⟩ := append_refines (.cons leftRep (.cons deltaRep .nil)) rfl leftOk
  obtain ⟨rightKept, rightBack, secondSum⟩ := append_refines
    (.cons (rightRep.frame leftKept) (.cons (deltaRep.frame leftKept) .nil)) rfl rightOk
  have added := leftKept.trans rightKept
  obtain ⟨plainKept, plainBack, plainRep⟩ := append_refines
    (.cons (leftRep.frame added) (.cons (rightRep.frame added) .nil)) rfl plainOk
  obtain ⟨shiftedKept, shiftedBack, shiftedRep⟩ := append_refines
    (.cons (firstSum.frame (rightKept.trans plainKept)) (.cons (secondSum.frame plainKept) .nil)) rfl shiftedOk
  exact ⟨added.trans (plainKept.trans shiftedKept), shiftedBack ∘ plainBack ∘ rightBack ∘ leftBack,
    plainRep.frame shiftedKept, shiftedRep⟩

private theorem inferOffsetProof_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (leftRep : Represents state.arena left a) (rightRep : Represents state.arena right b)
    (deltaRep : Represents state.arena delta d) (proofRep : Represents state.arena proof p)
    (success : (inferOffsetProof infer normal limit depth state forward left right delta proof).result = .ok answer)
    (ambient : Prefix (inferOffsetProof infer normal limit depth state forward left right delta proof).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (if forward then .ltAdd a b d p else .ltCancel a b d p)
      (inferOffsetProof infer normal limit depth state forward left right delta proof) answer := by
  unfold inferOffsetProof at success ambient ⊢
  obtain ⟨operands, operandsOk, operandsNext⟩ := Outcome.next_success success
  rw [operandsNext] at success ambient ⊢
  obtain ⟨bounds, boundsOk, boundsNext⟩ := Outcome.next_success success
  rw [boundsNext] at success ambient ⊢
  obtain ⟨proofPairs, proofOk, proofNext⟩ := Outcome.next_success success
  rw [proofNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checked := checkFixed infer normal limit depth state .u64 [left, right, delta]
  let assembled := offsetBounds checked.state left right delta
  have checkedProgress := checkFixed_progress (operand := .u64) (args := [left, right, delta]) (depth := depth)
    childProgress (fun state root _ => normalProgress state root) room
  have checkedRoom := checkedProgress.accepted room operands operandsOk
  have boundsProgress := offsetBounds_progress (limit := limit) checked.state left right delta
  have boundsRoom := boundsProgress.accepted checkedRoom bounds boundsOk
  have proofProgress := requireOperands_progress (state := assembled.state)
    (expected := if forward then bounds.1 else bounds.2) (args := [proof]) (depth := depth)
    childProgress (fun state ref _ => normalProgress state ref) boundsRoom
  obtain ⟨checkedKept, checkedBack, typed⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    onBase room (.cons leftRep (.cons rightRep (.cons deltaRep .nil))) rfl operandsOk
    (boundsProgress.kept.trans (proofProgress.kept.trans ambient))
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨boundsKept, boundsBack, plainRep, shiftedRep⟩ := offsetBounds_refines
    (leftRep.frame checkedKept) (rightRep.frame checkedKept) (deltaRep.frame checkedKept) boundsOk
  have given : Represents assembled.state.arena (if forward then bounds.1 else bounds.2)
      (if forward then .lt a b else .lt (.uadd a d) (.uadd b d)) := by
    cases forward
    · exact shiftedRep
    · exact plainRep
  have throughBounds := checkedKept.trans boundsKept
  obtain ⟨proofKept, proofBack, typedProof⟩ := requireOperands_refines normalSound normalProgress childSound
    childProgress (onBase.trans throughBounds) boundsRoom (.cons (proofRep.frame throughBounds) .nil) given
    proofOk ambient (fun pair member => retained pair (List.mem_append_right _ member))
  have evidence := typedProof p List.mem_cons_self
  simp only [expand, expandArgs] at typed
  have first := typed a List.mem_cons_self
  have second := typed b (List.mem_cons_of_mem _ List.mem_cons_self)
  have offset := typed d (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  cases forward
  · refine ⟨throughBounds.trans proofKept, proofBack ∘ boundsBack ∘ checkedBack, _, plainRep.frame proofKept, ?_⟩
    simp only [Bool.false_eq_true, ite_false, Term.lt, Term.uadd, expand, expandArgs] at evidence
    simp only [Bool.false_eq_true, ite_false, Term.ltCancel, Term.lt, expand, expandArgs]
    exact .ltCancel first second offset evidence
  · refine ⟨throughBounds.trans proofKept, proofBack ∘ boundsBack ∘ checkedBack, _, shiftedRep.frame proofKept, ?_⟩
    simp only [ite_true, Term.lt, expand, expandArgs] at evidence
    simp only [ite_true, Term.ltAdd, Term.lt, Term.uadd, expand, expandArgs]
    exact .ltAdd first second offset evidence

private theorem transitiveBounds_refines
    (leftRep : Represents state.arena left a) (middleRep : Represents state.arena middle b)
    (rightRep : Represents state.arena right c)
    (success : (transitiveBounds state left middle right).result = .ok bounds) :
    let after := (transitiveBounds state left middle right).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after bounds.1 (.lt a b) ∧ Represents after bounds.2 (.lt b (.uadd c (.natural 1))) := by
  unfold transitiveBounds at success ⊢
  obtain ⟨successor, successorOk, successorNext⟩ := Outcome.next_success success
  rw [successorNext] at success ⊢
  obtain ⟨lower, lowerOk, lowerNext⟩ := Outcome.next_success success
  rw [lowerNext] at success ⊢
  obtain ⟨upper, upperOk, upperNext⟩ := Outcome.next_success success
  rw [upperNext] at success ⊢
  simp only [Except.ok.injEq] at success
  subst bounds
  obtain ⟨successorKept, successorBack, successorRep⟩ := addOne_refines rightRep successorOk
  obtain ⟨lowerKept, lowerBack, lowerRep⟩ := append_refines
    (.cons (leftRep.frame successorKept) (.cons (middleRep.frame successorKept) .nil)) rfl lowerOk
  have throughLower := successorKept.trans lowerKept
  obtain ⟨upperKept, upperBack, upperRep⟩ := append_refines
    (.cons (middleRep.frame throughLower) (.cons (successorRep.frame lowerKept) .nil)) rfl upperOk
  exact ⟨throughLower.trans upperKept, upperBack ∘ lowerBack ∘ successorBack, lowerRep.frame upperKept, upperRep⟩

private theorem inferTransitiveProof_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (leftRep : Represents state.arena left a) (middleRep : Represents state.arena middle b)
    (rightRep : Represents state.arena right c) (lowerRep : Represents state.arena lower p)
    (upperRep : Represents state.arena upper q)
    (success : (inferTransitiveProof infer normal limit depth state left middle right lower upper).result = .ok answer)
    (ambient : Prefix (inferTransitiveProof infer normal limit depth state left middle right lower upper).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.ltLe a b c p q)
      (inferTransitiveProof infer normal limit depth state left middle right lower upper) answer := by
  unfold inferTransitiveProof at success ambient ⊢
  obtain ⟨operands, operandsOk, operandsNext⟩ := Outcome.next_success success
  rw [operandsNext] at success ambient ⊢
  obtain ⟨bounds, boundsOk, boundsNext⟩ := Outcome.next_success success
  rw [boundsNext] at success ambient ⊢
  obtain ⟨lowerPairs, lowerOk, lowerNext⟩ := Outcome.next_success success
  rw [lowerNext] at success ambient ⊢
  obtain ⟨upperPairs, upperOk, upperNext⟩ := Outcome.next_success success
  rw [upperNext] at success ambient ⊢
  obtain ⟨selected, selectedOk, selectedNext⟩ := Outcome.next_success success
  rw [selectedNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let operandsCheck := checkFixed infer normal limit depth state .u64 [left, middle, right]
  let assembled := transitiveBounds operandsCheck.state left middle right
  let lowerCheck := requireOperands infer normal limit depth bounds.1 assembled.state [lower]
  let upperCheck := requireOperands infer normal limit depth bounds.2 lowerCheck.state [upper]
  have operandsProgress := checkFixed_progress (operand := .u64) (args := [left, middle, right]) (depth := depth)
    childProgress (fun state root _ => normalProgress state root) room
  have operandsRoom := operandsProgress.accepted room operands operandsOk
  have boundsProgress := transitiveBounds_progress (limit := limit) operandsCheck.state left middle right
  have boundsRoom := boundsProgress.accepted operandsRoom bounds boundsOk
  have lowerProgress := requireOperands_progress (state := assembled.state)
    (expected := bounds.1) (args := [lower]) (depth := depth)
    childProgress (fun state ref _ => normalProgress state ref) boundsRoom
  have lowerRoom := lowerProgress.accepted boundsRoom lowerPairs lowerOk
  have upperProgress := requireOperands_progress (state := lowerCheck.state)
    (expected := bounds.2) (args := [upper]) (depth := depth)
    childProgress (fun state ref _ => normalProgress state ref) lowerRoom
  have resultFinal := (append_progress (limit := limit) upperCheck.state .lt [left,right]).kept.trans ambient
  have upperFinal := upperProgress.kept.trans resultFinal
  obtain ⟨operandsKept, operandsBack, typed⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    onBase room (.cons leftRep (.cons middleRep (.cons rightRep .nil))) rfl operandsOk
    (boundsProgress.kept.trans (lowerProgress.kept.trans upperFinal))
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨boundsKept, boundsBack, needLower, needUpper⟩ := transitiveBounds_refines
    (leftRep.frame operandsKept) (middleRep.frame operandsKept) (rightRep.frame operandsKept) boundsOk
  have throughBounds := operandsKept.trans boundsKept
  obtain ⟨lowerKept, lowerBack, lowerTyped⟩ := requireOperands_refines normalSound normalProgress childSound childProgress
    (onBase.trans throughBounds) boundsRoom (.cons (lowerRep.frame throughBounds) .nil) needLower lowerOk upperFinal
    (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
  have throughLower := throughBounds.trans lowerKept
  obtain ⟨upperKept, upperBack, upperTyped⟩ := requireOperands_refines normalSound normalProgress childSound childProgress
    (onBase.trans throughLower) lowerRoom (.cons (upperRep.frame throughLower) .nil) (needUpper.frame lowerKept) upperOk
    resultFinal (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _ member)))
  have throughUpper := throughLower.trans upperKept
  obtain ⟨resultKept, resultBack, resultRep⟩ := append_refines
    (.cons (leftRep.frame throughUpper) (.cons (rightRep.frame throughUpper) .nil)) rfl selectedOk
  refine ⟨throughUpper.trans resultKept, resultBack ∘ upperBack ∘ lowerBack ∘ boundsBack ∘ operandsBack, _, resultRep, ?_⟩
  simp only [Term.ltLe, expand, expandArgs]
  simp only [Term.lt, Term.uadd, Term.natural, expand, expandArgs] at typed lowerTyped upperTyped
  exact .ltLe (typed a List.mem_cons_self) (typed b (List.mem_cons_of_mem _ List.mem_cons_self))
    (typed c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (lowerTyped p List.mem_cons_self) (upperTyped q List.mem_cons_self)

private theorem finishConditional_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (thenTypeRep : Represents state.arena thenType written)
    (thenTyped : LoanTyping.HasType env [] thenContext true (expand env consequent) (expand env written))
    (alternativeRep : Represents state.arena alternative other)
    (success : (finishConditional infer normal limit depth state thenType alternative).result = .ok answer)
    (ambient : Prefix (finishConditional infer normal limit depth state thenType alternative).state.arena final)
    (retained : RetainedComparisons final answer) :
    let output := finishConditional infer normal limit depth state thenType alternative
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ result, Represents output.state.arena answer.typeRoot result ∧
        LoanTyping.HasType env [] thenContext true (expand env consequent) ((expand env result).rename Nat.succ) ∧
        LoanTyping.HasType env [] ctx true (expand env other) (expand env result) := by
  unfold finishConditional at success ambient ⊢
  obtain ⟨normalRoot, normalOk, normalNext⟩ := Outcome.next_success success
  rw [normalNext] at success ambient ⊢
  obtain ⟨selected, loweredOk, loweredNext⟩ := Outcome.next_success success
  rw [loweredNext] at success ambient ⊢
  obtain ⟨compared, comparedOk, comparedNext⟩ := Outcome.next_success success
  rw [comparedNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let normalized := normal state thenType
  have normalRoom := (normalProgress state thenType).accepted room normalRoot normalOk
  have loweringRoom := (lowerType_progress limit depth normalized.state normalRoot).accepted normalRoom selected loweredOk
  obtain ⟨normalKept, normalBack, exposed, exposedRep, change⟩ := normalSound onBase thenTypeRep normalOk
  obtain ⟨loweredKept, loweredBack, residual, lowerRep, weakened⟩ := lowerType_refines exposedRep loweredOk
  have throughLowering := normalKept.trans loweredKept
  obtain ⟨checkedKept, checkedBack, checked⟩ := requireOperands_refines normalSound normalProgress childSound
    childProgress (onBase.trans throughLowering) loweringRoom (.cons (alternativeRep.frame throughLowering) .nil)
    lowerRep comparedOk ambient retained
  refine ⟨throughLowering.trans checkedKept, checkedBack ∘ loweredBack ∘ normalBack,
    residual, lowerRep.frame checkedKept, ?_, checked _ List.mem_cons_self⟩
  rw [← EnvironmentDelta.expand_renaming wf.admissible, weakened]
  exact thenTyped.convert change.converted

private theorem inferConditional_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (thenSound : ∀ {entered assumption}, Prefix state.arena entered →
      Represents entered assumption (.node (conditionOp equality) [a, b]) →
      InferSound env entered (⟨expand env (.node (conditionOp equality) [a, b]), true⟩ :: ctx)
        limit (inferThen assumption))
    (thenProgress : ∀ assumption state root, state.steps ≤ limit → Progress limit state (inferThen assumption state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (firstRep : Represents state.arena left a) (secondRep : Represents state.arena right b)
    (thenRep : Represents state.arena yes consequent) (alternativeRep : Represents state.arena no alternative)
    (success : (inferConditional infer inferThen normal limit depth state equality left right yes no).result = .ok answer)
    (ambient : Prefix (inferConditional infer inferThen normal limit depth state equality left right yes no).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.node (conditionalOp equality) [a, b, consequent, alternative])
      (inferConditional infer inferThen normal limit depth state equality left right yes no) answer := by
  unfold inferConditional at success ambient ⊢
  obtain ⟨conditionPairs, checkedOk, checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  obtain ⟨assumption, assumedOk, assumedNext⟩ := Outcome.next_success success
  rw [assumedNext] at success ambient ⊢
  obtain ⟨consequentType, thenOk, thenNext⟩ := Outcome.next_success success
  rw [thenNext] at success ambient ⊢
  obtain ⟨finished, finishOk, finishNext⟩ := Outcome.next_success success
  rw [finishNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checked := checkFixed infer normal limit depth state .u64 [left, right]
  have conditionProgress := checkFixed_progress (operand := .u64) (args := [left, right]) (depth := depth)
    childProgress (fun state root _ => normalProgress state root) room
  have checkedRoom := conditionProgress.accepted room conditionPairs checkedOk
  let opened := append checked.state (conditionOp equality) [left, right]
  have openProgress := append_progress (limit := limit) checked.state (conditionOp equality) [left, right]
  have openedRoom := openProgress.accepted checkedRoom assumption assumedOk
  have bodyProgress := thenProgress assumption opened.state yes openedRoom
  have consequentRoom := bodyProgress.accepted openedRoom consequentType thenOk
  have finishedProgress := finishConditional_progress (state := (inferThen assumption opened.state yes).state)
    (depth := depth) (thenType := consequentType.typeRoot) (alternative := no) childProgress normalProgress consequentRoom
  have thenFinal := finishedProgress.kept.trans ambient
  have openedFinal := bodyProgress.kept.trans thenFinal
  have checkedFinal := openProgress.kept.trans openedFinal
  obtain ⟨checkedKept, checkedBack, operands⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    onBase room (.cons firstRep (.cons secondRep .nil)) rfl checkedOk checkedFinal
    (fun pair found => retained pair (List.mem_append_left _ (List.mem_append_left _ found)))
  obtain ⟨assumedKept, assumedBack, assumptionRep⟩ := append_refines
    (.cons (firstRep.frame checkedKept) (.cons (secondRep.frame checkedKept) .nil))
    (by cases equality <;> rfl) assumedOk
  have throughAssumption := checkedKept.trans assumedKept
  obtain ⟨thenKept, thenBack, _, inferredRep, inferredTyped⟩ := thenSound throughAssumption assumptionRep
    (.refl _) openedRoom (thenRep.frame throughAssumption) thenOk thenFinal
    (fun pair found => retained pair (List.mem_append_left _ (List.mem_append_right _ found)))
  have throughThen := throughAssumption.trans thenKept
  obtain ⟨finishedKept, finishedBack, result, resultRep, yesTyped, noTyped⟩ := finishConditional_refines
    wf normalSound normalProgress childSound childProgress (onBase.trans throughThen) consequentRoom
    inferredRep inferredTyped (alternativeRep.frame throughThen) finishOk ambient
    (fun pair found => retained pair (List.mem_append_right _ found))
  refine ⟨throughThen.trans finishedKept, finishedBack ∘ thenBack ∘ assumedBack ∘ checkedBack, result, resultRep, ?_⟩
  simp only [expand, expandArgs] at operands
  have left := operands _ List.mem_cons_self
  have right := operands _ (List.mem_cons_of_mem _ List.mem_cons_self)
  cases equality
  · simp only [conditionOp, conditionalOp, Bool.false_eq_true, ite_false, expand, expandArgs] at yesTyped ⊢
    exact .ifLt left right yesTyped noTyped
  · simp only [conditionOp, conditionalOp, ite_true, expand, expandArgs] at yesTyped ⊢
    exact .ifEq left right yesTyped noTyped

private theorem predicateType_refines (success : (predicateType state).result = .ok selected) :
    let after := (predicateType state).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (.pi false .u64 .prop) := by
  unfold predicateType at success ⊢
  obtain ⟨word, wordOk, wordNext⟩ := Outcome.next_success success
  rw [wordNext] at success ⊢
  obtain ⟨proposition, propOk, propNext⟩ := Outcome.next_success success
  rw [propNext] at success ⊢
  obtain ⟨wordKept, wordBack, wordRep⟩ := append_refines .nil rfl wordOk
  obtain ⟨propKept, propBack, propRep⟩ := append_refines .nil rfl propOk
  obtain ⟨piKept, piBack, resultRep⟩ := append_refines (.cons (wordRep.frame propKept) (.cons propRep .nil)) rfl success
  exact ⟨wordKept.trans (propKept.trans piKept), piBack ∘ propBack ∘ wordBack, resultRep⟩

private theorem checkPredicate_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (predicateRep : Represents state.arena predicate p)
    (success : (checkPredicate infer normal limit depth state predicate).result = .ok comparisons)
    (ambient : Prefix (checkPredicate infer normal limit depth state predicate).state.arena final)
    (retained : ∀ pair ∈ comparisons, PairRetained final pair) :
    let after := (checkPredicate infer normal limit depth state predicate).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] ctx true (expand env p) (.pi false .u64 .prop) := by
  unfold checkPredicate at success ambient ⊢
  obtain ⟨expected, expectedOk, expectedNext⟩ := Outcome.next_success success
  rw [expectedNext] at success ambient ⊢
  obtain ⟨expectedKept, expectedBack, expectedRep⟩ := predicateType_refines expectedOk
  have within := (predicateType_progress state).accepted room expected expectedOk
  obtain ⟨checkedKept, checkedBack, typed⟩ := requireOperands_refines normalSound normalProgress childSound childProgress
    (onBase.trans expectedKept) within (.cons (predicateRep.frame expectedKept) .nil) expectedRep success ambient retained
  refine ⟨expectedKept.trans checkedKept, checkedBack ∘ expectedBack, ?_⟩
  simpa only [Term.pi, Term.u64, Term.prop, expand, expandArgs] using typed p List.mem_cons_self

private theorem inferRefine_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (predicateRep : Represents state.arena predicate p)
    (success : (inferRefine infer normal limit depth state predicate).result = .ok answer)
    (ambient : Prefix (inferRefine infer normal limit depth state predicate).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.refine p) (inferRefine infer normal limit depth state predicate) answer := by
  unfold inferRefine at success ambient ⊢
  obtain ⟨comparisons, checkedOk, checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  obtain ⟨root, outputOk, outputNext⟩ := Outcome.next_success success
  rw [outputNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checked := checkPredicate infer normal limit depth state predicate
  have outputKept := (append_progress (limit := limit) checked.state (.universe 0) []).kept
  obtain ⟨kept, backward, typed⟩ := checkPredicate_refines normalSound normalProgress childSound childProgress
    onBase room predicateRep checkedOk (outputKept.trans ambient) retained
  obtain ⟨outputKept, outputBack, represented⟩ := append_refines .nil rfl outputOk
  refine ⟨kept.trans outputKept, outputBack ∘ backward, _, represented, ?_⟩
  simp only [Term.refine, expand, expandArgs]
  exact .refine typed

private theorem checkPredicateEvidence_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (predicateRep : Represents state.arena predicate p) (wordRep : Represents state.arena word a)
    (evidenceRep : Represents state.arena evidence q)
    (success : (checkPredicateEvidence infer normal limit depth state predicate word evidence).result = .ok comparisons)
    (ambient : Prefix (checkPredicateEvidence infer normal limit depth state predicate word evidence).state.arena final)
    (retained : ∀ pair ∈ comparisons, PairRetained final pair) :
    let after := (checkPredicateEvidence infer normal limit depth state predicate word evidence).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] ctx true (expand env q) (.app (expand env p) (expand env a)) := by
  unfold checkPredicateEvidence at success ambient ⊢
  obtain ⟨expected, expectedOk, expectedNext⟩ := Outcome.next_success success
  rw [expectedNext] at success ambient ⊢
  obtain ⟨expectedKept, expectedBack, expectedRep⟩ := append_refines (.cons predicateRep (.cons wordRep .nil)) rfl expectedOk
  have within := (append_progress state .app [predicate, word]).accepted room expected expectedOk
  obtain ⟨checkedKept, checkedBack, typed⟩ := requireOperands_refines normalSound normalProgress childSound childProgress
    (onBase.trans expectedKept) within (.cons (evidenceRep.frame expectedKept) .nil) expectedRep success ambient retained
  refine ⟨expectedKept.trans checkedKept, checkedBack ∘ expectedBack, ?_⟩
  simpa only [Term.app, expand, expandArgs] using typed q List.mem_cons_self

private theorem inferPack_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (predicateRep : Represents state.arena predicate p) (wordRep : Represents state.arena word a)
    (evidenceRep : Represents state.arena evidence q)
    (success : (inferPack infer normal limit depth state predicate word evidence).result = .ok answer)
    (ambient : Prefix (inferPack infer normal limit depth state predicate word evidence).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.pack p a q) (inferPack infer normal limit depth state predicate word evidence) answer := by
  unfold inferPack at success ambient ⊢
  obtain ⟨predicatePairs, predicateOk, predicateNext⟩ := Outcome.next_success success
  rw [predicateNext] at success ambient ⊢
  obtain ⟨wordPairs, wordOk, wordNext⟩ := Outcome.next_success success
  rw [wordNext] at success ambient ⊢
  obtain ⟨proofPairs, proofOk, proofNext⟩ := Outcome.next_success success
  rw [proofNext] at success ambient ⊢
  obtain ⟨selected, outputOk, outputNext⟩ := Outcome.next_success success
  rw [outputNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let predicateCheck := checkPredicate infer normal limit depth state predicate
  have predicateProgress := checkPredicate_progress (depth := depth) (predicate := predicate) childProgress normalProgress room
  have predicateRoom := predicateProgress.accepted room predicatePairs predicateOk
  let wordCheck := checkFixed infer normal limit depth predicateCheck.state .u64 [word]
  have wordProgress := checkFixed_progress (operand := .u64) (args := [word]) (depth := depth)
    childProgress (fun state root _ => normalProgress state root) predicateRoom
  have wordRoom := wordProgress.accepted predicateRoom wordPairs wordOk
  let proofCheck := checkPredicateEvidence infer normal limit depth wordCheck.state predicate word evidence
  have proofProgress := checkPredicateEvidence_progress (depth := depth) (predicate := predicate) (word := word)
    (evidence := evidence) childProgress normalProgress wordRoom
  have proofFinal := (append_progress (limit := limit) proofCheck.state .refine [predicate]).kept.trans ambient
  have wordFinal := proofProgress.kept.trans proofFinal
  have predicateFinal := wordProgress.kept.trans wordFinal
  obtain ⟨predicateKept, predicateBack, predicateTyped⟩ := checkPredicate_refines normalSound normalProgress childSound
    childProgress onBase room predicateRep predicateOk predicateFinal
    (fun pair found => retained pair (List.mem_append_left _ (List.mem_append_left _ found)))
  obtain ⟨wordKept, wordBack, wordTyped⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    (onBase.trans predicateKept) predicateRoom (.cons (wordRep.frame predicateKept) .nil) rfl wordOk wordFinal
    (fun pair found => retained pair (List.mem_append_left _ (List.mem_append_right _ found)))
  have throughWord := predicateKept.trans wordKept
  obtain ⟨proofKept, proofBack, proofTyped⟩ := checkPredicateEvidence_refines normalSound normalProgress childSound childProgress
    (onBase.trans throughWord) wordRoom (predicateRep.frame throughWord) (wordRep.frame throughWord)
    (evidenceRep.frame throughWord) proofOk proofFinal (fun pair found => retained pair (List.mem_append_right _ found))
  have throughProof := throughWord.trans proofKept
  obtain ⟨outputKept, outputBack, outputRep⟩ := append_refines (.cons (predicateRep.frame throughProof) .nil) rfl outputOk
  refine ⟨throughProof.trans outputKept, outputBack ∘ proofBack ∘ wordBack ∘ predicateBack, _, outputRep, ?_⟩
  simp only [expand, expandArgs] at wordTyped
  simp only [Term.pack, expand, expandArgs]
  exact .pack predicateTyped (wordTyped a List.mem_cons_self) proofTyped

private theorem refinement_type_read (represented : Represents arena root type)
    (read : arena[root]? = some (.node .refine [predicate])) :
    ∃ p, type = .refine p ∧ Represents arena predicate p := by
  cases represented with
  | var found => rw [read] at found; cases found
  | node found _ children =>
    rw [read] at found
    cases found
    cases children with
    | cons represented tail =>
      cases tail
      exact ⟨_, rfl, represented⟩

private theorem refinementProjectionType_refines (predicateRep : Represents state.arena predicate p)
    (subjectRep : Represents state.arena subject s)
    (success : (refinementProjectionType state evidence predicate subject).result = .ok selected) :
    let after := (refinementProjectionType state evidence predicate subject).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (if evidence then .app p (.witness s) else .u64) := by
  cases evidence
  · exact append_refines .nil rfl success
  · simp only [refinementProjectionType, ite_true] at success ⊢
    obtain ⟨witness, witnessOk, witnessNext⟩ := Outcome.next_success success
    rw [witnessNext] at success ⊢
    obtain ⟨witnessKept, witnessBack, witnessRep⟩ := append_refines (.cons subjectRep .nil) rfl witnessOk
    obtain ⟨resultKept, resultBack, resultRep⟩ := append_refines
      (.cons (predicateRep.frame witnessKept) (.cons witnessRep .nil)) rfl success
    exact ⟨witnessKept.trans resultKept, resultBack ∘ witnessBack, resultRep⟩

private theorem inferRefinementProjection_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (subjectRep : Represents state.arena subject s)
    (success : (inferRefinementProjection infer normal state evidence subject).result = .ok answer)
    (ambient : Prefix (inferRefinementProjection infer normal state evidence subject).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (if evidence then .proof s else .witness s)
      (inferRefinementProjection infer normal state evidence subject) answer := by
  unfold inferRefinementProjection at success ambient ⊢
  obtain ⟨sourceType, inferredOk, inferredNext⟩ := Outcome.next_success success
  rw [inferredNext] at success ambient ⊢
  obtain ⟨typeRoot, normalOk, normalNext⟩ := Outcome.next_success success
  rw [normalNext] at success ambient ⊢
  split at success
  case h_2 => simp [discard] at success
  case h_1 predicate read =>
    simp only [read] at ambient
    obtain ⟨selected, outputOk, outputNext⟩ := Outcome.next_success success
    rw [outputNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    have subjectProgress := childProgress state subject room
    let normalized := normal (infer state subject).state sourceType.typeRoot
    have typeProgress := normalProgress (infer state subject).state sourceType.typeRoot
    have outputProgress := refinementProjectionType_progress (limit := limit) normalized.state evidence predicate subject
    have subjectFinal := typeProgress.kept.trans (outputProgress.kept.trans ambient)
    obtain ⟨_, sourceBack, _, sourceRep, typed⟩ := childSound onBase room subjectRep inferredOk subjectFinal retained
    obtain ⟨typeKept, typeBack, refinement, refinementRep, converted⟩ :=
      normalSound (onBase.trans subjectProgress.kept) sourceRep normalOk
    obtain ⟨p, shape, predicateRep⟩ := refinement_type_read refinementRep read
    have throughType := subjectProgress.kept.trans typeKept
    obtain ⟨resultKept, resultBack, resultRep⟩ := refinementProjectionType_refines predicateRep
      (subjectRep.frame throughType) outputOk
    have refinementTyped : LoanTyping.HasType env [] ctx true (expand env s) (.refine (expand env p)) := by
      simpa only [shape, Term.refine, expand, expandArgs] using typed.convert converted.converted
    refine ⟨throughType.trans resultKept, resultBack ∘ typeBack ∘ sourceBack, _, resultRep, ?_⟩
    cases evidence
    · simp only [Bool.false_eq_true, ite_false, Term.witness, Term.u64, expand, expandArgs]
      exact .witness refinementTyped
    · simp only [ite_true, Term.proof, Term.app, Term.witness, expand, expandArgs]
      exact .proof refinementTyped

private theorem inferTransport_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (predicateRep : Represents state.arena predicate p) (equalityRep : Represents state.arena equality e)
    (payloadRep : Represents state.arena payload q)
    (success : (inferTransport infer normal limit depth state predicate equality payload).result = .ok answer)
    (ambient : Prefix (inferTransport infer normal limit depth state predicate equality payload).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.transport p e q)
      (inferTransport infer normal limit depth state predicate equality payload) answer := by
  unfold inferTransport at success ambient ⊢
  obtain ⟨predicatePairs, predicateOk, predicateNext⟩ := Outcome.next_success success
  rw [predicateNext] at success ambient ⊢
  obtain ⟨inferred, equalityOk, equalityNext⟩ := Outcome.next_success success
  rw [equalityNext] at success ambient ⊢
  obtain ⟨typeRoot, exposedOk, exposedNext⟩ := Outcome.next_success success
  rw [exposedNext] at success ambient ⊢
  split at success
  case h_2 => simp [discard] at success
  case h_1 left right read =>
    simp only [read] at ambient
    obtain ⟨proofPairs, proofOk, proofNext⟩ := Outcome.next_success success
    rw [proofNext] at success ambient ⊢
    obtain ⟨selected, outputOk, outputNext⟩ := Outcome.next_success success
    rw [outputNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    let checked := checkPredicate infer normal limit depth state predicate
    have predicateRoom := (checkPredicate_progress (depth := depth) (predicate := predicate)
      childProgress normalProgress room).accepted room predicatePairs predicateOk
    let evidence := infer checked.state equality
    have evidenceProgress := childProgress checked.state equality predicateRoom
    have evidenceRoom := evidenceProgress.accepted predicateRoom inferred equalityOk
    let exposed := normal evidence.state inferred.typeRoot
    have exposure := normalProgress evidence.state inferred.typeRoot
    have exposedRoom := exposure.accepted evidenceRoom typeRoot exposedOk
    let checkProof := checkPredicateEvidence infer normal limit depth exposed.state predicate left payload
    have proofProgress := checkPredicateEvidence_progress (depth := depth) (state := exposed.state)
      (predicate := predicate) (word := left) (evidence := payload) childProgress normalProgress exposedRoom
    have proofFinal := (append_progress (limit := limit) checkProof.state .app [predicate, right]).kept.trans ambient
    have evidenceFinal := exposure.kept.trans (proofProgress.kept.trans proofFinal)
    obtain ⟨predicateKept, predicateBack, typedPredicate⟩ := checkPredicate_refines normalSound normalProgress
      childSound childProgress onBase room predicateRep predicateOk (evidenceProgress.kept.trans evidenceFinal)
      (fun pair member => retained pair (List.mem_append_left _ (List.mem_append_left _ member)))
    obtain ⟨evidenceKept, evidenceBack, _, evidenceRep, typedEvidence⟩ := childSound
      (onBase.trans predicateKept) predicateRoom (equalityRep.frame predicateKept) equalityOk evidenceFinal
      (fun pair member => retained pair (List.mem_append_left _ (List.mem_append_right _ member)))
    have throughEvidence := predicateKept.trans evidenceKept
    obtain ⟨exposedKept, exposedBack, _, exposedRep, changed⟩ := normalSound
      (onBase.trans throughEvidence) evidenceRep exposedOk
    obtain ⟨a, b, shape, leftRep, rightRep⟩ := binary_read exposedRep read
    have typedEq : LoanTyping.HasType env [] ctx true (expand env e) (.eq (expand env a) (expand env b)) := by
      simpa only [shape, Term.eq, expand, expandArgs] using typedEvidence.convert changed.converted
    have throughType := throughEvidence.trans exposedKept
    obtain ⟨proofKept, proofBack, typedProof⟩ := checkPredicateEvidence_refines normalSound normalProgress
      childSound childProgress (onBase.trans throughType) exposedRoom (predicateRep.frame throughType) leftRep
      (payloadRep.frame throughType) proofOk proofFinal (fun pair member => retained pair (List.mem_append_right _ member))
    have throughProof := throughType.trans proofKept
    obtain ⟨outputKept, outputBack, resultRep⟩ := append_refines
      (.cons (predicateRep.frame throughProof) (.cons (rightRep.frame proofKept) .nil)) rfl outputOk
    refine ⟨throughProof.trans outputKept, outputBack ∘ proofBack ∘ exposedBack ∘ evidenceBack ∘ predicateBack,
      _, resultRep, ?_⟩
    simp only [Term.transport, expand, expandArgs]
    exact .transport typedPredicate typedEq typedProof

/-- A successful application returns the captured Pi body instantiated with
the original graph operand. The proof exposes a real function type and
reflects the accepted argument comparison under its retention evidence. -/
theorem inferApp_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (fn : Represents state.arena function f) (arg : Represents state.arena argument a)
    (success : (inferApp infer normal limit depth state function argument).result = .ok answer)
    (ambient : Prefix (inferApp infer normal limit depth state function argument).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.app f a) (inferApp infer normal limit depth state function argument) answer := by
  unfold inferApp at success ambient ⊢
  obtain ⟨fType, fOk, fNext⟩ := Outcome.next_success success
  rw [fNext] at success ambient ⊢
  obtain ⟨exposed, exposedOk, exposedNext⟩ := Outcome.next_success success
  rw [exposedNext] at success ambient ⊢
  split at success
  case h_2 => simp [discard] at success
  case h_1 erased domain result read =>
    simp only [read] at ambient
    obtain ⟨aType, argOk, argNext⟩ := Outcome.next_success success
    rw [argNext] at success ambient ⊢
    obtain ⟨pair, checkedOk, checkedNext⟩ := Outcome.next_success success
    rw [checkedNext] at success ambient ⊢
    obtain ⟨selected, substitutedOk, substitutedNext⟩ := Outcome.next_success success
    rw [substitutedNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    have progressF := childProgress state function room
    have fRoom := progressF.accepted room fType fOk
    have progressPi := normalProgress (infer state function).state fType.typeRoot
    have exposedRoom := progressPi.accepted fRoom exposed exposedOk
    let exposedState := (normal (infer state function).state fType.typeRoot).state
    have progressA := childProgress exposedState argument exposedRoom
    have argRoom := progressA.accepted exposedRoom aType argOk
    have progressCheck := requireTypes_progress (actual := aType.typeRoot) (expected := domain)
      (argument := argument) (depth := depth) (fun state ref _ => normalProgress state ref) argRoom
    let afterCheck := (requireTypes normal limit depth (infer exposedState argument).state
      aType.typeRoot domain argument).state
    have progressSub := instantiate_progress limit depth afterCheck result argument
    change Prefix (instantiate limit depth afterCheck result argument).state.arena final at ambient
    have checkFinal := progressSub.kept.trans ambient
    have argFinal := progressCheck.kept.trans checkFinal
    have funFinal := progressPi.kept.trans (progressA.kept.trans argFinal)
    have ⟨_, fBack, rawFunctionType, fRep, fTyped⟩ :=
      childSound onBase room fn fOk funFinal (fun check member =>
        retained check (List.mem_append_left _ (List.mem_append_left _ member)))
    obtain ⟨_, piBack, exposedType, piRef, converted⟩ := normalSound
      (onBase.trans progressF.kept) fRep exposedOk
    obtain ⟨dom, cod, sameType, domRep, codRep⟩ := binary_read piRef read
    have throughPi := progressF.kept.trans progressPi.kept
    obtain ⟨_, argBack, rawArgumentType, aRep, aTyped⟩ := childSound (onBase.trans throughPi) exposedRoom
      (arg.frame throughPi) argOk argFinal (fun check member =>
        retained check (List.mem_append_left _ (List.mem_append_right _ member)))
    have throughArgument := throughPi.trans progressA.kept
    obtain ⟨_, checkBack, compatible⟩ := requireTypes_refines normalSound (onBase.trans throughArgument)
      aRep (domRep.frame progressA.kept) checkedOk checkFinal (retained pair (by simp))
    have afterExpose := progressA.kept.trans progressCheck.kept
    have throughCheck := throughPi.trans afterExpose
    obtain ⟨_, subBack, resultRep⟩ := NativeCoreTransformExact.substitute_refines
      (codRep.frame afterExpose) (arg.frame throughCheck) (liftTransform_success substitutedOk)
    have calleeTyped : LoanTyping.HasType env [] ctx true (expand env f)
        (.pi erased (expand env dom) (expand env cod)) := by
      have exactType := fTyped.convert converted.converted
      rw [sameType] at exactType
      simpa only [Term.pi, EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs] using exactType
    have argumentTyped := aTyped.convert compatible
    have appTyped := LoanTyping.HasType.app calleeTyped argumentTyped (Or.inl rfl)
    have instantiation : expand env (cod.subst (single a)) =
        (expand env cod).subst (single (expand env a)) := by
      rw [EnvironmentDelta.expand_substitution wf.admissible]
      congr 1
      funext index
      cases index <;> simp only [single, expand]
    refine ⟨throughCheck.trans progressSub.kept, subBack ∘ checkBack ∘ argBack ∘ piBack ∘ fBack,
      cod.subst (single a), resultRep, ?_⟩
    rw [instantiation]
    change LoanTyping.HasType env [] ctx true (.app (expand env f) (expand env a))
      ((expand env cod).subst (single (expand env a))) at appTyped
    simpa only [Term.app, EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs] using appTyped

private theorem emit_refines
    (arity : op.arity = 0)
    (typed : LoanTyping.HasType env [] ctx true (expand env term) (expand env (.node op [])))
    (success : (emit state op).result = .ok answer) :
    Refines env state.arena ctx term (emit state op) answer := by
  obtain ⟨ref, added, shape⟩ := plain_success (original := append state op []) success
  subst answer
  obtain ⟨kept, backward, represented⟩ := append_refines .nil arity.symm added
  exact ⟨kept, backward, .node op [], represented, typed⟩

private theorem variable_refines (wf : UnifiedProgram.EnvWellFormed env)
    (context : ContextRep env state.arena bindings ctx) {index : Nat} (found : bindings[index]? = some binding)
    (success : (shiftInferred limit depth state binding.typeRoot (index + 1)).result = .ok answer) :
    Refines env state.arena ctx (.var index) (shiftInferred limit depth state binding.typeRoot (index + 1)) answer := by
  obtain ⟨written, represented, typedLookup⟩ := context.lookup_type found
  obtain ⟨ref, shifted, shape⟩ := plain_success
    (original := shiftType limit depth state binding.typeRoot (index + 1)) success
  subst answer
  obtain ⟨kept, backward, shiftedType⟩ := shiftType_refines represented shifted
  refine ⟨kept, backward, _, shiftedType, ?_⟩
  rw [EnvironmentDelta.expand_renaming wf.admissible, expand]
  exact .var typedLookup (Or.inl rfl)

private theorem global_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions state.arena roots definitions) {index : Nat} (found : roots[index]? = some row)
    (success : (shiftInferred limit depth state row.typeRoot amount).result = .ok answer) :
    Refines env state.arena ctx (.node (.global index) [])
      (shiftInferred limit depth state row.typeRoot amount) answer := by
  obtain ⟨entry, written, checked, represented, expanded⟩ := checked_type_at history aligned found
  obtain ⟨ref, shifted, shape⟩ := plain_success (original := shiftType limit depth state row.typeRoot amount) success
  subst answer
  obtain ⟨kept, backward, shiftedType⟩ := shiftType_refines represented shifted
  have closed := (history.wellFormed.globals index entry checked).1
  have original : LoanTyping.HasType env [] ctx true (.node (.global index) []) entry.type := by
    have direct := LoanTyping.HasType.global (loans := []) (ctx := ctx) (ghost := true) checked
    rwa [Environment.closed_rename closed] at direct
  refine ⟨kept, backward, _, shiftedType, ?_⟩
  rw [EnvironmentDelta.expand_global checked, EnvironmentDelta.expand_renaming history.wellFormed.admissible,
    expanded, Environment.closed_rename closed]
  exact history.delta_preserves checked original

/-- Every supported successful ghost inference derives the represented
result type in the original expanded context. -/
theorem runWithData_sound {normal : NormalAt}
    (metadata : DataFamilies env isData)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    InferSound env base ctx limit (runWithData normal roots visible limit isData depth bindings) := by
  induction depth generalizing base bindings ctx with
  | zero =>
      intro state root term answer final _ _ _ success _ _
      by_cases exhausted : limit < state.steps + 1 <;>
        simp [runWithData, tick, NativeCoreUnsignedCancellation.tick, exhausted] at success
  | succ depth ih =>
      have child {later nextRows nextCtx} (kept : Prefix base later) (represented : ContextRep env later nextRows nextCtx) :
          InferSound env later nextCtx limit (runWithData normal roots visible limit isData depth nextRows) :=
        ih (NativeCoreNestedAliases.frame_definitions aligned kept) represented
          (fun d _ _ _ _ extension source success => normalSound d (kept.trans extension) source success)
      have sameContext : InferSound env base ctx limit (runWithData normal roots visible limit isData depth bindings) :=
        child (.refl _) context
      intro state root term answer final onBase room source success ambient retained
      simp only [runWithData] at success ambient ⊢
      obtain ⟨entered, within⟩ := tick_success success
      rw [entered] at success ambient ⊢
      cases source with
      | var read =>
          simp only [read] at success ⊢
          split at success
          · exact variable_refines (state := {state with steps := state.steps + 1}) history.wellFormed
              (context.frame onBase) (by assumption) success
          · simp [discard] at success
      | @node _ op refs terms read arity children =>
          simp only [read] at success ambient ⊢
          cases op <;> simp only [Op.arity] at arity
          all_goals first | (simp [discard] at success; done) | skip
          all_goals try
            have empty := List.length_eq_zero_iff.mp arity
            subst refs
            cases children
          all_goals try dsimp only at success ambient ⊢
          case global.nil =>
            split at success
            · rename_i earlier
              simp only [ite_eq_left earlier]
              split at success
              · exact global_refines (state := {state with steps := state.steps + 1}) history
                  (NativeCoreNestedAliases.frame_definitions aligned onBase)
                  (by assumption) success
              · simp [discard] at success
            · simp at success
          case «universe».nil =>
            split at success
            · rename_i allowed
              simp only [ite_eq_left allowed]
              apply emit_refines (by rfl) _ success
              simp only [expand, expandArgs]
              exact .univ allowed
            · simp [discard] at success
          case prop.nil =>
            exact emit_refines rfl (by simp only [expand, expandArgs]; exact .prop) success
          case u64.nil =>
            exact emit_refines rfl (by simp only [expand, expandArgs]; exact .u64) success
          case i64.nil =>
            exact emit_refines rfl (by simp only [expand, expandArgs]; exact .i64) success
          case natural.nil =>
            split at success
            · rename_i allowed
              simp only [ite_eq_left allowed]
              apply emit_refines (by rfl) _ success
              simp only [expand, expandArgs]
              exact .natural allowed
            · simp [discard] at success
          case integer.nil =>
            split at success
            · rename_i bound
              simp only [ite_eq_left bound]
              apply emit_refines (by rfl) _ success
              simp only [expand, expandArgs]
              obtain ⟨lower, upper⟩ := bound
              exact .integer lower upper
            · simp [discard] at success
          case array | buffer =>
            have length : refs.length = 1 := arity
            obtain ⟨argument, rfl⟩ := List.length_eq_one_iff.mp length
            cases children with
            | cons child tail =>
              cases tail
              dsimp only at success ambient ⊢
              apply inferFixed_refines (state := {state with steps := state.steps + 1})
                (operand := .u64) (output := .universe 0) (depth := depth)
                (normalSound depth) (normalProgress depth) sameContext
                (fun _ _ budget => runWithData_progress normalProgress budget)
                onBase within (.cons child .nil) rfl .nil rfl success ambient retained
              intro typed
              simp only [expand, expandArgs] at typed ⊢
              first
              | exact .array (typed _ List.mem_cons_self)
              | exact .buffer (typed _ List.mem_cons_self)
          case refl =>
            have length : refs.length = 1 := arity
            obtain ⟨argument, rfl⟩ := List.length_eq_one_iff.mp length
            cases children with
            | cons child tail =>
              cases tail
              dsimp only at success ambient ⊢
              apply inferFixed_refines (state := {state with steps := state.steps + 1})
                (operand := .u64) (output := .eq) (depth := depth)
                (normalSound depth) (normalProgress depth) sameContext
                (fun _ _ budget => runWithData_progress normalProgress budget)
                onBase within (.cons child .nil) rfl (.cons child (.cons child .nil)) rfl success ambient retained
              intro typed
              simp only [expand, expandArgs] at typed ⊢
              exact .refl (typed _ List.mem_cons_self)
          case zeroLe =>
            have length : refs.length = 1 := arity
            obtain ⟨argument, rfl⟩ := List.length_eq_one_iff.mp length
            cases children with
            | cons child tail =>
              cases tail
              dsimp only at success ambient ⊢
              exact inferZeroLe_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                (normalSound depth) (normalProgress depth) sameContext
                (fun _ _ budget => runWithData_progress normalProgress budget)
                onBase within child success ambient retained
          case refine | witness | proof =>
            have length : refs.length = 1 := arity
            obtain ⟨argument, rfl⟩ := List.length_eq_one_iff.mp length
            cases children with
            | cons childRep tail =>
              cases tail
              dsimp only at success ambient ⊢
              first
              | exact inferRefine_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                  (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runWithData_progress normalProgress budget)
                  onBase within childRep success ambient retained
              | exact inferRefinementProjection_refines (state := {state with steps := state.steps + 1})
                  (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runWithData_progress normalProgress budget)
                  onBase within childRep success ambient retained
          case pack =>
            have length : refs.length = 3 := arity
            rcases refs with _ | ⟨predicate, _ | ⟨word, _ | ⟨evidence, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons predicateRep rest =>
              cases rest with
              | cons wordRep rest =>
                cases rest with
                | cons evidenceRep tail =>
                  cases tail
                  dsimp only at success ambient ⊢
                  exact inferPack_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                    (normalSound depth) (normalProgress depth) sameContext
                    (fun _ _ budget => runWithData_progress normalProgress budget)
                    onBase within predicateRep wordRep evidenceRep success ambient retained
          case transport =>
            have length : refs.length = 3 := arity
            rcases refs with _ | ⟨predicate, _ | ⟨equality, _ | ⟨payload, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons predicateRep rest =>
              cases rest with
              | cons equalityRep rest =>
                cases rest with
                | cons payloadRep tail =>
                  cases tail
                  dsimp only at success ambient ⊢
                  exact inferTransport_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                    (normalSound depth) (normalProgress depth) sameContext
                    (fun _ _ budget => runWithData_progress normalProgress budget)
                    onBase within predicateRep equalityRep payloadRep success ambient retained
          case usub =>
            have length : refs.length = 3 := arity
            rcases refs with _ | ⟨numerator, _ | ⟨denominator, _ | ⟨proof, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons first rest =>
              cases rest with
              | cons second rest =>
                cases rest with
                | cons bound tail =>
                  cases tail
                  dsimp only at success ambient ⊢
                  exact inferSubtract_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                    (normalSound depth) (normalProgress depth) sameContext
                    (fun _ _ budget => runWithData_progress normalProgress budget)
                    onBase within first second bound success ambient retained
          case eq | lt | uadd | arith =>
            have length : refs.length = 2 := arity
            rcases refs with _ | ⟨left, _ | ⟨right, _ | ⟨_, _⟩⟩⟩ <;> simp at length
            cases children with
            | cons first rest =>
              cases rest with
              | cons second tail =>
                cases tail
                dsimp only at success ambient ⊢
                apply inferFixed_refines (state := {state with steps := state.steps + 1})
                  (depth := depth)
                  (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runWithData_progress normalProgress budget)
                  onBase within (.cons first (.cons second .nil)) rfl .nil rfl success ambient retained
                intro typed
                simp only [expand, expandArgs] at typed ⊢
                have left := typed _ List.mem_cons_self
                have right := typed _ (List.mem_cons_of_mem _ List.mem_cons_self)
                first | exact .eq left right | exact .lt left right | exact .uadd left right | exact .arith left right
          case decide | strict =>
            have length : refs.length = 2 := arity
            rcases refs with _ | ⟨left, _ | ⟨right, _ | ⟨_, _⟩⟩⟩ <;> simp at length
            cases children with
            | cons first rest =>
              cases rest with
              | cons second tail =>
                cases tail
                dsimp only at success ambient ⊢
                first
                | exact inferDecide_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                    (normalSound depth) (normalProgress depth) sameContext
                    (fun _ _ budget => runWithData_progress normalProgress budget)
                    onBase within first second success ambient retained
                | exact inferStrict_refines (state := {state with steps := state.steps + 1}) sameContext
                    (fun _ _ budget => runWithData_progress normalProgress budget)
                    onBase within first second success ambient retained
          case ltAdd | ltCancel =>
            have length : refs.length = 4 := arity
            rcases refs with _ | ⟨left, _ | ⟨right, _ | ⟨delta, _ | ⟨proof, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons leftRep rest =>
              cases rest with
              | cons rightRep rest =>
                cases rest with
                | cons deltaRep rest =>
                  cases rest with
                  | cons proofRep tail =>
                    cases tail
                    dsimp only at success ambient ⊢
                    exact inferOffsetProof_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                      (normalSound depth) (normalProgress depth) sameContext
                      (fun _ _ budget => runWithData_progress normalProgress budget)
                      onBase within leftRep rightRep deltaRep proofRep success ambient retained
          case ltLe =>
            have length : refs.length = 5 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons leftRep rest =>
              cases rest with
              | cons middleRep rest =>
                cases rest with
                | cons rightRep rest =>
                  cases rest with
                  | cons lowerRep rest =>
                    cases rest with
                    | cons upperRep tail =>
                      cases tail
                      dsimp only at success ambient ⊢
                      exact inferTransitiveProof_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                        (normalSound depth) (normalProgress depth) sameContext
                        (fun _ _ budget => runWithData_progress normalProgress budget)
                        onBase within leftRep middleRep rightRep lowerRep upperRep success ambient retained
          case ifLt | ifEq =>
            have length : refs.length = 4 := arity
            rcases refs with _ | ⟨left, _ | ⟨right, _ | ⟨yes, _ | ⟨no, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons leftRep rest =>
              cases rest with
              | cons rightRep rest =>
                cases rest with
                | cons thenRep rest =>
                  cases rest with
                  | cons alternativeRep tail =>
                    cases tail
                    dsimp only at success ambient ⊢
                    apply inferConditional_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                      history.wellFormed (normalSound depth) (normalProgress depth) sameContext
                      (fun _ _ budget => runWithData_progress normalProgress budget) ?_
                      (fun _ _ _ budget => runWithData_progress normalProgress budget)
                      onBase within leftRep rightRep thenRep alternativeRep success ambient retained
                    intro entered assumption kept represented
                    have extended := onBase.trans kept
                    have bindAssumption {term} (source : Represents entered assumption term) :
                        ContextRep env entered (⟨assumption, true⟩ :: bindings) (⟨expand env term, true⟩ :: ctx) :=
                      .cons ⟨term, source, rfl, rfl⟩ (context.frame extended)
                    intro enteredState ref term selected after onContext withinRoom held found finalPrefix retainedPairs
                    exact child extended (bindAssumption represented) onContext withinRoom held found finalPrefix retainedPairs
          case pi | lam =>
            rename_i erased
            have length : refs.length = 2 := arity
            rcases refs with _ | ⟨domain, _ | ⟨body, _ | ⟨_, _⟩⟩⟩ <;> simp at length
            cases children with
            | @cons _ written _ _ domainRep rest =>
              cases rest with
              | cons bodyRep tail =>
                cases tail
                dsimp only at success ambient ⊢
                apply inferBinding_refines (state := {state with steps := state.steps + 1}) metadata
                  (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runWithData_progress normalProgress budget) ?_
                  (fun _ _ budget => runWithData_progress normalProgress budget)
                  onBase within domainRep bodyRep success ambient retained
                intro later kept
                have extended := onBase.trans kept
                have bound : ContextRep env later (⟨domain, erased⟩ :: bindings)
                    (⟨expand env written, erased⟩ :: ctx) :=
                  .cons ⟨written, domainRep.frame kept, rfl, rfl⟩ (context.frame extended)
                intro entered ref term selected after onContext withinRoom represented found finalPrefix retainedPairs
                exact child extended bound onContext withinRoom represented found finalPrefix retainedPairs
          case app =>
            have refsLength : refs.length = 2 := arity
            rcases refs with _ | ⟨function, _ | ⟨argument, _ | ⟨_, _⟩⟩⟩ <;> simp at refsLength
            case _ =>
              cases children with
              | cons fn tail =>
                cases tail with
                | cons arg tail =>
                  cases tail
                  exact inferApp_refines (state := {state with steps := state.steps + 1})
                    history.wellFormed (normalSound depth) (normalProgress depth) sameContext
                    (fun _ _ budget => runWithData_progress normalProgress budget)
                    onBase within fn arg success ambient retained

theorem runWith_sound {normal : NormalAt}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    InferSound env base ctx limit (runWith normal roots visible limit depth bindings) :=
  runWithData_sound (fun _ found => by cases found) history aligned context normalProgress normalSound

private theorem nested_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) :
    VisitsFrom base (ExpandedNormalization env) (NativeCoreNestedAliases.run roots visible limit depth) := by
  intro state ref term selected onBase source success
  obtain ⟨kept, backward, result⟩ := NativeCoreNestedAliases.run_refines history aligned onBase source success
  exact ⟨kept, backward, result⟩

theorem run_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx) :
    InferSound env base ctx limit (run roots visible limit depth bindings) :=
  runWith_sound history aligned context (NativeCoreNestedAliases.run_progress roots visible limit)
    (fun _ => nested_sound history aligned)

def CheckedInferences (snapshot : NativeFamilyWire.Snapshot) (env : Environment)
    (normalize : Nat → Nat → NormalAt) : Prop :=
  ∀ {index limit depth initial : Nat} {row : Roots},
    snapshot.definitions[index]? = some row →
    let start : State := ⟨snapshot.arena, initial⟩
    let output := runWithData (normalize index limit) snapshot.definitions index limit
      (NativeCoreGhostSort.isDataAt env) depth [] start row.valueRoot
    initial ≤ limit →
      Progress limit start output ∧
      ∀ answer, output.result = .ok answer → RetainedComparisons output.state.arena answer →
        Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
        ∃ (entry : GlobalDeclaration) (source inferred : Term),
          env.globals[index]? = some entry ∧ Represents snapshot.arena row.valueRoot source ∧
          Represents output.state.arena answer.typeRoot inferred ∧
          LoanTyping.HasType env [] [] true (expand env source) (expand env inferred) ∧
          LoanTyping.Conversion.Conv env (expand env inferred) entry.type

/-- Exact-byte admission supplies both the original graph operand and its
checked declaration type. Successful inference in the covered fragment uses
the earlier visibility bound and computes a represented type convertible to
that original type by Loan64 uniqueness. -/
theorem admitted_program_infers_with
    (normalize : Environment → NativeFamilyWire.Snapshot → Nat → Nat → NormalAt)
    (metered : ∀ env snapshot visible limit depth state root,
      Progress limit state (normalize env snapshot visible limit depth state root))
    (sound : ∀ {env snapshot definitions declarations},
      LoanTyping.MixedProgram.History definitions declarations env →
      RepresentsDefinitions snapshot.arena snapshot.definitions definitions →
      ∀ visible limit depth, VisitsFrom snapshot.arena (ExpandedNormalization env)
        (normalize env snapshot visible limit depth))
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      CheckedInferences snapshot env (normalize env snapshot) := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, valid, aligned, _, history, wf⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial row found start output room
  refine ⟨runWithData_progress (metered env snapshot index limit) room, ?_⟩
  intro answer success retained
  obtain ⟨entry, raw, recorded, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  obtain ⟨kept, forwards, inferred, held, inferredTyped⟩ :=
    runWithData_sound (NativeCoreGhostSort.isDataAt_sound env) history aligned .nil
      (metered env snapshot index limit) (sound history aligned index limit)
      (.refl _) room source.2 success (.refl _) retained
  exact ⟨kept, forwards valid, entry, raw.value, inferred, recorded, source.2, held, inferredTyped,
    inferredTyped.unique wf typed⟩

theorem admitted_program_infers
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      CheckedInferences snapshot env (NativeCoreNestedAliases.run snapshot.definitions) :=
  admitted_program_infers_with (fun _ snapshot => NativeCoreNestedAliases.run snapshot.definitions)
    (fun _ snapshot => NativeCoreNestedAliases.run_progress snapshot.definitions)
    (fun history aligned _ _ _ => nested_sound history aligned) admitted

/-- The same inference schedule uses recursive family normalization for
both Pi exposure and the argument-type comparison. -/
theorem admitted_family_program_infers
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      CheckedInferences snapshot env (NativeCoreExpandedFamilies.raw env snapshot.families snapshot.definitions) :=
  admitted_program_infers_with
    (fun env snapshot => NativeCoreExpandedFamilies.raw env snapshot.families snapshot.definitions)
    (fun env snapshot => NativeCoreExpandedFamilies.raw_progress env snapshot.families snapshot.definitions)
    (fun history aligned _ _ _ state ref term selected onBase source success => by
      obtain ⟨kept, backward, result⟩ := NativeCoreExpandedFamilies.raw_refines history aligned onBase source success
      exact ⟨kept, backward, result⟩) admitted

namespace Examples

private def proofOf (witness : Term) : Term := .eq witness witness
private def seven : Term := .natural 7
private def argument : Term := .node (.global 1) []
private def source : Term := .app (.app (.node (.global 0) []) seven) argument
private def familyType : Term :=
  .pi false .u64 (.pi true (proofOf (.var 0)) (proofOf (.var 1)))
private def familyValue : Term := .lam false .u64 (.lam true (proofOf (.var 0)) (.var 0))
private def definitions : List GlobalDeclaration :=
  [⟨familyType, familyValue⟩, ⟨proofOf seven, .refl seven⟩, ⟨proofOf seven, source⟩]
private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨6, 8⟩, ⟨10, 11⟩, ⟨10, 15⟩]
  families := []
  arena := #[.node .u64 [], .var 0, .var 1, .node .eq [1, 1], .node .eq [2, 2],
    .node (.pi true) [3, 4], .node (.pi false) [0, 5], .node (.lam true) [3, 1],
    .node (.lam false) [0, 7], .node (.natural 7) [], .node .eq [9, 9], .node .refl [9],
    .node (.global 0) [], .node (.global 1) [], .node .app [12, 9], .node .app [14, 13]]
private def start : State := ⟨snapshot.arena, 0⟩
private def finalArena : Arena :=
  snapshot.arena ++ #[.node .u64 [], .node .eq [9, 9], .node .eq [9, 9], .node (.pi true) [17, 18]]
private def answer : Inferred := ⟨18, [(16, 0), (10, 17)]⟩

/-- Inference exposes a dependent Pi, instantiates its outer word binder,
then checks the ghost proof against the resulting domain and returns the
instantiated codomain. The two checks use the live appended rows. -/
theorem admitted_dependent_spine_executes :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run snapshot.definitions 2 59 24 [] start 15 = ⟨⟨finalArena, 59⟩, .ok answer⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def env : Environment :=
  ⟨#[⟨familyType, familyValue⟩, ⟨proofOf seven, .refl seven⟩,
    ⟨proofOf seven, .app (.app familyValue seven) (.refl seven)⟩], #[]⟩

private theorem concrete_comparisons_retained : RetainedComparisons finalArena answer := by
  have literal : FullyRetained seven := .node (by decide) rfl rfl (by simp)
  have word : FullyRetained .u64 := .node (by decide) rfl rfl (by simp)
  have evidence : FullyRetained (proofOf seven) := .node (by decide) rfl rfl (by
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst child
    exact literal)
  intro pair member
  change pair ∈ [(16, 0), (10, 17)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  obtain (rfl | rfl) := member
  · exact ⟨.u64, .u64, decode_sound (fuel := 2) rfl, decode_sound (fuel := 2) rfl, word, word⟩
  · exact ⟨proofOf seven, proofOf seven, decode_sound (fuel := 3) rfl, decode_sound (fuel := 3) rfl,
      evidence, evidence⟩

/-- The result root of the admitted spine actually represents its checked
dependent proposition, and the inference proof types the original operand. -/
theorem admitted_dependent_spine_typed :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    Represents finalArena answer.typeRoot (proofOf seven) ∧
    LoanTyping.HasType env [] [] true (expand env source) (proofOf seven) := by
  have history : LoanTyping.MixedProgram.History definitions [] env :=
    LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
  have aligned : RepresentsDefinitions snapshot.arena snapshot.definitions definitions := decodeRoots_sound (by cbv)
  have represented : Represents start.arena 15 source := decode_sound (fuel := 6) rfl
  have computed := admitted_dependent_spine_executes.2
  have output : Represents finalArena answer.typeRoot (proofOf seven) := decode_sound (fuel := 3) rfl
  obtain ⟨_, _, inferred, supplied, typed⟩ :=
    run_sound (limit := 59) (depth := 24) (visible := 2) history aligned ContextRep.nil
      (.refl _) (by decide) represented (congrArg Outcome.result computed) (by rw [computed]; exact .refl _)
      concrete_comparisons_retained
  rw [computed] at supplied
  rw [supplied.unique output] at typed
  exact ⟨admitted_dependent_spine_executes.1, output,
    by simpa only [proofOf, Term.eq, seven, Term.natural, expand, expandArgs] using typed⟩

theorem last_substitution_exhaustion_keeps_inferred_pi :
    run snapshot.definitions 2 56 24 [] start 15 =
      ⟨⟨finalArena, 57⟩, .error (.substitution (.tick (.stepLimit 18)))⟩ := by cbv

/-- Looking up the older erased proof shifts its stored domain by two in
ghost mode, visiting both occurrences of the younger term's index. -/
theorem open_variable_weakening_appends_domain :
    run snapshot.definitions 2 4 8 [⟨0, false⟩, ⟨3, true⟩, ⟨0, false⟩] start 2 =
      ⟨⟨snapshot.arena ++ #[.var 2, .var 2, .node .eq [16, 17]], 4⟩, .ok ⟨18, []⟩⟩ := by cbv

private def sum : Term := .uadd (.natural 7) (.natural 1)
private def reflexive : GlobalDeclaration := ⟨.eq sum sum, .refl sum⟩
private def primitiveSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨3, 4⟩]
  families := []
  arena := #[.node (.natural 7) [], .node (.natural 1) [], .node .uadd [0, 1],
    .node .eq [2, 2], .node .refl [2], .node (.integer 1) [], .node .eq [5, 2]]
private def primitiveStart : State := ⟨primitiveSnapshot.arena, 0⟩
private def primitiveFinal : Arena := primitiveSnapshot.arena ++
  #[.node .u64 [], .node .u64 [], .node .u64 [], .node .u64 [], .node .u64 [], .node .eq [2, 2]]
private def primitiveAnswer : Inferred := ⟨12, [(9, 8), (10, 8), (11, 7)]⟩

/-- Refl checks its compound word before emitting equality at the original
operand reference. Both checks inside UAdd reuse a single expected row. -/
theorem admitted_reflexive_sum_executes :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot primitiveSnapshot) = true ∧
    run primitiveSnapshot.definitions 0 13 16 [] primitiveStart 4 =
      ⟨⟨primitiveFinal, 13⟩, .ok primitiveAnswer⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

theorem admitted_reflexive_sum_typed :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot primitiveSnapshot) = true ∧
    Represents primitiveFinal primitiveAnswer.typeRoot reflexive.type ∧
    LoanTyping.HasType ⟨#[⟨reflexive.type, reflexive.value⟩], #[]⟩ [] [] true reflexive.value reflexive.type := by
  let env : Environment := ⟨#[⟨reflexive.type, reflexive.value⟩], #[]⟩
  have history : LoanTyping.MixedProgram.History [reflexive] [] env :=
    LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
  have aligned : RepresentsDefinitions primitiveSnapshot.arena primitiveSnapshot.definitions [reflexive] :=
    decodeRoots_sound (by cbv)
  have source : Represents primitiveStart.arena 4 reflexive.value := decode_sound (fuel := 4) rfl
  have output : Represents primitiveFinal primitiveAnswer.typeRoot reflexive.type := decode_sound (fuel := 4) rfl
  have retained : RetainedComparisons primitiveFinal primitiveAnswer := by
    have word : FullyRetained .u64 := .node (by decide) rfl rfl (by simp)
    intro pair member
    change pair ∈ [(9, 8), (10, 8), (11, 7)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      exact ⟨.u64, .u64, decode_sound (fuel := 1) rfl, decode_sound (fuel := 1) rfl, word, word⟩
  have computed := admitted_reflexive_sum_executes.2
  obtain ⟨_, _, type, represented, typed⟩ := run_sound (limit := 13) (depth := 16) (visible := 0)
    history aligned ContextRep.nil (.refl _) (by decide) source (congrArg Outcome.result computed)
    (by rw [computed]; exact .refl _) retained
  rw [computed] at represented
  rw [represented.unique output] at typed
  exact ⟨admitted_reflexive_sum_executes.1, output,
    by
      change LoanTyping.HasType env [] [] true reflexive.value reflexive.type
      simpa only [reflexive, sum, Term.refl, Term.eq, Term.uadd, Term.natural, expand, expandArgs] using typed⟩

/-- Equality stops at the signed first operand's type comparison and retains
the two rows already appended. -/
theorem primitive_first_mismatch_keeps_checked_prefix :
    run primitiveSnapshot.definitions 0 13 16 [] primitiveStart 6 =
      ⟨⟨primitiveSnapshot.arena ++ #[.node .u64 [], .node .i64 []], 5⟩,
        .error (.outsideFragment 5)⟩ := by cbv

private def erasedBinderSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨5, 3⟩]
  families := []
  arena := #[.node .u64 [], .var 0, .node .refl [1], .node (.lam true) [0, 2],
    .node .eq [1, 1], .node (.pi true) [0, 4]]

/-- The inferred codomain uses the fresh erased word as a de Bruijn index.
The result keeps the written parameter type and the synthesized equality. -/
theorem admitted_erased_lambda_infers :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot erasedBinderSnapshot) = true ∧
    run erasedBinderSnapshot.definitions 0 10 16 [] ⟨erasedBinderSnapshot.arena, 0⟩ 3 =
      ⟨⟨erasedBinderSnapshot.arena ++ #[.node (.universe 0) [], .node .u64 [],
        .node .eq [1, 1], .node (.pi true) [0, 8]], 10⟩, .ok ⟨9, [(0, 7)]⟩⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def highestProduct : NativeFamilyWire.Snapshot where
  definitions := [⟨4, 3⟩]
  families := []
  arena := #[.node (.universe 31) [], .node (.natural 0) [], .node .eq [1, 1],
    .node (.pi false) [0, 2], .node .prop []]

/-- A Prop codomain determines the Pi sort even under the largest written
universe. The administrative successor is used for the binder check. -/
theorem admitted_impredicative_product_infers :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot highestProduct) = true ∧
    run highestProduct.definitions 0 13 16 [] ⟨highestProduct.arena, 0⟩ 3 =
      ⟨⟨highestProduct.arena ++ #[.node (.universe 32) [], .node .u64 [], .node .u64 [],
        .node .u64 [], .node .prop [], .node .prop []], 13⟩, .ok ⟨10, [(7, 6), (8, 6)]⟩⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def decisionSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨2, 6⟩]
  families := []
  arena := #[.node (.natural 1) [], .node (.natural 2) [], .node .lt [0, 1],
    .node .decide [0, 1], .node .decide [1, 0], .node (.integer 0) [], .node .strict [5, 3]]

/-- Strict checks the prefix first and returns the original inequality type
of the checked second term after Decide validates the numerical ordering. -/
theorem admitted_strict_decision_infers :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot decisionSnapshot) = true ∧
    run decisionSnapshot.definitions 0 13 16 [] ⟨decisionSnapshot.arena, 0⟩ 6 =
      ⟨⟨decisionSnapshot.arena ++ #[.node .i64 [], .node .u64 [], .node .u64 [],
        .node .u64 [], .node .lt [0, 1]], 13⟩, .ok ⟨11, [(9, 8), (10, 8)]⟩⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

/-- Numeric rejection follows both type checks and preserves their rows. -/
theorem false_decision_keeps_operand_rows :
    run decisionSnapshot.definitions 0 11 16 [] ⟨decisionSnapshot.arena, 0⟩ 4 =
      ⟨⟨decisionSnapshot.arena ++ #[.node .u64 [], .node .u64 [], .node .u64 []], 11⟩,
        .error (.outsideFragment 4)⟩ := by cbv

private def wordMax : Nat := 18446744073709551615
private def zeroBoundSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨5, 1⟩]
  families := []
  arena := #[.node (.natural wordMax) [], .node .zeroLe [0], .node (.natural 0) [],
    .node (.natural 1) [], .node .uadd [0, 3], .node .lt [2, 4]]

/-- ZeroLe retains the original maximum-width word and expresses its
successor as a ghost sum in the inferred proposition. -/
theorem admitted_zero_bound_keeps_wide_successor :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot zeroBoundSnapshot) = true ∧
    run zeroBoundSnapshot.definitions 0 5 16 [] ⟨zeroBoundSnapshot.arena, 0⟩ 1 =
      ⟨⟨zeroBoundSnapshot.arena ++ #[.node .u64 [], .node .u64 [], .node (.natural 0) [],
        .node (.natural 1) [], .node .uadd [0, 9], .node .lt [8, 10]], 5⟩, .ok ⟨11, [(7, 6)]⟩⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def subtractionSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨3, 2⟩]
  families := []
  arena := #[.node (.natural 0) [], .node .zeroLe [0], .node .usub [0, 0, 1], .node .u64 []]

/-- Budget exhaustion during the bound comparison keeps both the required
and inferred proposition rows. -/
theorem subtraction_limit_keeps_both_bound_graphs :
    run subtractionSnapshot.definitions 0 14 16 [] ⟨subtractionSnapshot.arena, 0⟩ 2 =
      ⟨⟨subtractionSnapshot.arena ++ #[.node .u64 [], .node .u64 [], .node .u64 [],
        .node (.natural 1) [], .node .uadd [0, 7], .node .lt [0, 8], .node .u64 [], .node .u64 [],
        .node (.natural 0) [], .node (.natural 1) [], .node .uadd [0, 13], .node .lt [12, 14]], 15⟩,
        .error (.tick (.stepLimit 15))⟩ := by cbv


private def conditionalSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨4, 5⟩]
  families := []
  arena := #[.node (.natural 1) [], .node (.natural 2) [], .var 0, .node .decide [0, 1],
    .node .lt [0, 1], .node .ifLt [0, 1, 2, 3]]

/-- The consequent uses its erased comparison witness. The returned
inequality type is lowered and checked against the alternative. -/
theorem admitted_conditional_infers_outside_assumption :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot conditionalSnapshot) = true ∧
    run conditionalSnapshot.definitions 0 39 16 [] ⟨conditionalSnapshot.arena, 0⟩ 5 =
      ⟨⟨conditionalSnapshot.arena ++ #[.node .u64 [], .node .u64 [], .node .u64 [], .node .lt [0, 1],
        .node .u64 [], .node .u64 [], .node .u64 [], .node .lt [0, 1]], 39⟩,
        .ok ⟨9, [(7, 6), (8, 6), (11, 10), (12, 10), (13, 9)]⟩⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def refinementSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨5, 4⟩]
  families := []
  arena := #[.node .u64 [], .var 0, .node .eq [1, 1], .node (.lam false) [0, 2],
    .node .refine [3], .node (.universe 0) []]

/-- Refine uses the same work counter to infer the predicate's body and
compare its Pi type to the synthesized U64-to-Prop arrow. -/
theorem admitted_refinement_infers_universe :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot refinementSnapshot) = true ∧
    run refinementSnapshot.definitions 0 24 24 [] ⟨refinementSnapshot.arena, 0⟩ 4 =
      ⟨⟨refinementSnapshot.arena ++ #[.node .u64 [], .node .prop [], .node (.pi false) [6, 7],
        .node (.universe 0) [], .node .u64 [], .node .prop [], .node (.pi false) [0, 11],
        .node (.universe 0) []], 24⟩, .ok ⟨13, [(0, 10), (0, 10), (12, 8)]⟩⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def packedSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨4, 7⟩]
  families := []
  arena := #[.node .u64 [], .var 0, .node .eq [1, 1], .node (.lam false) [0, 2],
    .node .refine [3], .node (.natural 7) [], .node .refl [5], .node .pack [3, 5, 6]]

/-- The predicate application is committed before checking the evidence.
Its argument is the original word reference used in Pack. -/
theorem pack_limit_keeps_required_application :
    run packedSnapshot.definitions 0 28 24 [] ⟨packedSnapshot.arena, 0⟩ 7 =
      ⟨⟨packedSnapshot.arena ++ #[.node .u64 [], .node .prop [], .node (.pi false) [8, 9],
        .node (.universe 0) [], .node .u64 [], .node .prop [], .node (.pi false) [0, 13],
        .node .u64 [], .node .u64 [], .node .app [3, 5]], 29⟩, .error (.tick (.stepLimit 6))⟩ := by cbv

private def refinementProofSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨4, 7⟩, ⟨10, 9⟩]
  families := []
  arena := packedSnapshot.arena ++ #[.node (.global 0) [], .node .proof [8], .node .eq [5, 5]]

/-- Proof retains the original reference under Witness and applies the
predicate exposed by the earlier declaration's refinement type. -/
theorem admitted_refinement_proof_keeps_original_subject :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot refinementProofSnapshot) = true ∧
    run refinementProofSnapshot.definitions 1 14 24 [] ⟨refinementProofSnapshot.arena, 0⟩ 9 =
      ⟨⟨refinementProofSnapshot.arena ++ #[.node .witness [8], .node .app [3, 11]], 14⟩, .ok ⟨12, []⟩⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def transportedSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨7, 6⟩]
  families := []
  arena := #[.node .u64 [], .var 0, .node .eq [1, 1], .node (.lam false) [0, 2],
    .node (.natural 7) [], .node .refl [4], .node .transport [3, 5, 5], .node .eq [4, 4]]

/-- Transport checks the predicate and then exposes equality before
allocating its source fiber. It retains that fiber on budget exhaustion
entering the payload inference. -/
theorem admitted_transport_limit_keeps_source_fiber :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot transportedSnapshot) = true ∧
    run transportedSnapshot.definitions 0 32 24 [] ⟨transportedSnapshot.arena, 0⟩ 6 =
      ⟨⟨transportedSnapshot.arena ++ #[.node .u64 [], .node .prop [], .node (.pi false) [8, 9],
        .node (.universe 0) [], .node .u64 [], .node .prop [], .node (.pi false) [0, 13],
        .node .u64 [], .node .u64 [], .node .eq [4, 4], .node .app [3, 4]], 33⟩,
        .error (.tick (.stepLimit 5))⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def offsetSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨7, 4⟩]
  families := []
  arena := #[.node (.natural 0) [], .node (.natural 1) [], .node (.natural 2) [],
    .node .decide [0, 1], .node .ltAdd [0, 1, 2, 3], .node .uadd [0, 2],
    .node .uadd [1, 2], .node .lt [5, 6]]

/-- Both propositions are committed before the proof is visited. A
successful derivation then returns the shifted root without rebuilding it. -/
theorem admitted_offset_proof_keeps_both_bounds :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot offsetSnapshot) = true ∧
    run offsetSnapshot.definitions 0 13 16 [] ⟨offsetSnapshot.arena, 0⟩ 4 =
      ⟨⟨offsetSnapshot.arena ++ #[.node .u64 [], .node .u64 [], .node .u64 [], .node .u64 [],
        .node .uadd [0, 2], .node .uadd [1, 2], .node .lt [0, 1], .node .lt [12, 13]], 14⟩,
        .error (.tick (.stepLimit 3))⟩ ∧
    (run offsetSnapshot.definitions 0 64 16 [] ⟨offsetSnapshot.arena, 0⟩ 4).result.map Inferred.typeRoot = .ok 15 := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def transitiveSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨7, 6⟩]
  families := []
  arena := #[.node (.natural 0) [], .node (.natural 1) [], .node (.natural 2) [], .node (.natural 3) [],
    .node .decide [0, 1], .node .decide [1, 3], .node .ltLe [0, 1, 2, 4, 5], .node .lt [0, 2]]

/-- The first proof is visited only after both comparison bounds have been
built. At a larger budget the restricted normalizer reaches the upper
bound's addition, which it does not yet handle. -/
theorem admitted_transitive_proof_keeps_ordered_bounds :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot transitiveSnapshot) = true ∧
    run transitiveSnapshot.definitions 0 13 24 [] ⟨transitiveSnapshot.arena, 0⟩ 6 =
      ⟨⟨transitiveSnapshot.arena ++ #[.node .u64 [], .node .u64 [], .node .u64 [], .node .u64 [],
        .node (.natural 1) [], .node .uadd [2, 12], .node .lt [0, 1], .node .lt [1, 13]], 14⟩,
        .error (.tick (.stepLimit 4))⟩ ∧
    (run transitiveSnapshot.definitions 0 96 24 [] ⟨transitiveSnapshot.arena, 0⟩ 6).result =
      .error (.outsideFragment 13) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

end Examples

end Jihoo.NativeKernel.NativeCoreGhostSpineInference
