import Jihoo.NativeCoreGhostTypeRequirement
import Jihoo.NativeCoreGhostConstructorInference
import Jihoo.NativeCoreGhostOwnerReturns
import Jihoo.NativeCoreGhostTakeInference
import Jihoo.NativeCoreGhostFoldInference
import Jihoo.NativeCoreGhostLoopInference
import Jihoo.NativeCoreGhostLendInference
import Jihoo.NativeCoreGhostSort
import Jihoo.NativeCoreGhostBinderCheck
import Jihoo.NativeCoreGhostReferenceTypes
import Jihoo.NativeCoreGhostLiteralAddition
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
open NativeCoreGhostBinderCheck
open NativeCoreGhostReferenceTypes

structure GraphBinding where
  typeRoot : Nat
  erased : Bool
  deriving Repr

abbrev NormalAt := Nat → Visit

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

private def inferElements (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (root count : Nat) (elements : List Nat) : Outcome Inferred :=
  if elements.length = count ∧ count < 2^64 then
    (checkFixed infer normal limit depth state .i64 elements).next fun checked comparisons =>
      (append checked (.natural count) []).next fun afterLength length =>
        (append afterLength .array [length]).next fun after result => ⟨after,.ok ⟨result,comparisons⟩⟩
  else discard state root

private def inferAlloc (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (count fill : Nat) : Outcome Inferred :=
  (checkFixed infer normal limit depth state .u64 [count]).next fun afterCount countPairs =>
    (checkFixed infer normal limit depth afterCount .i64 [fill]).next fun afterFill fillPairs =>
      (append afterFill .buffer [count]).next fun after result => ⟨after,.ok ⟨result,countPairs ++ fillPairs⟩⟩

private def bufferLength (infer : Infer) (normal : Visit) (state : State) (buffer : Nat) :
    Outcome (Nat × List (Nat × Nat)) :=
  (infer state buffer).next fun inferred found =>
    (normal inferred found.typeRoot).next fun exposed root =>
      match exposed.arena[root]? with
      | some (.node .buffer [length]) => ⟨exposed,.ok (length,found.compared)⟩
      | _ => discard exposed buffer

private def inferFree (infer : Infer) (normal : Visit) (state : State) (buffer tail : Nat) : Outcome Inferred :=
  (bufferLength infer normal state buffer).next fun afterBuffer checked =>
    (infer afterBuffer tail).next fun after result =>
      ⟨after,.ok ⟨result.typeRoot,checked.2 ++ result.compared⟩⟩

private def checkIndexEvidence (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (index length proof : Nat) : Outcome (List (Nat × Nat)) :=
  (append state .lt [index,length]).next fun formed expected =>
    requireOperands infer normal limit depth expected formed [proof]

private def ownerFamily (infer : Infer) (normal : Visit) (state : State) (owner family : Nat) :
    Outcome (List (Nat × Nat)) :=
  (infer state owner).next fun checked type =>
    (normal checked type.typeRoot).next fun after root =>
      match after.arena[root]? with
      | some (.node (.ind actual _) _) =>
          if actual = family then ⟨after,.ok type.compared⟩ else discard after owner
      | _ => discard after owner

private def inferDrop (infer : Infer) (normal : Visit) (isBoxed : Nat → Bool)
    (shapeTable : Nat → Option (Nat × Bool)) (state : State) (root family owner rest : Nat) : Outcome Inferred :=
  if (shapeTable family).isSome && isBoxed family then
    (ownerFamily infer normal state owner family).next fun retained pairs =>
      (infer retained rest).next fun after inferred =>
        ⟨after,.ok ⟨inferred.typeRoot,pairs ++ inferred.compared⟩⟩
  else discard state root

private def inferStore (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (buffer index value proof : Nat) : Outcome Inferred :=
  (bufferLength infer normal state buffer).next fun afterBuffer checked =>
    (checkFixed infer normal limit depth afterBuffer .u64 [index]).next fun afterIndex indexPairs =>
      (checkFixed infer normal limit depth afterIndex .i64 [value]).next fun afterValue valuePairs =>
        (checkIndexEvidence infer normal limit depth afterValue index checked.1 proof).next fun afterProof proofPairs =>
          (append afterProof .buffer [checked.1]).next fun after result =>
            ⟨after,.ok ⟨result,checked.2 ++ (indexPairs ++ (valuePairs ++ proofPairs))⟩⟩

private def checkOwnedType (normal : Visit) (isBoxed : Nat → Bool) (state : State)
    (original inferred : Nat) : Outcome Unit :=
  (NativeCoreGhostSort.sort normal state inferred).next fun afterSort sort =>
    if sort = .type 0 then requireOwned normal isBoxed afterSort original original
    else discard afterSort original

private def inferReference (infer : Infer) (normal : Visit) (isBoxed : Nat → Bool) (state : State)
    (original : Nat) : Outcome Inferred :=
  (infer state original).next fun afterType inferred =>
    (checkOwnedType normal isBoxed afterType original inferred.typeRoot).next fun afterOwner _ =>
      (append afterOwner (.universe 0) []).next fun after root =>
        ⟨after,.ok ⟨root,inferred.compared⟩⟩

private def inferBorrow (infer : Infer) (normal : Visit) (isBoxed : Nat → Bool) (state : State)
    (original : Nat) : Outcome Inferred :=
  (infer state original).next fun afterType inferred =>
    (requireOwned normal isBoxed afterType inferred.typeRoot original).next fun afterOwner _ =>
      (append afterOwner .ref [inferred.typeRoot]).next fun after root =>
        ⟨after,.ok ⟨root,inferred.compared⟩⟩

private def inferDeref (infer : Infer) (normal : Visit) (state : State) (original : Nat) : Outcome Inferred :=
  (infer state original).next fun afterType inferred =>
    (referenceTarget normal afterType inferred.typeRoot original).next fun after root =>
      ⟨after,.ok ⟨root,inferred.compared⟩⟩

private def readIndexType (normal : Visit) (state : State) (subject typeRoot : Nat) : Outcome (Nat × Bool) :=
  (normal state typeRoot).next fun exposed root =>
    match exposed.arena[root]? with
    | some (.node .array [length]) => ⟨exposed,.ok (length,false)⟩
    | some (.node .ref [inner]) =>
      (normal exposed inner).next fun after expanded =>
        match after.arena[expanded]? with
        | some (.node .buffer [length]) => ⟨after,.ok (length,true)⟩
        | _ => discard after subject
    | _ => discard exposed subject

private def inferIndex (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (subject index proof : Nat) : Outcome Inferred :=
  (infer state subject).next fun afterSubject subjectType =>
    (readIndexType normal afterSubject subject subjectType.typeRoot).next fun exposed bound =>
      (checkFixed infer normal limit depth exposed .u64 [index]).next fun afterIndex indexPairs =>
        (checkIndexEvidence infer normal limit depth afterIndex index bound.1 proof).next fun afterProof proofPairs =>
          (append afterProof .i64 []).next fun after result =>
            ⟨after,.ok ⟨result,subjectType.compared ++ (indexPairs ++ proofPairs)⟩⟩

private def lowerLoadType (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  liftTransform (NativeCoreTransformExact.run limit depth state root (.shift (-2)) 0)

private def checkLoadDomains (normal : Visit) (limit depth : Nat) (state : State)
    (length continuation valueDomain ownerDomain : Nat) : Outcome ((Nat × Nat) × (Nat × Nat)) :=
  (append state .i64 []).next fun afterValue signed =>
    (shiftType limit depth afterValue length 1).next fun afterShift lifted =>
      (append afterShift .buffer [lifted]).next fun afterOwner buffer =>
        (requireTypes normal limit depth afterOwner valueDomain signed continuation).next fun afterFirst first =>
          (requireTypes normal limit depth afterFirst ownerDomain buffer continuation).next fun after second =>
            ⟨after,.ok (first,second)⟩

private def finishLoad (normal : Visit) (limit depth : Nat) (state : State)
    (length continuation typeRoot : Nat) : Outcome Inferred :=
  (normal state typeRoot).next fun exposed root =>
    match exposed.arena[root]? with
    | some (.node (.pi false) [valueDomain, rest]) =>
      match exposed.arena[rest]? with
      | some (.node (.pi false) [ownerDomain, result]) =>
        (checkLoadDomains normal limit depth exposed length continuation valueDomain ownerDomain).next
          fun afterCheck pairs =>
            (normal afterCheck result).next fun normalized normalRoot =>
              (lowerLoadType limit depth normalized normalRoot).next fun after outside =>
                ⟨after,.ok ⟨outside,[pairs.1,pairs.2]⟩⟩
      | _ => discard exposed continuation
    | _ => discard exposed continuation

private def inferLoad (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (buffer index proof continuation : Nat) : Outcome Inferred :=
  (bufferLength infer normal state buffer).next fun afterBuffer checked =>
    (checkFixed infer normal limit depth afterBuffer .u64 [index]).next fun afterIndex indexPairs =>
      (checkIndexEvidence infer normal limit depth afterIndex index checked.1 proof).next fun afterProof proofPairs =>
        (infer afterProof continuation).next fun afterContinuation inferred =>
          (finishLoad normal limit depth afterContinuation checked.1 continuation inferred.typeRoot).next fun after result =>
            ⟨after,.ok ⟨result.typeRoot,checked.2 ++ (indexPairs ++ (proofPairs ++
              (inferred.compared ++ result.compared)))⟩⟩

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

private def exposeImpossibleBound (normal : Visit) (state : State) (proof typeRoot : Nat) : Outcome Unit :=
  (normal state typeRoot).next fun exposed inequality =>
    match exposed.arena[inequality]? with
    | some (.node .lt [_, upper]) =>
      (normal exposed upper).next fun after top =>
        match after.arena[top]? with
        | some (.node (.natural 0) []) => ⟨after,.ok ()⟩
        | _ => discard after proof
    | _ => discard exposed proof

private def inferAbsurd (infer : Infer) (normal : Visit) (state : State) (target proof : Nat) : Outcome Inferred :=
  (infer state target).next fun formed targetType =>
    (NativeCoreGhostSort.sort normal formed targetType.typeRoot).next fun afterSort _ =>
      (infer afterSort proof).next fun inferred proofType =>
        (exposeImpossibleBound normal inferred proof proofType.typeRoot).next fun after _ =>
          ⟨after,.ok ⟨target,targetType.compared ++ proofType.compared⟩⟩

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

/-- Native family index checks restart at the compiler's full depth. The
shared work counter continues from the outer inference visit. -/
private def indexCheckDepth : Nat := 128

def FamilyShapeTable (env : Environment) (shapeTable : Nat → Option (Nat × Bool)) : Prop :=
  ∀ family count data, shapeTable family = some (count,data) → ∃ entry,
    env.families[family]? = some entry ∧ entry.declaration.arity = count ∧ entry.declaration.data = data

def visibleFamilyShape (env : Environment) (visible family : Nat) : Option (Nat × Bool) := do
  let entry ← env.families[family]?
  if entry.declaration.globals ≤ visible then
    some (entry.declaration.arity,entry.declaration.data)
  else none

theorem visibleFamilyShape_sound (env : Environment) (visible : Nat) :
    FamilyShapeTable env (visibleFamilyShape env visible) := by
  intro family count data found
  unfold visibleFamilyShape at found
  obtain ⟨entry,selected,descriptor⟩ := Option.bind_eq_some_iff.mp found
  split at descriptor
  · cases descriptor
    exact ⟨entry,selected,rfl,rfl⟩
  · cases descriptor

private def inferFamily (infer : Infer) (normal : Visit) (limit : Nat)
    (shapeTable : Nat → Option (Nat × Bool)) (state : State) (root family count : Nat)
    (indices : List Nat) : Outcome Inferred :=
  match shapeTable family with
  | none => discard state root
  | some (arity,data) =>
      if indices.length = arity ∧ count = arity then
        inferFixed infer normal limit indexCheckDepth state .u64 indices (if data then .universe 0 else .prop) []
      else discard state root

/-- The list reverses the compiler's physical list of bindings so that
de Bruijn index zero looks up the newest binding. Visibility is shared
by inference and all type normalization visits. -/
def runVisits (normal : NormalAt) (roots : List Roots) (visible limit : Nat)
    (isData isBoxed : Nat → Bool) (shapeTable : Nat → Option (Nat × Bool))
    (constructorRoots : Nat → Nat → Option Nat) :
    Nat → Nat → List GraphBinding → Infer
  | 0, depth, _, state, root => tick limit depth state root (fun entered => discard entered root)
  | _ + 1, 0, _, state, root => tick limit 0 state root (fun entered => discard entered root)
  | visits + 1, depth + 1, ctx, state, root =>
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
        | some (.node (.con family constructor _) fields) =>
            NativeCoreGhostConstructorInference.runSelected
              (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) limit depth root ctx.length constructorRoots entered family constructor fields
        | some (.node (.ind family count) indices) =>
            inferFamily (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits indexCheckDepth ctx)
              (normal indexCheckDepth) limit shapeTable entered root family count indices
        | some (.node .array [n]) | some (.node .buffer [n]) =>
            inferFixed (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              .u64 [n] (.universe 0) []
        | some (.node (.elements count) elements) =>
            inferElements (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              root count elements
        | some (.node .alloc [n, fill]) =>
            inferAlloc (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered n fill
        | some (.node (.drop family) [owner, tail]) =>
            inferDrop (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) isBoxed shapeTable entered root family owner tail
        | some (.node .free [buffer, tail]) =>
            inferFree (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) entered buffer tail
        | some (.node .store [buffer, index, value, proof]) =>
            inferStore (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              buffer index value proof
        | some (.node .load [buffer, index, proof, continuation]) =>
            inferLoad (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              buffer index proof continuation
        | some (.node .ref [owner]) =>
            inferReference (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) isBoxed entered owner
        | some (.node (.back erased) [owner, motive]) =>
            NativeCoreGhostOwnerReturns.runBack
              (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) isBoxed limit depth entered erased owner motive
        | some (.node (.give erased) [motive, owner, result]) =>
            NativeCoreGhostOwnerReturns.runGive
              (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) isBoxed limit depth entered erased motive owner result
        | some (.node .take [subject, continuation]) =>
            NativeCoreGhostTakeInference.run
              (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) limit depth entered subject continuation
        | some (.node .fold [count, initial, body]) =>
            let familyLayouts := fun family => (shapeTable family).map fun _ => isBoxed family
            NativeCoreGhostFoldInference.runWith isBoxed (CoreEffectAnalysis.graphMemoryFreeWith familyLayouts)
              (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) limit depth entered count initial body
        | some (.node .loop [count, motive, initial, body]) =>
            let familyLayouts := fun family => (shapeTable family).map fun _ => isBoxed family
            NativeCoreGhostLoopInference.run isBoxed (CoreEffectAnalysis.graphMemoryFreeWith familyLayouts)
              (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) limit depth entered count motive initial body
        | some (.node .lend [owner, reader, continuation]) =>
            NativeCoreGhostLendInference.run
              (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) isData isBoxed limit depth entered owner reader continuation
        | some (.node .borrow [owner]) =>
            inferBorrow (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) isBoxed entered owner
        | some (.node .deref [reference]) =>
            inferDeref (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (normal depth) entered reference
        | some (.node .index [subject, index, proof]) =>
            inferIndex (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              subject index proof
        | some (.node .eq [a, b]) | some (.node .lt [a, b]) =>
            inferFixed (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              .u64 [a, b] .prop []
        | some (.node .refl [a]) =>
            inferFixed (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              .u64 [a] .eq [a, a]
        | some (.node .uadd [a, b]) =>
            inferFixed (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              .u64 [a, b] .u64 []
        | some (.node (.arith _) [a, b]) =>
            inferFixed (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              .i64 [a, b] .i64 []
        | some (.node .decide [a, b]) =>
            inferDecide (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              root a b
        | some (.node .strict [a, b]) =>
            inferStrict (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) entered a b
        | some (.node .zeroLe [a]) =>
            inferZeroLe (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered a
        | some (.node .usub [a, b, proof]) =>
            inferSubtract (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              a b proof
        | some (.node .ltAdd [a, b, delta, proof]) =>
            inferOffsetProof (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              true a b delta proof
        | some (.node .ltCancel [a, b, delta, proof]) =>
            inferOffsetProof (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              false a b delta proof
        | some (.node .ltLe [a, b, c, lower, upper]) =>
            inferTransitiveProof (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              a b c lower upper
        | some (.node .ifEq [a, b, yes, no]) =>
            inferConditional (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (fun assumption => runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth (⟨assumption, true⟩ :: ctx))
              (normal depth) limit depth entered true a b yes no
        | some (.node .ifLt [a, b, yes, no]) =>
            inferConditional (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (fun assumption => runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth (⟨assumption, true⟩ :: ctx))
              (normal depth) limit depth entered false a b yes no
        | some (.node .refine [predicate]) =>
            inferRefine (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered predicate
        | some (.node .pack [predicate, word, evidence]) =>
            inferPack (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              predicate word evidence
        | some (.node .transport [predicate, equality, payload]) =>
            inferTransport (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered
              predicate equality payload
        | some (.node .absurd [target, proof]) =>
            inferAbsurd (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) entered target proof
        | some (.node .witness [subject]) =>
            inferRefinementProjection (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) entered false subject
        | some (.node .proof [subject]) =>
            inferRefinementProjection (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) entered true subject
        | some (.node (.pi erased) [a, b]) =>
            inferBinding (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth (⟨a, erased⟩ :: ctx))
              (normal depth) isData entered true erased a b
        | some (.node (.lam erased) [a, b]) =>
            inferBinding (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx)
              (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth (⟨a, erased⟩ :: ctx))
              (normal depth) isData entered false erased a b
        | some (.node .app [f, a]) =>
            inferApp (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth ctx) (normal depth) limit depth entered f a
        | _ => discard entered root

def runWithConstructors (normal : NormalAt) (roots : List Roots) (visible limit : Nat)
    (isData isBoxed : Nat → Bool) (shapeTable : Nat → Option (Nat × Bool))
    (constructorRoots : Nat → Nat → Option Nat) (depth : Nat) (ctx : List GraphBinding) : Infer :=
  fun state root =>
    runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots (limit+1-state.steps) depth ctx state root

def runWithFamilyShapes (normal : NormalAt) (roots : List Roots) (visible limit : Nat)
    (isData isBoxed : Nat → Bool) (shapeTable : Nat → Option (Nat × Bool)) : Nat → List GraphBinding → Infer :=
  runWithConstructors normal roots visible limit isData isBoxed shapeTable (fun _ _ => none)

def runWithFamilyKinds (normal : NormalAt) (roots : List Roots) (visible limit : Nat)
    (isData isBoxed : Nat → Bool) : Nat → List GraphBinding → Infer :=
  runWithFamilyShapes normal roots visible limit isData isBoxed (fun _ => none)

def runWithData (normal : NormalAt) (roots : List Roots) (visible limit : Nat) (isData : Nat → Bool) :
    Nat → List GraphBinding → Infer :=
  runWithFamilyKinds normal roots visible limit isData (fun _ => false)

def runWith (normal : NormalAt) (roots : List Roots) (visible limit : Nat) : Nat → List GraphBinding → Infer :=
  runWithData normal roots visible limit (fun _ => false)

def run (roots : List Roots) (visible limit : Nat) : Nat → List GraphBinding → Infer :=
  runWith (NativeCoreGhostLiteralAddition.run roots visible limit) roots visible limit

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

private theorem inferFamily_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferFamily infer normal limit shapeTable state root family count indices) := by
  unfold inferFamily
  split
  · exact Progress.atState _ _
  · split
    · exact inferFixed_progress infers (fun state root _ => normalizes state root) room
    · exact Progress.atState _ _

private theorem bufferLength_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (bufferLength infer normal state buffer) := by
  apply next_progress (infers _ _ room) room
  intro _ _ _
  apply (normalizes _ _).next
  intro root
  split <;> exact Progress.atState _ _

private theorem ownerFamily_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) : Progress limit state (ownerFamily infer normal state owner family) := by
  unfold ownerFamily
  apply (infers _ _ room).next
  intro inferred
  apply (normalizes _ _).next
  intro selected
  split
  · split <;> exact Progress.atState _ _
  · exact Progress.atState _ _

private theorem inferDrop_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (inferDrop infer normal isBoxed shapeTable state root family owner rest) := by
  unfold inferDrop
  split
  · apply next_progress (ownerFamily_progress infers normalizes room) room
    intro _ _ remaining
    exact (infers _ _ remaining).next (fun _ => Progress.atState _ _)
  · exact Progress.atState _ _

private theorem inferFree_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferFree infer normal state buffer tail) := by
  apply next_progress (bufferLength_progress infers normalizes room) room
  intro _ _ bufferRoom
  exact (infers _ _ bufferRoom).next (fun _ => Progress.atState _ _)

private theorem checkIndexEvidence_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (checkIndexEvidence infer normal limit depth state index length proof) := by
  apply next_progress (append_progress _ _ _) room
  intro _ _ expectedRoom
  exact requireOperands_progress infers (fun state ref _ => normalizes state ref) expectedRoom

private theorem inferStore_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferStore infer normal limit depth state buffer index value proof) := by
  apply next_progress (bufferLength_progress infers normalizes room) room
  intro _ _ bufferRoom
  apply next_progress (checkFixed_progress infers (fun state ref _ => normalizes state ref) bufferRoom) bufferRoom
  intro _ _ indexRoom
  apply next_progress (checkFixed_progress infers (fun state ref _ => normalizes state ref) indexRoom) indexRoom
  intro _ _ valueRoom
  apply next_progress (checkIndexEvidence_progress infers normalizes valueRoom) valueRoom
  intro _ _ _
  exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)

private theorem checkOwnedType_progress
    (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (checkOwnedType normal isBoxed state original inferred) := by
  unfold checkOwnedType
  apply (NativeCoreGhostSort.sort_progress normalizes).next
  intro sort
  split
  · exact requireOwned_progress normalizes
  · exact Progress.atState _ _

private theorem inferReference_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferReference infer normal isBoxed state original) := by
  apply (infers _ _ room).next
  intro inferred
  exact (checkOwnedType_progress normalizes).next (fun _ => (append_progress _ _ _).next (fun _ => Progress.atState _ _))

private theorem inferBorrow_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferBorrow infer normal isBoxed state original) := by
  apply (infers _ _ room).next
  intro inferred
  exact (requireOwned_progress normalizes).next (fun _ => (append_progress _ _ _).next (fun _ => Progress.atState _ _))

private theorem inferDeref_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferDeref infer normal state original) :=
  (infers _ _ room).next (fun _ => (referenceTarget_progress normalizes).next (fun _ => Progress.atState _ _))

private theorem readIndexType_progress
    (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (readIndexType normal state subject typeRoot) := by
  apply (normalizes _ _).next
  intro root
  split
  · exact Progress.atState _ _
  · apply (normalizes _ _).next
    intro expanded
    split <;> exact Progress.atState _ _
  · exact Progress.atState _ _

private theorem inferIndex_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferIndex infer normal limit depth state subject index proof) := by
  apply next_progress (infers _ _ room) room
  intro _ _ subjectRoom
  apply next_progress (readIndexType_progress normalizes) subjectRoom
  intro _ _ boundRoom
  apply next_progress (checkFixed_progress infers (fun state ref _ => normalizes state ref) boundRoom) boundRoom
  intro _ _ indexRoom
  apply next_progress (checkIndexEvidence_progress infers normalizes indexRoom) indexRoom
  intro _ _ _
  exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)

private theorem lowerLoadType_progress (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (lowerLoadType limit depth state root) :=
  liftTransform_progress (NativeCoreTransformExact.run_progress limit depth state root (.shift (-2)) 0)

private theorem checkLoadDomains_progress
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (checkLoadDomains normal limit depth state length continuation valueDomain ownerDomain) := by
  apply next_progress (append_progress _ _ _) room
  intro _ _ valueRoom
  apply next_progress (shiftType_progress _ _ _ _ _) valueRoom
  intro _ _ shiftRoom
  apply next_progress (append_progress _ _ _) shiftRoom
  intro _ _ ownerRoom
  apply next_progress (requireTypes_progress (fun state ref _ => normalizes state ref) ownerRoom) ownerRoom
  intro _ _ firstRoom
  exact (requireTypes_progress (fun state ref _ => normalizes state ref) firstRoom).next (fun _ => Progress.atState _ _)

private theorem finishLoad_progress
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (finishLoad normal limit depth state length continuation typeRoot) := by
  unfold finishLoad
  apply next_progress (normalizes _ _) room
  intro _ _ exposedRoom
  split
  · split
    · apply next_progress (checkLoadDomains_progress normalizes exposedRoom) exposedRoom
      intro _ _ checkedRoom
      exact (normalizes _ _).next (fun _ => (lowerLoadType_progress _ _ _ _).next (fun _ => Progress.atState _ _))
    · exact Progress.atState _ _
  · exact Progress.atState _ _

private theorem inferLoad_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferLoad infer normal limit depth state buffer index proof continuation) := by
  apply next_progress (bufferLength_progress infers normalizes room) room
  intro _ _ bufferRoom
  apply next_progress (checkFixed_progress infers (fun state ref _ => normalizes state ref) bufferRoom) bufferRoom
  intro _ _ indexRoom
  apply next_progress (checkIndexEvidence_progress infers normalizes indexRoom) indexRoom
  intro _ _ proofRoom
  apply next_progress (infers _ _ proofRoom) proofRoom
  intro _ _ continuationRoom
  exact (finishLoad_progress normalizes continuationRoom).next (fun _ => Progress.atState _ _)

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

private theorem inferElements_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferElements infer normal limit depth state root count elements) := by
  unfold inferElements
  split
  · apply next_progress (checkFixed_progress infers (fun state ref _ => normalizes state ref) room) room
    intro _ _ _
    exact (append_progress _ _ _).next (fun _ => (append_progress _ _ _).next (fun _ => Progress.atState _ _))
  · exact Progress.atState _ _

private theorem inferAlloc_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferAlloc infer normal limit depth state count fill) := by
  apply next_progress (checkFixed_progress infers (fun state ref _ => normalizes state ref) room) room
  intro _ _ countRoom
  apply next_progress (checkFixed_progress infers (fun state ref _ => normalizes state ref) countRoom) countRoom
  intro _ _ _
  exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)

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

private theorem exposeImpossibleBound_progress
    (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (exposeImpossibleBound normal state proof typeRoot) := by
  apply (normalizes _ _).next
  intro inequality
  split
  · apply (normalizes _ _).next
    intro top
    split <;> exact Progress.atState _ _
  · exact Progress.atState _ _

private theorem inferAbsurd_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferAbsurd infer normal state target proof) := by
  apply next_progress (infers _ _ room) room
  intro _ _ formedRoom
  apply next_progress (NativeCoreGhostSort.sort_progress normalizes) formedRoom
  intro _ _ sortRoom
  apply next_progress (infers _ _ sortRoom) sortRoom
  intro _ _ _
  exact (exposeImpossibleBound_progress normalizes).next (fun _ => Progress.atState _ _)

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
theorem runVisits_progress {normal : NormalAt} {roots : List Roots} {bindings : List GraphBinding}
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth bindings state root) := by
  induction visits generalizing depth state root bindings with
  | zero => exact tick_progress (fun _ _ => Progress.atState _ _)
  | succ visits ih =>
    cases depth with
    | zero => exact tick_progress (fun _ _ => Progress.atState _ _)
    | succ depth =>
      simp only [runVisits]
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
        | exact NativeCoreGhostConstructorInference.runSelected_progress
            (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferFamily_progress (fun _ _ room => ih (depth := indexCheckDepth) room)
            (normalProgress indexCheckDepth) within
        | exact inferElements_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferAlloc_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferDrop_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferFree_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferStore_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferLoad_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferReference_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact NativeCoreGhostOwnerReturns.runBack_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact NativeCoreGhostOwnerReturns.runGive_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact NativeCoreGhostTakeInference.run_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact NativeCoreGhostFoldInference.runWith_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact NativeCoreGhostLoopInference.run_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact NativeCoreGhostLendInference.run_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferBorrow_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferDeref_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferIndex_progress (fun _ _ room => ih room) (normalProgress depth) within
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
        | exact inferAbsurd_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferRefinementProjection_progress (fun _ _ room => ih room) (normalProgress depth) within
        | exact inferBinding_progress (fun _ _ room => ih room) (fun _ _ room => ih room)
            (normalProgress depth) within
        | exact inferApp_progress (fun _ _ room => ih room)
            (fun state ref _ => normalProgress depth state ref) within
        | simpa only [discard] using (Progress.atState (limit := limit) entered
            (.error (.outsideFragment root) : Except NativeCorePureComputationNormal.Error Inferred))

theorem runWithConstructors_progress {normal : NormalAt} {roots : List Roots} {bindings : List GraphBinding}
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state
      (runWithConstructors normal roots visible limit isData isBoxed shapeTable constructorRoots depth bindings state root) :=
  runVisits_progress normalProgress room

theorem runWithFamilyShapes_progress {normal : NormalAt} {roots : List Roots} {bindings : List GraphBinding}
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runWithFamilyShapes normal roots visible limit isData isBoxed shapeTable depth bindings state root) :=
  runWithConstructors_progress normalProgress room

theorem runWithFamilyKinds_progress {normal : NormalAt} {roots : List Roots} {bindings : List GraphBinding}
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runWithFamilyKinds normal roots visible limit isData isBoxed depth bindings state root) :=
  runWithFamilyShapes_progress normalProgress room

theorem runWithData_progress {normal : NormalAt} {roots : List Roots} {bindings : List GraphBinding}
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runWithData normal roots visible limit isData depth bindings state root) :=
  runWithFamilyKinds_progress normalProgress room

theorem runWith_progress {normal : NormalAt} {roots : List Roots} {bindings : List GraphBinding}
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runWith normal roots visible limit depth bindings state root) :=
  runWithData_progress normalProgress room

theorem run_progress {roots : List Roots} {bindings : List GraphBinding}
    (room : state.steps ≤ limit) :
    Progress limit state (run roots visible limit depth bindings state root) :=
  runWith_progress (NativeCoreGhostLiteralAddition.run_progress roots visible limit) room

/-- Each graph row records the written domain in pre-binder scope. -/
def BindingRep (env : Environment) (arena : Arena) (row : GraphBinding) (binding : Binding) : Prop :=
  ∃ term, Represents arena row.typeRoot term ∧ binding.ty = expand env term ∧ binding.erased = row.erased

inductive ContextRep (env : Environment) (arena : Arena) : List GraphBinding → Context → Prop where
  | nil : ContextRep env arena [] []
  | cons : BindingRep env arena row binding → ContextRep env arena rows ctx →
      ContextRep env arena (row :: rows) (binding :: ctx)

private theorem ContextRep.length_eq (represented : ContextRep env arena bindings ctx) :
    bindings.length = ctx.length := by
  induction represented with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

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

private theorem inferFamily_refines
    (metadata : FamilyShapeTable env shapeTable)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (indicesRep : RepresentsList state.arena indices args)
    (success : (inferFamily infer normal limit shapeTable state root family count indices).result = .ok answer)
    (ambient : Prefix (inferFamily infer normal limit shapeTable state root family count indices).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.node (.ind family count) args)
      (inferFamily infer normal limit shapeTable state root family count indices) answer := by
  unfold inferFamily at success ambient ⊢
  split at success
  · simp [discard] at success
  · rename_i arity data selected
    simp only [selected] at ambient ⊢
    split at success
    · rename_i counts
      simp only [ite_eq_left counts] at ambient ⊢
      obtain ⟨entry,found,arityKnown,dataKnown⟩ := metadata family arity data selected
      have countCorrect : (expandArgs env args).length = count := by
        rw [EnvironmentDelta.expandArgs_map,List.length_map,← NativeCoreIdentical.represented_length indicesRep,
          counts.1,counts.2]
      have resultArity : ([] : List Nat).length = (if data then Op.universe 0 else .prop).arity := by cases data <;> rfl
      apply inferFixed_refines normalSound normalProgress childSound childProgress onBase room
        indicesRep rfl .nil resultArity success ambient retained
      intro checked
      have typed : ∀ term ∈ expandArgs env args, LoanTyping.HasType env [] ctx true term .u64 := by
        intro term member
        rw [EnvironmentDelta.expandArgs_map] at member
        obtain ⟨source,written,rfl⟩ := List.mem_map.mp member
        simpa only [Term.u64,expand,expandArgs] using checked source written
      have formed := LoanTyping.HasType.ind (ghost := true) found (counts.2.trans arityKnown.symm) countCorrect typed
      cases data <;> simp only [dataKnown,Bool.false_eq_true,ite_false,ite_true,Term.univ,Term.prop,expand,expandArgs] at formed ⊢
      all_goals exact formed
    · simp [discard] at success

private theorem inferElements_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (elementsRep : RepresentsList state.arena refs elements)
    (success : (inferElements infer normal limit depth state root count refs).result = .ok answer)
    (ambient : Prefix (inferElements infer normal limit depth state root count refs).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.elements count elements)
      (inferElements infer normal limit depth state root count refs) answer := by
  unfold inferElements at success ambient ⊢
  split at success
  · rename_i permitted
    simp only [ite_eq_left permitted] at ambient ⊢
    obtain ⟨pairs,checkedOk,checkedNext⟩ := Outcome.next_success success
    rw [checkedNext] at success ambient ⊢
    obtain ⟨length,lengthOk,lengthNext⟩ := Outcome.next_success success
    rw [lengthNext] at success ambient ⊢
    obtain ⟨selected,outputOk,outputNext⟩ := Outcome.next_success success
    rw [outputNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    let checked := checkFixed infer normal limit depth state .i64 refs
    let emitted := append checked.state (.natural count) []
    have tail := (append_progress (limit := limit) checked.state (.natural count) []).kept.trans
      ((append_progress (limit := limit) emitted.state .array [length]).kept.trans ambient)
    obtain ⟨checkedKept,checkedBack,typed⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
      onBase room elementsRep rfl checkedOk tail retained
    obtain ⟨lengthKept,lengthBack,lengthRep⟩ := append_refines .nil rfl lengthOk
    obtain ⟨resultKept,resultBack,resultRep⟩ := append_refines (.cons lengthRep .nil) rfl outputOk
    have elementsLength : (expandArgs env elements).length = count := by
      rw [EnvironmentDelta.expandArgs_map,List.length_map,← NativeCoreIdentical.represented_length elementsRep]
      exact permitted.1
    have members : ∀ term ∈ expandArgs env elements, LoanTyping.HasType env [] ctx true term .i64 := by
      intro term found
      rw [EnvironmentDelta.expandArgs_map] at found
      obtain ⟨original,member,rfl⟩ := List.mem_map.mp found
      simpa only [Term.i64,expand,expandArgs] using typed original member
    have arrayTyped := LoanTyping.HasType.elements elementsLength (elementsLength.symm ▸ permitted.2) members
    refine ⟨checkedKept.trans (lengthKept.trans resultKept),resultBack ∘ lengthBack ∘ checkedBack,_,resultRep,?_⟩
    simpa only [Term.elements,Term.array,Term.natural,expand,expandArgs,elementsLength] using arrayTyped
  · simp [discard] at success

private theorem inferAlloc_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (countRep : Represents state.arena count n) (fillRep : Represents state.arena fill x)
    (success : (inferAlloc infer normal limit depth state count fill).result = .ok answer)
    (ambient : Prefix (inferAlloc infer normal limit depth state count fill).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.alloc n x) (inferAlloc infer normal limit depth state count fill) answer := by
  unfold inferAlloc at success ambient ⊢
  obtain ⟨countPairs,countOk,countNext⟩ := Outcome.next_success success
  rw [countNext] at success ambient ⊢
  obtain ⟨fillPairs,fillOk,fillNext⟩ := Outcome.next_success success
  rw [fillNext] at success ambient ⊢
  obtain ⟨selected,outputOk,outputNext⟩ := Outcome.next_success success
  rw [outputNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let counts := checkFixed infer normal limit depth state .u64 [count]
  let fills := checkFixed infer normal limit depth counts.state .i64 [fill]
  have countProgress := checkFixed_progress (state := state) (operand := .u64) (args := [count]) (depth := depth)
    childProgress (fun state ref _ => normalProgress state ref) room
  have countRoom := countProgress.accepted room countPairs countOk
  have fillProgress := checkFixed_progress (state := counts.state) (operand := .i64) (args := [fill]) (depth := depth)
    childProgress (fun state ref _ => normalProgress state ref) countRoom
  have fillFinal := (append_progress (limit := limit) fills.state .buffer [count]).kept.trans ambient
  obtain ⟨countKept,countBack,countTyped⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    onBase room (.cons countRep .nil) rfl countOk (fillProgress.kept.trans fillFinal)
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨fillKept,fillBack,fillTyped⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    (onBase.trans countKept) countRoom (.cons (fillRep.frame countKept) .nil) rfl fillOk fillFinal
    (fun pair member => retained pair (List.mem_append_right _ member))
  have throughFill := countKept.trans fillKept
  obtain ⟨resultKept,resultBack,represented⟩ := append_refines (.cons (countRep.frame throughFill) .nil) rfl outputOk
  refine ⟨throughFill.trans resultKept,resultBack ∘ fillBack ∘ countBack,_,represented,?_⟩
  simp only [expand,expandArgs] at countTyped fillTyped
  simp only [Term.alloc,expand,expandArgs]
  exact .alloc (countTyped n List.mem_cons_self) (fillTyped x List.mem_cons_self)

private theorem unary_read (represented : Represents arena root term)
    (read : arena[root]? = some (.node op [ref])) :
    ∃ child, term = .node op [child] ∧ Represents arena ref child := by
  cases represented with
  | var other => rw [read] at other; cases other
  | node other arity args =>
    rw [read] at other
    cases other
    cases args with
    | cons first tail => cases tail; exact ⟨_,rfl,first⟩

private theorem bufferLength_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (bufferRep : Represents state.arena buffer b)
    (success : (bufferLength infer normal state buffer).result = .ok answer)
    (ambient : Prefix (bufferLength infer normal state buffer).state.arena final)
    (retained : ∀ pair ∈ answer.2, PairRetained final pair) :
    let after := (bufferLength infer normal state buffer).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ length, Represents after answer.1 length ∧
        LoanTyping.HasType env [] ctx true (expand env b) (.buffer (expand env length)) := by
  unfold bufferLength at success ambient ⊢
  obtain ⟨found,foundOk,foundNext⟩ := Outcome.next_success success
  rw [foundNext] at success ambient ⊢
  obtain ⟨root,exposedOk,exposedNext⟩ := Outcome.next_success success
  rw [exposedNext] at success ambient ⊢
  split at success
  · rename_i length read
    simp only [read] at ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    have inferred := childProgress state buffer room
    have normalized := normalProgress (infer state buffer).state found.typeRoot
    obtain ⟨_,inferredBack,_,foundRep,typed⟩ := childSound onBase room bufferRep foundOk
      (normalized.kept.trans ambient) retained
    obtain ⟨kept,backward,residual,held,converted⟩ := normalSound (onBase.trans inferred.kept) foundRep exposedOk
    obtain ⟨count,shape,countRep⟩ := unary_read held read
    refine ⟨inferred.kept.trans kept,backward ∘ inferredBack,count,countRep,?_⟩
    simpa only [shape,Term.buffer,expand,expandArgs] using typed.convert converted.converted
  · simp [discard] at success

private theorem ownerFamily_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (source : Represents state.arena owner written)
    (success : (ownerFamily infer normal state owner family).result = .ok compared)
    (ambient : Prefix (ownerFamily infer normal state owner family).state.arena final)
    (retained : ∀ pair ∈ compared, PairRetained final pair) :
    let after := (ownerFamily infer normal state owner family).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ arity indices, LoanTyping.HasType env [] ctx true (expand env written) (.node (.ind family arity) indices) := by
  unfold ownerFamily at success ambient ⊢
  obtain ⟨inferred,inferredOk,inferredNext⟩ := Outcome.next_success success
  rw [inferredNext] at success ambient ⊢
  obtain ⟨selected,normalized,normNext⟩ := Outcome.next_success success
  rw [normNext] at success ambient ⊢
  split at success
  · rename_i actual arity refs read
    split at success
    · rename_i same
      subst actual
      simp only [Except.ok.injEq] at success
      subst compared
      simp only [read,ite_true] at ambient ⊢
      have progress := normalProgress (infer state owner).state inferred.typeRoot
      obtain ⟨checked,checkBack,_,typeRep,typed⟩ := childSound onBase room source inferredOk
        (progress.kept.trans ambient) retained
      obtain ⟨kept,backward,residual,held,changed⟩ := normalSound (onBase.trans checked) typeRep normalized
      have shape : ∃ values, residual = .node (.ind family arity) values := by
        cases held with
        | var selected => rw [read] at selected; cases selected
        | node selected => rw [read] at selected; cases selected; exact ⟨_,rfl⟩
      obtain ⟨values,shape⟩ := shape
      rw [shape] at changed
      exact ⟨checked.trans kept,backward ∘ checkBack,arity,expandArgs env values,
        typed.convert (by simpa only [expand] using changed.converted)⟩
    · simp [discard] at success
  · simp [discard] at success

private theorem inferDrop_refines
    (metadata : BoxedFamilies env isBoxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (source : Represents state.arena owner x) (continued : Represents state.arena rest r)
    (success : (inferDrop infer normal isBoxed shapeTable state root family owner rest).result = .ok answer)
    (ambient : Prefix (inferDrop infer normal isBoxed shapeTable state root family owner rest).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.node (.drop family) [x,r])
      (inferDrop infer normal isBoxed shapeTable state root family owner rest) answer := by
  unfold inferDrop at success ambient ⊢
  split at success
  · rename_i allowed
    simp only [ite_eq_left allowed] at ambient ⊢
    obtain ⟨entry,found,boxed⟩ := metadata family (Bool.and_eq_true_iff.mp allowed).2
    obtain ⟨first,firstOk,firstNext⟩ := Outcome.next_success success
    rw [firstNext] at success ambient ⊢
    obtain ⟨tail,tailOk,tailNext⟩ := Outcome.next_success success
    rw [tailNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    let checked := ownerFamily infer normal state owner family
    have ownerRoom := (ownerFamily_progress (owner := owner) (family := family) childProgress normalProgress room).accepted
      room first firstOk
    have tailProgress := childProgress checked.state rest ownerRoom
    obtain ⟨ownerKept,ownerBack,_,_,typedOwner⟩ := ownerFamily_refines normalSound normalProgress childSound
      onBase room source firstOk (tailProgress.kept.trans ambient) (fun pair member => retained pair (List.mem_append_left _ member))
    obtain ⟨tailKept,tailBack,_,resultRep,typedTail⟩ := childSound (onBase.trans ownerKept) ownerRoom
      (continued.frame ownerKept) tailOk ambient (fun pair member => retained pair (List.mem_append_right _ member))
    refine ⟨ownerKept.trans tailKept,tailBack ∘ ownerBack,_,resultRep,?_⟩
    simpa only [expand,expandArgs] using LoanTyping.HasType.drop found boxed typedOwner typedTail
  · simp [discard] at success

private theorem inferFree_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (bufferRep : Represents state.arena buffer b) (tailRep : Represents state.arena tail t)
    (success : (inferFree infer normal state buffer tail).result = .ok answer)
    (ambient : Prefix (inferFree infer normal state buffer tail).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.free b t) (inferFree infer normal state buffer tail) answer := by
  unfold inferFree at success ambient ⊢
  obtain ⟨checked,bufferOk,bufferNext⟩ := Outcome.next_success success
  rw [bufferNext] at success ambient ⊢
  obtain ⟨result,tailOk,tailNext⟩ := Outcome.next_success success
  rw [tailNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checkedBuffer := bufferLength infer normal state buffer
  have bufferProgress := bufferLength_progress (state := state) (buffer := buffer) childProgress normalProgress room
  have bufferRoom := bufferProgress.accepted room checked bufferOk
  have tailProgress := childProgress checkedBuffer.state tail bufferRoom
  obtain ⟨bufferKept,bufferBack,_,_,typedBuffer⟩ := bufferLength_refines normalSound normalProgress childSound
    childProgress onBase room bufferRep bufferOk (tailProgress.kept.trans ambient)
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨tailKept,tailBack,_,resultRep,typedTail⟩ := childSound (onBase.trans bufferKept) bufferRoom
    (tailRep.frame bufferKept) tailOk ambient (fun pair member => retained pair (List.mem_append_right _ member))
  refine ⟨bufferKept.trans tailKept,tailBack ∘ bufferBack,_,resultRep,?_⟩
  simp only [Term.free,expand,expandArgs]
  exact .free typedBuffer typedTail

private theorem checkIndexEvidence_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (indexRep : Represents state.arena index i) (lengthRep : Represents state.arena length n)
    (proofRep : Represents state.arena proof p)
    (success : (checkIndexEvidence infer normal limit depth state index length proof).result = .ok pairs)
    (ambient : Prefix (checkIndexEvidence infer normal limit depth state index length proof).state.arena final)
    (retained : ∀ pair ∈ pairs, PairRetained final pair) :
    let after := (checkIndexEvidence infer normal limit depth state index length proof).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] ctx true (expand env p) (.lt (expand env i) (expand env n)) := by
  unfold checkIndexEvidence at success ambient ⊢
  obtain ⟨need,needOk,needNext⟩ := Outcome.next_success success
  rw [needNext] at success ambient ⊢
  obtain ⟨needKept,needBack,needRep⟩ := append_refines (.cons indexRep (.cons lengthRep .nil)) rfl needOk
  have needRoom := (append_progress state .lt [index,length]).accepted room need needOk
  obtain ⟨proofKept,proofBack,typed⟩ := requireOperands_refines normalSound normalProgress childSound childProgress
    (onBase.trans needKept) needRoom (.cons (proofRep.frame needKept) .nil) needRep success ambient retained
  refine ⟨needKept.trans proofKept,proofBack ∘ needBack,?_⟩
  simpa only [Term.lt,expand,expandArgs] using typed p List.mem_cons_self

private theorem inferStore_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (bufferRep : Represents state.arena buffer b) (indexRep : Represents state.arena index i)
    (valueRep : Represents state.arena value v) (proofRep : Represents state.arena proof p)
    (success : (inferStore infer normal limit depth state buffer index value proof).result = .ok answer)
    (ambient : Prefix (inferStore infer normal limit depth state buffer index value proof).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.store b i v p) (inferStore infer normal limit depth state buffer index value proof) answer := by
  unfold inferStore at success ambient ⊢
  obtain ⟨checked,bufferOk,bufferNext⟩ := Outcome.next_success success
  rw [bufferNext] at success ambient ⊢
  obtain ⟨indexPairs,indexOk,indexNext⟩ := Outcome.next_success success
  rw [indexNext] at success ambient ⊢
  obtain ⟨valuePairs,valueOk,valueNext⟩ := Outcome.next_success success
  rw [valueNext] at success ambient ⊢
  obtain ⟨proofPairs,proofOk,proofNext⟩ := Outcome.next_success success
  rw [proofNext] at success ambient ⊢
  obtain ⟨result,outputOk,outputNext⟩ := Outcome.next_success success
  rw [outputNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checkedBuffer := bufferLength infer normal state buffer
  let checkedIndex := checkFixed infer normal limit depth checkedBuffer.state .u64 [index]
  let checkedValue := checkFixed infer normal limit depth checkedIndex.state .i64 [value]
  let checkedProof := checkIndexEvidence infer normal limit depth checkedValue.state index checked.1 proof
  have bufferProgress := bufferLength_progress (state := state) (buffer := buffer) childProgress normalProgress room
  have bufferRoom := bufferProgress.accepted room checked bufferOk
  have indexProgress := checkFixed_progress (state := checkedBuffer.state) (operand := .u64) (args := [index])
    (depth := depth) childProgress (fun state root _ => normalProgress state root) bufferRoom
  have indexRoom := indexProgress.accepted bufferRoom indexPairs indexOk
  have valueProgress := checkFixed_progress (state := checkedIndex.state) (operand := .i64) (args := [value])
    (depth := depth) childProgress (fun state root _ => normalProgress state root) indexRoom
  have valueRoom := valueProgress.accepted indexRoom valuePairs valueOk
  have proofProgress := checkIndexEvidence_progress (state := checkedValue.state) (index := index) (length := checked.1)
    (proof := proof) (depth := depth) childProgress normalProgress valueRoom
  have proofFinal := (append_progress (limit := limit) checkedProof.state .buffer [checked.1]).kept.trans ambient
  have valueFinal := proofProgress.kept.trans proofFinal
  have indexFinal := valueProgress.kept.trans valueFinal
  obtain ⟨bufferKept,bufferBack,_,lengthRep,typedBuffer⟩ := bufferLength_refines normalSound normalProgress childSound
    childProgress onBase room bufferRep bufferOk (indexProgress.kept.trans indexFinal)
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨indexKept,indexBack,typedIndex⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    (onBase.trans bufferKept) bufferRoom (.cons (indexRep.frame bufferKept) .nil) rfl indexOk indexFinal
    (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
  have throughIndex := bufferKept.trans indexKept
  obtain ⟨valueKept,valueBack,typedValue⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    (onBase.trans throughIndex) indexRoom (.cons (valueRep.frame throughIndex) .nil) rfl valueOk valueFinal
    (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))))
  have throughValue := throughIndex.trans valueKept
  have lengthHeld := lengthRep.frame (indexKept.trans valueKept)
  obtain ⟨proofKept,proofBack,typedProof⟩ := checkIndexEvidence_refines normalSound normalProgress childSound childProgress
    (onBase.trans throughValue) valueRoom (indexRep.frame throughValue) lengthHeld (proofRep.frame throughValue)
    proofOk proofFinal (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ member))))
  obtain ⟨outputKept,outputBack,resultRep⟩ := append_refines (.cons (lengthHeld.frame proofKept) .nil) rfl outputOk
  refine ⟨throughValue.trans (proofKept.trans outputKept),outputBack ∘ proofBack ∘ valueBack ∘ indexBack ∘ bufferBack,
    _,resultRep,?_⟩
  simp only [expand,expandArgs] at typedIndex typedValue
  simp only [Term.store,expand,expandArgs]
  exact .store typedBuffer (typedIndex i List.mem_cons_self) (typedValue v List.mem_cons_self) typedProof

private theorem checkLoadDomains_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (lengthRep : Represents state.arena length n)
    (valueRep : Represents state.arena valueDomain x)
    (ownerRep : Represents state.arena ownerDomain b)
    (success : (checkLoadDomains normal limit depth state length continuation valueDomain ownerDomain).result = .ok pairs)
    (ambient : Prefix (checkLoadDomains normal limit depth state length continuation valueDomain ownerDomain).state.arena final)
    (firstKept : PairRetained final pairs.1) (secondKept : PairRetained final pairs.2) :
    let after := (checkLoadDomains normal limit depth state length continuation valueDomain ownerDomain).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.Conversion.Conv env (expand env x) .i64 ∧
      LoanTyping.Conversion.Conv env (expand env b) (.buffer ((expand env n).rename Nat.succ)) := by
  unfold checkLoadDomains at success ambient ⊢
  obtain ⟨signed,signedOk,signedNext⟩ := Outcome.next_success success
  rw [signedNext] at success ambient ⊢
  obtain ⟨lifted,liftedOk,liftedNext⟩ := Outcome.next_success success
  rw [liftedNext] at success ambient ⊢
  obtain ⟨buffer,bufferOk,bufferNext⟩ := Outcome.next_success success
  rw [bufferNext] at success ambient ⊢
  obtain ⟨first,firstOk,firstNext⟩ := Outcome.next_success success
  rw [firstNext] at success ambient ⊢
  obtain ⟨second,secondOk,secondNext⟩ := Outcome.next_success success
  rw [secondNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst pairs
  let emitted := append state .i64 []
  let shifted := shiftType limit depth emitted.state length 1
  let assembled := append shifted.state .buffer [lifted]
  let compared := requireTypes normal limit depth assembled.state valueDomain signed continuation
  have signedRoom := (append_progress (limit := limit) state .i64 []).accepted room signed signedOk
  have liftedRoom := (shiftType_progress limit depth emitted.state length 1).accepted signedRoom lifted liftedOk
  have bufferRoom := (append_progress (limit := limit) shifted.state .buffer [lifted]).accepted liftedRoom buffer bufferOk
  have firstProgress := requireTypes_progress (state := assembled.state) (limit := limit) (depth := depth)
    (actual := valueDomain) (expected := signed) (argument := continuation) (fun state root _ => normalProgress state root) bufferRoom
  have firstRoom := firstProgress.accepted bufferRoom first firstOk
  have secondProgress := requireTypes_progress (state := compared.state) (limit := limit) (depth := depth)
    (actual := ownerDomain) (expected := buffer) (argument := continuation) (fun state root _ => normalProgress state root) firstRoom
  obtain ⟨signedPrefix,signedBack,signedRep⟩ := append_refines (op := .i64) .nil rfl signedOk
  obtain ⟨liftedPrefix,liftedBack,liftedRep⟩ := shiftType_refines (lengthRep.frame signedPrefix) liftedOk
  have throughShift := signedPrefix.trans liftedPrefix
  obtain ⟨bufferPrefix,bufferBack,bufferRep⟩ := append_refines (.cons liftedRep .nil) rfl bufferOk
  have throughBuffer := throughShift.trans bufferPrefix
  obtain ⟨firstPrefix,firstBack,valueConv⟩ := requireTypes_refines normalSound (onBase.trans throughBuffer)
    (valueRep.frame throughBuffer) (signedRep.frame (liftedPrefix.trans bufferPrefix)) firstOk (secondProgress.kept.trans ambient) firstKept
  have throughFirst := throughBuffer.trans firstPrefix
  obtain ⟨secondPrefix,secondBack,ownerConv⟩ := requireTypes_refines normalSound (onBase.trans throughFirst)
    (ownerRep.frame throughFirst) (bufferRep.frame firstPrefix) secondOk ambient secondKept
  refine ⟨throughFirst.trans secondPrefix,secondBack ∘ firstBack ∘ bufferBack ∘ liftedBack ∘ signedBack,
    ?_,?_⟩
  · simpa only [Term.i64,expand,expandArgs] using valueConv
  · simpa only [Term.buffer,EnvironmentDelta.expand_node_cons,expandArgs,EnvironmentDelta.expand_renaming wf.admissible] using ownerConv

private theorem finishLoad_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (lengthRep : Represents state.arena length n) (typeRep : Represents state.arena typeRoot kType)
    (success : (finishLoad normal limit depth state length continuation typeRoot).result = .ok answer)
    (ambient : Prefix (finishLoad normal limit depth state length continuation typeRoot).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (finishLoad normal limit depth state length continuation typeRoot).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ valueDomain ownerDomain result written outside,
        Represents after answer.typeRoot outside ∧
        LoanTyping.Conversion.Conv env (expand env kType) (.pi false valueDomain (.pi false ownerDomain result)) ∧
        LoanTyping.Conversion.Conv env valueDomain .i64 ∧
        LoanTyping.Conversion.Conv env ownerDomain (.buffer ((expand env n).rename Nat.succ)) ∧
        LoanTyping.Conversion.Conv env result written ∧
        PartialRenaming.shift (-2) 0 written = some (expand env outside) := by
  unfold finishLoad at success ambient ⊢
  obtain ⟨root,exposedOk,exposedNext⟩ := Outcome.next_success success
  rw [exposedNext] at success ambient ⊢
  split at success
  · rename_i valueDomain rest outer
    simp only [outer] at ambient
    split at success
    · rename_i ownerDomain result inner
      simp only [inner] at ambient
      obtain ⟨pairs,domainsOk,domainsNext⟩ := Outcome.next_success success
      rw [domainsNext] at success ambient ⊢
      obtain ⟨normalRoot,resultOk,resultNext⟩ := Outcome.next_success success
      rw [resultNext] at success ambient ⊢
      obtain ⟨outside,loweredOk,loweredNext⟩ := Outcome.next_success success
      rw [loweredNext] at success ambient ⊢
      simp only [Except.ok.injEq] at success
      subst answer
      let exposed := normal state typeRoot
      let checked := checkLoadDomains normal limit depth exposed.state length continuation valueDomain ownerDomain
      let normalized := normal checked.state result
      have exposedRoom := (normalProgress state typeRoot).accepted room root exposedOk
      have resultProgress := normalProgress checked.state result
      have lowerProgress := lowerLoadType_progress limit depth normalized.state normalRoot
      obtain ⟨exposedPrefix,exposedBack,exposedType,exposedRep,typeConv⟩ := normalSound onBase typeRep exposedOk
      obtain ⟨x,tail,shape,valueRep,tailRep⟩ := binary_read exposedRep outer
      obtain ⟨b,r,tailShape,ownerRep,resultRep⟩ := binary_read tailRep inner
      obtain ⟨checkedPrefix,checkedBack,valueConv,ownerConv⟩ := checkLoadDomains_refines wf normalSound normalProgress
        (onBase.trans exposedPrefix) exposedRoom (lengthRep.frame exposedPrefix) valueRep ownerRep domainsOk
        (resultProgress.kept.trans (lowerProgress.kept.trans ambient))
        (retained pairs.1 (by simp)) (retained pairs.2 (by simp))
      have throughCheck := exposedPrefix.trans checkedPrefix
      obtain ⟨normalizedPrefix,normalizedBack,normalType,normalRep,resultConv⟩ := normalSound
        (onBase.trans throughCheck) (resultRep.frame checkedPrefix) resultOk
      obtain ⟨lowerPrefix,lowerBack,residual,removed,outsideRep⟩ :=
        (NativeCoreTransformExact.run_refines (mode := .shift (-2)) (binders := 0) (value := normalType)
          normalRep trivial (liftTransform_success loweredOk)).1
      change PartialRenaming.shift (-2) 0 normalType = some residual at removed
      have weakened := load_result_reweakens removed
      have removedExpanded : PartialRenaming.shift (-2) 0 (expand env normalType) = some (expand env residual) := by
        rw [← weakened,EnvironmentDelta.expand_renaming wf.admissible]
        exact load_result_shifted (expand env residual)
      refine ⟨throughCheck.trans (normalizedPrefix.trans lowerPrefix),
        lowerBack ∘ normalizedBack ∘ checkedBack ∘ exposedBack,_,_,_,_,residual,outsideRep,?_,
        valueConv,ownerConv,resultConv.converted,removedExpanded⟩
      simpa only [shape,tailShape,Term.pi,EnvironmentDelta.expand_node_cons,expandArgs] using typeConv.converted
    · simp [discard] at success
  · simp [discard] at success

private theorem inferLoad_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (bufferRep : Represents state.arena buffer b) (indexRep : Represents state.arena index i)
    (proofRep : Represents state.arena proof p) (continuationRep : Represents state.arena continuation k)
    (success : (inferLoad infer normal limit depth state buffer index proof continuation).result = .ok answer)
    (ambient : Prefix (inferLoad infer normal limit depth state buffer index proof continuation).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.load b i p k) (inferLoad infer normal limit depth state buffer index proof continuation) answer := by
  unfold inferLoad at success ambient ⊢
  obtain ⟨checked,bufferOk,bufferNext⟩ := Outcome.next_success success
  rw [bufferNext] at success ambient ⊢
  obtain ⟨indexPairs,indexOk,indexNext⟩ := Outcome.next_success success
  rw [indexNext] at success ambient ⊢
  obtain ⟨proofPairs,proofOk,proofNext⟩ := Outcome.next_success success
  rw [proofNext] at success ambient ⊢
  obtain ⟨inferred,continuationOk,continuationNext⟩ := Outcome.next_success success
  rw [continuationNext] at success ambient ⊢
  obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checkedBuffer := bufferLength infer normal state buffer
  let checkedIndex := checkFixed infer normal limit depth checkedBuffer.state .u64 [index]
  let checkedProof := checkIndexEvidence infer normal limit depth checkedIndex.state index checked.1 proof
  let callback := infer checkedProof.state continuation
  have bufferProgress := bufferLength_progress (state := state) (buffer := buffer) childProgress normalProgress room
  have bufferRoom := bufferProgress.accepted room checked bufferOk
  have indexProgress := checkFixed_progress (state := checkedBuffer.state) (operand := .u64) (args := [index])
    (depth := depth) childProgress (fun state root _ => normalProgress state root) bufferRoom
  have indexRoom := indexProgress.accepted bufferRoom indexPairs indexOk
  have proofProgress := checkIndexEvidence_progress (state := checkedIndex.state) (index := index) (length := checked.1)
    (proof := proof) (depth := depth) childProgress normalProgress indexRoom
  have proofRoom := proofProgress.accepted indexRoom proofPairs proofOk
  have callbackProgress := childProgress checkedProof.state continuation proofRoom
  have callbackRoom := callbackProgress.accepted proofRoom inferred continuationOk
  have resultProgress := finishLoad_progress (state := callback.state) (length := checked.1) (continuation := continuation)
    (typeRoot := inferred.typeRoot) (depth := depth) normalProgress callbackRoom
  have callbackFinal := resultProgress.kept.trans ambient
  have proofFinal := callbackProgress.kept.trans callbackFinal
  have indexFinal := proofProgress.kept.trans proofFinal
  obtain ⟨bufferKept,bufferBack,_,lengthRep,typedBuffer⟩ := bufferLength_refines normalSound normalProgress childSound
    childProgress onBase room bufferRep bufferOk (indexProgress.kept.trans indexFinal)
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨indexKept,indexBack,typedIndex⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    (onBase.trans bufferKept) bufferRoom (.cons (indexRep.frame bufferKept) .nil) rfl indexOk indexFinal
    (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
  have throughIndex := bufferKept.trans indexKept
  obtain ⟨proofKept,proofBack,typedProof⟩ := checkIndexEvidence_refines normalSound normalProgress childSound childProgress
    (onBase.trans throughIndex) indexRoom (indexRep.frame throughIndex) (lengthRep.frame indexKept) (proofRep.frame throughIndex)
    proofOk proofFinal (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ member))))
  have throughProof := throughIndex.trans proofKept
  obtain ⟨callbackKept,callbackBack,_,callbackRep,typedCallback⟩ := childSound (onBase.trans throughProof) proofRoom
    (continuationRep.frame throughProof) continuationOk callbackFinal
    (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ member)))))
  have throughCallback := throughProof.trans callbackKept
  obtain ⟨resultKept,resultBack,_,_,_,_,_,resultRep,callbackConv,valueConv,ownerConv,resultConv,removed⟩ :=
    finishLoad_refines wf normalSound normalProgress (onBase.trans throughCallback) callbackRoom
      (lengthRep.frame (indexKept.trans (proofKept.trans callbackKept))) callbackRep resultOk ambient
      (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _ member)))))
  refine ⟨throughCallback.trans resultKept,resultBack ∘ callbackBack ∘ proofBack ∘ indexBack ∘ bufferBack,
    _,resultRep,?_⟩
  simp only [expand,expandArgs] at typedIndex
  simp only [Term.load,expand,expandArgs]
  exact .load typedBuffer (typedIndex i List.mem_cons_self) typedProof
    (typedCallback.convert callbackConv) valueConv ownerConv resultConv removed (Or.inl rfl)

private theorem checkOwnedType_refines
    (metadata : BoxedFamilies env isBoxed) (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena)
    (owner : Represents state.arena original term) (inferredType : Represents state.arena inferred written)
    (success : (checkOwnedType normal isBoxed state original inferred).result = .ok ()) :
    let after := (checkOwnedType normal isBoxed state original inferred).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.Conversion.Conv env (expand env written) (.univ 0) ∧ LoanTyping.Owned env (expand env term) := by
  unfold checkOwnedType at success ⊢
  obtain ⟨sort,sortOk,sortNext⟩ := Outcome.next_success success
  rw [sortNext] at success ⊢
  split at success
  · rename_i shape
    subst sort
    obtain ⟨sortKept,sortBack,converted⟩ := NativeCoreGhostSort.sort_refines normalSound onBase inferredType sortOk
    obtain ⟨ownerKept,ownerBack,owned⟩ := requireOwned_refines metadata normalSound (onBase.trans sortKept)
      (owner.frame sortKept) success
    exact ⟨sortKept.trans ownerKept,ownerBack ∘ sortBack,converted,owned⟩
  · simp [discard] at success

private theorem inferReference_refines
    (metadata : BoxedFamilies env isBoxed) (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (owner : Represents state.arena original term)
    (success : (inferReference infer normal isBoxed state original).result = .ok answer)
    (ambient : Prefix (inferReference infer normal isBoxed state original).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.ref term) (inferReference infer normal isBoxed state original) answer := by
  unfold inferReference at success ambient ⊢
  obtain ⟨inferred,inferOk,inferNext⟩ := Outcome.next_success success
  rw [inferNext] at success ambient ⊢
  obtain ⟨⟨⟩,ownedOk,ownedNext⟩ := Outcome.next_success success
  rw [ownedNext] at success ambient ⊢
  obtain ⟨root,outputOk,outputNext⟩ := Outcome.next_success success
  rw [outputNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checked := checkOwnedType normal isBoxed (infer state original).state original inferred.typeRoot
  have ownedProgress := checkOwnedType_progress (state := (infer state original).state) (isBoxed := isBoxed)
    (original := original) (inferred := inferred.typeRoot) normalProgress
  have outputProgress := append_progress (limit := limit) checked.state (.universe 0) []
  obtain ⟨inferKept,inferBack,_,inferredRep,ownerTyped⟩ := childSound onBase room owner inferOk
    (ownedProgress.kept.trans (outputProgress.kept.trans ambient)) retained
  obtain ⟨ownedKept,ownedBack,sortConv,owned⟩ := checkOwnedType_refines metadata normalSound
    (onBase.trans inferKept) (owner.frame inferKept) inferredRep ownedOk
  obtain ⟨outputKept,outputBack,resultRep⟩ := append_refines .nil rfl outputOk
  refine ⟨inferKept.trans (ownedKept.trans outputKept),outputBack ∘ ownedBack ∘ inferBack,_,resultRep,?_⟩
  simpa only [Term.ref,Term.univ,expand,expandArgs] using LoanTyping.HasType.refOwned (ownerTyped.convert sortConv) owned

private theorem inferBorrow_refines
    (metadata : BoxedFamilies env isBoxed) (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (owner : Represents state.arena original term)
    (success : (inferBorrow infer normal isBoxed state original).result = .ok answer)
    (ambient : Prefix (inferBorrow infer normal isBoxed state original).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.borrow term) (inferBorrow infer normal isBoxed state original) answer := by
  unfold inferBorrow at success ambient ⊢
  obtain ⟨inferred,inferOk,inferNext⟩ := Outcome.next_success success
  rw [inferNext] at success ambient ⊢
  obtain ⟨⟨⟩,ownedOk,ownedNext⟩ := Outcome.next_success success
  rw [ownedNext] at success ambient ⊢
  obtain ⟨root,outputOk,outputNext⟩ := Outcome.next_success success
  rw [outputNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checked := requireOwned normal isBoxed (infer state original).state inferred.typeRoot original
  have ownedProgress := requireOwned_progress (state := (infer state original).state) (isBoxed := isBoxed)
    (root := inferred.typeRoot) (rejected := original) normalProgress
  have outputProgress := append_progress (limit := limit) checked.state .ref [inferred.typeRoot]
  obtain ⟨inferKept,inferBack,_,inferredRep,ownerTyped⟩ := childSound onBase room owner inferOk
    (ownedProgress.kept.trans (outputProgress.kept.trans ambient)) retained
  obtain ⟨ownedKept,ownedBack,owned⟩ :=
    requireOwned_refines metadata normalSound (onBase.trans inferKept) inferredRep ownedOk
  obtain ⟨outputKept,outputBack,resultRep⟩ := append_refines (.cons (inferredRep.frame ownedKept) .nil) rfl outputOk
  refine ⟨inferKept.trans (ownedKept.trans outputKept),outputBack ∘ ownedBack ∘ inferBack,_,resultRep,?_⟩
  simpa only [Term.borrow,Term.ref,expand,expandArgs] using LoanTyping.HasType.ghostBorrowOwned ownerTyped owned

private theorem inferDeref_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (reference : Represents state.arena original term)
    (success : (inferDeref infer normal state original).result = .ok answer)
    (ambient : Prefix (inferDeref infer normal state original).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.deref term) (inferDeref infer normal state original) answer := by
  unfold inferDeref at success ambient ⊢
  obtain ⟨inferred,inferOk,inferNext⟩ := Outcome.next_success success
  rw [inferNext] at success ambient ⊢
  obtain ⟨root,exposedOk,exposedNext⟩ := Outcome.next_success success
  rw [exposedNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  have targetProgress := referenceTarget_progress (state := (infer state original).state) (root := inferred.typeRoot)
    (rejected := original) normalProgress
  obtain ⟨inferKept,inferBack,_,inferredRep,referenceTyped⟩ :=
    childSound onBase room reference inferOk (targetProgress.kept.trans ambient) retained
  obtain ⟨targetKept,targetBack,_,targetRep,converted⟩ :=
    referenceTarget_refines normalSound (onBase.trans inferKept) inferredRep exposedOk
  refine ⟨inferKept.trans targetKept,targetBack ∘ inferBack,_,targetRep,?_⟩
  simpa only [Term.deref,expand,expandArgs] using LoanTyping.HasType.ghostDerefOwned (referenceTyped.convert converted)

private theorem readIndexType_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (source : Represents state.arena typeRoot type)
    (success : (readIndexType normal state subject typeRoot).result = .ok bound) :
    let after := (readIndexType normal state subject typeRoot).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ count, Represents after bound.1 count ∧ LoanTyping.Conversion.Conv env (expand env type)
        (if bound.2 then .ref (.buffer (expand env count)) else .array (expand env count)) := by
  unfold readIndexType at success ⊢
  obtain ⟨root,normalized,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,residual,held,changed⟩ := normalSound onBase source normalized
  split at success
  · rename_i length read
    simp only [Except.ok.injEq] at success
    subst bound
    obtain ⟨count,shape,countRep⟩ := unary_read held read
    exact ⟨kept,backward,count,countRep,
      by simpa only [shape,Term.array,expand,expandArgs,Bool.false_eq_true,ite_false] using changed.converted⟩
  · rename_i inner read
    obtain ⟨expanded,innerOk,innerNext⟩ := Outcome.next_success success
    rw [innerNext] at success ⊢
    obtain ⟨written,shape,innerRep⟩ := unary_read held read
    obtain ⟨innerKept,innerBack,innerResidual,innerHeld,innerChanged⟩ := normalSound (onBase.trans kept) innerRep innerOk
    split at success
    · rename_i length readBuffer
      simp only [Except.ok.injEq] at success
      subst bound
      obtain ⟨count,innerShape,countRep⟩ := unary_read innerHeld readBuffer
      have outerConv : LoanTyping.Conversion.Conv env (expand env type) (.ref (expand env written)) := by
        simpa only [shape,Term.ref,expand,expandArgs] using changed.converted
      have innerConv : LoanTyping.Conversion.Conv env (expand env written) (.buffer (expand env count)) := by
        simpa only [innerShape,Term.buffer,expand,expandArgs] using innerChanged.converted
      exact ⟨kept.trans innerKept,innerBack ∘ backward,count,countRep,
        outerConv.trans (.node .ref (.cons innerConv .nil))⟩
    · simp [discard] at success
  · simp [discard] at success

private theorem inferIndex_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (subjectRep : Represents state.arena subject x) (indexRep : Represents state.arena index i)
    (proofRep : Represents state.arena proof p)
    (success : (inferIndex infer normal limit depth state subject index proof).result = .ok answer)
    (ambient : Prefix (inferIndex infer normal limit depth state subject index proof).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.index x i p) (inferIndex infer normal limit depth state subject index proof) answer := by
  unfold inferIndex at success ambient ⊢
  obtain ⟨subjectType,subjectOk,subjectNext⟩ := Outcome.next_success success
  rw [subjectNext] at success ambient ⊢
  obtain ⟨bound,boundOk,boundNext⟩ := Outcome.next_success success
  rw [boundNext] at success ambient ⊢
  obtain ⟨indexPairs,indexOk,indexNext⟩ := Outcome.next_success success
  rw [indexNext] at success ambient ⊢
  obtain ⟨proofPairs,proofOk,proofNext⟩ := Outcome.next_success success
  rw [proofNext] at success ambient ⊢
  obtain ⟨result,outputOk,outputNext⟩ := Outcome.next_success success
  rw [outputNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checkedSubject := infer state subject
  let exposed := readIndexType normal checkedSubject.state subject subjectType.typeRoot
  let checkedIndex := checkFixed infer normal limit depth exposed.state .u64 [index]
  let checkedProof := checkIndexEvidence infer normal limit depth checkedIndex.state index bound.1 proof
  have subjectProgress := childProgress state subject room
  have subjectRoom := subjectProgress.accepted room subjectType subjectOk
  have exposure := readIndexType_progress (state := checkedSubject.state) (subject := subject)
    (typeRoot := subjectType.typeRoot) normalProgress
  have boundRoom := exposure.accepted subjectRoom bound boundOk
  have indexProgress := checkFixed_progress (state := exposed.state) (operand := .u64) (args := [index])
    (depth := depth) childProgress (fun state root _ => normalProgress state root) boundRoom
  have indexRoom := indexProgress.accepted boundRoom indexPairs indexOk
  have proofProgress := checkIndexEvidence_progress (state := checkedIndex.state) (index := index) (length := bound.1)
    (proof := proof) (depth := depth) childProgress normalProgress indexRoom
  have proofFinal := (append_progress (limit := limit) checkedProof.state .i64 []).kept.trans ambient
  have indexFinal := proofProgress.kept.trans proofFinal
  obtain ⟨subjectKept,subjectBack,_,subjectTypeRep,typedSubject⟩ := childSound onBase room subjectRep subjectOk
    (exposure.kept.trans (indexProgress.kept.trans indexFinal)) (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨exposedKept,exposedBack,_,lengthRep,decoded⟩ := readIndexType_refines normalSound
    (onBase.trans subjectKept) subjectTypeRep boundOk
  have throughType := subjectKept.trans exposedKept
  obtain ⟨indexKept,indexBack,typedIndex⟩ := checkFixed_refines normalSound normalProgress childSound childProgress
    (onBase.trans throughType) boundRoom (.cons (indexRep.frame throughType) .nil) rfl indexOk indexFinal
    (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
  have throughIndex := throughType.trans indexKept
  obtain ⟨proofKept,proofBack,typedProof⟩ := checkIndexEvidence_refines normalSound normalProgress childSound childProgress
    (onBase.trans throughIndex) indexRoom (indexRep.frame throughIndex) (lengthRep.frame indexKept)
    (proofRep.frame throughIndex) proofOk proofFinal (fun pair member => retained pair (List.mem_append_right _
      (List.mem_append_right _ member)))
  obtain ⟨outputKept,outputBack,resultRep⟩ := append_refines .nil rfl outputOk
  refine ⟨throughIndex.trans (proofKept.trans outputKept),outputBack ∘ proofBack ∘ indexBack ∘ exposedBack ∘ subjectBack,
    _,resultRep,?_⟩
  simp only [expand,expandArgs] at typedIndex
  simp only [Term.index,expand,expandArgs]
  cases reference : bound.2
  · simp only [reference,Bool.false_eq_true,ite_false] at decoded
    exact .index (typedSubject.convert decoded) (typedIndex i List.mem_cons_self) typedProof
  · simp only [reference,ite_true] at decoded
    exact .borrowedIndex (typedSubject.convert decoded) (typedIndex i List.mem_cons_self) typedProof

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
    ∃ p, type = .refine p ∧ Represents arena predicate p := unary_read represented read

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

private theorem exposeImpossibleBound_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (represented : Represents state.arena typeRoot type)
    (success : (exposeImpossibleBound normal state proof typeRoot).result = .ok ()) :
    let after := (exposeImpossibleBound normal state proof typeRoot).state.arena
    ∃ left, Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.Conversion.Conv env (expand env type) (.lt (expand env left) (.natural 0)) := by
  unfold exposeImpossibleBound at success ⊢
  obtain ⟨inequality,exposedOk,exposedNext⟩ := Outcome.next_success success
  rw [exposedNext] at success ⊢
  split at success
  case h_2 => simp [discard] at success
  case h_1 left upper read =>
    obtain ⟨top,upperOk,upperNext⟩ := Outcome.next_success success
    rw [upperNext] at success ⊢
    split at success
    case h_2 => simp [discard] at success
    case h_1 readZero =>
      obtain ⟨kept,backward,residual,held,changed⟩ := normalSound onBase represented exposedOk
      obtain ⟨a,b,shape,_,rightRep⟩ := binary_read held read
      obtain ⟨upperKept,upperBack,_,topRep,upperChanged⟩ := normalSound (onBase.trans kept) rightRep upperOk
      have zero : LoanTyping.Conversion.Conv env (expand env b) (.natural 0) := by
        have written := topRep.unique (Represents.node readZero rfl .nil)
        simpa only [written,Term.natural,expand,expandArgs] using upperChanged.converted
      have inequality : LoanTyping.Conversion.Conv env (expand env type) (.lt (expand env a) (expand env b)) := by
        simpa only [shape,Term.lt,expand,expandArgs] using changed.converted
      exact ⟨a,kept.trans upperKept,upperBack ∘ backward,
        inequality.trans (.node .lt (.cons (.refl _) (.cons zero .nil)))⟩

private theorem inferAbsurd_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (targetRep : Represents state.arena target t) (proofRep : Represents state.arena proof p)
    (success : (inferAbsurd infer normal state target proof).result = .ok answer)
    (ambient : Prefix (inferAbsurd infer normal state target proof).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.absurd t p) (inferAbsurd infer normal state target proof) answer := by
  unfold inferAbsurd at success ambient ⊢
  obtain ⟨targetTy,targetOk,targetNext⟩ := Outcome.next_success success
  rw [targetNext] at success ambient ⊢
  obtain ⟨sort,sortOk,sortNext⟩ := Outcome.next_success success
  rw [sortNext] at success ambient ⊢
  obtain ⟨proofTy,proofOk,proofNext⟩ := Outcome.next_success success
  rw [proofNext] at success ambient ⊢
  obtain ⟨_,impossibleOk,impossibleNext⟩ := Outcome.next_success success
  rw [impossibleNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let targetCheck := infer state target
  let sortCheck := NativeCoreGhostSort.sort normal targetCheck.state targetTy.typeRoot
  let proofCheck := infer sortCheck.state proof
  have targetProgress := childProgress state target room
  have targetRoom := targetProgress.accepted room targetTy targetOk
  have sortProgress := NativeCoreGhostSort.sort_progress (state := targetCheck.state)
    (typeRoot := targetTy.typeRoot) normalProgress
  have sortRoom := sortProgress.accepted targetRoom sort sortOk
  have proofProgress := childProgress sortCheck.state proof sortRoom
  have boundProgress := exposeImpossibleBound_progress (state := proofCheck.state)
    (proof := proof) (typeRoot := proofTy.typeRoot) normalProgress
  have proofFinal := boundProgress.kept.trans ambient
  obtain ⟨targetKept,targetBack,_,heldTarget,targetTyped⟩ := childSound onBase room targetRep targetOk
    (sortProgress.kept.trans (proofProgress.kept.trans proofFinal))
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨sortKept,sortBack,targetSort⟩ := NativeCoreGhostSort.sort_refines normalSound
    (onBase.trans targetKept) heldTarget sortOk
  have throughSort := targetKept.trans sortKept
  obtain ⟨proofKept,proofBack,_,heldProof,proofTyped⟩ := childSound (onBase.trans throughSort) sortRoom
    (proofRep.frame throughSort) proofOk proofFinal (fun pair member => retained pair (List.mem_append_right _ member))
  have throughProof := throughSort.trans proofKept
  obtain ⟨_,boundKept,boundBack,impossible⟩ := exposeImpossibleBound_refines normalSound
    (onBase.trans throughProof) heldProof impossibleOk
  have kept := throughProof.trans boundKept
  refine ⟨kept,boundBack ∘ proofBack ∘ sortBack ∘ targetBack,_,targetRep.frame kept,?_⟩
  simp only [Term.absurd,expand,expandArgs]
  exact .absurd (targetTyped.convert targetSort) (proofTyped.convert impossible) (Or.inl rfl)

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
theorem runVisits_sound {normal : NormalAt}
    (metadata : DataFamilies env isData) (boxedMetadata : BoxedFamilies env isBoxed)
    (familyMetadata : FamilyShapeTable env shapeTable)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (constructorMetadata : NativeCoreGhostConstructorInference.ConstructorTable env base constructorRoots)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    InferSound env base ctx limit (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth bindings) := by
  induction visits generalizing depth base bindings ctx with
  | zero =>
      intro state root term answer final _ _ _ success _ _
      simp only [runVisits] at success
      have entered := (tick_success success).1
      rw [entered] at success
      exact False.elim (by simp [discard] at success)
  | succ visits ih =>
    cases depth with
    | zero =>
      intro state root term answer final _ _ _ success _ _
      by_cases exhausted : limit < state.steps + 1 <;>
        simp [runVisits, tick, NativeCoreUnsignedCancellation.tick, exhausted] at success
    | succ depth =>
      have child {later nextRows nextCtx nextDepth} (kept : Prefix base later) (represented : ContextRep env later nextRows nextCtx) :
          InferSound env later nextCtx limit (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits nextDepth nextRows) :=
        ih (constructorMetadata.frame kept) (NativeCoreNestedAliases.frame_definitions aligned kept) represented
          (fun d _ _ _ _ extension source success => normalSound d (kept.trans extension) source success)
      have sameContext : InferSound env base ctx limit (runVisits normal roots visible limit isData isBoxed shapeTable constructorRoots visits depth bindings) :=
        child (.refl _) context
      intro state root term answer final onBase room source success ambient retained
      simp only [runVisits] at success ambient ⊢
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
          case elim | view | caseOf =>
            simp only [discard, reduceCtorEq] at success
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
                (fun _ _ budget => runVisits_progress normalProgress budget)
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
                (fun _ _ budget => runVisits_progress normalProgress budget)
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
                (fun _ _ budget => runVisits_progress normalProgress budget)
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
                  (fun _ _ budget => runVisits_progress normalProgress budget)
                  onBase within childRep success ambient retained
              | exact inferRefinementProjection_refines (state := {state with steps := state.steps + 1})
                  (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runVisits_progress normalProgress budget)
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
                    (fun _ _ budget => runVisits_progress normalProgress budget)
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
                    (fun _ _ budget => runVisits_progress normalProgress budget)
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
                    (fun _ _ budget => runVisits_progress normalProgress budget)
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
                  (fun _ _ budget => runVisits_progress normalProgress budget)
                  onBase within (.cons first (.cons second .nil)) rfl .nil rfl success ambient retained
                intro typed
                simp only [expand, expandArgs] at typed ⊢
                have left := typed _ List.mem_cons_self
                have right := typed _ (List.mem_cons_of_mem _ List.mem_cons_self)
                first | exact .eq left right | exact .lt left right | exact .uadd left right | exact .arith left right
          case con family constructor count =>
            have length := context.length_eq
            rw [length] at success ambient ⊢
            exact NativeCoreGhostConstructorInference.runSelected_refines
              (state := {state with steps := state.steps + 1}) (depth := depth)
              history.wellFormed constructorMetadata (normalSound depth) (normalProgress depth) sameContext
              (fun _ _ budget => runVisits_progress normalProgress budget)
              onBase within children arity success ambient retained
          case ind family count =>
            exact inferFamily_refines (state := {state with steps := state.steps + 1}) familyMetadata
              (normalSound indexCheckDepth) (normalProgress indexCheckDepth) (child (.refl _) context)
              (fun _ _ budget => runVisits_progress normalProgress budget)
              onBase within children success ambient retained
          case elements count =>
            exact inferElements_refines (state := {state with steps := state.steps + 1}) (depth := depth)
              (normalSound depth) (normalProgress depth) sameContext
              (fun _ _ budget => runVisits_progress normalProgress budget)
              onBase within children success ambient retained
          case alloc =>
            have length : refs.length = 2 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp at length
            cases children with
            | cons countRep rest =>
              cases rest with
              | cons fillRep tail =>
                cases tail
                dsimp only at success ambient ⊢
                exact inferAlloc_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                  (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runVisits_progress normalProgress budget)
                  onBase within countRep fillRep success ambient retained
          case drop family =>
            have length : refs.length = 2 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp at length
            cases children with
            | cons ownerRep rest =>
              cases rest with
              | cons tailRep tail =>
                cases tail
                dsimp only at success ambient ⊢
                exact inferDrop_refines (state := {state with steps := state.steps + 1})
                  boxedMetadata (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runVisits_progress normalProgress budget)
                  onBase within ownerRep tailRep success ambient retained
          case free =>
            have length : refs.length = 2 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp at length
            cases children with
            | cons bufferRep rest =>
              cases rest with
              | cons tailRep tail =>
                cases tail
                dsimp only at success ambient ⊢
                exact inferFree_refines (state := {state with steps := state.steps + 1})
                  (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runVisits_progress normalProgress budget)
                  onBase within bufferRep tailRep success ambient retained
          case load =>
            have length : refs.length = 4 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons bufferRep rest =>
              cases rest with
              | cons indexRep rest =>
                cases rest with
                | cons proofRep rest =>
                  cases rest with
                  | cons continuationRep tail =>
                    cases tail
                    dsimp only at success ambient ⊢
                    exact inferLoad_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                      history.wellFormed (normalSound depth) (normalProgress depth) sameContext
                      (fun _ _ budget => runVisits_progress normalProgress budget)
                      onBase within bufferRep indexRep proofRep continuationRep success ambient retained
          case back erased =>
            have length : refs.length = 2 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp at length
            cases children with
            | cons ownerRep tail =>
              cases tail with
              | cons motiveRep tail =>
                cases tail
                dsimp only at success ambient ⊢
                exact NativeCoreGhostOwnerReturns.runBack_refines (state := {state with steps := state.steps + 1})
                  boxedMetadata (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runVisits_progress normalProgress budget)
                  onBase within ownerRep motiveRep success ambient retained
          case give erased =>
            have length : refs.length = 3 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons motiveRep tail =>
              cases tail with
              | cons ownerRep tail =>
                cases tail with
                | cons resultRep tail =>
                  cases tail
                  dsimp only at success ambient ⊢
                  exact NativeCoreGhostOwnerReturns.runGive_refines (state := {state with steps := state.steps + 1})
                    boxedMetadata (normalSound depth) (normalProgress depth) sameContext
                    (fun _ _ budget => runVisits_progress normalProgress budget)
                    onBase within motiveRep ownerRep resultRep success ambient retained
          case take =>
            have length : refs.length = 2 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp at length
            cases children with
            | cons subjectRep tail =>
              cases tail with
              | cons continuationRep tail =>
                cases tail
                dsimp only at success ambient ⊢
                exact NativeCoreGhostTakeInference.run_refines (state := {state with steps := state.steps + 1})
                  history.wellFormed (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runVisits_progress normalProgress budget)
                  onBase within subjectRep continuationRep success ambient retained
          case fold =>
            have length : refs.length = 3 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons countRep tail =>
              cases tail with
              | cons initialRep tail =>
                cases tail with
                | cons bodyRep tail =>
                  cases tail
                  dsimp only at success ambient ⊢
                  exact NativeCoreGhostFoldInference.runWith_refines (state := {state with steps := state.steps + 1})
                    history.wellFormed boxedMetadata (normalSound depth) (normalProgress depth) sameContext
                    (fun _ _ budget => runVisits_progress normalProgress budget)
                    onBase within countRep initialRep bodyRep success ambient retained
          case loop =>
            have length : refs.length = 4 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons countRep tail =>
              cases tail with
              | cons motiveRep tail =>
                cases tail with
                | cons initialRep tail =>
                  cases tail with
                  | cons bodyRep tail =>
                    cases tail
                    dsimp only at success ambient ⊢
                    exact NativeCoreGhostLoopInference.run_refines (state := {state with steps := state.steps + 1})
                      history.wellFormed (normalSound depth) (normalProgress depth) sameContext
                      (fun _ _ budget => runVisits_progress normalProgress budget)
                      onBase within countRep motiveRep initialRep bodyRep success ambient retained
          case lend =>
            have length : refs.length = 3 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons ownerRep tail =>
              cases tail with
              | cons readerRep tail =>
                cases tail with
                | cons contRep tail =>
                  cases tail
                  dsimp only at success ambient ⊢
                  exact NativeCoreGhostLendInference.run_refines (state := {state with steps := state.steps + 1})
                    history.wellFormed metadata boxedMetadata (normalSound depth) (normalProgress depth) sameContext
                    (fun _ _ budget => runVisits_progress normalProgress budget)
                    onBase within ownerRep readerRep contRep success ambient retained
          case ref | borrow | deref =>
            have length : refs.length = 1 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> simp at length
            cases children with
            | cons childRep tail =>
              cases tail
              dsimp only at success ambient ⊢
              first
              | exact inferReference_refines (state := {state with steps := state.steps + 1}) boxedMetadata
                  (normalSound depth) (normalProgress depth) sameContext
                  onBase within childRep success ambient retained
              | exact inferBorrow_refines (state := {state with steps := state.steps + 1}) boxedMetadata
                  (normalSound depth) (normalProgress depth) sameContext
                  onBase within childRep success ambient retained
              | exact inferDeref_refines (state := {state with steps := state.steps + 1})
                  (normalSound depth) (normalProgress depth) sameContext
                  onBase within childRep success ambient retained
          case index =>
            have length : refs.length = 3 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons subjectRep rest =>
              cases rest with
              | cons indexRep rest =>
                cases rest with
                | cons proofRep tail =>
                  cases tail
                  dsimp only at success ambient ⊢
                  exact inferIndex_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                    (normalSound depth) (normalProgress depth) sameContext
                    (fun _ _ budget => runVisits_progress normalProgress budget)
                    onBase within subjectRep indexRep proofRep success ambient retained
          case store =>
            have length : refs.length = 4 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at length
            cases children with
            | cons bufferRep rest =>
              cases rest with
              | cons indexRep rest =>
                cases rest with
                | cons valueRep rest =>
                  cases rest with
                  | cons proofRep tail =>
                    cases tail
                    dsimp only at success ambient ⊢
                    exact inferStore_refines (state := {state with steps := state.steps + 1}) (depth := depth)
                      (normalSound depth) (normalProgress depth) sameContext
                      (fun _ _ budget => runVisits_progress normalProgress budget)
                      onBase within bufferRep indexRep valueRep proofRep success ambient retained
          case absurd =>
            have length : refs.length = 2 := arity
            rcases refs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp at length
            cases children with
            | cons targetRep rest =>
              cases rest with
              | cons proofRep tail =>
                cases tail
                dsimp only at success ambient ⊢
                exact inferAbsurd_refines (state := {state with steps := state.steps + 1})
                  (normalSound depth) (normalProgress depth) sameContext
                  (fun _ _ budget => runVisits_progress normalProgress budget)
                  onBase within targetRep proofRep success ambient retained
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
                    (fun _ _ budget => runVisits_progress normalProgress budget)
                    onBase within first second success ambient retained
                | exact inferStrict_refines (state := {state with steps := state.steps + 1}) sameContext
                    (fun _ _ budget => runVisits_progress normalProgress budget)
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
                      (fun _ _ budget => runVisits_progress normalProgress budget)
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
                        (fun _ _ budget => runVisits_progress normalProgress budget)
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
                      (fun _ _ budget => runVisits_progress normalProgress budget) ?_
                      (fun _ _ _ budget => runVisits_progress normalProgress budget)
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
                  (fun _ _ budget => runVisits_progress normalProgress budget) ?_
                  (fun _ _ budget => runVisits_progress normalProgress budget)
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
                    (fun _ _ budget => runVisits_progress normalProgress budget)
                    onBase within fn arg success ambient retained

theorem runWithConstructors_sound {normal : NormalAt}
    (metadata : DataFamilies env isData) (boxedMetadata : BoxedFamilies env isBoxed)
    (familyMetadata : FamilyShapeTable env shapeTable)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (constructorMetadata : NativeCoreGhostConstructorInference.ConstructorTable env base constructorRoots)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    InferSound env base ctx limit (runWithConstructors normal roots visible limit isData isBoxed shapeTable constructorRoots depth bindings) := by
  intro state root term answer final onBase room source success ambient retained
  exact runVisits_sound metadata boxedMetadata familyMetadata history constructorMetadata aligned context normalProgress normalSound
    onBase room source success ambient retained

theorem runWithFamilyShapes_sound {normal : NormalAt}
    (metadata : DataFamilies env isData) (boxedMetadata : BoxedFamilies env isBoxed)
    (familyMetadata : FamilyShapeTable env shapeTable)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    InferSound env base ctx limit (runWithFamilyShapes normal roots visible limit isData isBoxed shapeTable depth bindings) :=
  runWithConstructors_sound metadata boxedMetadata familyMetadata history
    (fun _ _ _ impossible => by cases impossible) aligned context normalProgress normalSound

theorem runWithFamilyKinds_sound {normal : NormalAt}
    (metadata : DataFamilies env isData) (boxedMetadata : BoxedFamilies env isBoxed)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    InferSound env base ctx limit (runWithFamilyKinds normal roots visible limit isData isBoxed depth bindings) :=
  runWithFamilyShapes_sound metadata boxedMetadata (fun _ _ _ impossible => by cases impossible)
    history aligned context normalProgress normalSound

theorem runWithData_sound {normal : NormalAt}
    (metadata : DataFamilies env isData)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    InferSound env base ctx limit (runWithData normal roots visible limit isData depth bindings) :=
  runWithFamilyKinds_sound metadata (fun _ found => by cases found) history aligned context normalProgress normalSound

theorem runWith_sound {normal : NormalAt}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    InferSound env base ctx limit (runWith normal roots visible limit depth bindings) :=
  runWithData_sound (fun _ found => by cases found) history aligned context normalProgress normalSound

private theorem literal_normal_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) :
    VisitsFrom base (ExpandedNormalization env) (NativeCoreGhostLiteralAddition.run roots visible limit depth) := by
  intro state ref term selected onBase source success
  obtain ⟨kept, backward, result⟩ := NativeCoreGhostLiteralAddition.run_refines history aligned onBase source success
  exact ⟨kept, backward, result⟩

theorem run_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx) :
    InferSound env base ctx limit (run roots visible limit depth bindings) :=
  runWith_sound history aligned context (NativeCoreGhostLiteralAddition.run_progress roots visible limit)
    (fun _ => literal_normal_sound history aligned)

def CheckedInferences (snapshot : NativeFamilyWire.Snapshot) (env : Environment)
    (normalize : Nat → Nat → NormalAt) : Prop :=
  ∀ {index limit depth initial : Nat} {row : Roots},
    snapshot.definitions[index]? = some row →
    let start : State := ⟨snapshot.arena, initial⟩
    let output := runWithConstructors (normalize index limit) snapshot.definitions index limit
      (NativeCoreGhostSort.isDataAt env) (isBoxedAt env) (visibleFamilyShape env index)
      (NativeCoreGhostConstructorInference.constructorAt snapshot.families index) depth [] start row.valueRoot
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
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, valid, aligned, familyGraph, history, wf⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial row found start output room
  refine ⟨runWithConstructors_progress (metered env snapshot index limit) room, ?_⟩
  intro answer success retained
  obtain ⟨entry, raw, recorded, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  obtain ⟨kept, forwards, inferred, held, inferredTyped⟩ :=
    runWithConstructors_sound (NativeCoreGhostSort.isDataAt_sound env) (isBoxedAt_sound env)
      (visibleFamilyShape_sound env index) history
      (NativeCoreGhostConstructorInference.constructorAt_sound history familyGraph index) aligned .nil
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
      CheckedInferences snapshot env (NativeCoreGhostLiteralAddition.run snapshot.definitions) :=
  admitted_program_infers_with (fun _ snapshot => NativeCoreGhostLiteralAddition.run snapshot.definitions)
    (fun _ snapshot => NativeCoreGhostLiteralAddition.run_progress snapshot.definitions)
    (fun history aligned _ _ _ => literal_normal_sound history aligned) admitted

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
built. The recursive normalizer folds the literal upper bound's successor
while checking the second proof and retains the original result endpoints. -/
theorem admitted_transitive_proof_keeps_ordered_bounds :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot transitiveSnapshot) = true ∧
    run transitiveSnapshot.definitions 0 13 24 [] ⟨transitiveSnapshot.arena, 0⟩ 6 =
      ⟨⟨transitiveSnapshot.arena ++ #[.node .u64 [], .node .u64 [], .node .u64 [], .node .u64 [],
        .node (.natural 1) [], .node .uadd [2, 12], .node .lt [0, 1], .node .lt [1, 13]], 14⟩,
        .error (.tick (.stepLimit 4))⟩ ∧
    (let finished := run transitiveSnapshot.definitions 0 96 24 [] ⟨transitiveSnapshot.arena, 0⟩ 6
     finished.state.steps = 57 ∧ finished.state.arena.size = 27 ∧
       finished.result.map Inferred.typeRoot = .ok 26 ∧ finished.state.arena[26]? = some (.node .lt [0, 2])) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def absurdSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨6,5⟩]
  families := []
  arena := #[.node (.natural 0) [], .node .lt [0,0], .node .u64 [], .var 0,
    .node .absurd [2,3], .node (.lam true) [1,4], .node (.pi true) [1,2]]

/-- The closed function is admitted with an erased impossible hypothesis.
Its body checks the target sort, then exposes and normalizes the inequality's
upper endpoint. It returns the original target reference. -/
theorem admitted_absurd_infers_original_target :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot absurdSnapshot) = true ∧
    (let finished := run absurdSnapshot.definitions 0 24 24 [⟨1,true⟩] ⟨absurdSnapshot.arena,0⟩ 4
     finished.state.steps = 11 ∧ finished.result.map Inferred.typeRoot = .ok 2) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def arraySnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨4,2⟩]
  families := []
  arena := #[.node (.integer 3) [],.node (.integer (-4)) [],.node (.elements 2) [0,1],
    .node (.natural 2) [],.node .array [3]]

/-- The native array length is appended only after all elements check. -/
theorem admitted_array_inference_checks_elements_before_length :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot arraySnapshot) = true ∧
    run arraySnapshot.definitions 0 5 20 [] ⟨arraySnapshot.arena,0⟩ 2 =
      ⟨⟨arraySnapshot.arena ++ #[.node .i64 [],.node .i64 []],6⟩,
        .error (.tick (.stepLimit 1))⟩ ∧
    (let output := run arraySnapshot.definitions 0 9 20 [] ⟨arraySnapshot.arena,0⟩ 2
     output.result.map Inferred.typeRoot = .ok 9 ∧ output.state.arena[9]? = some (.node .array [8])) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def allocationSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨3,2⟩]
  families := []
  arena := #[.node (.natural 2) [],.node (.integer (-7)) [],.node .alloc [0,1],.node .buffer [0]]

/-- The allocation checks the word count before the signed fill and writes
the original count under Buffer. -/
theorem admitted_allocation_inference_keeps_original_count :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot allocationSnapshot) = true ∧
    run allocationSnapshot.definitions 0 9 20 [] ⟨allocationSnapshot.arena,0⟩ 2 =
      ⟨⟨allocationSnapshot.arena ++ #[.node .u64 [],.node .u64 [],.node .i64 [],.node .i64 [],.node .buffer [0]],9⟩,
        .ok ⟨8,[(5,4),(7,6)]⟩⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def bufferOperationsSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨8,5⟩,⟨9,7⟩]
  families := []
  arena := #[.node (.natural 2) [],.node (.natural 0) [],.node (.integer (-7)) [],.node .alloc [0,2],
    .node .decide [1,0],.node .store [3,1,2,4],.node (.natural 9) [],.node .free [5,6],
    .node .buffer [0],.node .u64 []]

/-- Store exposes the actual buffer length, then establishes its index proof.
Free checks the same owned value before returning the checked tail type. -/
theorem admitted_buffer_operations_infer_original_lengths :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot bufferOperationsSnapshot) = true ∧
    (let halted := run bufferOperationsSnapshot.definitions 0 20 32 [] ⟨bufferOperationsSnapshot.arena,0⟩ 5
     halted.state.steps = 21 ∧ halted.result = .error (.tick (.stepLimit 4)) ∧
       halted.state.arena.size = 20 ∧ halted.state.arena[19]? = some (.node .lt [1,0])) ∧
    (let stored := run bufferOperationsSnapshot.definitions 0 40 32 [] ⟨bufferOperationsSnapshot.arena,0⟩ 5
     stored.state.steps = 40 ∧ stored.result.map Inferred.typeRoot = .ok 24 ∧
       stored.state.arena[24]? = some (.node .buffer [0])) ∧
    (let released := run bufferOperationsSnapshot.definitions 0 44 32 [] ⟨bufferOperationsSnapshot.arena,0⟩ 7
     released.state.steps = 44 ∧ released.result.map Inferred.typeRoot = .ok 25 ∧
       released.state.arena[25]? = some (.node .u64 [])) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def indexSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨11,6⟩,⟨13,12⟩]
  families := []
  arena := #[.node (.natural 2) [],.node (.natural 1) [],.node (.integer 3) [],.node (.integer (-4)) [],
    .node (.elements 2) [2,3],.node .decide [1,0],.node .index [4,1,5],.node .buffer [0],.node .ref [7],
    .var 0,.node .index [9,1,5],.node .i64 [],.node (.lam false) [8,10],.node (.pi false) [8,11]]

/-- Indexing a newly constructed array uses its emitted length. Indexing a
borrow normalizes the inner buffer type separately before forming the proof. -/
theorem admitted_array_and_borrowed_index_infer_signed_result :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot indexSnapshot) = true ∧
    (let array := run indexSnapshot.definitions 0 36 32 [] ⟨indexSnapshot.arena,0⟩ 6
     array.state.steps = 36 ∧ array.result.map Inferred.typeRoot = .ok 26 ∧
       array.state.arena[21]? = some (.node .lt [1,17]) ∧ array.state.arena[26]? = some (.node .i64 [])) ∧
    (let borrowed := run indexSnapshot.definitions 0 34 32 [⟨8,false⟩] ⟨indexSnapshot.arena,0⟩ 10
     borrowed.state.steps = 34 ∧ borrowed.result.map Inferred.typeRoot = .ok 21 ∧
       borrowed.state.arena[16]? = some (.node .lt [1,0]) ∧ borrowed.state.arena[21]? = some (.node .i64 [])) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def loadSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨17,15⟩]
  families := []
  arena := #[.node (.natural 0) [],.node .u64 [],.node .i64 [],.var 0,.node .lt [0,3],.var 1,
    .node (.integer (-7)) [],.node .alloc [5,6],.var 2,.node .buffer [8],.node .free [3,5],
    .node (.lam false) [9,10],.node (.lam false) [2,11],.node .load [7,0,3,12],
    .node (.lam true) [4,13],.node (.lam false) [1,14],.node (.pi true) [4,2],.node (.pi false) [1,16]]

/-- Load shifts the original open length into the callback before checking the
new owner domain. The callback result survives lowering past both binders. -/
theorem admitted_load_checks_dependent_callback :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot loadSnapshot) = true ∧
    (let stopped := run loadSnapshot.definitions 0 66 32 [⟨4,true⟩,⟨1,false⟩] ⟨loadSnapshot.arena,0⟩ 13
     stopped.state.steps = 67 ∧ stopped.state.arena.size = 37 ∧
       stopped.result = .error (.substitution (.tick (.stepLimit 2)))) ∧
    (let completed := run loadSnapshot.definitions 0 67 32 [⟨4,true⟩,⟨1,false⟩] ⟨loadSnapshot.arena,0⟩ 13
     completed.state.steps = 67 ∧ completed.state.arena.size = 37 ∧
       completed.state.arena[24]? = some (.node .lt [0,5]) ∧
       completed.state.arena[35]? = some (.var 2) ∧ completed.state.arena[36]? = some (.node .buffer [35]) ∧
       completed.result.map Inferred.typeRoot = .ok 2) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def referencesSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨7,3⟩]
  families := []
  arena := #[.node (.natural 2) [],.node (.integer (-7)) [],.node .buffer [0],.node .ref [2],
    .node .alloc [0,1],.node .borrow [4],.node .deref [5],.node (.universe 0) []]

/-- Ref checks its sort and ownership. Borrow retains the inferred type root
and Deref exposes that root without allocating a new buffer type. -/
theorem admitted_buffer_reference_graph :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot referencesSnapshot) = true ∧
    (let form := run referencesSnapshot.definitions 0 9 32 [] ⟨referencesSnapshot.arena,0⟩ 3
     form.state.steps = 9 ∧ form.result.map Inferred.typeRoot = .ok 11) ∧
    (let loan := run referencesSnapshot.definitions 0 12 32 [] ⟨referencesSnapshot.arena,0⟩ 5
     loan.state.steps = 12 ∧ loan.result.map Inferred.typeRoot = .ok 13 ∧
       loan.state.arena[13]? = some (.node .ref [12])) ∧
    (let read := run referencesSnapshot.definitions 0 16 32 [] ⟨referencesSnapshot.arena,0⟩ 6
     read.state.steps = 16 ∧ read.result.map Inferred.typeRoot = .ok 12 ∧
       read.state.arena[12]? = some (.node .buffer [0])) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def familyReferenceSnapshot (recursive : Bool) : NativeFamilyWire.Snapshot where
  definitions := []
  families := [⟨true,0,0,0,[1,3]⟩]
  arena := #[.node (.natural 0) [],.node (.ind 0 0) [],.node .u64 [],
    .node (.pi false) [if recursive then 1 else 2,1],.var 0,.node .borrow [4],.node .deref [5],
    .node .u64 [],.node .u64 [],.node .u64 []]

private def referenceEnvironment (recursive : Bool) : Option Environment := do
  let (definitions,families) ← NativeFamilyWire.decodeProgram (familyReferenceSnapshot recursive)
  LoanTyping.MixedProgram.checkProgram 64 128 definitions (families.map NativeLoanMixedAdmission.declaration)

/-- The checked recursive family permits a ghost borrow and retains its
original type. A checked flat family with the same arity rejects that borrow. -/
theorem admitted_family_reference_metadata :
    let boxed := (referenceEnvironment true).getD empty
    let flat := (referenceEnvironment false).getD empty
    let boxedSnapshot := familyReferenceSnapshot true
    let flatSnapshot := familyReferenceSnapshot false
    let borrowed := runWithFamilyKinds (NativeCoreExpandedFamilies.raw boxed boxedSnapshot.families [] 0 7)
      [] 0 7 (NativeCoreGhostSort.isDataAt boxed) (isBoxedAt boxed) 32 [⟨1,false⟩] ⟨boxedSnapshot.arena,0⟩ 6
    let rejected := runWithFamilyKinds (NativeCoreExpandedFamilies.raw flat flatSnapshot.families [] 0 4)
      [] 0 4 (NativeCoreGhostSort.isDataAt flat) (isBoxedAt flat) 32 [⟨1,false⟩] ⟨flatSnapshot.arena,0⟩ 5
    referenceEnvironment true = some boxed ∧ referenceEnvironment false = some flat ∧
      isBoxedAt boxed 0 = true ∧ isBoxedAt flat 0 = false ∧
      borrowed.state.steps = 7 ∧ borrowed.state.arena[10]? = some (.node .ref [1]) ∧
      borrowed.result.map Inferred.typeRoot = .ok 1 ∧
      rejected.state.steps = 4 ∧ rejected.state.arena = flatSnapshot.arena ∧
      rejected.result = .error (.outsideFragment 4) := by
  cbv

private def indexedFamilySnapshot (data : Bool) : NativeFamilyWire.Snapshot where
  definitions := []
  families := [⟨data,0,1,0,[1]⟩]
  arena := #[.node (.natural 0) [],.node (.ind 0 1) [0],.node (.ind 0 0) [],.node .u64 [],.node .u64 []]

private def indexedFamilyEnvironment (data : Bool) : Option Environment := do
  let (definitions,families) ← NativeFamilyWire.decodeProgram (indexedFamilySnapshot data)
  LoanTyping.MixedProgram.checkProgram 64 128 definitions (families.map NativeLoanMixedAdmission.declaration)

/-- An outer inference depth of one still checks the family index at the
compiler's fixed depth. The same arena walk yields Prop or Type0 according
to the actually checked family declaration. -/
theorem admitted_family_indices_use_fixed_depth :
    ∀ data : Bool,
      let env := (indexedFamilyEnvironment data).getD empty
      let snapshot := indexedFamilySnapshot data
      let formed := runWithFamilyShapes (NativeCoreExpandedFamilies.raw env snapshot.families [] 0 5)
        [] 0 5 (NativeCoreGhostSort.isDataAt env) (isBoxedAt env) (visibleFamilyShape env 0) 1 [] ⟨snapshot.arena,0⟩ 1
      let wrong := runWithFamilyShapes (NativeCoreExpandedFamilies.raw env snapshot.families [] 0 1)
        [] 0 1 (NativeCoreGhostSort.isDataAt env) (isBoxedAt env) (visibleFamilyShape env 0) 1 [] ⟨snapshot.arena,0⟩ 2
      indexedFamilyEnvironment data = some env ∧
      visibleFamilyShape env 0 0 = some (1,data) ∧
      formed.state.steps = 5 ∧ formed.state.arena.size = 8 ∧
      formed.result.map Inferred.typeRoot = .ok 7 ∧
      formed.state.arena[7]? = some (.node (if data then .universe 0 else .prop) []) ∧
      wrong.state.steps = 1 ∧ wrong.state.arena = snapshot.arena ∧ wrong.result = .error (.outsideFragment 2) := by
  intro data
  cases data <;> cbv

private def dropSnapshot (recursive : Bool) : NativeFamilyWire.Snapshot :=
  let reference := familyReferenceSnapshot recursive
  { reference with arena := reference.arena ++ #[.node (.integer (-3)) [],.node (.drop 0) [4,10]] }

private def dropVisit (recursive : Bool) (limit : Nat) : Outcome Inferred :=
  let env := (referenceEnvironment recursive).getD empty
  let snapshot := dropSnapshot recursive
  let normal := NativeCoreExpandedFamilies.raw env snapshot.families [] 0 limit
  runWithConstructors normal [] 0 limit (NativeCoreGhostSort.isDataAt env) (isBoxedAt env)
    (visibleFamilyShape env 0) (NativeCoreGhostConstructorInference.constructorAt snapshot.families 0)
    32 [⟨1,false⟩] ⟨snapshot.arena,0⟩ 11

/-- Drop consults the boxed layout before the owner is visited. A typed
boxed family releases its owner and preserves the tail's I64 type. -/
theorem admitted_boxed_drop_checks_owner_and_tail :
    (let released := dropVisit true 5
     released.state.steps = 5 ∧ released.result.map Inferred.typeRoot = .ok 12 ∧
       released.state.arena[12]? = some (.node .i64 [])) ∧
    dropVisit false 1 =
      ⟨⟨(dropSnapshot false).arena,1⟩,.error (.outsideFragment 11)⟩ := by cbv

end Examples

end Jihoo.NativeKernel.NativeCoreGhostSpineInference
