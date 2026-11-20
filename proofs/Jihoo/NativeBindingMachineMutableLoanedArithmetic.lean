import Jihoo.NativeBindingMachineMutableComputedBorrow
import Jihoo.NativeBindingMachineReferenceSizes
import Jihoo.NativeLoanArithmeticProofConsistency

/-! A scalar reader can read its newly opened reference and retained
references at computed indices. Signed arithmetic preserves read order. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity

theorem projectRaw_arithmetic_operands
    (checked : projectRaw fuel env loans ctx (.arith op left right) = some receipt) :
    ∃ depth first second,
      projectRaw depth env loans ctx left = some first ∧ projectRaw depth env loans ctx right = some second ∧
      receipt = .seq first (.seq second .pure) := by
  cases fuel with
  | zero => cases checked
  | succ depth =>
      have equivalent : projectRaw (depth+1) env loans ctx (.arith op left right) =
          projectRaw (depth+1) env loans ctx (.strict left right) := rfl
      obtain ⟨first,second,leftChecked,rightChecked,shape⟩ := strict_projection (equivalent ▸ checked)
      exact ⟨depth,first,second,leftChecked,rightChecked,shape⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

inductive ReaderReference where
  | bound
  | captured (slot : Nat)

namespace ReaderReference

def slot : ReaderReference → Nat
  | .bound => 0
  | .captured index => index+1

def specialized (owner : Nat) : ReaderReference → Term
  | .bound => .borrow (.var owner)
  | .captured index => .var index

def token (code : Code) (fresh : Nat) : ReaderReference → Option Nat
  | .bound => some fresh
  | .captured index =>
      match code.values[index]? with
      | some (some (.reference token)) => some token
      | _ => none

end ReaderReference

inductive LoanedArithmetic where
  | literal (number : Int)
  | read (reference : ReaderReference) (index : UnsignedOperand) (evidence : Term)
  | arithmetic (op : Arith) (left right : LoanedArithmetic)

namespace LoanedArithmetic

def term : LoanedArithmetic → Term
  | .literal number => .integer number
  | .read reference index evidence =>
      .index (.var reference.slot) (index.rename Nat.succ).term (evidence.rename Nat.succ)
  | .arithmetic op left right => .arith op left.term right.term

def specialized (owner : Nat) : LoanedArithmetic → Term
  | .literal number => .integer number
  | .read reference index evidence => .index (reference.specialized owner) index.term evidence
  | .arithmetic op left right => .arith op (specialized owner left) (specialized owner right)

theorem specialize_term (tree : LoanedArithmetic) (owner : Nat) :
    Lending.read (.var owner) tree.term = tree.specialized owner := by
  induction tree with
  | literal number => simp only [term,specialized,Lending.read,Term.subst,substArgs]
  | read reference index evidence =>
      cases reference <;>
        simp only [term,specialized,ReaderReference.slot,ReaderReference.specialized,
          UnsignedOperand.rename_term,Lending.read,Term.subst,substArgs,Op.binders,liftSub,Term.shift_subst_single,single]
  | arithmetic op left right leftSpecialized rightSpecialized =>
      change left.term.subst (single (.borrow (.var owner))) = _ at leftSpecialized
      change right.term.subst (single (.borrow (.var owner))) = _ at rightSpecialized
      simp only [term,specialized,Lending.read,Term.subst,substArgs,Op.binders,liftSub,leftSpecialized,rightSpecialized]

def ticks : LoanedArithmetic → Nat
  | .literal _ => 1
  | .read _ index _ => 3+((index.rename Nat.succ).ticks+1)
  | .arithmetic _ left right => 1+(left.ticks+(1+(right.ticks+1)))

def ArithmeticEvidence (meanings : Nat → Term) : LoanedArithmetic → Prop
  | .literal _ => True
  | .read _ _ evidence => Semantics.LoanArithmetic.Supported (evidence.subst meanings)
  | .arithmetic _ left right => ArithmeticEvidence meanings left ∧ ArithmeticEvidence meanings right

structure Observation where
  number : Int
  events : List Event

/-- Interpret only successful word and signed arithmetic. Each leaf
observes the indexed cells reached through its own reference. The
evidence, which the machine erases, separately determines the read guards. -/
def replay (original : Code) (heap : SizedBufferHeap.IndexedState) (fresh : Nat) (meanings : Nat → Term) :
    LoanedArithmetic → Option Observation
  | .literal number => if ValueReduction.signed64 number then some ⟨number,[]⟩ else none
  | .read reference index _ => do
      let token ← reference.token original fresh
      let object ← heap.metadata.heap.lease token
      let offset ← index.value meanings
      let payload := heap.cell object offset
      pure ⟨decodeInteger payload,[.legacy (.heap (.read token offset payload))]⟩
  | .arithmetic op left right => do
      let first ← replay original heap fresh meanings left
      let second ← replay original heap fresh meanings right
      let number := ValueReduction.arithmetic op first.number second.number
      if ValueReduction.signed64 number then some ⟨number,first.events ++ second.events⟩ else none

private theorem no_reference_array (admissible : EnvironmentDelta.Admissible env)
    (kind : ValueKind env (.reference token) (.array count)) : False := by
  obtain ⟨domain,converted⟩ := kind
  exact RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) converted admissible

private theorem selected_capture {original : Code} {slot token : Nat}
    (selected : ReaderReference.token original fresh (.captured slot) = some token) :
    original.values[slot]? = some (some (.reference token)) := by
  simp only [ReaderReference.token] at selected
  split at selected
  · cases selected
    assumption
  · contradiction

private theorem captured_index_size
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false (.index (.var slot) index evidence) type)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (references : ReferenceSizes env heap original meanings)
    (stored : original.values[slot]? = some (some (.reference token)))
    (leased : heap.heap.lease token = some object) :
    ∃ size,
      LoanTyping.HasType env loans original.context false index .u64 ∧
      LoanTyping.HasType env loans original.context true evidence (.lt index size) ∧
      LoanTyping.Conversion.Conv env (.natural (heap.length object)) (size.subst meanings) := by
  obtain ⟨size,reference,indexTyped,bound⟩ := typed.index_inputs
  rcases reference with array | reference
  · have closed : LoanClosingTyped env loans false (original.child (.var slot)) meanings
        ((Term.array size).subst meanings) := ⟨context.closing,.array size,array,.refl _⟩
    obtain ⟨value,selected,kind⟩ := (context.child _).variable_kind history closed (aligned.child _) rfl
    have same : value = .reference token := Option.some.inj (Option.some.inj (selected.symm.trans stored))
    subst value
    have arrayKind : ValueKind env (.reference token) (.array (size.subst meanings)) := by
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using kind
    exact False.elim (no_reference_array history.wellFormed.admissible arrayKind)
  · obtain ⟨referent,length,actual,_,sized,represented⟩ := references.typed_variable history reference stored
    have same := Option.some.inj (actual.symm.trans leased)
    subst referent
    rw [sized]
    have closed : LoanTyping.Conversion.Conv env (.ref (.buffer (.natural length)))
        (.ref (.buffer (size.subst meanings))) := by
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using represented
    exact ⟨size,indexTyped,bound,(closed.ref_injective history.wellFormed.admissible).buffer_injective
      history.wellFormed.admissible⟩

/-- The original read judgment and selected lease determine the word type,
the exact bound type, and the physical interpretation of its upper endpoint. -/
theorem reference_index_typing
    {heap : SizedBufferHeap.IndexedState}
    (reference : ReaderReference) (word : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false
      (.index (reference.specialized owner) word.term evidence) type)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (sizes : OwnerSizes env heap.metadata original meanings)
    (references : ReferenceSizes env heap.metadata original meanings)
    (stored : original.values[owner]? = some (some (.owner borrowedObject)))
    (borrowed : heap.metadata.heap.lease fresh = some borrowedObject)
    (selected : reference.token original fresh = some token)
    (leased : heap.metadata.heap.lease token = some object) :
    ∃ size, LoanTyping.HasType env loans original.context false word.term .u64 ∧
      LoanTyping.HasType env loans original.context true evidence (.lt word.term size) ∧
      LoanTyping.Conversion.Conv env (.natural (heap.metadata.length object)) (size.subst meanings) := by
  cases reference with
  | bound =>
      cases selected
      have same : borrowedObject = object := Option.some.inj (borrowed.symm.trans leased)
      subst object
      obtain ⟨size,ownerTyped,indexTyped,bound⟩ := typed.named_index_owner history.wellFormed
      have exactSize : OwnerSize env heap.metadata borrowedObject (.buffer (size.subst meanings)) := by
        simpa only [Term.subst,substArgs,Op.binders,liftSub] using sizes.typed_variable history ownerTyped stored
      exact ⟨size,indexTyped,bound,exactSize.buffer_length history⟩
  | captured slot =>
      exact captured_index_size history typed context aligned references (selected_capture selected) leased

private theorem checked_reference_index
    (reference : ReaderReference) (word : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false
      (.index (reference.specialized owner) word.term evidence) type)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (sizes : OwnerSizes env heap.metadata original meanings)
    (references : ReferenceSizes env heap.metadata original meanings)
    (stored : original.values[owner]? = some (some (.owner borrowedObject)))
    (borrowed : heap.metadata.heap.lease fresh = some borrowedObject)
    (selected : reference.token original fresh = some token)
    (leased : heap.metadata.heap.lease token = some object)
    (checked : LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans original.context
      (.index (reference.specialized owner) word.term evidence) = some receipt)
    (supported : Semantics.LoanArithmetic.Supported (evidence.subst meanings))
    (offsetValue : word.value meanings = some offset)
    (domain readerBody origin : Term) (stack : List Frame) (pending : List (BufferFrame × List Frame)) :
    let entry := enter false domain readerBody original.context original.origins original.values origin (some (.reference fresh))
    let expression := Term.index (.var reference.slot) (word.rename Nat.succ).term (evidence.rename Nat.succ)
    let duration := 3+((word.rename Nat.succ).ticks+1)
    run duration ⟨heap,.evaluate (entry.child expression),stack,pending⟩ =
      ⟨⟨heap,.returned (.integer (decodeInteger (heap.cell object offset))),stack,pending⟩,
        [.legacy (.heap (.read token offset (heap.cell object offset)))],duration⟩ := by
  let entry := enter false domain readerBody original.context original.origins original.values origin (some (.reference fresh))
  have selectedRuntime : entry.values[reference.slot]? = some (some (.reference token)) := by
    cases reference with
    | bound => cases selected; rfl
    | captured slot => exact selected_capture (original := original) (slot := slot) selected
  obtain ⟨size,indexTyped,evidenceTyped,physical⟩ := reference_index_typing reference word history typed
    context aligned sizes references stored borrowed selected leased
  obtain ⟨depth,_,indexReceipt,_,indexProjected,_⟩ := LoanTyping.ResourceQuantity.projectRaw_index_operands checked
  have indexClosed : LoanClosingTyped env loans false (original.child word.term) meanings .u64 :=
    ⟨context.closing,.u64,indexTyped,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  obtain ⟨_,converted,_,runIndex⟩ := word.checked_run_under_binder history indexClosed context aligned
    indexProjected offsetValue domain readerBody origin (some (.reference fresh))
  have evidenceClosed : LoanTyping.HasType env [] [] true (evidence.subst meanings)
      (.lt (word.term.subst meanings) (size.subst meanings)) := by
    simpa only [Term.lt,Term.subst,substArgs,Op.binders,liftSub] using
      evidenceTyped.ghostSubstitution history.wellFormed context.closing
  have within : offset < heap.metadata.length object :=
    Semantics.LoanArithmetic.supported_affine_bound history.wellFormed (.literal offset)
      evidenceClosed supported converted physical.symm (fun _ => 0)
  have read : heap.read token offset = some (heap.cell object offset) := by
    unfold SizedBufferHeap.IndexedState.read
    rw [leased]
    exact ite_eq_left within
  exact reference_index_operand_runs _ rfl rfl selectedRuntime (runIndex heap (.indexOffset token :: stack) pending) read

/-- The genuine reader projection supplies each recursive operand receipt.
Successful replay agrees with the actual runtime in read order, exact
captured token and cell, and the final signed value. All frames and the
indexed heap are retained until the enclosing reader closes. -/
theorem checked_run (tree : LoanedArithmetic)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false (tree.specialized owner) type)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (sizes : OwnerSizes env heap.metadata original meanings)
    (references : ReferenceSizes env heap.metadata original meanings)
    (stored : original.values[owner]? = some (some (.owner object)))
    (leased : heap.metadata.heap.lease fresh = some object)
    (checked : LoanTyping.ResourceQuantity.projectRaw depth env loans original.context (tree.specialized owner) = some receipt)
    (evidence : tree.ArithmeticEvidence meanings)
    (observed : tree.replay original heap fresh meanings = some observation)
    (domain readerBody origin : Term) (stack : List Frame) (pending : List (BufferFrame × List Frame)) :
    let entry := enter false domain readerBody original.context original.origins original.values origin (some (.reference fresh))
    run tree.ticks ⟨heap,.evaluate (entry.child tree.term),stack,pending⟩ =
      ⟨⟨heap,.returned (.integer observation.number),stack,pending⟩,observation.events,tree.ticks⟩ := by
  let entry := enter false domain readerBody original.context original.origins original.values origin (some (.reference fresh))
  induction tree generalizing type depth receipt observation stack with
  | literal number =>
      simp only [replay] at observed
      split at observed
      · rename_i bounded
        cases observed
        simp only [term,ticks,run,step,Code.child,evaluateAction,bounded,ite_true,executeLegacy,execute,Option.map_none]
        rfl
      · contradiction
  | read reference word bound =>
      simp only [replay] at observed
      obtain ⟨token,tokenFound,rest⟩ := Option.bind_eq_some_iff.mp observed
      obtain ⟨queried,objectFound,rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨offset,offsetValue,result⟩ := Option.bind_eq_some_iff.mp rest
      cases result
      exact checked_reference_index reference word history typed context aligned sizes references stored leased
        tokenFound objectFound checked evidence offsetValue domain readerBody origin stack pending
  | arithmetic op left right leftRec rightRec =>
      obtain ⟨leftTyped,rightTyped⟩ := typed.arith_inputs
      obtain ⟨fuel,leftReceipt,rightReceipt,leftChecked,rightChecked,_⟩ :=
        LoanTyping.ResourceQuantity.projectRaw_arithmetic_operands checked
      simp only [replay] at observed
      obtain ⟨lhs,leftValue,rest⟩ := Option.bind_eq_some_iff.mp observed
      obtain ⟨rhs,rightValue,result⟩ := Option.bind_eq_some_iff.mp rest
      split at result
      · rename_i bounded
        cases result
        let leftStack := .arithmeticLeft op (entry.child right.term) :: stack
        let rightStack := .arithmeticRight op lhs.number :: stack
        have leftStart : step ⟨heap,.evaluate (entry.child (.arith op left.term right.term)),stack,pending⟩ =
            some (⟨heap,.evaluate (entry.child left.term),leftStack,pending⟩,none) := rfl
        have rightStart : step ⟨heap,.returned (.integer lhs.number),leftStack,pending⟩ =
            some (⟨heap,.evaluate (entry.child right.term),rightStack,pending⟩,none) := rfl
        have finish : run 1 ⟨heap,.returned (.integer rhs.number),rightStack,pending⟩ =
            ⟨⟨heap,.returned (.integer (ValueReduction.arithmetic op lhs.number rhs.number)),stack,pending⟩,[],1⟩ := by
          simp only [rightStack,run,step,returnAction,bounded,ite_true,executeLegacy,execute,Option.map_none]
          rfl
        have leftRun := leftRec leftTyped leftChecked evidence.1 leftValue leftStack
        have rightRun := rightRec rightTyped rightChecked evidence.2 rightValue rightStack
        simpa only [term,ticks,List.append_nil,List.nil_append] using
          join_runs (noevent_step_run leftStart) (join_runs leftRun
            (join_runs (noevent_step_run rightStart) (join_runs rightRun finish)))
      · contradiction

end LoanedArithmetic

/-- From the original checked Lend, the actual freshly opened reference and
retained references supply the reader's cells. A successful tree restores
the original scalar and canonical owner receipts, closes its own token, and
keeps every older reference's observed cells and dependent interpretation. -/
theorem reachable_loaned_arithmetic_restore (program : Term) (fuel : Nat) (tree : LoanedArithmetic)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .lend (.var owner) (.lam false (.ref (.buffer count)) tree.term)
      (.lam false first (.lam false again body)))
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (references : ReferenceSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (evidence : tree.ArithmeticEvidence meanings)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let before := (run fuel (initial program)).state
    let token := before.heap.metadata.heap.nextLease
    let origin := (Term.var owner).subst code.origins
    let reader := enter false (.ref (.buffer count)) tree.term code.context code.origins code.values
      (.borrow origin) (some (.reference token))
    let duration := 5+(tree.ticks+5)
    let result := run duration before
    ∃ object, code.values[owner]? = some (some (.owner object)) ∧
      ∀ observation, tree.replay code ⟨SizedBufferHeap.lend before.heap.metadata object,before.heap.cell⟩
        token meanings = some observation →
      let number := observation.number
      let closed : SizedBufferHeap.IndexedState :=
        ⟨SizedBufferHeap.close (SizedBufferHeap.lend before.heap.metadata object) token,before.heap.cell⟩
      let actual := restoredContinuation code first again body origin reader.origin object (.integer number)
      let canonical := canonicalContinuation code owner first body reader.origin (.integer number)
      let nextMeanings := consValues (.integer number) meanings
      result = ⟨⟨closed,.evaluate actual,before.stack,before.pending⟩,
        [.legacy (.heap (.beginLease token object)),.legacy (.activate false tree.term (.borrow origin))] ++
          observation.events ++ [.legacy (.heap (.close token)),.legacy (.activate false (.lam false again body) reader.origin),
          .legacy (.activate false body origin)],duration⟩ ∧
      closed.metadata.heap.lease token = none ∧
      (∀ older < token, ∀ cell, closed.read older cell = before.heap.read older cell) ∧
      ¬ StateReferenceOccurs token result.state ∧ ReaderInventory closed.metadata (readerFrames before.activeStack) ∧
      CanonicalView actual canonical (Jihoo.Quantity.openOwner (owner+1)) ∧
      ReferenceSizes env closed.metadata canonical nextMeanings ∧
      LoanClosingTyped env loans false canonical nextMeanings type ∧ ValueContext env canonical nextMeanings ∧
      OwnerSizes env closed.metadata canonical nextMeanings ∧
      LoanSlots canonical loans before.activeStack ∧ LoanCoverage canonical loans before.activeStack ∧
      ∃ rest, LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans canonical.context canonical.term = some rest ∧
        LoanTyping.ResourceQuantity.LoanBudget canonical.context.length loans rest ∧ rest.demand (owner+1) = some 1 ∧
        OwnerDemandWorld closed.metadata canonical rest ∧ OwnerDemandWorld.Total canonical rest ∧
        ∀ alias, alias ≠ owner → code.values[alias]? = some (some (.owner object)) → rest.demand (alias+1) = some 0 := by
  let before := (run fuel (initial program)).state
  let token := before.heap.metadata.heap.nextLease
  let origin := (Term.var owner).subst code.origins
  let domain := Term.ref (.buffer count)
  let reader := enter false domain tree.term code.context code.origins code.values (.borrow origin) (some (.reference token))
  let duration := 5+(tree.ticks+5)
  have checkedLend := shape ▸ checked
  obtain ⟨_,_,_,_,_,_,_,_,_,source,readTyped,_,_,_,readProjected,_,_,_,_⟩ :=
    LoanTyping.ResourceQuantity.dependent_raw_project_contract checkedLend
  rw [tree.specialize_term] at readTyped readProjected
  obtain ⟨ownerType,_,_,ghostOwner,_,_,domainType,_,_⟩ :=
    source.explicitLendReaderInputs history.wellFormed
  have domainBuffer : LoanTyping.Conversion.Conv env domain (.ref ownerType) := domainType
  have toBuffer : LoanTyping.Conversion.Conv env ownerType (.buffer count) :=
    (domainBuffer.ref_injective history.wellFormed.admissible).symm
  obtain ⟨_,runtimeOwner⟩ := source.lend_named_owner
  have sameOwnerType := (runtimeOwner.ghost []).unique history.wellFormed (ghostOwner.convert toBuffer)
  have ownerClosing : LoanClosingTyped env loans false (code.child (.var owner)) meanings
      ((Term.buffer count).subst meanings) :=
    ⟨typed.1,.buffer count,runtimeOwner.convert sameOwnerType,.refl _⟩
  have aligned := initial_run_code_aligned program fuel SizedBufferHeap.empty evaluating
  obtain ⟨value,stored,kind⟩ := (context.child _).variable_kind history ownerClosing (aligned.child _) rfl
  have buffer : ValueKind env value (.buffer (count.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using kind
  obtain ⟨object,rfl⟩ := buffer_kind_is_owner history.wellFormed.admissible buffer
  let openedHeap : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.lend before.heap.metadata object,before.heap.cell⟩
  refine ⟨object,stored,?_⟩
  intro observation observed
  let lender := Frame.lendFinish token object (some (code.context.length-owner)) origin reader.origin
    (code.child (.lam false first (.lam false again body)))
  let reading := lender :: before.stack
  let atReader : State := ⟨openedHeap,.evaluate reader,reading,before.pending⟩
  have use := LoanTyping.ResourceQuantity.projectRaw_lend_owner_demand checkedLend
  have live := (world.live_once owner object 0 stored use).1
  have opened : run 5 before = ⟨atReader,
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false tree.term (.borrow origin))],5⟩ :=
    named_reader_steps before evaluating shape stored live
  have leased : openedHeap.metadata.heap.lease token = some object := by
    simp [openedHeap,SizedBufferHeap.lend,HeapLeases.put,token]
  have referenceSizes : ReferenceSizes env openedHeap.metadata code meanings :=
    references.lend (initial_run_invariant program fuel).1 object
  have openedSizes : OwnerSizes env openedHeap.metadata code meanings :=
    sizes.steps (.cons (.beginLease live) .nil)
  let returned : State := ⟨openedHeap,.returned (.integer observation.number),reading,before.pending⟩
  have readRun : run tree.ticks atReader = ⟨returned,observation.events,tree.ticks⟩ := by
    have executed := tree.checked_run (heap := openedHeap) history readTyped context aligned
      openedSizes referenceSizes stored leased readProjected
      evidence observed domain tree.term (.borrow origin) reading before.pending
    exact executed
  have finishedRead := join_runs opened readRun
  have reached : (run (fuel+(5+tree.ticks)) (initial program)).state = returned := by
    have observed := congrArg Result.state (run_add fuel (5+tree.ticks) (initial program))
    change (run (fuel+(5+tree.ticks)) (initial program)).state = (run (5+tree.ticks) before).state at observed
    rw [finishedRead] at observed
    exact observed
  have resultControl : (run (fuel+(5+tree.ticks)) (initial program)).state.control =
      .returned (.integer observation.number) := by rw [reached]
  have actualFrame : (run (fuel+(5+tree.ticks)) (initial program)).state.stack = reading := by rw [reached]
  have resultType : LoanTyping.Conversion.Conv env .i64 (first.subst meanings) := by
    have principal : LoanTyping.Conversion.Conv env .i64 first := by cases tree <;> exact readTyped.principalView
    simpa only [Term.subst,substArgs] using principal.substitution meanings history.wellFormed.closed
  have resultKind : ValueKind env (.integer observation.number) (first.subst meanings) := resultType
  have width := (initial_run_numbers program (fuel+(5+tree.ticks))).legacy.2.1
  change ControlNumbers (run (fuel+(5+tree.ticks)) (initial program)).state.control at width
  rw [resultControl] at width
  have signed := ValueNumbers.integerBound width
  have valueTyped : LoanTyping.HasType env [] [] true (.integer observation.number) (first.subst meanings) :=
    (LoanTyping.HasType.integer signed.1 signed.2).convert resultType
  obtain ⟨closeStep,_,retired,otherLeases,inventory⟩ :=
    reachable_lend_return_nonescape program (fuel+(5+tree.ticks)) history typed shape resultControl resultKind actualFrame
  rw [reached] at closeStep retired otherLeases inventory
  let closed : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.close openedHeap.metadata token,before.heap.cell⟩
  let actual := restoredContinuation code first again body origin reader.origin object (.integer observation.number)
  have resumed := resume_lend_continuation_steps returned closed code first again body origin reader.origin observation.number
    token object before.stack before.pending closeStep
  have finished : run duration before = ⟨⟨closed,.evaluate actual,before.stack,before.pending⟩,
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false tree.term (.borrow origin))] ++
        observation.events ++ [.legacy (.heap (.close token)),.legacy (.activate false (.lam false again body) reader.origin),
        .legacy (.activate false body origin)],duration⟩ := by
    simpa only [List.append_assoc] using join_runs opened (join_runs readRun resumed)
  have older : ∀ previous < token, closed.metadata.heap.lease previous = before.heap.metadata.heap.lease previous := by
    intro previous earlier
    change (SizedBufferHeap.close openedHeap.metadata token).heap.lease previous = _
    rw [otherLeases _ (Nat.ne_of_lt earlier)]
    change (SizedBufferHeap.lend before.heap.metadata object).heap.lease previous = _
    simp [SizedBufferHeap.lend,HeapLeases.put,token,Nat.ne_of_lt earlier]
  have otherReads : ∀ previous < token, ∀ cell, closed.read previous cell = before.heap.read previous cell := by
    intro previous earlier cell
    unfold SizedBufferHeap.IndexedState.read
    rw [older previous earlier]
    rfl
  obtain ⟨savedReady,stackReady,pendingReady⟩ :=
    initial_run_finish_capture_bounds program (fuel+(5+tree.ticks)) actualFrame
  rw [reached] at pendingReady
  have actualReady : CodeReferences token actual := ValuesReferences.retained .owner (.retained .integer savedReady)
  have absent : ¬ StateReferenceOccurs token ⟨closed,.evaluate actual,before.stack,before.pending⟩ := by
    intro occurs
    rcases occurs with (control | ⟨frame,member,occurs⟩) | pending
    · exact actualReady.fresh_absent control
    · exact stackReady.fresh_absent member occurs
    · exact pendingReady.fresh_absent pending
  have closedSizes := reachable_run_owner_sizes program fuel duration sizes
  rw [finished] at closedSizes
  have closedWorld : OwnerDemandWorld closed.metadata code receipt := ⟨world.live_once,world.exclusive⟩
  have retained := (referenceSizes.close savedReady).enter_nonreference false first
    (body.rename (Jihoo.Quantity.openOwner (owner+1))) reader.origin (.integer observation.number)
    (some (.integer observation.number)) (by intro _ impossible; cases impossible)
  exact ⟨finished,retired,otherReads,finished.symm ▸ absent,inventory,
    restored_canonical_view code stored first again body reader.origin (.integer observation.number),retained,
    canonical_integer_restore_demand history shape typed context valueTyped closedSizes slots coverage
      entered stored checkedLend budget closedWorld complete reader.origin⟩

namespace Examples

private def twoLoanValues : Term :=
  let buffer := Term.buffer (.natural 2)
  let bound := Term.decide (.natural 1) (.natural 2)
  let index := UnsignedOperand.add (.literal 0) (.literal 1)
  let computedBound := Term.decide index.term (.natural 2)
  let read := LoanedArithmetic.arithmetic .add (.read .bound index computedBound)
    (.read (.captured 1) index computedBound)
  let release := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let inner := Term.lend (.var 0) (.lam false (.ref buffer) read.term) release
  let writtenInner := Term.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 31) bound
  let withInner := Term.app (.lam false buffer inner) writtenInner
  let olderRead := Term.index (.var 0) (.natural 1) bound
  let outer := Term.lend (.var 0) (.lam false (.ref buffer) (.arith .add withInner olderRead)) release
  let writtenOuter := Term.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 8) bound
  .app (.lam false buffer outer) writtenOuter

set_option maxRecDepth 4096 in
/-- The inner reader adds cells from its own lease and the captured outer
reference. Its close leaves the outer lease readable at its written value. -/
theorem captured_two_loan_reads_and_restores_outer :
    LoanTyping.MixedProgram.checkDeclaration 96 192 .empty ⟨.i64,twoLoanValues⟩ =
      some ⟨.i64,twoLoanValues⟩ ∧
    let result := run 140 (initial twoLoanValues)
    observe result = .integer 47 ∧
      result.events.filterMap (fun event => match event with
        | .legacy (.heap (.read token offset payload)) => some (token,offset,payload)
        | _ => none) = [(1,1,encodeInteger 31),(0,1,encodeInteger 8),(0,1,encodeInteger 8)] ∧
      result.events.filterMap Event.lifecycle? =
        [.alloc 0 2 (encodeInteger 3),.beginLease 0 0,.alloc 1 2 (encodeInteger 3),
          .beginLease 1 1,.close 1,.free 1,.close 0,.free 0] := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
