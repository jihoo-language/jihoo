import Jihoo.NativeBindingMachineMutableComputedStore

/-! A word expression in a named Lend reader may use old captures while
the fresh reference stays in its own private slot. The read uses the
current indexed cell and the original specialized source receipt. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

theorem HasType.lend_named_owner
    (typed : HasType env loans ctx false (.lend (.var owner) reader continuation) type) :
    ∃ ownerType, HasType env loans ctx false (.var owner) ownerType := by
  obtain ⟨_,rule,_⟩ := typed.lendView
  cases rule with
  | generic owner => exact ⟨_,owner⟩
  | dependentCode owner => exact ⟨_,owner⟩

namespace ResourceQuantity
open Jihoo.Quantity NativeQuantity

/-- Index checks both runtime operands. Its erased evidence does not enter
the resource projection. -/
theorem projectRaw_index_operands
    (checked : projectRaw fuel env loans ctx (.index reference index evidence) = some receipt) :
    ∃ depth referenceReceipt indexReceipt,
      projectRaw depth env loans ctx reference = some referenceReceipt ∧
      projectRaw depth env loans ctx index = some indexReceipt ∧
      receipt = .seq referenceReceipt (.seq indexReceipt .pure) := by
  cases fuel with
  | zero => cases checked
  | succ depth =>
      have same : projectRaw (depth+1) env loans ctx (.index reference index evidence) =
          projectRaw (depth+1) env loans ctx (.strict reference index) := rfl
      obtain ⟨referenceReceipt,indexReceipt,referenceChecked,indexChecked,shape⟩ := strict_projection (same ▸ checked)
      exact ⟨depth,referenceReceipt,indexReceipt,referenceChecked,indexChecked,shape⟩

end ResourceQuantity
end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

namespace UnsignedOperand

theorem rename_term (operand : UnsignedOperand) (indices : Nat → Nat) :
    (operand.rename indices).term = operand.term.rename indices := by
  induction operand with
  | literal number => simp only [rename,term,Term.rename,renameArgs]
  | captured slot => simp only [rename,term,Term.rename]
  | add left right leftRenamed rightRenamed =>
      simp only [rename,term,Term.rename,renameArgs,Op.binders,liftRenaming,leftRenamed,rightRenamed]

/-- The new reader reference occupies slot zero; the original word index
and erased evidence move under that binder. -/
def referenceReader (operand : UnsignedOperand) (evidence : Term) : Term :=
  .index (.var 0) (operand.rename Nat.succ).term (evidence.rename Nat.succ)

theorem referenceReader_specialized (operand : UnsignedOperand) (evidence : Term) (owner : Nat) :
    Lending.read (.var owner) (operand.referenceReader evidence) =
      .index (.borrow (.var owner)) operand.term evidence := by
  simp only [referenceReader,rename_term,Lending.read,Term.subst,substArgs,Op.binders,liftSub,
    Term.shift_subst_single,single]

private theorem captures_under_binder (operand : UnsignedOperand) (code : Code)
    (erased : Bool) (domain body origin : Term) (argument : Option Value) :
    (operand.rename Nat.succ).CapturesMatch
      (enter erased domain body code.context code.origins code.values origin argument) code Nat.pred := by
  induction operand with
  | literal => trivial
  | captured slot => rfl
  | add left right leftMatch rightMatch => exact ⟨leftMatch,rightMatch⟩

/-- Interpret the same checked word expression underneath an extra
retained binder. Only the captured slots used by the expression are
related, so the extra reference may be present in the runtime CODE. -/
theorem checked_run_under_binder (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false (code.child operand.term) meanings .u64)
    (context : ValueContext env code meanings) (aligned : CodeAligned code)
    (checked : LoanTyping.ResourceQuantity.projectRaw depth env loans code.context operand.term = some receipt)
    (observed : operand.value meanings = some offset)
    (domain body origin : Term) (argument : Option Value) :
    let entry := enter false domain body code.context code.origins code.values origin argument
    let index := operand.rename Nat.succ
    offset < 2^64 ∧ LoanTyping.Conversion.Conv env (operand.term.subst meanings) (.natural offset) ∧
    (∀ slot object, code.values[slot]? = some (some (.owner object)) → receipt.demand slot = some 0) ∧
    ∀ (heap : SizedBufferHeap.IndexedState) (stack : List Frame) (pending : List (BufferFrame × List Frame)),
      run index.ticks ⟨heap,.evaluate (entry.child index.term),stack,pending⟩ =
        ⟨⟨heap,.returned (.natural offset),stack,pending⟩,[],index.ticks⟩ := by
  let entry := enter false domain body code.context code.origins code.values origin argument
  let index := operand.rename Nat.succ
  have sameTerm : index.term.rename Nat.pred = operand.term := by
    rw [show index.term = operand.term.rename Nat.succ from operand.rename_term Nat.succ,Term.rename_comp]
    change operand.term.rename (fun slot => (slot+1).pred) = operand.term
    exact Term.rename_id _
  have sameValue : index.value (meanings ∘ Nat.pred) = some offset := by
    rw [show index = operand.rename Nat.succ from rfl,rename_value]
    exact observed
  have typedSource : LoanClosingTyped env loans false (code.child (index.term.rename Nat.pred)) meanings .u64 :=
    sameTerm.symm ▸ typed
  have projected : LoanTyping.ResourceQuantity.projectRaw depth env loans code.context (index.term.rename Nat.pred) =
      some receipt := by rwa [sameTerm]
  have captures : index.CapturesMatch entry code Nat.pred := captures_under_binder operand code false domain body origin argument
  have replay := index.checked_run_captures history captures typedSource context aligned projected sameValue
  rwa [sameTerm] at replay

end UnsignedOperand

/-- The actual reference slot runs a computed Index through its two legacy
operand frames. Its current indexed read is the only memory event. -/
theorem reference_index_operand_runs (state : State)
    (evaluating : state.control = .evaluate code)
    (shape : code.term = .index (.var referenceSlot) index evidence)
    (reference : code.values[referenceSlot]? = some (some (.reference token)))
    (indexRun : run indexTicks ⟨state.heap,.evaluate (code.child index),.indexOffset token :: state.stack,state.pending⟩ =
      ⟨⟨state.heap,.returned (.natural offset),.indexOffset token :: state.stack,state.pending⟩,[],indexTicks⟩)
    (read : state.heap.read token offset = some payload) :
    let duration := 3+(indexTicks+1)
    run duration state = ⟨⟨state.heap,.returned (.integer (decodeInteger payload)),state.stack,state.pending⟩,
      [.legacy (.heap (.read token offset payload))],duration⟩ := by
  have entry : run 3 state = ⟨⟨state.heap,.evaluate (code.child index),.indexOffset token :: state.stack,state.pending⟩,[],3⟩ := by
    simp only [run,step,evaluating,shape,Code.child,evaluateAction,reference,executeLegacy,execute,returnAction,Option.map_none]
    rfl
  have finish : run 1 ⟨state.heap,.returned (.natural offset),.indexOffset token :: state.stack,state.pending⟩ =
      ⟨⟨state.heap,.returned (.integer (decodeInteger payload)),state.stack,state.pending⟩,
        [.legacy (.heap (.read token offset payload))],1⟩ := by
    simp only [run,step,returnAction,executeLegacy,read]
    rfl
  exact join_runs entry (join_runs indexRun finish)

/-- The original checked named Lend selects its Buffer, opens its actual
reference, evaluates a computed index, and reads the current indexed cell.
It closes only that lease and restores the typed scalar and canonical
owner demand through both actual continuation bindings. -/
theorem reachable_computed_reference_reader_restore (program : Term) (fuel : Nat) (index : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .lend (.var owner) (.lam false domain (index.referenceReader evidence))
      (.lam false first (.lam false again body)))
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (decideEvidence : evidence.subst meanings = .decide left right)
    (computed : index.value meanings = some offset)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let before := (run fuel (initial program)).state
    let token := before.heap.metadata.heap.nextLease
    let origin := (Term.var owner).subst code.origins
    let readBody := index.referenceReader evidence
    let reader := enter false domain readBody code.context code.origins code.values (.borrow origin) (some (.reference token))
    let readTicks := 3+((index.rename Nat.succ).ticks+1)
    let duration := 5+(readTicks+5)
    let result := run duration before
    ∃ object,
      let payload := before.heap.cell object offset
      let number := decodeInteger payload
      let closed : SizedBufferHeap.IndexedState :=
        ⟨SizedBufferHeap.close (SizedBufferHeap.lend before.heap.metadata object) token,before.heap.cell⟩
      let actual := restoredContinuation code first again body origin reader.origin object (.integer number)
      let canonical := canonicalContinuation code owner first body reader.origin (.integer number)
      let nextMeanings := consValues (.integer number) meanings
      code.values[owner]? = some (some (.owner object)) ∧ offset < before.heap.metadata.length object ∧
      result = ⟨⟨closed,.evaluate actual,before.stack,before.pending⟩,
        [.legacy (.heap (.beginLease token object)),.legacy (.activate false readBody (.borrow origin)),
          .legacy (.heap (.read token offset payload)),.legacy (.heap (.close token)),
          .legacy (.activate false (.lam false again body) reader.origin),.legacy (.activate false body origin)],duration⟩ ∧
      closed.metadata.heap.lease token = none ∧
      (∀ outer < token, closed.metadata.heap.lease outer = before.heap.metadata.heap.lease outer) ∧
      ¬ StateReferenceOccurs token result.state ∧ ReaderInventory closed.metadata (readerFrames before.activeStack) ∧
      CanonicalView actual canonical (Jihoo.Quantity.openOwner (owner+1)) ∧
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
  let readBody := index.referenceReader evidence
  let reader := enter false domain readBody code.context code.origins code.values (.borrow origin) (some (.reference token))
  let readTicks := 3+((index.rename Nat.succ).ticks+1)
  let duration := 5+(readTicks+5)
  have checkedLend := shape ▸ checked
  obtain ⟨_,_,_,_,_,_,_,_,_,source,readTyped,_,_,_,readProjected,_,_,_,_⟩ :=
    LoanTyping.ResourceQuantity.dependent_raw_project_contract checkedLend
  rw [index.referenceReader_specialized] at readTyped readProjected
  obtain ⟨size,typedIndexOwner,typedIndex,typedEvidence⟩ := readTyped.named_index_owner history.wellFormed
  obtain ⟨_,typedOwner⟩ := source.lend_named_owner
  have convertedOwner := (typedOwner.ghost []).unique history.wellFormed (typedIndexOwner.ghost [])
  have ownerClosing : LoanClosingTyped env loans false (code.child (.var owner)) meanings ((Term.buffer size).subst meanings) :=
    ⟨typed.1,.buffer size,typedOwner.convert convertedOwner,.refl _⟩
  have aligned := initial_run_code_aligned program fuel SizedBufferHeap.empty evaluating
  obtain ⟨runtimeOwner,stored,kind⟩ := (context.child _).variable_kind history ownerClosing (aligned.child _) rfl
  have buffer : ValueKind env runtimeOwner (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using kind
  obtain ⟨object,rfl⟩ := buffer_kind_is_owner history.wellFormed.admissible buffer
  obtain ⟨_,_,_,_,indexProjected,_⟩ := LoanTyping.ResourceQuantity.projectRaw_index_operands readProjected
  have indexClosing : LoanClosingTyped env (Loans.enter code.context.length owner loans) false
      (code.child index.term) meanings .u64 :=
    ⟨typed.1,.u64,typedIndex,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  obtain ⟨_,indexConverted,_,indexRun⟩ :=
    index.checked_run_under_binder history indexClosing context aligned indexProjected computed domain readBody
      (.borrow origin) (some (.reference token))
  have ownerSize : OwnerSize env before.heap.metadata object (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using sizes.typed_variable history typedIndexOwner stored
  have evidenceClosed : LoanTyping.HasType env [] [] true (.decide left right)
      (.lt (index.term.subst meanings) (size.subst meanings)) := by
    simpa only [decideEvidence,Term.subst,substArgs,Op.binders,liftSub] using
      typedEvidence.ghostSubstitution history.wellFormed typed.1
  have within := evidenceClosed.decide_converted_bound history.wellFormed.admissible indexConverted
    (ownerSize.buffer_length history)
  have use := LoanTyping.ResourceQuantity.projectRaw_lend_owner_demand checkedLend
  have live := (world.live_once owner object 0 stored use).1
  let lender := Frame.lendFinish token object (some (code.context.length-owner)) origin reader.origin
    (code.child (.lam false first (.lam false again body)))
  let reading : List Frame := lender :: before.stack
  let openedHeap : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.lend before.heap.metadata object,before.heap.cell⟩
  let atReader : State := ⟨openedHeap,.evaluate reader,reading,before.pending⟩
  have opened : run 5 before = ⟨atReader,
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false readBody (.borrow origin))],5⟩ :=
    named_reader_steps before evaluating shape stored live
  have leased : openedHeap.metadata.heap.lease token = some object := by
    simp [openedHeap,SizedBufferHeap.lend,HeapLeases.put,token]
  let payload := before.heap.cell object offset
  let number := decodeInteger payload
  have read : openedHeap.read token offset = some payload := by
    unfold SizedBufferHeap.IndexedState.read
    rw [leased]
    exact ite_eq_left within
  let returned : State := ⟨openedHeap,.returned (.integer number),reading,before.pending⟩
  have readRun : run readTicks atReader = ⟨returned,[.legacy (.heap (.read token offset payload))],readTicks⟩ :=
    reference_index_operand_runs atReader rfl rfl (by rfl)
      (indexRun openedHeap (.indexOffset token :: reading) before.pending) read
  have finishedRead := join_runs opened readRun
  have reached : (run (fuel+(5+readTicks)) (initial program)).state = returned := by
    have observed := congrArg Result.state (run_add fuel (5+readTicks) (initial program))
    change (run (fuel+(5+readTicks)) (initial program)).state = (run (5+readTicks) before).state at observed
    rw [finishedRead] at observed
    exact observed
  have resultControl : (run (fuel+(5+readTicks)) (initial program)).state.control = .returned (.integer number) := by
    rw [reached]
  have actualFrame : (run (fuel+(5+readTicks)) (initial program)).state.stack = reading := by rw [reached]
  have resultType : LoanTyping.Conversion.Conv env .i64 (first.subst meanings) := by
    have principal : LoanTyping.Conversion.Conv env .i64 first := readTyped.principalView
    simpa only [Term.subst,substArgs] using principal.substitution meanings history.wellFormed.closed
  have resultKind : ValueKind env (.integer number) (first.subst meanings) := resultType
  have fit := decode_integer_bound ((initial_run_numbers program fuel).cells object offset)
  have valueTyped : LoanTyping.HasType env [] [] true (.integer number) (first.subst meanings) :=
    (LoanTyping.HasType.integer fit.1 fit.2).convert resultType
  obtain ⟨closeStep,_,retired,otherLeases,inventory⟩ :=
    reachable_lend_return_nonescape program (fuel+(5+readTicks)) history typed shape resultControl resultKind actualFrame
  rw [reached] at closeStep retired otherLeases inventory
  let closed : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.close openedHeap.metadata token,before.heap.cell⟩
  let actual := restoredContinuation code first again body origin reader.origin object (.integer number)
  have resumed := resume_lend_continuation_steps returned closed code first again body origin reader.origin number token object
    before.stack before.pending closeStep
  have finished : run duration before = ⟨⟨closed,.evaluate actual,before.stack,before.pending⟩,
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false readBody (.borrow origin)),
        .legacy (.heap (.read token offset payload)),.legacy (.heap (.close token)),
        .legacy (.activate false (.lam false again body) reader.origin),.legacy (.activate false body origin)],duration⟩ :=
    join_runs opened (join_runs readRun resumed)
  have older : ∀ outer < token, closed.metadata.heap.lease outer = before.heap.metadata.heap.lease outer := by
    intro outer previous
    change (SizedBufferHeap.close openedHeap.metadata token).heap.lease outer = _
    rw [otherLeases _ (Nat.ne_of_lt previous)]
    change (SizedBufferHeap.lend before.heap.metadata object).heap.lease outer = _
    simp [SizedBufferHeap.lend,HeapLeases.put,token,Nat.ne_of_lt previous]
  obtain ⟨savedReady,stackReady,pendingReady⟩ :=
    initial_run_finish_capture_bounds program (fuel+(5+readTicks)) actualFrame
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
  exact ⟨object,stored,within,finished,retired,older,finished.symm ▸ absent,inventory,
    restored_canonical_view code stored first again body reader.origin (.integer number),
    canonical_integer_restore_demand history shape typed context valueTyped closedSizes slots coverage
      entered stored checkedLend budget closedWorld complete reader.origin⟩

/-- After the computed loaned read has closed its lease, Free consumes
the restored owner through either retained alias. The actual typed tail
keeps its complete demand and every enclosing reader observation. -/
theorem reachable_computed_reference_reader_then_free (program : Term) (fuel : Nat) (index : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .lend (.var owner) (.lam false domain (index.referenceReader evidence))
      (.lam false first (.lam false again (.free (.var releaseIndex) tail))))
    (selected : releaseIndex = 0 ∨ releaseIndex = owner+2)
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (decideEvidence : evidence.subst meanings = .decide left right)
    (computed : index.value meanings = some offset)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let before := (run fuel (initial program)).state
    let token := before.heap.metadata.heap.nextLease
    let origin := (Term.var owner).subst code.origins
    let readBody := index.referenceReader evidence
    let reader := enter false domain readBody code.context code.origins code.values (.borrow origin) (some (.reference token))
    let body := Term.free (.var releaseIndex) tail
    let duration := (5+((3+((index.rename Nat.succ).ticks+1))+5))+3
    let result := run duration before
    ∃ object,
      let payload := before.heap.cell object offset
      let number := decodeInteger payload
      let closed := SizedBufferHeap.close (SizedBufferHeap.lend before.heap.metadata object) token
      let actual := restoredContinuation code first again body origin reader.origin object (.integer number)
      let canonical := canonicalContinuation code owner first body reader.origin (.integer number)
      let indices := Jihoo.Quantity.openOwner (owner+1)
      let next := canonical.child (tail.rename indices)
      let nextMeanings := consValues (.integer number) meanings
      code.values[owner]? = some (some (.owner object)) ∧
      result = ⟨⟨⟨SizedBufferHeap.release closed object,before.heap.cell⟩,
        .evaluate (actual.child tail),before.stack,before.pending⟩,
        [.legacy (.heap (.beginLease token object)),.legacy (.activate false readBody (.borrow origin)),
          .legacy (.heap (.read token offset payload)),.legacy (.heap (.close token)),
          .legacy (.activate false (.lam false again body) reader.origin),
          .legacy (.activate false body origin),.legacy (.heap (.free object))],duration⟩ ∧
      result.state.heap.metadata.heap.lease token = none ∧ result.state.heap.metadata.heap.live object = false ∧
      (∀ outer < token, result.state.heap.metadata.heap.lease outer = before.heap.metadata.heap.lease outer) ∧
      ¬ StateReferenceOccurs token result.state ∧
      CanonicalView (actual.child tail) next indices ∧
      LoanClosingTyped env loans false next nextMeanings type ∧ ValueContext env next nextMeanings ∧
      OwnerSizes env result.state.heap.metadata next nextMeanings ∧
      LoanSlots next loans result.state.activeStack ∧ LoanCoverage next loans result.state.activeStack ∧
      ∃ residual,
        LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans next.context next.term = some residual ∧
        LoanTyping.ResourceQuantity.LoanBudget next.context.length loans residual ∧
        OwnerDemandWorld result.state.heap.metadata next residual ∧ OwnerDemandWorld.Total next residual ∧
        ∀ alias, next.values[alias]? = some (some (.owner object)) → residual.demand alias = some 0 := by
  let before := (run fuel (initial program)).state
  let token := before.heap.metadata.heap.nextLease
  let origin := (Term.var owner).subst code.origins
  let readBody := index.referenceReader evidence
  let reader := enter false domain readBody code.context code.origins code.values (.borrow origin) (some (.reference token))
  let body := Term.free (.var releaseIndex) tail
  let readTicks := 3+((index.rename Nat.succ).ticks+1)
  let done := 5+(readTicks+5)
  obtain ⟨object,stored,_,restored,retired,otherLeases,absent,_,view,nextTyped,nextContext,nextSizes,nextSlots,nextCoverage,
    rest,restChecked,restBudget,_,nextWorld,nextTotal,_⟩ :=
    reachable_computed_reference_reader_restore (resourceFuel := resourceFuel+2) program fuel index history evaluating shape
      typed context sizes slots coverage entered decideEvidence computed checked budget world complete
  let closed : SizedBufferHeap.IndexedState :=
    ⟨SizedBufferHeap.close (SizedBufferHeap.lend before.heap.metadata object) token,before.heap.cell⟩
  let number := decodeInteger (before.heap.cell object offset)
  let actual := restoredContinuation code first again body origin reader.origin object (.integer number)
  let canonical := canonicalContinuation code owner first body reader.origin (.integer number)
  let atFree : State := ⟨closed,.evaluate actual,before.stack,before.pending⟩
  have reached : (run (fuel+done) (initial program)).state = atFree := by
    have observed := congrArg Result.state (run_add fuel done (initial program))
    change (run (fuel+done) (initial program)).state = (run done before).state at observed
    rw [restored] at observed
    exact observed
  have ready : (run (fuel+done) (initial program)).state.control = .evaluate actual := by rw [reached]
  have mapped : Jihoo.Quantity.openOwner (owner+1) releaseIndex = owner+1 := by
    rcases selected with rfl | rfl <;> rfl
  have sourceStored : canonical.values[owner+1]? = some (some (.owner object)) := stored
  have actualStored : actual.values[releaseIndex]? = some (some (.owner object)) := by
    rw [view.values releaseIndex,mapped]
    exact sourceStored
  obtain ⟨freed,dead,tailView,tailTyped,tailContext,tailSizes,tailCoverage,tailSlots,
    residual,tailChecked,tailBudget,tailWorld,tailTotal,noAliases⟩ :=
    reachable_canonical_free_preserves_owner_demand program (fuel+done) ready view (by rfl)
      nextTyped nextContext (reached.symm ▸ nextSizes) (reached.symm ▸ nextCoverage)
      (reached.symm ▸ nextSlots) actualStored restChecked restBudget (reached.symm ▸ nextWorld) nextTotal
  have finalState : (run (done+3) before).state = (run 3 (run (fuel+done) (initial program)).state).state := by
    have observed := congrArg Result.state (run_add done 3 before)
    change (run (done+3) before).state = (run 3 (run done before).state).state at observed
    rw [restored] at observed
    exact observed.trans (congrArg (fun state => (run 3 state).state) reached.symm)
  have completeRun := run_add done 3 before
  dsimp only at completeRun
  rw [← finalState] at dead
  rw [reached] at freed
  rw [restored,freed] at completeRun
  refine ⟨object,stored,completeRun,?_,dead,?_,?_,tailView,tailTyped,tailContext,finalState.symm ▸ tailSizes,
    finalState.symm ▸ tailSlots,finalState.symm ▸ tailCoverage,residual,tailChecked,tailBudget,
    finalState.symm ▸ tailWorld,tailTotal,noAliases⟩
  · rw [completeRun]
    exact retired
  · intro outer earlier
    rw [completeRun]
    exact otherLeases outer earlier
  · rw [completeRun]
    rw [restored] at absent
    exact absent

namespace Examples

private def computedLoanReadsStore : Term :=
  let buffer := Term.buffer (.natural 3)
  let index := fun slot => UnsignedOperand.add (.captured slot) (.add (.literal 1) (.literal 0))
  let value := IntegerOperand.arithmetic .add (.captured 2) (.arithmetic .mul (.literal 2) (.literal 3))
  let written := Term.store (.var 0) (index 3).term value.term (.var 1)
  let continuation := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let read := (index 4).referenceReader (.var 2)
  let borrowed := Term.lend (.var 0) (.lam false (.ref buffer) read) continuation
  let afterAllocation := Term.app (.lam false buffer borrowed) written
  let selected := Term.app (.lam false buffer afterAllocation) (.alloc (.natural 3) (.integer 3))
  let branch := Term.ifLt (index 1).term (.natural 3) selected (.integer 0)
  .app (.lam false .u64 (.app (.lam false .i64 branch) (.integer 40))) (.natural 1)

set_option maxRecDepth 4096 in
/-- A real computed Store feeds the borrowed Index of a checked Lend.
The reader sees the new cell, then the lease closes before its owner is freed. -/
theorem computed_loan_reads_store_then_frees :
    LoanTyping.MixedProgram.checkDeclaration 64 128 .empty ⟨.i64,computedLoanReadsStore⟩ =
      some ⟨.i64,computedLoanReadsStore⟩ ∧
    let result := run 100 (initial computedLoanReadsStore)
    observe result = .integer 46 ∧
      result.events.filterMap (fun event => match event with
        | .store _ _ _ | .legacy (.heap (.read _ _ _)) => some event
        | _ => none) = [.store 0 2 (encodeInteger 46),.legacy (.heap (.read 0 2 (encodeInteger 46)))] ∧
      result.events.filterMap Event.lifecycle? = [.alloc 0 3 (encodeInteger 3),.beginLease 0 0,.close 0,.free 0] ∧
      result.state.heap.metadata.heap.lease 0 = none ∧ result.state.heap.metadata.heap.live 0 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
