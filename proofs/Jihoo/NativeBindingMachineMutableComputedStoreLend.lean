import Jihoo.NativeBindingMachineMutableComputedBorrow

/-! An actual computed Store argument becomes the Buffer in the called
body's Lend. The indexed write, loaned read, and release correspond to
the same physical owner and the original checked body. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

/-- The checked application writes through a computed index, passes that
owner to the original closure, and reads the same cell under a fresh lease.
The reader returns the stored integer and Free releases its owner. Every
older lease keeps its indexed observations, and the typed tail keeps the
original residual loan and ownership interpretation. -/
theorem reachable_computed_store_lend_free (program : Term) (fuel : Nat)
    (index : UnsignedOperand) (value : IntegerOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .app (.lam false (.buffer count)
      (.lend (.var 0) (.lam false domain ((index.rename Nat.succ).referenceReader (evidence.rename Nat.succ)))
        (.lam false first (.lam false again (.free (.var releaseIndex) tail)))))
      (.store (.var owner) index.term value.term evidence))
    (releaseAlias : releaseIndex = 0 ∨ releaseIndex = 2)
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (decideEvidence : evidence.subst meanings = .decide left right)
    (computedIndex : index.value meanings = some offset)
    (computedValue : value.value meanings = some number)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+4) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let before := (run fuel (initial program)).state
    let token := before.heap.metadata.heap.nextLease
    let storeTicks := 3+(3+(index.ticks+(1+(value.ticks+1)))+1)
    let loanIndex := index.rename Nat.succ
    let lendTicks := (5+((3+((loanIndex.rename Nat.succ).ticks+1))+5))+3
    let argument := Term.store (.var owner) index.term value.term evidence
    let origin := (code.child argument).origin
    let callback := Term.free (.var releaseIndex) tail
    let readerBody := loanIndex.referenceReader (evidence.rename Nat.succ)
    let lendBody := Term.lend (.var 0) (.lam false domain readerBody) (.lam false first (.lam false again callback))
    let result := run (storeTicks+lendTicks) before
    ∃ (object : Nat) (written : SizedBufferHeap.IndexedState),
      let entry := enter false (.buffer count) lendBody code.context code.origins code.values origin (some (.owner object))
      let reader := enter false domain readerBody entry.context entry.origins entry.values (.borrow origin) (some (.reference token))
      let actual := restoredContinuation entry first again callback origin reader.origin object (.integer number)
      let canonical := canonicalContinuation entry 0 first callback reader.origin (.integer number)
      let indices := Jihoo.Quantity.openOwner 1
      let next := canonical.child (tail.rename indices)
      let nextMeanings := consValues (.integer number) (consValues (argument.subst meanings) meanings)
      code.values[owner]? = some (some (.owner object)) ∧
      result = ⟨⟨⟨SizedBufferHeap.release (SizedBufferHeap.close (SizedBufferHeap.lend before.heap.metadata object) token) object,
          written.cell⟩,.evaluate (actual.child tail),before.stack,before.pending⟩,
        [.store object offset (encodeInteger number),.legacy (.activate false lendBody origin),
          .legacy (.heap (.beginLease token object)),.legacy (.activate false readerBody (.borrow origin)),
          .legacy (.heap (.read token offset (encodeInteger number))),.legacy (.heap (.close token)),
          .legacy (.activate false (.lam false again callback) reader.origin),
          .legacy (.activate false callback origin),.legacy (.heap (.free object))],storeTicks+lendTicks⟩ ∧
      result.state.heap.metadata.heap.lease token = none ∧ result.state.heap.metadata.heap.live object = false ∧
      ¬ StateReferenceOccurs token result.state ∧ result.state.heap.cell object offset = encodeInteger number ∧
      (∀ queried cell, queried ≠ object ∨ cell ≠ offset → result.state.heap.cell queried cell = before.heap.cell queried cell) ∧
      (∀ older < token, ∀ cell, result.state.heap.read older cell = before.heap.read older cell) ∧
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
  let storeTicks := 3+(3+(index.ticks+(1+(value.ticks+1)))+1)
  let loanIndex := index.rename Nat.succ
  let lendTicks := (5+((3+((loanIndex.rename Nat.succ).ticks+1))+5))+3
  let argument := Term.store (.var owner) index.term value.term evidence
  let origin := (code.child argument).origin
  let callback := Term.free (.var releaseIndex) tail
  let readerBody := loanIndex.referenceReader (evidence.rename Nat.succ)
  let lendBody := Term.lend (.var 0) (.lam false domain readerBody) (.lam false first (.lam false again callback))
  let argumentMeaning := argument.subst meanings
  let callMeanings := consValues argumentMeaning meanings
  obtain ⟨object,heap,stored,storeRun,metadata,bytes,decoded,otherCells,oldReads,nextTyped,nextContext,
    nextSizes,nextSlots,nextCoverage,bodyReceipt,bodyChecked,bodyBudget,bodyWorld,bodyTotal,_,_⟩ :=
    reachable_computed_store_buffer_call (resourceFuel := resourceFuel+1) program fuel index value history evaluating shape
      typed context sizes slots coverage entered decideEvidence computedIndex computedValue checked budget world complete
  let entry := enter false (.buffer count) lendBody code.context code.origins code.values origin (some (.owner object))
  let atBody : State := ⟨heap,.evaluate entry,before.stack,before.pending⟩
  change run storeTicks before = ⟨atBody,[.store object offset (encodeInteger number),
    .legacy (.activate false lendBody origin)],storeTicks⟩ at storeRun
  have reached : (run (fuel+storeTicks) (initial program)).state = atBody := by
    have observed := congrArg Result.state (run_add fuel storeTicks (initial program))
    change (run (fuel+storeTicks) (initial program)).state = (run storeTicks before).state at observed
    rw [storeRun] at observed
    exact observed
  have selecting : (run (fuel+storeTicks) (initial program)).state.control = .evaluate entry := by rw [reached]
  have deeper : Loans.Entered entry.context.length loans := by
    intro frame member
    exact Nat.le_trans (entered frame member) (Nat.le_succ _)
  have loanComputed : loanIndex.value callMeanings = some offset := by
    change (index.rename Nat.succ).value callMeanings = some offset
    rw [UnsignedOperand.rename_value]
    exact computedIndex
  have loanProof : (evidence.rename Nat.succ).subst callMeanings = .decide left right := by
    simpa only [callMeanings,shift_subst_consValues] using decideEvidence
  obtain ⟨borrowedObject,selected,lendRun,retired,dead,older,absent,tailView,tailTyped,tailContext,tailSizes,
    tailSlots,tailCoverage,residual,tailChecked,tailBudget,tailWorld,tailTotal,noAliases⟩ :=
    reachable_computed_reference_reader_then_free program (fuel+storeTicks) loanIndex history selecting
      (by rfl) releaseAlias nextTyped nextContext (reached.symm ▸ nextSizes) (reached.symm ▸ nextSlots)
      (reached.symm ▸ nextCoverage) deeper loanProof loanComputed bodyChecked bodyBudget (reached.symm ▸ bodyWorld) bodyTotal
  have same : object = borrowedObject := Value.owner.inj (Option.some.inj (Option.some.inj selected))
  subst borrowedObject
  rw [reached] at lendRun retired dead older absent tailView tailTyped tailContext tailSizes tailSlots tailCoverage
  rw [reached] at tailChecked tailBudget tailWorld tailTotal noAliases
  have sameOrigin : (Term.var 0).subst entry.origins = origin := by
    simp only [entry,enter,Term.subst,consValues]
  have sameMetadata : atBody.heap.metadata = before.heap.metadata := metadata
  have sameToken : atBody.heap.metadata.heap.nextLease = token :=
    congrArg (fun metadata : SizedBufferHeap.State => metadata.heap.nextLease) sameMetadata
  have readDecoded : decodeInteger (atBody.heap.cell object offset) = number := decoded
  have readBytes : atBody.heap.cell object offset = encodeInteger number := bytes
  simp only [sameOrigin,sameToken,readDecoded]
    at lendRun retired older absent tailView tailTyped tailContext tailSizes tailSlots tailCoverage
  simp only [sameOrigin,sameToken,readDecoded] at tailChecked tailBudget tailWorld tailTotal noAliases
  rw [readBytes,sameMetadata] at lendRun
  have completeRun := join_runs storeRun lendRun
  have finalState : (run (storeTicks+lendTicks) before).state = (run lendTicks atBody).state := by
    have observed := congrArg Result.state (run_add storeTicks lendTicks before)
    dsimp only at observed
    rw [storeRun] at observed
    exact observed
  refine ⟨object,heap,stored,completeRun,finalState.symm ▸ retired,finalState.symm ▸ dead,finalState.symm ▸ absent,
    ?_,?_,?_,tailView,tailTyped,tailContext,finalState.symm ▸ tailSizes,finalState.symm ▸ tailSlots,
    finalState.symm ▸ tailCoverage,residual,tailChecked,tailBudget,finalState.symm ▸ tailWorld,tailTotal,noAliases⟩
  · rw [completeRun]
    exact bytes
  · intro queried cell other
    rw [completeRun]
    exact otherCells queried cell other
  · intro previous old cell
    have retained : (run (storeTicks+lendTicks) before).state.heap.metadata.heap.lease previous =
        before.heap.metadata.heap.lease previous :=
      (congrArg (fun state : State => state.heap.metadata.heap.lease previous) finalState).trans
        ((older previous old).trans (congrArg (fun metadata : SizedBufferHeap.State => metadata.heap.lease previous) sameMetadata))
    calc
      _ = heap.read previous cell := by
        unfold SizedBufferHeap.IndexedState.read
        rw [retained,metadata,completeRun]
        rfl
      _ = before.heap.read previous cell := oldReads previous cell

namespace Examples

private def innerComputedStoreLend : Term :=
  let buffer := Term.buffer (.natural 3)
  let index := UnsignedOperand.add (.captured 3) (.add (.literal 1) (.literal 0))
  let value := IntegerOperand.arithmetic .add (.captured 2) (.arithmetic .mul (.literal 2) (.literal 3))
  let written := Term.store (.var 0) index.term value.term (.var 1)
  let read := (index.rename Nat.succ).referenceReader (.var 2)
  let inner := Term.lend (.var 0) (.lam false (.ref buffer) read)
    (.lam false .i64 (.lam false buffer (.free (.var 2) (.var 1))))
  let called := Term.app (.lam false buffer inner) written
  let allocated := Term.app (.lam false buffer called) (.alloc (.natural 3) (.integer 3))
  let tested := Term.uadd (.var 1) (.uadd (.natural 1) (.natural 0))
  let branch := Term.ifLt tested (.natural 3) allocated (.integer 0)
  .app (.lam false .u64 (.app (.lam false .i64 branch) (.integer 40))) (.natural 1)

private def nestedComputedStoreLend : Term :=
  let buffer := Term.buffer (.natural 1)
  let outerRead := Term.index (.var 0) (.natural 0) (.decide (.natural 0) (.natural 1))
  let observed := Term.arith .add outerRead (.arith .add innerComputedStoreLend outerRead)
  let release := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let outer := Term.lend (.var 0) (.lam false (.ref buffer) observed) release
  .app (.lam false buffer outer) (.alloc (.natural 1) (.integer 5))

set_option maxRecDepth 4096 in
/-- Under a real older lease, the inner computed write and borrowed read
use a distinct allocation. The older lease observes its same cell after
the inner close and Free, then closes and releases its own allocation. -/
theorem nested_computed_store_lend_keeps_outer_read :
    LoanTyping.MixedProgram.checkDeclaration 96 192 .empty ⟨.i64,nestedComputedStoreLend⟩ =
      some ⟨.i64,nestedComputedStoreLend⟩ ∧
    let result := run 140 (initial nestedComputedStoreLend)
    observe result = .integer 56 ∧
      result.events.filterMap (fun event => match event with
        | .store _ _ _ | .legacy (.heap (.read _ _ _)) => some event
        | _ => none) =
        [.legacy (.heap (.read 0 0 (encodeInteger 5))),.store 1 2 (encodeInteger 46),
          .legacy (.heap (.read 1 2 (encodeInteger 46))),.legacy (.heap (.read 0 0 (encodeInteger 5)))] ∧
      result.events.filterMap Event.lifecycle? =
        [.alloc 0 1 (encodeInteger 5),.beginLease 0 0,.alloc 1 3 (encodeInteger 3),
          .beginLease 1 1,.close 1,.free 1,.close 0,.free 0] ∧
      result.state.heap.metadata.heap.nextLease = 2 := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
