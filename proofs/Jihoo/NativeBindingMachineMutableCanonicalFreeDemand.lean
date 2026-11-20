import Jihoo.NativeBindingMachineMutableDemandTotality
import Jihoo.NativeBindingMachineMutableReaderReturnDemand

/-! The real machine may retain two aliases of one returned owner. Free
uses the canonical source receipt to consume the physical unit from either
runtime slot, then transports the original typed continuation world. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds

private theorem variable_free_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .free (.var owner) tail)
    (stored : code.values[owner]? = some (some (.owner object)))
    (live : state.heap.metadata.heap.live object = true)
    (guard : freeGuard state.heap.metadata object = true) :
    let released : SizedBufferHeap.IndexedState :=
      ⟨SizedBufferHeap.release state.heap.metadata object,state.heap.cell⟩
    run 3 state = ⟨⟨released,.evaluate (code.child tail),state.stack,state.pending⟩,
      [.legacy (.heap (.free object))],3⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,stored,executeLegacy,execute,returnAction,
    live,guard,ite_true,Option.map_none,Option.map_some]
  rfl

/-- Physical liveness and a single source use follow from the complete
quantity receipt and its owner world. The actual runtime alias can differ
from the single canonical source slot without introducing a second unit. -/
theorem reachable_canonical_free_preserves_owner_demand (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (shape : actual.term = .free (.var owner) tail)
    (typed : LoanClosingTyped env loans false source meanings type)
    (values : ValueContext env source meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata source meanings)
    (coverage : LoanCoverage source loans (run fuel (initial term)).state.activeStack)
    (slots : LoanSlots source loans (run fuel (initial term)).state.activeStack)
    (stored : actual.values[owner]? = some (some (.owner object)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context
      source.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial term)).state.heap.metadata source receipt)
    (complete : OwnerDemandWorld.Total source receipt) :
    let before := (run fuel (initial term)).state
    let sourceTail := source.child (tail.rename indices)
    let result := run 3 before
    result = ⟨⟨⟨SizedBufferHeap.release before.heap.metadata object,before.heap.cell⟩,
      .evaluate (actual.child tail),before.stack,before.pending⟩,[.legacy (.heap (.free object))],3⟩ ∧
    result.state.heap.metadata.heap.live object = false ∧
    CanonicalView (actual.child tail) sourceTail indices ∧
    LoanClosingTyped env loans false sourceTail meanings type ∧ ValueContext env sourceTail meanings ∧
    OwnerSizes env result.state.heap.metadata sourceTail meanings ∧
    LoanCoverage sourceTail loans result.state.activeStack ∧ LoanSlots sourceTail loans result.state.activeStack ∧
    ∃ residual,
      LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans sourceTail.context sourceTail.term =
        some residual ∧ LoanTyping.ResourceQuantity.LoanBudget sourceTail.context.length loans residual ∧
      OwnerDemandWorld result.state.heap.metadata sourceTail residual ∧ OwnerDemandWorld.Total sourceTail residual ∧
      ∀ alias, sourceTail.values[alias]? = some (some (.owner object)) → residual.demand alias = some 0 := by
  let before := (run fuel (initial term)).state
  let sourceTail := source.child (tail.rename indices)
  have sourceShape : source.term = .free (.var (indices owner)) (tail.rename indices) := by
    rw [← view.termEq,shape]
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming]
  have sourceStored := (view.values owner).symm.trans stored
  rw [sourceShape] at checked
  obtain ⟨_,residual,_,_,tailChecked,receiptShape⟩ := LoanTyping.ResourceQuantity.projectRaw_free_variable checked
  obtain ⟨consumption,counted⟩ := complete (indices owner) object sourceStored
  rw [receiptShape] at counted
  obtain ⟨remaining,residualDemand,added⟩ :
      ∃ remaining, residual.demand (indices owner) = some remaining ∧ 1+remaining = consumption := by
    cases observed : residual.demand (indices owner) with
    | none =>
        simp [Jihoo.Quantity.Control.demand,observed,bind,Option.bind] at counted
    | some remaining =>
        exact ⟨remaining,rfl,by simpa [Jihoo.Quantity.Control.demand,observed,bind,Option.bind] using counted⟩
  have originalUse : receipt.demand (indices owner) = some (remaining+1) := by
    rw [receiptShape]
    simpa only [Nat.add_comm remaining 1,added] using counted
  obtain ⟨live,empty⟩ := world.live_once (indices owner) object remaining sourceStored originalUse
  have one : receipt.demand (indices owner) = some 1 := by simpa only [empty,Nat.zero_add] using originalUse
  have unused : residual.demand (indices owner) = some 0 := empty ▸ residualDemand
  have inactive := LoanTyping.ResourceQuantity.projectRaw_free_inactive checked budget
  have invariant := initial_run_invariant term fuel
  have guard := (invariant.2.free_guard_iff invariant.1).mpr (coverage.inactive sourceStored inactive)
  have ran := variable_free_steps before evaluating shape stored live guard
  obtain ⟨closing,localType,sourceTyped,converted⟩ := typed
  rw [sourceShape] at sourceTyped
  have afterTyped : LoanClosingTyped env loans false sourceTail meanings type :=
    ⟨closing,localType,sourceTyped.free_tail,converted⟩
  have residualSizes := (reachable_run_owner_sizes term fuel 3 sizes).child (tail.rename indices)
  have allOldAliases : ∀ alias, sourceTail.values[alias]? = some (some (.owner object)) →
      residual.demand alias = some 0 := by
    intro alias aliased
    by_cases same : alias = indices owner
    · exact same.symm ▸ unused
    · have noDemand := world.exclusive (indices owner) alias object 0 (Ne.symm same) sourceStored aliased one
      rw [receiptShape] at noDemand
      cases observed : residual.demand alias with
      | none => simp [Jihoo.Quantity.Control.demand,Ne.symm same,observed,bind,Option.bind] at noDemand
      | some demand =>
          have zero : demand = 0 := by
            simpa [Jihoo.Quantity.Control.demand,Ne.symm same,observed,bind,Option.bind] using noDemand
          simp [zero]
  rw [receiptShape] at world complete budget one
  have nextWorld := world.release (tail := tail.rename indices) sourceStored one unused
  have nextTotal := complete.free_tail (tail := tail.rename indices)
  refine ⟨ran,?_⟩
  dsimp only at ran ⊢
  rw [ran]
  exact ⟨by simp [SizedBufferHeap.release,HeapLeases.put],view.child tail,afterTyped,values.child _,
    ran ▸ residualSizes,coverage.child _,slots.child _,residual,tailChecked,budget.sequence.2.sequence.1,
    nextWorld,nextTotal,allOldAliases⟩

/-- The direct named reader, its close, and Free through either of the
retained aliases are one actual 18-step prefix. The arbitrary checked
tail retains its original type and complete owner-demand world. -/
theorem reachable_named_reader_then_free_alias (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .lend (.var owner)
      (.lam false domain (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))))
      (.lam false first (.lam false again (.free (.var releaseIndex) tail))))
    (selected : releaseIndex = 0 ∨ releaseIndex = owner+2)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial term)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial term)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial term)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let state := (run fuel (initial term)).state
    let origin := (Term.var owner).subst code.origins
    let token := state.heap.metadata.heap.nextLease
    let reader := Term.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))
    let readerCode := enter false domain reader code.context code.origins code.values
      (.borrow origin) (some (.reference token))
    let payload := state.heap.cell object offset
    let number := decodeInteger payload
    let body := Term.free (.var releaseIndex) tail
    let actual := restoredContinuation code first again body origin readerCode.origin object (.integer number)
    let source := canonicalContinuation code owner first body readerCode.origin (.integer number)
    let nextMeanings := consValues (.integer number) meanings
    let indexMap := Jihoo.Quantity.openOwner (owner+1)
    let sourceTail := source.child (tail.rename indexMap)
    let result := run 18 state
    result.steps = 18 ∧ result.state.control = .evaluate (actual.child tail) ∧
    result.events =
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false reader (.borrow origin)),
        .legacy (.heap (.read token offset payload)),.legacy (.heap (.close token)),
        .legacy (.activate false (.lam false again body) readerCode.origin),.legacy (.activate false body origin),
        .legacy (.heap (.free object))] ∧
    result.state.heap.metadata.heap.lease token = none ∧ result.state.heap.metadata.heap.live object = false ∧
    (∀ outer < token, result.state.heap.metadata.heap.lease outer = state.heap.metadata.heap.lease outer) ∧
    CanonicalView (actual.child tail) sourceTail indexMap ∧
    LoanClosingTyped env loans false sourceTail nextMeanings type ∧ ValueContext env sourceTail nextMeanings ∧
    OwnerSizes env result.state.heap.metadata sourceTail nextMeanings ∧
    LoanCoverage sourceTail loans result.state.activeStack ∧ LoanSlots sourceTail loans result.state.activeStack ∧
    ∃ residual,
      LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans sourceTail.context sourceTail.term =
        some residual ∧ LoanTyping.ResourceQuantity.LoanBudget sourceTail.context.length loans residual ∧
      OwnerDemandWorld result.state.heap.metadata sourceTail residual ∧ OwnerDemandWorld.Total sourceTail residual ∧
      ∀ alias, sourceTail.values[alias]? = some (some (.owner object)) → residual.demand alias = some 0 := by
  let state := (run fuel (initial term)).state
  let origin := (Term.var owner).subst code.origins
  let token := state.heap.metadata.heap.nextLease
  let reader := Term.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))
  let readerCode := enter false domain reader code.context code.origins code.values
    (.borrow origin) (some (.reference token))
  let number := decodeInteger (state.heap.cell object offset)
  let body := Term.free (.var releaseIndex) tail
  let actual := restoredContinuation code first again body origin readerCode.origin object (.integer number)
  let source := canonicalContinuation code owner first body readerCode.origin (.integer number)
  obtain ⟨ran,closed,_,outer,_,view,nextTyped,nextValues,nextSizes,nextSlots,nextCoverage,
    rest,restChecked,nextBudget,_,nextWorld,nextTotal,_⟩ :=
    reachable_named_index_reader_restore_demand (resourceFuel := resourceFuel+2) term fuel history evaluating
      shape typed context sizes slots coverage entered stored checked budget world complete
  have mapped : Jihoo.Quantity.openOwner (owner+1) releaseIndex = owner+1 := by
    rcases selected with rfl | rfl <;> rfl
  have sourceStored : source.values[owner+1]? = some (some (.owner object)) := stored
  have actualStored : actual.values[releaseIndex]? = some (some (.owner object)) := by
    rw [view.values releaseIndex,mapped]
    exact sourceStored
  have reached := run_add fuel 15 (initial term)
  have beforeFree : (run (fuel+15) (initial term)).state = (run 15 state).state := by
    have fields := congrArg Result.state reached
    exact fields
  have atFree : (run (fuel+15) (initial term)).state.control = .evaluate actual := by
    rw [beforeFree,ran]
  obtain ⟨freed,dead,tailView,tailTyped,tailValues,tailSizes,tailCoverage,tailSlots,resource⟩ :=
    reachable_canonical_free_preserves_owner_demand term (fuel+15) atFree view (by rfl)
      nextTyped nextValues (beforeFree.symm ▸ nextSizes) (beforeFree.symm ▸ nextCoverage)
      (beforeFree.symm ▸ nextSlots) actualStored restChecked nextBudget (beforeFree.symm ▸ nextWorld) nextTotal
  have entire := run_add 15 3 state
  have sameState : (run 18 state).state = (run 3 (run (fuel+15) (initial term)).state).state := by
    rw [beforeFree]
    have fields := congrArg Result.state entire
    exact fields
  have eventTrace : (run 18 state).events =
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false reader (.borrow origin)),
        .legacy (.heap (.read token offset (state.heap.cell object offset))),.legacy (.heap (.close token)),
        .legacy (.activate false (.lam false again body) readerCode.origin),.legacy (.activate false body origin),
        .legacy (.heap (.free object))] := by
    dsimp only at entire
    rw [← beforeFree,freed,ran] at entire
    have fields := congrArg Result.events entire
    exact fields
  have countSteps : (run 18 state).steps = 18 := by
    dsimp only at entire
    rw [← beforeFree,freed,ran] at entire
    have fields := congrArg Result.steps entire
    exact fields
  have tailControl : (run 18 state).state.control = .evaluate (actual.child tail) := by
    rw [sameState,freed]
  have closedLease : (run 18 state).state.heap.metadata.heap.lease token = none := by
    rw [sameState,freed]
    exact beforeFree.symm ▸ closed
  have outerLeases : ∀ kept < token,
      (run 18 state).state.heap.metadata.heap.lease kept = state.heap.metadata.heap.lease kept := by
    intro kept range
    rw [sameState,freed]
    exact beforeFree.symm ▸ outer kept range
  dsimp only
  exact ⟨countSteps,tailControl,eventTrace,closedLease,sameState.symm ▸ dead,outerLeases,tailView,
    tailTyped,tailValues,sameState.symm ▸ tailSizes,sameState.symm ▸ tailCoverage,sameState.symm ▸ tailSlots,
    sameState.symm ▸ resource⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
