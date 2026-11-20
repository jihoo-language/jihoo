import Jihoo.NativeBindingMachineMutableDynamicStore

/-! A captured-index owned Load carries its original dependent typing and
complete ownership interpretation through both actual callback bindings. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

theorem source_load_slots
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (first again body origin : Term) (object : Nat) (number : Int) :
    LoanSlots (restoredContinuation code first again body origin (.integer number) object (.integer number))
      loans stack := by
  let firstEntry := enter false first (.lam false again body) code.context code.origins code.values
    (.integer number) (some (.integer number))
  have one : LoanSlots firstEntry loans stack :=
    slots.enter entered false first (.lam false again body) (.integer number) (some (.integer number))
  have deeper : Loans.Entered firstEntry.context.length loans := by
    intro frame member
    exact Nat.le_trans (entered frame member) (Nat.le_succ _)
  exact one.enter deeper false again body origin (some (.owner object))

private theorem slot_not_index {code : Code} {owner index object offset : Nat}
    (storedOwner : code.values[owner]? = some (some (Value.owner object)))
    (storedIndex : code.values[index]? = some (some (Value.natural offset))) :
    owner ≠ index := by
  intro same
  subst index
  rw [storedOwner] at storedIndex
  cases storedIndex

/-- Original source typing and the complete projected resource world
select the actual owned Buffer and dynamic index. The real callback entry
keeps the exact read, dependent type, sizes, and every enclosing loan.
Its two original scopes supply the retained owner's exclusive demand,
the shifted capture demands, and the callback's own loan budget. -/
theorem reachable_captured_load_handoff (program : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata source meanings)
    (slots : LoanSlots source loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage source loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered source.context.length loans)
    (indexErasure : (lookup actual.context index).map (·.erased) =
      (lookup source.context (indices index)).map (·.erased))
    (shape : actual.term = .load (.var owner) (.var index) evidence (.lam false first (.lam false again body)))
    (decideEvidence : evidence.subst (meanings ∘ indices) = .decide left right)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans source.context source.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata source receipt)
    (complete : OwnerDemandWorld.Total source receipt) :
    let before := (run fuel (initial program)).state
    let result := run 9 before
    ∃ object offset,
      let payload := before.heap.cell object offset
      let number := decodeInteger payload
      let origin := (actual.child (.var owner)).origin
      let actualNext := restoredContinuation actual first again body origin (.integer number) object (.integer number)
      let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
        (body.rename (liftRenaming 2 indices)) origin (.integer number) object (.integer number)
      let nextMeanings := consValues (meanings (indices owner)) (consValues (.integer number) meanings)
      actual.values[owner]? = some (some (.owner object)) ∧ actual.values[index]? = some (some (.natural offset)) ∧
      meanings (indices index) = .natural offset ∧ offset < 2^64 ∧ offset < before.heap.metadata.length object ∧
      result = ⟨⟨before.heap,.evaluate actualNext,before.stack,before.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) (.integer number)),
          .legacy (.activate false body origin)],9⟩ ∧
      CanonicalView actualNext sourceNext (liftRenaming 2 indices) ∧
      LoanClosingTyped env loans false sourceNext nextMeanings type ∧ ValueContext env sourceNext nextMeanings ∧
      OwnerSizes env result.state.heap.metadata sourceNext nextMeanings ∧
      LoanSlots sourceNext loans result.state.activeStack ∧ LoanCoverage sourceNext loans result.state.activeStack ∧
      ∃ rawReceipt,
        LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans sourceNext.context sourceNext.term =
          some rawReceipt ∧
        let effective := reclose (functionTail sourceNext.term rawReceipt)
        LoanTyping.ResourceQuantity.LoanBudget sourceNext.context.length loans effective ∧
        effective.demand 0 = some 1 ∧ OwnerDemandWorld result.state.heap.metadata sourceNext effective ∧
        OwnerDemandWorld.Total sourceNext effective ∧
        ∀ alias, source.values[alias]? = some (some (.owner object)) → effective.demand (alias+2) = some 0 := by
  let before := (run fuel (initial program)).state
  let sourceFirst := first.rename indices
  let sourceAgain := again.rename (liftRenaming 1 indices)
  let sourceBody := body.rename (liftRenaming 2 indices)
  have sourceShape : source.term = .load (.var (indices owner)) (.var (indices index))
      (evidence.rename indices) (.lam false sourceFirst (.lam false sourceAgain sourceBody)) := by
    rw [← view.termEq,shape]
    simp only [sourceFirst,sourceAgain,sourceBody,Term.rename,renameArgs,Op.binders,liftRenaming]
  have wholeTyped := typed
  obtain ⟨closing,localType,sourceTyped,_⟩ := typed
  rw [sourceShape] at sourceTyped
  obtain ⟨size,ownerTyped,indexTyped,_⟩ := sourceTyped.load_inputs
  have closedOwner : LoanClosingTyped env loans false (source.child (.var (indices owner))) meanings
      ((Term.buffer size).subst meanings) :=
    ⟨closing,.buffer size,ownerTyped,.refl _⟩
  obtain ⟨actualOwner,sourceStored,kind⟩ :=
    (context.child _).variable_kind history closedOwner (aligned.child _) rfl
  have buffer : ValueKind env actualOwner (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using kind
  obtain ⟨object,rfl⟩ := buffer_kind_is_owner history.wellFormed.admissible buffer
  have closedIndex : LoanClosingTyped env loans false (source.child (.var (indices index))) meanings .u64 :=
    ⟨closing,.u64,indexTyped,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  obtain ⟨actualIndex,sourceIndex,indexKind⟩ :=
    (context.child _).variable_kind history closedIndex (aligned.child _) rfl
  obtain ⟨position,rfl⟩ := indexKind.natural_shape history.wellFormed.admissible
  have distinct := slot_not_index sourceStored sourceIndex
  have storedOwner := (view.values owner).trans sourceStored
  obtain ⟨bodyFuel,_,firstMode,ownerMode,rawReceipt,fuelShape,indexChecked,resolved,bodyChecked,receiptShape⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_named_load_scopes (sourceShape ▸ checked)
  have fuelEq : bodyFuel = resourceFuel := by omega
  subst bodyFuel
  obtain ⟨_,_,_,ownerType,_⟩ := LoanTyping.load_retained_body history.wellFormed sourceTyped
  rw [LoanTyping.ResourceQuantity.raw_variable_use indexChecked,
    resolved.convertible_buffer_linear history.wellFormed.admissible ownerType] at receiptShape
  let effective := reclose (functionTail sourceBody rawReceipt)
  let operands : Jihoo.Quantity.Control := .seq (.use (indices owner)) (.seq (.use (indices index)) .pure)
  let scopes : Jihoo.Quantity.Control := .scope firstMode (.scope .linear effective)
  have receiptShape : receipt = .seq operands (.once scopes) := receiptShape
  have singleOperand : operands.demand (indices owner) = some 1 := by
    simp [operands,Control.demand,Ne.symm distinct]
  obtain ⟨_,_,_,_,separation⟩ := (receiptShape ▸ world).sequence (receiptShape ▸ complete)
  have zero := separation (indices owner) (indices owner) object 0 sourceStored sourceStored singleOperand
  change scopes.demand (indices owner) = some 0 at zero
  have one : receipt.demand (indices owner) = some 1 := by
    rw [receiptShape]
    simp [Control.demand,singleOperand,zero]
  have live := (world.live_once (indices owner) object 0 sourceStored one).1
  obtain ⟨offset,storedIndex,indexMeaning,indexWidth,within,_,readOnly,_,_,_⟩ :=
    reachable_typed_variable_load program fuel history evaluating view wholeTyped context sizes indexErasure shape
      decideEvidence storedOwner live coverage checked budget
  obtain ⟨contextOffset,executed,nextView,nextTyped,nextContext,nextSizes,nextCoverage,_⟩ :=
    reachable_variable_load_contexts program fuel history evaluating view wholeTyped context sizes indexErasure shape
      decideEvidence storedOwner live coverage entered checked budget
  have sameEvents := congrArg Result.events (executed.symm.trans readOnly)
  have sameOffset : contextOffset = offset := by
    exact (Event.load.inj (List.cons.inj sameEvents).1).2.1
  subst contextOffset
  have checkedIndex := (view.values index).symm.trans storedIndex
  have demand := LoanTyping.ResourceQuantity.LoadDemand.of_scopes receiptShape one
  let number := decodeInteger (before.heap.cell object offset)
  let origin := (actual.child (.var owner)).origin
  obtain ⟨nextWorld,aliases⟩ := world.load_handoff sourceStored checkedIndex one demand
    sourceFirst sourceAgain sourceBody origin number
  have nextTotal := complete.load_handoff checkedIndex demand sourceFirst sourceAgain sourceBody origin object number
  have heapEq := congrArg (fun output : Result => output.state.heap.metadata) executed
  have stackEq := congrArg (fun output : Result => output.state.activeStack) executed
  change (run 9 before).state.activeStack = before.activeStack at stackEq
  have nextSlots := source_load_slots slots entered sourceFirst sourceAgain sourceBody origin object number
  have callbackBudget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans scopes :=
    (receiptShape ▸ budget).sequence.2
  have deeper : Loans.Entered (source.context.length+1) loans := by
    intro frame member
    exact Nat.le_trans (entered frame member) (Nat.le_succ _)
  have bodyBudget := (callbackBudget.scope entered).scope deeper
  exact ⟨object,offset,storedOwner,storedIndex,indexMeaning,indexWidth,within,executed,nextView,nextTyped,nextContext,
    nextSizes,stackEq.symm ▸ nextSlots,nextCoverage,rawReceipt,bodyChecked,bodyBudget,demand.returned,
    heapEq.symm ▸ nextWorld,nextTotal,aliases⟩

/-- The callback can release its newly returned owner in three further
steps. Exactly the cell read at entry is retained as the scalar binding.
The actual successor keeps the original dependent tail type, both loan
invariants, and the complete demand of every live remaining owner. -/
theorem reachable_captured_load_then_free (program : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata source meanings)
    (slots : LoanSlots source loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage source loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered source.context.length loans)
    (indexErasure : (lookup actual.context index).map (·.erased) =
      (lookup source.context (indices index)).map (·.erased))
    (shape : actual.term = .load (.var owner) (.var index) evidence
      (.lam false first (.lam false again (.free (.var 0) tail))))
    (decideEvidence : evidence.subst (meanings ∘ indices) = .decide left right)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+5) env loans source.context source.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata source receipt)
    (complete : OwnerDemandWorld.Total source receipt) :
    let before := (run fuel (initial program)).state
    let result := run 12 before
    ∃ object offset,
      let body := Term.free (.var 0) tail
      let payload := before.heap.cell object offset
      let number := decodeInteger payload
      let origin := (actual.child (.var owner)).origin
      let actualNext := restoredContinuation actual first again body origin (.integer number) object (.integer number)
      let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
        (body.rename (liftRenaming 2 indices)) origin (.integer number) object (.integer number)
      let sourceTail := sourceNext.child (tail.rename (liftRenaming 2 indices))
      let nextMeanings := consValues (meanings (indices owner)) (consValues (.integer number) meanings)
      actual.values[owner]? = some (some (.owner object)) ∧ actual.values[index]? = some (some (.natural offset)) ∧
      meanings (indices index) = .natural offset ∧ offset < before.heap.metadata.length object ∧
      result = ⟨⟨⟨SizedBufferHeap.release before.heap.metadata object,before.heap.cell⟩,
        .evaluate (actualNext.child tail),before.stack,before.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) (.integer number)),
          .legacy (.activate false body origin),.legacy (.heap (.free object))],12⟩ ∧
      result.state.heap.metadata.heap.live object = false ∧
      CanonicalView (actualNext.child tail) sourceTail (liftRenaming 2 indices) ∧
      LoanClosingTyped env loans false sourceTail nextMeanings type ∧ ValueContext env sourceTail nextMeanings ∧
      OwnerSizes env result.state.heap.metadata sourceTail nextMeanings ∧
      LoanSlots sourceTail loans result.state.activeStack ∧ LoanCoverage sourceTail loans result.state.activeStack ∧
      ∃ residual,
        LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans sourceTail.context sourceTail.term =
          some residual ∧
        LoanTyping.ResourceQuantity.LoanBudget sourceTail.context.length loans residual ∧
        OwnerDemandWorld result.state.heap.metadata sourceTail residual ∧ OwnerDemandWorld.Total sourceTail residual ∧
        ∀ alias, sourceTail.values[alias]? = some (some (.owner object)) → residual.demand alias = some 0 := by
  let before := (run fuel (initial program)).state
  let body := Term.free (.var 0) tail
  obtain ⟨object,offset,stored,storedIndex,indexMeaning,_,within,executed,nextView,nextTyped,
    nextContext,nextSizes,nextSlots,nextCoverage,receipt,projected,bodyBudget,_,bodyWorld,bodyTotal,_⟩ :=
    reachable_captured_load_handoff (resourceFuel := resourceFuel+2) program fuel history evaluating view typed context
      aligned sizes slots coverage entered indexErasure shape decideEvidence checked budget world complete
  let number := decodeInteger (before.heap.cell object offset)
  let origin := (actual.child (.var owner)).origin
  let actualNext := restoredContinuation actual first again body origin (.integer number) object (.integer number)
  let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
    (body.rename (liftRenaming 2 indices)) origin (.integer number) object (.integer number)
  have bodyShape : sourceNext.term = .free (.var 0) (tail.rename (liftRenaming 2 indices)) := by
    change body.rename (liftRenaming 2 indices) = _
    simp only [body,Term.rename,renameArgs,Op.binders,liftRenaming]
    rfl
  have raw := projected
  change LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans sourceNext.context sourceNext.term =
    some receipt at raw
  rw [bodyShape] at raw
  have effective := LoanTyping.ResourceQuantity.projectRaw_free_callback_body raw
  change LoanTyping.ResourceQuantity.LoanBudget sourceNext.context.length loans
    (reclose (functionTail sourceNext.term receipt)) at bodyBudget
  change OwnerDemandWorld (run 9 before).state.heap.metadata sourceNext
    (reclose (functionTail sourceNext.term receipt)) at bodyWorld
  change OwnerDemandWorld.Total sourceNext (reclose (functionTail sourceNext.term receipt)) at bodyTotal
  rw [bodyShape,effective] at bodyBudget bodyWorld bodyTotal
  have reached : (run (fuel+9) (initial program)).state = (run 9 before).state := by
    have observed := congrArg Result.state (run_add fuel 9 (initial program))
    exact observed
  have atFree : (run (fuel+9) (initial program)).state.control = .evaluate actualNext := by
    rw [reached,executed]
  obtain ⟨freed,dead,tailView,tailTyped,tailContext,tailSizes,tailCoverage,tailSlots,
    residual,tailChecked,tailBudget,tailWorld,tailTotal,noAliases⟩ :=
    reachable_canonical_free_preserves_owner_demand program (fuel+9) atFree nextView (by rfl)
      nextTyped nextContext (reached.symm ▸ nextSizes) (reached.symm ▸ nextCoverage) (reached.symm ▸ nextSlots)
      (by rfl) projected bodyBudget (reached.symm ▸ bodyWorld) bodyTotal
  have finalState : (run 12 before).state = (run 3 (run (fuel+9) (initial program)).state).state := by
    rw [reached]
    have observed := congrArg Result.state (run_add 9 3 before)
    exact observed
  have entire := run_add 9 3 before
  dsimp only at entire
  rw [← reached,freed,reached,executed] at entire
  exact ⟨object,offset,stored,storedIndex,indexMeaning,within,entire,finalState.symm ▸ dead,tailView,tailTyped,tailContext,
    finalState.symm ▸ tailSizes,finalState.symm ▸ tailSlots,finalState.symm ▸ tailCoverage,residual,
    tailChecked,tailBudget,finalState.symm ▸ tailWorld,tailTotal,noAliases⟩

namespace Examples

private def capturedStoreLoadFree : Term :=
  let buffer := Term.buffer (.natural 2)
  let value := IntegerOperand.arithmetic .add (.captured 1) (.literal 6)
  let written := Term.store (.alloc (.natural 2) (.integer 3)) (.var 2) value.term (.var 0)
  let continuation := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let loaded := Term.load (.var 0) (.var 3) (.var 1) continuation
  let selected := Term.app (.lam false buffer loaded) written
  let branch := Term.ifLt (.var 1) (.natural 2) selected (.integer 0)
  .app (.lam false .u64 (.app (.lam false .i64 branch) (.integer 40))) (.natural 1)

set_option maxRecDepth 4096 in
/-- An actual branch certificate and captured index drive the indexed
Store and Load. The callback reads the written cell and frees its owner. -/
theorem captured_store_load_free_reads_written_cell :
    LoanTyping.MixedProgram.checkDeclaration 64 128 .empty ⟨.i64,capturedStoreLoadFree⟩ =
      some ⟨.i64,capturedStoreLoadFree⟩ ∧
    let result := run 70 (initial capturedStoreLoadFree)
    observe result = .integer 46 ∧
      result.events.filterMap (fun event => match event with
        | .store object offset payload | .load object offset payload => some (object,offset,payload)
        | _ => none) = [(0,1,encodeInteger 46),(0,1,encodeInteger 46)] ∧
      result.events.filterMap Event.lifecycle? = [.alloc 0 2 (encodeInteger 3),.free 0] ∧
      result.state.heap.metadata.heap.live 0 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
