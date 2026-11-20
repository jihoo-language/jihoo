import Jihoo.NativeBindingMachineMutableArithmeticReaderTree
import Jihoo.NativeBindingMachineMutableCanonicalFreeDemand

/-! The computed reader's actual close resumes the original retained body.
The checked resource projection supplies the restored owner unit, including
the zero demand of other aliases of the same physical allocation. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

private theorem bind_lend_continuation (heap : SizedBufferHeap.IndexedState)
    (code : Code) (first again body ownerOrigin resultOrigin : Term) (number : Int) (object : Nat)
    (stack : List Frame) (pending : List (BufferFrame × List Frame)) :
    let continuation := code.child (.lam false first (.lam false again body))
    let next := restoredContinuation code first again body ownerOrigin resultOrigin object (.integer number)
    run 4 ⟨heap,.evaluate continuation,.lendContinuation object ownerOrigin resultOrigin (.integer number) :: stack,
      pending⟩ =
      ⟨⟨heap,.evaluate next,stack,pending⟩,
        [.legacy (.activate false (.lam false again body) resultOrigin),.legacy (.activate false body ownerOrigin)],4⟩ := by
  simp only [run,step,Code.child,evaluateAction,executeLegacy,execute,returnAction,applyValue,
    enter,restoredContinuation,Option.map_none,Option.map_some]
  rfl

/-- A real close step is followed by the four transitions that bind the
observed integer and the restored owner in the original continuation. -/
theorem resume_lend_continuation_steps (state : State) (heap : SizedBufferHeap.IndexedState)
    (code : Code) (first again body ownerOrigin resultOrigin : Term) (number : Int) (token object : Nat)
    (stack : List Frame) (pending : List (BufferFrame × List Frame))
    (closed : step state = some (⟨heap,.evaluate (code.child (.lam false first (.lam false again body))),
      .lendContinuation object ownerOrigin resultOrigin (.integer number) :: stack,pending⟩,
      some (.legacy (.heap (.close token))))) :
    let next := restoredContinuation code first again body ownerOrigin resultOrigin object (.integer number)
    run 5 state = ⟨⟨heap,.evaluate next,stack,pending⟩,
      [.legacy (.heap (.close token)),.legacy (.activate false (.lam false again body) resultOrigin),
        .legacy (.activate false body ownerOrigin)],5⟩ := by
  rw [run,closed]
  dsimp only
  rw [bind_lend_continuation]
  rfl

/-- Restore the canonical integer binding and its owner accounting from the
same checked Lend receipt. The selected reader evaluation is independent of
this proof as long as it supplies the observed integer at the original type. -/
theorem canonical_integer_restore_demand
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (shape : code.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (argument : LoanTyping.HasType env [] [] true (.integer number) (first.subst meanings))
    (sizes : OwnerSizes env heap code meanings) (slots : LoanSlots code loans stack)
    (coverage : LoanCoverage code loans stack) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld heap code receipt) (complete : OwnerDemandWorld.Total code receipt)
    (resultOrigin : Term) :
    let canonical := canonicalContinuation code owner first body resultOrigin (.integer number)
    let nextMeanings := consValues (.integer number) meanings
    LoanClosingTyped env loans false canonical nextMeanings type ∧ ValueContext env canonical nextMeanings ∧
    OwnerSizes env heap canonical nextMeanings ∧ LoanSlots canonical loans stack ∧ LoanCoverage canonical loans stack ∧
    ∃ rest, LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans canonical.context canonical.term = some rest ∧
      LoanTyping.ResourceQuantity.LoanBudget canonical.context.length loans rest ∧
      rest.demand (owner+1) = some 1 ∧ OwnerDemandWorld heap canonical rest ∧ OwnerDemandWorld.Total canonical rest ∧
      ∀ alias, alias ≠ owner → code.values[alias]? = some (some (.owner object)) → rest.demand (alias+1) = some 0 := by
  obtain ⟨_,_,_,_,_,rest,_,_,_,_,_,binder,bodyTyped,_,_,restProjected,_,ownerOne,receiptShape⟩ :=
    LoanTyping.ResourceQuantity.dependent_raw_project_contract checked
  rw [receiptShape] at world complete budget
  obtain ⟨_,_,restWorld,restTotal,_⟩ := world.sequence complete
  have scopeValid := NativeQuantity.demand_localScopes _ ownerOne
  obtain ⟨nextWorld,nextTotal⟩ := restWorld.enter_integer_scope restTotal scopeValid first
    (body.rename (Jihoo.Quantity.openOwner (owner+1))) resultOrigin number
  have restoredOne : rest.demand (owner+1) = some 1 := (demand_under_checked_scope scopeValid owner).symm.trans ownerOne
  have aliases : ∀ alias, alias ≠ owner → code.values[alias]? = some (some (.owner object)) →
      rest.demand (alias+1) = some 0 := by
    intro alias other found
    have unused := restWorld.exclusive owner alias object 0 (Ne.symm other) stored found ownerOne
    exact (demand_under_checked_scope scopeValid alias).symm.trans unused
  obtain ⟨nextTyped,nextContext⟩ := typed_canonical_integer_restore history typed context shape
    argument binder bodyTyped stored resultOrigin
  have nextSizes := sizes.enter_integer first (body.rename (Jihoo.Quantity.openOwner (owner+1))) resultOrigin number
  have nextSlots := slots.enter entered false first (body.rename (Jihoo.Quantity.openOwner (owner+1)))
    resultOrigin (some (.integer number))
  have nextCoverage := coverage.enter_nonowner entered false first (body.rename (Jihoo.Quantity.openOwner (owner+1)))
    resultOrigin (some (.integer number)) (by intro queried impossible; cases impossible)
  rw [LoanTyping.ResourceQuantity.restore_body_is_alias] at restProjected
  exact ⟨nextTyped,nextContext,nextSizes,nextSlots,nextCoverage,rest,restProjected,budget.sequence.2.scope entered,
    restoredOne,nextWorld,nextTotal,aliases⟩

/-- A successful typed arithmetic reader runs from the original named Lend
through both actual continuation bindings. The canonical continuation keeps
the original dependent result type and the exact residual checked receipt.
The returned owner still has one physical unit of demand, while retained
aliases of that allocation carry zero. -/
theorem reachable_arithmetic_tree_restore_demand (term : Term) (fuel : Nat) (reader : ArithmeticReader)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .lend (.var owner) (.lam false domain reader.term)
      (.lam false first (.lam false again body)))
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial term)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial term)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial term)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let state := (run fuel (initial term)).state
    let origin := (Term.var owner).subst code.origins
    let token := state.heap.metadata.heap.nextLease
    let entry := enter false domain reader.term code.context code.origins code.values (.borrow origin) (some (.reference token))
    let readerState := (run 5 state).state
    let trace := reader.replay entry readerState.heap token object readerState.stack
    trace.outcome = .integer number →
    let closed : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.close readerState.heap.metadata token,state.heap.cell⟩
    let actual := restoredContinuation code first again body origin entry.origin object (.integer number)
    let canonical := canonicalContinuation code owner first body entry.origin (.integer number)
    let nextMeanings := consValues (.integer number) meanings
    let duration := 5+(trace.ticks+5)
    let result := run duration state
    result = ⟨⟨closed,.evaluate actual,state.stack,state.pending⟩,
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false reader.term (.borrow origin))] ++
      trace.events ++ [.legacy (.heap (.close token)),.legacy (.activate false (.lam false again body) entry.origin),
        .legacy (.activate false body origin)],duration⟩ ∧
    closed.metadata.heap.lease token = none ∧
    (∀ outer < token, closed.metadata.heap.lease outer = state.heap.metadata.heap.lease outer) ∧
    ReaderInventory closed.metadata (readerFrames state.activeStack) ∧
    ¬ StateReferenceOccurs token result.state ∧
    CanonicalView actual canonical (Jihoo.Quantity.openOwner (owner+1)) ∧
    LoanClosingTyped env loans false canonical nextMeanings type ∧ ValueContext env canonical nextMeanings ∧
    OwnerSizes env closed.metadata canonical nextMeanings ∧
    LoanSlots canonical loans state.activeStack ∧ LoanCoverage canonical loans state.activeStack ∧
    ∃ rest, LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans canonical.context canonical.term = some rest ∧
      LoanTyping.ResourceQuantity.LoanBudget canonical.context.length loans rest ∧
      rest.demand (owner+1) = some 1 ∧ OwnerDemandWorld closed.metadata canonical rest ∧
      OwnerDemandWorld.Total canonical rest ∧
      ∀ alias, alias ≠ owner → code.values[alias]? = some (some (.owner object)) → rest.demand (alias+1) = some 0 := by
  let state := (run fuel (initial term)).state
  let origin := (Term.var owner).subst code.origins
  let token := state.heap.metadata.heap.nextLease
  let entry := enter false domain reader.term code.context code.origins code.values (.borrow origin) (some (.reference token))
  let readerState := (run 5 state).state
  let trace := reader.replay entry readerState.heap token object readerState.stack
  dsimp only
  intro success
  have computedShape : code.term = .lend (.var owner) (.lam false domain reader.term)
      (.lam false first (.lam false again body)) := shape
  rw [shape] at checked
  have one := LoanTyping.ResourceQuantity.projectRaw_lend_owner_demand checked
  have live := (world.live_once owner object 0 stored one).1
  have opened := named_reader_steps state evaluating shape stored live
  dsimp only at opened
  have readerPrefix : (run (fuel+5) (initial term)).state = readerState := by
    have same := congrArg Result.state (run_add fuel 5 (initial term))
    exact same
  have readerStateShape := congrArg Result.state opened
  change readerState = _ at readerStateShape
  have readerEvaluating : (run (fuel+5) (initial term)).state.control = .evaluate entry := by
    rw [readerPrefix,readerStateShape]
  have stackShape : (run (fuel+5) (initial term)).state.stack = .lendFinish token object
      (some (code.context.length-owner)) origin entry.origin (code.child (.lam false first (.lam false again body))) :: state.stack := by
    rw [readerPrefix,readerStateShape]
  have readerSizes := reachable_run_owner_sizes term fuel 5 sizes
  have stage := reachable_arithmetic_tree_lend_close term (fuel+5) reader history typed computedShape
    (readerPrefix.symm ▸ readerSizes) stored readerEvaluating stackShape
  rw [readerPrefix] at stage
  dsimp only at stage
  change (run trace.ticks readerState = trace.result readerState.heap readerState.stack readerState.pending) ∧ _ at stage
  obtain ⟨computed,exit⟩ := stage
  change trace.outcome = .integer number at success
  rw [success] at exit
  dsimp only at exit
  obtain ⟨argument,closedStep,_,retired,outerLeases,readerInventory⟩ := exit
  let closed : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.close readerState.heap.metadata token,state.heap.cell⟩
  let actual := restoredContinuation code first again body origin entry.origin object (.integer number)
  have cellSame : readerState.heap.cell = state.heap.cell := by rw [readerStateShape]
  have pendingSame : readerState.pending = state.pending := by rw [readerStateShape]
  rw [cellSame,pendingSame] at closedStep readerInventory
  have afterComputed : run 5 (run trace.ticks readerState).state = ⟨⟨closed,.evaluate actual,state.stack,state.pending⟩,
      [.legacy (.heap (.close token)),.legacy (.activate false (.lam false again body) entry.origin),
        .legacy (.activate false body origin)],5⟩ :=
    resume_lend_continuation_steps _ closed code first again body origin entry.origin number token object
      state.stack state.pending closedStep
  have finished : run (5+(trace.ticks+5)) state = ⟨⟨closed,.evaluate actual,state.stack,state.pending⟩,
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false reader.term (.borrow origin))] ++
      trace.events ++ [.legacy (.heap (.close token)),.legacy (.activate false (.lam false again body) entry.origin),
        .legacy (.activate false body origin)],5+(trace.ticks+5)⟩ := by
    rw [run_add 5]
    dsimp only
    rw [run_add trace.ticks]
    dsimp only
    rw [afterComputed,computed]
    have openingEvents := congrArg Result.events opened
    have openingSteps := congrArg Result.steps opened
    rw [openingEvents,openingSteps]
    simp only [ArithmeticReader.Trace.result,List.append_assoc]
    rfl
  have older : ∀ outer < token, closed.metadata.heap.lease outer = state.heap.metadata.heap.lease outer := by
    intro outer previous
    rw [outerLeases _ (Nat.ne_of_lt previous),readerStateShape]
    simp [SizedBufferHeap.lend,HeapLeases.put,token,Nat.ne_of_lt previous]
  have captureBounds := initial_run_finish_capture_bounds term (fuel+5) stackShape
  rw [readerPrefix,pendingSame] at captureBounds
  obtain ⟨savedReady,stackReady,pendingReady⟩ := captureBounds
  have nextReady : CodeReferences token actual := ValuesReferences.retained .owner (.retained .integer savedReady)
  have noEscape : ¬ StateReferenceOccurs token ⟨closed,.evaluate actual,state.stack,state.pending⟩ := by
    intro occurs
    rcases occurs with (control | ⟨frame,member,occurs⟩) | pending
    · exact nextReady.fresh_absent control
    · exact stackReady.fresh_absent member occurs
    · exact pendingReady.fresh_absent pending
  have sameLive : closed.metadata.heap.live = state.heap.metadata.heap.live := by
    change (SizedBufferHeap.close readerState.heap.metadata token).heap.live = state.heap.metadata.heap.live
    rw [readerStateShape]
    rfl
  have closedWorld : OwnerDemandWorld closed.metadata code receipt :=
    ⟨fun index object uses selected demanded => by rw [sameLive]; exact world.live_once index object uses selected demanded,
      world.exclusive⟩
  have closedSizes := reachable_run_owner_sizes term fuel (5+(trace.ticks+5)) sizes
  rw [finished] at closedSizes
  exact ⟨finished,retired,older,readerInventory,finished.symm ▸ noEscape,
    restored_canonical_view code stored first again body entry.origin _,
    canonical_integer_restore_demand history computedShape typed context argument closedSizes slots coverage
      entered stored checked budget closedWorld complete entry.origin⟩

/-- A computed reader followed by immediate Free consumes its unique
restored owner through either retained runtime alias. The accepted tail
keeps its original type and a complete residual receipt with zero demand
through every alias of the released allocation. -/
theorem reachable_arithmetic_tree_then_free_alias (term : Term) (fuel : Nat) (reader : ArithmeticReader)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .lend (.var owner) (.lam false domain reader.term)
      (.lam false first (.lam false again (.free (.var releaseIndex) tail))))
    (selected : releaseIndex = 0 ∨ releaseIndex = owner+2)
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
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
    let entry := enter false domain reader.term code.context code.origins code.values (.borrow origin) (some (.reference token))
    let readerState := (run 5 state).state
    let trace := reader.replay entry readerState.heap token object readerState.stack
    trace.outcome = .integer number →
    let body := Term.free (.var releaseIndex) tail
    let actual := restoredContinuation code first again body origin entry.origin object (.integer number)
    let canonical := canonicalContinuation code owner first body entry.origin (.integer number)
    let sourceTail := canonical.child (tail.rename (Jihoo.Quantity.openOwner (owner+1)))
    let nextMeanings := consValues (.integer number) meanings
    let duration := 5+(trace.ticks+5)
    let handoff := run duration state
    let result := run (duration+3) state
    result = ⟨⟨⟨SizedBufferHeap.release handoff.state.heap.metadata object,handoff.state.heap.cell⟩,
      .evaluate (actual.child tail),state.stack,state.pending⟩,
      handoff.events ++ [.legacy (.heap (.free object))],duration+3⟩ ∧
    result.state.heap.metadata.heap.live object = false ∧ result.state.heap.metadata.heap.lease token = none ∧
    ¬ StateReferenceOccurs token result.state ∧
    CanonicalView (actual.child tail) sourceTail (Jihoo.Quantity.openOwner (owner+1)) ∧
    LoanClosingTyped env loans false sourceTail nextMeanings type ∧ ValueContext env sourceTail nextMeanings ∧
    OwnerSizes env result.state.heap.metadata sourceTail nextMeanings ∧
    LoanCoverage sourceTail loans result.state.activeStack ∧ LoanSlots sourceTail loans result.state.activeStack ∧
    ∃ residual,
      LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans sourceTail.context sourceTail.term = some residual ∧
      LoanTyping.ResourceQuantity.LoanBudget sourceTail.context.length loans residual ∧
      OwnerDemandWorld result.state.heap.metadata sourceTail residual ∧ OwnerDemandWorld.Total sourceTail residual ∧
      ∀ alias, sourceTail.values[alias]? = some (some (.owner object)) → residual.demand alias = some 0 := by
  let state := (run fuel (initial term)).state
  let origin := (Term.var owner).subst code.origins
  let token := state.heap.metadata.heap.nextLease
  let entry := enter false domain reader.term code.context code.origins code.values (.borrow origin) (some (.reference token))
  let readerState := (run 5 state).state
  let trace := reader.replay entry readerState.heap token object readerState.stack
  let duration := 5+(trace.ticks+5)
  let handoff := run duration state
  let body := Term.free (.var releaseIndex) tail
  let actual := restoredContinuation code first again body origin entry.origin object (.integer number)
  let canonical := canonicalContinuation code owner first body entry.origin (.integer number)
  dsimp only
  intro success
  obtain ⟨resumed,closed,_,_,noEscape,view,nextTyped,nextContext,nextSizes,nextSlots,nextCoverage,
    rest,restChecked,restBudget,_,nextWorld,nextTotal,_⟩ :=
    reachable_arithmetic_tree_restore_demand (resourceFuel := resourceFuel+2) term fuel reader history evaluating shape
      typed context sizes slots coverage entered stored checked budget world complete success
  have elapsed : (run (fuel+duration) (initial term)).state = handoff.state := by
    have same := congrArg Result.state (run_add fuel duration (initial term))
    exact same
  have atFree : (run (fuel+duration) (initial term)).state.control = .evaluate actual := by
    rw [elapsed]
    change (run duration state).state.control = _
    rw [resumed]
  have heapBeforeFree := congrArg (fun result : Result => result.state.heap.metadata) resumed
  change handoff.state.heap.metadata = _ at heapBeforeFree
  have stackBeforeFree := congrArg (fun result : Result => result.state.activeStack) resumed
  change handoff.state.activeStack = state.activeStack at stackBeforeFree
  have mapped : Jihoo.Quantity.openOwner (owner+1) releaseIndex = owner+1 := by
    rcases selected with rfl | rfl <;> rfl
  have sourceStored : canonical.values[owner+1]? = some (some (.owner object)) := stored
  have actualStored : actual.values[releaseIndex]? = some (some (.owner object)) := by
    rw [view.values releaseIndex,mapped]
    exact sourceStored
  have actualMetadata := (congrArg (fun current : State => current.heap.metadata) elapsed).trans heapBeforeFree
  have actualStack := (congrArg State.activeStack elapsed).trans stackBeforeFree
  obtain ⟨freed,dead,tailView,tailTyped,tailValues,tailSizes,tailCoverage,tailSlots,residual⟩ :=
    reachable_canonical_free_preserves_owner_demand term (fuel+duration) atFree view (by rfl)
      nextTyped nextContext (actualMetadata.symm ▸ nextSizes) (actualStack.symm ▸ nextCoverage)
      (actualStack.symm ▸ nextSlots) actualStored restChecked restBudget
      (actualMetadata.symm ▸ nextWorld) nextTotal
  have stateAfter : (run (duration+3) state).state = (run 3 (run (fuel+duration) (initial term)).state).state := by
    rw [elapsed]
    have same := congrArg Result.state (run_add duration 3 state)
    exact same
  have whole := run_add duration 3 state
  dsimp only at whole
  rw [← elapsed,freed] at whole
  have steps := congrArg Result.steps resumed
  change handoff.steps = duration at steps
  have tailStack := congrArg (fun result : Result => result.state.stack) resumed
  have tailPending := congrArg (fun result : Result => result.state.pending) resumed
  change handoff.state.stack = state.stack at tailStack
  change handoff.state.pending = state.pending at tailPending
  rw [elapsed,tailStack,tailPending,steps] at whole
  refine ⟨whole,stateAfter.symm ▸ dead,?_,?_,tailView,tailTyped,tailValues,stateAfter.symm ▸ tailSizes,
    stateAfter.symm ▸ tailCoverage,stateAfter.symm ▸ tailSlots,stateAfter.symm ▸ residual⟩
  · change (run (duration+3) state).state.heap.metadata.heap.lease token = none
    rw [whole]
    change handoff.state.heap.metadata.heap.lease token = none
    rw [heapBeforeFree]
    exact closed
  · change ¬ StateReferenceOccurs token (run (duration+3) state).state
    rw [whole]
    change ¬ StateReferenceOccurs token ⟨handoff.state.heap,.evaluate actual,state.stack,state.pending⟩
    change ¬ StateReferenceOccurs token (run duration state).state at noEscape
    rw [resumed] at noEscape
    exact noEscape

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
