import Jihoo.NativeBindingMachineMutableLoadContexts
import Jihoo.NativeLoanRawResourceOrigins

/-! An owned Load consumes the old source slot before making its returned
owner available. An immediate Free gives the same physical object back to
the heap and passes the original typed tail to evaluation. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity
variable {resource : Control}

private theorem free_callback_shape
    (checked : projectRaw (fuel+5) env loans ctx
      (.load (.var owner) index evidence (.lam false first (.lam false again (.free (.var 0) tail)))) =
      some resource) :
    ∃ indexControl firstMode againMode bodyControl,
      projectRaw (fuel+2) env loans (⟨again,false⟩ :: ⟨first,false⟩ :: ctx)
        (.free (.var 0) tail) = some bodyControl ∧
      resource = .seq (.seq (.use owner) (.seq indexControl .pure))
        (.once (.scope firstMode (.scope againMode bodyControl))) := by
  change (do
    let operands ← fields (projectRaw (fuel+4) env loans ctx)
      [.var owner,index,evidence,.lam false first (.lam false again (.free (.var 0) tail))] [0,1]
    let body ← projectRaw (fuel+4) env loans ctx (.lam false first (.lam false again (.free (.var 0) tail)))
    some (Control.seq operands (.once (caseBody 2 body)))) = some resource at checked
  generalize h : projectRaw (fuel+4) env loans ctx
    (.lam false first (.lam false again (.free (.var 0) tail))) = callback at checked
  simp only [fields,fetch,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.bind_some] at checked
  have ownerProjection : projectRaw (fuel+4) env loans ctx (.var owner) = (do
    let binding ← lookup ctx owner
    if binding.erased then none else some (.use owner)) := rfl
  rw [ownerProjection] at checked
  cases selected : lookup ctx owner with
  | none => simp [selected] at checked
  | some binding =>
      cases erased : binding.erased with
      | true => simp [selected,erased] at checked
      | false =>
          cases projectedIndex : projectRaw (fuel+4) env loans ctx index with
          | none => simp [selected,erased,projectedIndex] at checked
          | some indexControl =>
              cases callback with
              | none => simp [selected,erased,projectedIndex] at checked
              | some callbackControl =>
                  obtain ⟨firstMode,inner,projectedInner,outerShape⟩ := projectRaw_lambda_body h
                  obtain ⟨againMode,bodyControl,projectedBody,innerShape⟩ :=
                    projectRaw_lambda_body projectedInner
                  obtain ⟨_,rest,_,_,_,bodyShape⟩ := projectRaw_free_variable projectedBody
                  have scopes : caseBody 2 callbackControl = .scope firstMode (.scope againMode bodyControl) := by
                    rw [outerShape,innerShape,bodyShape]
                    rfl
                  exact ⟨indexControl,firstMode,againMode,bodyControl,projectedBody,by
                    simpa [selected,erased,projectedIndex,scopes] using checked.symm⟩

private theorem load_old_slot_zero
    (used : (Control.seq (.seq (.use owner) (.seq indexControl .pure)) (.once scopes)).demand owner = some 1) :
    scopes.demand owner = some 0 := by
  simp only [Control.demand,ite_true] at used
  cases index : indexControl.demand owner <;> cases callback : scopes.demand owner <;>
    simp [index,callback,bind,Option.bind] at used ⊢
  omega

/-- The actual Load receipt contains the pending Free and its tail. The
original owner has already been consumed, so the captured old slot has no
remaining demand in the tail. Both callback scopes preserve enclosing loans. -/
theorem projectRaw_load_free_authority
    (checked : projectRaw (fuel+5) env loans ctx
      (.load (.var owner) index evidence (.lam false first (.lam false again (.free (.var 0) tail)))) =
      some resource)
    (budget : LoanBudget ctx.length loans resource)
    (entered : Loans.Entered ctx.length loans)
    (used : resource.demand owner = some 1) :
    ∃ bodyControl tailControl,
      projectRaw (fuel+2) env loans (⟨again,false⟩ :: ⟨first,false⟩ :: ctx)
        (.free (.var 0) tail) = some bodyControl ∧
      LoanBudget (ctx.length+2) loans bodyControl ∧
      projectRaw (fuel+1) env loans (⟨again,false⟩ :: ⟨first,false⟩ :: ctx) tail = some tailControl ∧
      LoanBudget (ctx.length+2) loans tailControl ∧ tailControl.demand (owner+2) = some 0 := by
  obtain ⟨indexControl,firstMode,againMode,bodyControl,projected,rfl⟩ := free_callback_shape checked
  have oldSlot := Jihoo.Quantity.scopes_outer (modes := [firstMode,againMode]) (load_old_slot_zero used)
  have firstBudget : LoanBudget ctx.length loans (.scope firstMode (.scope againMode bodyControl)) :=
    budget.sequence.2
  have deeper : Loans.Entered (ctx.length+1) loans := by
    intro frame member
    exact Nat.le_trans (entered frame member) (Nat.le_succ _)
  have bodyBudget := (firstBudget.scope entered).scope deeper
  obtain ⟨_,tailControl,_,_,tailProjected,rfl⟩ := projectRaw_free_variable projected
  refine ⟨_,tailControl,projected,bodyBudget,tailProjected,bodyBudget.sequence.2.sequence.1,?_⟩
  cases result : tailControl.demand (owner+2) <;>
    simp [Control.demand,result,bind,Option.bind] at oldSlot ⊢
  exact oldSlot

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds

private theorem run_compose (first second : Nat) (state : State) :
    run (first+second) state =
      let before := run first state
      let after := run second before.state
      ⟨after.state,before.events ++ after.events,before.steps+after.steps⟩ := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add,run,List.nil_append]
  | succ first ih =>
      simp only [Nat.succ_add,run]
      cases observed : step state with
      | none =>
          have stopped (fuel : Nat) : run fuel state = ⟨state,[],0⟩ := by
            cases fuel <;> simp only [run,observed]
          simp only [stopped,List.nil_append,Nat.zero_add]
      | some result =>
          obtain ⟨next,event⟩ := result
          simp only
          rw [ih]
          simp only [List.append_assoc,Nat.add_assoc,Nat.add_comm]

private theorem free_three_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .free (.var owner) tail)
    (stored : code.values[owner]? = some (some (.owner object)))
    (live : state.heap.metadata.heap.live object = true)
    (guard : freeGuard state.heap.metadata object = true) :
    let released : SizedBufferHeap.IndexedState :=
      ⟨SizedBufferHeap.release state.heap.metadata object,state.heap.cell⟩
    run 3 state = ⟨⟨released,.evaluate (code.child tail),state.stack,state.pending⟩,
      [.legacy (.heap (.free object))],3⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,stored,executeLegacy,execute,
    returnAction,live,guard,↓reduceIte,Option.map_none,Option.map_some]
  rfl

/-- Read through an actual U64 slot and release the returned physical owner.
The callback's Free and the remaining typed CODE tail use the original
quantity receipt. Its old retained owner alias has zero residual demand. -/
theorem reachable_variable_load_free (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata source meanings)
    (indexErasure : (lookup actual.context index).map (·.erased) =
      (lookup source.context (indices index)).map (·.erased))
    (shape : actual.term = .load (.var owner) (.var index) evidence
      (.lam false first (.lam false again (.free (.var 0) tail))))
    (decideEvidence : evidence.subst (meanings ∘ indices) = .decide left right)
    (storedOwner : actual.values[owner]? = some (some (.owner object)))
    (live : (run fuel (initial term)).state.heap.metadata.heap.live object = true)
    (coverage : LoanCoverage source loans (run fuel (initial term)).state.activeStack)
    (entered : Loans.Entered source.context.length loans)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+5) env loans source.context
      source.term = some resource)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans resource)
    (used : resource.demand (indices owner) = some 1) :
    let state := (run fuel (initial term)).state
    ∃ offset,
      let payload := state.heap.cell object offset
      let value := Term.integer (decodeInteger payload)
      let origin := (actual.child (.var owner)).origin
      let body := Term.free (.var 0) tail
      let next := restoredContinuation actual first again body origin value object (.integer (decodeInteger payload))
      let sourceFirst := first.rename indices
      let sourceAgain := again.rename (liftRenaming 1 indices)
      let sourceBody := body.rename (liftRenaming 2 indices)
      let sourceNext := restoredContinuation source sourceFirst sourceAgain sourceBody origin
        value object (.integer (decodeInteger payload))
      let sourceTail := sourceNext.child (tail.rename (liftRenaming 2 indices))
      let sourceMeanings := consValues (meanings (indices owner)) (consValues value meanings)
      let sourceAlias := canonicalContinuation source (indices owner) sourceFirst sourceBody
        value (.integer (decodeInteger payload))
      let aliasMap := Jihoo.Quantity.openOwner (indices owner+1) ∘ liftRenaming 2 indices
      let aliasTail := sourceAlias.child (tail.rename aliasMap)
      let actualTail := next.child tail
      let released : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.release state.heap.metadata object,state.heap.cell⟩
      freeGuard state.heap.metadata object = true ∧ released.metadata.heap.live object = false ∧
      run 12 state = ⟨⟨released,.evaluate actualTail,state.stack,state.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) value),
          .legacy (.activate false body origin),.legacy (.heap (.free object))],12⟩ ∧
      LoanClosingTyped env loans false sourceTail sourceMeanings type ∧
      ValueContext env sourceTail sourceMeanings ∧ OwnerSizes env released.metadata sourceTail sourceMeanings ∧
      LoanCoverage sourceTail loans (run 12 state).state.activeStack ∧ Invariant (run 12 state).state ∧
      CanonicalView actualTail sourceTail (liftRenaming 2 indices) ∧
      CanonicalView actualTail aliasTail aliasMap ∧
      actualTail.values[owner+2]? = some (some (.owner object)) ∧
      aliasMap 0 = aliasMap (owner+2) ∧
      ∃ residual,
        LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans sourceTail.context sourceTail.term =
          some residual ∧ LoanTyping.ResourceQuantity.LoanBudget sourceTail.context.length loans residual ∧
        residual.demand (indices owner+2) = some 0 := by
  have loaded := reachable_variable_load_contexts term fuel history evaluating view typed context sizes
    indexErasure shape decideEvidence storedOwner live coverage entered (resourceFuel := resourceFuel+3) checked budget
  obtain ⟨offset,executed,nextView,resumed,nextContext,nextSizes,nextCoverage,aliasView,_,_,_⟩ := loaded
  let state := (run fuel (initial term)).state
  let number := decodeInteger (state.heap.cell object offset)
  let origin := (actual.child (.var owner)).origin
  let body := Term.free (.var 0) tail
  let actualNext := restoredContinuation actual first again body origin (.integer number) object (.integer number)
  let sourceFirst := first.rename indices
  let sourceAgain := again.rename (liftRenaming 1 indices)
  let sourceTailTerm := tail.rename (liftRenaming 2 indices)
  let sourceBody := body.rename (liftRenaming 2 indices)
  let sourceNext := restoredContinuation source sourceFirst sourceAgain sourceBody origin
    (.integer number) object (.integer number)
  have sourceShape : source.term = .load (.var (indices owner)) (.var (indices index))
      (evidence.rename indices)
      (.lam false sourceFirst (.lam false sourceAgain (.free (.var 0) sourceTailTerm))) := by
    rw [← view.termEq,shape]
    simp only [sourceFirst,sourceAgain,sourceTailTerm,Term.rename,renameArgs,Op.binders,liftRenaming]
    rfl
  have sourceBodyShape : sourceNext.term = .free (.var 0) sourceTailTerm := by
    simp only [sourceNext,sourceBody,sourceTailTerm,body,restoredContinuation,enter,
      Term.rename,renameArgs,Op.binders,liftRenaming]
    rfl
  rw [sourceShape] at checked
  obtain ⟨_,residual,freeProjected,freeBudget,tailProjected,tailBudget,oldZero⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_load_free_authority checked budget entered used
  have newSlot : sourceNext.values[0]? = some (some (.owner object)) := rfl
  have inactive : Loans.active sourceNext.context.length loans 0 = false :=
    LoanTyping.ResourceQuantity.projectRaw_free_inactive freeProjected freeBudget
  have loadedStack := congrArg (fun result : Result => result.state.activeStack) executed
  have noReader : ¬ ObjectReader object state.activeStack :=
    loadedStack ▸ nextCoverage.inactive newSlot inactive
  have invariant := initial_run_invariant term fuel
  have guard : freeGuard state.heap.metadata object = true :=
    (invariant.2.free_guard_iff invariant.1).mpr noReader
  have freed := free_three_steps (code := actualNext) (owner := 0) (tail := tail)
    ⟨state.heap,.evaluate actualNext,state.stack,state.pending⟩ rfl rfl rfl live guard
  have composed := run_compose 9 3 state
  dsimp only at composed
  rw [executed] at composed
  dsimp only at composed
  rw [freed] at composed
  have freeStep := SizedBufferHeap.Step.free live (freeGuard_unborrowed invariant.1 guard)
  have restoredHeap := congrArg (fun result : Result => result.state.heap.metadata) executed
  have tailSizes := ((restoredHeap ▸ nextSizes).steps (.cons freeStep .nil)).child sourceTailTerm
  obtain ⟨closing,localType,bodyTyped,converted⟩ := resumed
  change LoanTyping.HasType env loans sourceNext.context false sourceNext.term localType at bodyTyped
  rw [sourceBodyShape] at bodyTyped
  have tailTyped : LoanClosingTyped env loans false (sourceNext.child sourceTailTerm)
      (consValues (meanings (indices owner)) (consValues (.integer number) meanings)) type :=
    ⟨closing,localType,bodyTyped.free_tail,converted⟩
  have completedStack := congrArg (fun result : Result => result.state.activeStack) composed
  have tailCoverage : LoanCoverage (sourceNext.child sourceTailTerm) loans (run 12 state).state.activeStack :=
    completedStack.symm ▸ loadedStack ▸ nextCoverage.child sourceTailTerm
  refine ⟨offset,guard,?_,composed,tailTyped,nextContext.child sourceTailTerm,tailSizes,tailCoverage,
    run_invariant 12 invariant,nextView.child tail,aliasView.child tail,?_,rfl,⟨residual,tailProjected,tailBudget,oldZero⟩⟩
  · simp only [SizedBufferHeap.release,HeapLeases.put,ite_true]
  · simpa only [actualNext,restoredContinuation,enter,Code.child,List.getElem?_cons_succ] using storedOwner

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
