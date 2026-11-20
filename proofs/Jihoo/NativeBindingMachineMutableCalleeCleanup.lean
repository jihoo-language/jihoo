import Jihoo.NativeBindingMachineMutableCheckedClosure

/-! A pending argument's demanded physical owners remain live through a
checked cleanup prefix. The separation is on allocation identity, so it
also applies when the prefix and argument retain different slot names. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def FreeOperand (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool) : Term → Prop
  | .free owner _ => ∃ size, HasType env loans ctx mode owner (.buffer size)
  | _ => True

private theorem free_operand_typed (typed : HasType env loans ctx mode term type) : FreeOperand env loans ctx mode term := by
  apply HasType.rec (t := typed) (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun loans ctx mode term _ _ => FreeOperand env loans ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case free owner rest _ _ => exact ⟨_,owner⟩
  case dataElim => split <;> trivial

theorem HasType.free_owner_inputs (typed : HasType env loans ctx mode (.free owner tail) type) :
    ∃ size, HasType env loans ctx mode owner (.buffer size) :=
  free_operand_typed typed

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

def OwnerDemandSeparation (code : Code) (first later : Jihoo.Quantity.Control) : Prop :=
  ∀ slot alias object uses, code.values[slot]? = some (some (.owner object)) →
    code.values[alias]? = some (some (.owner object)) → first.demand slot = some (uses+1) →
    later.demand alias = some 0

/-- The actual heap lifecycle transports the capture world whenever its
demanded owners are excluded from the prefix's real Free events. -/
theorem OwnerDemandWorld.run_without_demanded_free (term : Term) (fuel duration : Nat)
    (world : OwnerDemandWorld (run fuel (Mutable.initial term)).state.heap.metadata code receipt)
    (avoids : ∀ slot object uses, code.values[slot]? = some (some (.owner object)) →
      receipt.demand slot = some (uses+1) →
      .free object ∉ (run duration (run fuel (Mutable.initial term)).state).events.filterMap Event.lifecycle?) :
    OwnerDemandWorld (run duration (run fuel (Mutable.initial term)).state).state.heap.metadata code receipt := by
  refine ⟨?_,world.exclusive⟩
  intro slot object uses stored demand
  obtain ⟨live,one⟩ := world.live_once slot object uses stored demand
  have older := (initial_run_invariant term fuel).1.allocated object live
  exact ⟨(reachable_run_owner_live_iff term fuel duration older).mpr ⟨live,avoids slot object uses stored demand⟩,one⟩

inductive CalleeCleanup where
  | integer (value : Int)
  | free (slot : Nat) (rest : CalleeCleanup)

namespace CalleeCleanup

def term : CalleeCleanup → Term
  | .integer value => .integer value
  | .free slot rest => .free (.var slot) rest.term

def ticks : CalleeCleanup → Nat
  | .integer _ => 1
  | .free _ rest => 3+rest.ticks

def value : CalleeCleanup → Int
  | .integer value => value
  | .free _ rest => rest.value

private theorem free_fuel (checked : LoanTyping.ResourceQuantity.projectRaw fuel env loans ctx
    (.free (.var owner) tail) = some receipt) : ∃ rest, fuel = rest+2 := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [LoanTyping.ResourceQuantity.projectRaw,Op.arity,LoanTyping.ResourceQuantity.runtimeFields,
            LoanTyping.ResourceQuantity.erasedNode,fields,fetch] at checked
      | succ rest => exact ⟨rest,rfl⟩

private theorem residual_separation
    (separate : OwnerDemandSeparation code (.seq (.use owner) (.seq rest .pure)) later) (tail : Term) :
    OwnerDemandSeparation (code.child tail) rest later := by
  intro slot alias object uses stored previous positive
  by_cases chosen : owner = slot
  · have demand : (Control.seq (.use owner) (.seq rest .pure)).demand slot = some ((uses+1)+1) := by
      simp [Control.demand,chosen,positive,Nat.add_comm]
    exact separate slot alias object (uses+1) stored previous demand
  · have demand : (Control.seq (.use owner) (.seq rest .pure)).demand slot = some (uses+1) := by
      simp [Control.demand,chosen,positive]
    exact separate slot alias object uses stored previous demand

private theorem checked_free_value (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .free (.var slot) tail)
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings) :
    ∃ object, code.values[slot]? = some (some (.owner object)) := by
  obtain ⟨closing,_,source,_⟩ := typed
  rw [shape] at source
  obtain ⟨length,argument⟩ := source.free_owner_inputs
  have checkedOwner : LoanClosingTyped env loans false (code.child (.var slot)) meanings ((Term.buffer length).subst meanings) :=
    ⟨closing,.buffer length,argument,.refl _⟩
  have aligned := initial_run_code_aligned term fuel SizedBufferHeap.empty evaluating
  obtain ⟨actual,stored,kind⟩ := (context.child (.var slot)).variable_kind history checkedOwner aligned rfl
  have buffer : ValueKind env actual (.buffer (length.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using kind
  obtain ⟨object,rfl⟩ := buffer_kind_is_owner history.wellFormed.admissible buffer
  exact ⟨object,stored⟩

/-- Checked cleanup may release any finite sequence of named Buffers, then
return its scalar. Every release is authenticated by the relevant source
use, and the actual event trace excludes every demanded sibling owner. -/
theorem reachable_cleanup_separated (cleanup : CalleeCleanup) (program : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code) (shape : code.term = cleanup.term)
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) (separated : OwnerDemandSeparation code receipt later) :
    let state := (run fuel (initial program)).state
    let result := run cleanup.ticks state
    result.steps = cleanup.ticks ∧ result.state.control = .returned (.integer cleanup.value) ∧
    result.state.stack = state.stack ∧ result.state.pending = state.pending ∧ result.state.heap.cell = state.heap.cell ∧
    (∀ slot object uses, code.values[slot]? = some (some (.owner object)) → later.demand slot = some (uses+1) →
      .free object ∉ result.events.filterMap Event.lifecycle?) := by
  induction cleanup generalizing fuel code receipt resourceFuel with
  | integer value =>
      have typedLiteral : LoanTyping.HasType env [] [] true (.integer value) type := by
        simpa only [shape,term,Term.subst,substArgs] using typed.closed history
      have bounded := typedLiteral.integer_bound
      simp only [run,step,evaluating,shape,term,ticks,CalleeCleanup.value,evaluateAction,executeLegacy,execute,
        bounded,ite_true,Option.map_none]
      exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro,by intros; exact List.not_mem_nil⟩
  | free owner rest ih =>
      let state := (run fuel (initial program)).state
      have ownerShape : code.term = .free (.var owner) rest.term := shape
      obtain ⟨resourceFuel,rfl⟩ := free_fuel (ownerShape ▸ checked)
      obtain ⟨object,stored⟩ := checked_free_value program fuel history evaluating ownerShape typed context
      have projected := LoanTyping.ResourceQuantity.projectRaw_free_variable (ownerShape ▸ checked)
      obtain ⟨_,residual,_,_,tailProjected,receiptShape⟩ := projected
      obtain ⟨_,slotsDemand⟩ := complete owner object stored
      have residualDefined : ∃ amount, residual.demand owner = some amount := by
        rw [receiptShape] at slotsDemand
        cases observed : residual.demand owner with
        | none => simp [Control.demand,observed] at slotsDemand
        | some amount => exact ⟨amount,rfl⟩
      obtain ⟨amount,amountDefined⟩ := residualDefined
      have consumed : receipt.demand owner = some (amount+1) := by
        rw [receiptShape]
        simp [Control.demand,amountDefined,Nat.add_comm]
      have noLater : ∀ slot, code.values[slot]? = some (some (.owner object)) → later.demand slot = some 0 :=
        fun slot found => separated owner slot object amount stored found consumed
      have nextSeparated : OwnerDemandSeparation (code.child rest.term) residual later := by
        rw [receiptShape] at separated
        exact residual_separation separated rest.term
      obtain ⟨freed,_,_,nextTyped,nextContext,nextSizes,nextCoverage,nextSlots,restReceipt,restChecked,
        restBudget,restWorld,restTotal,_⟩ :=
        reachable_canonical_free_preserves_owner_demand program fuel evaluating (CanonicalView.identity code)
          ownerShape typed context sizes coverage slots stored checked budget world complete
      have sameTail : rest.term.rename id = rest.term := Term.rename_id _
      rw [sameTail] at nextTyped nextContext nextSizes nextSlots nextCoverage restChecked restBudget restWorld restTotal
      have sameReceipt : restReceipt = residual := Option.some.inj (restChecked.symm.trans tailProjected)
      subst restReceipt
      have reached : (run (fuel+3) (initial program)).state = (run 3 state).state := by
        have fields := congrArg Result.state (run_add fuel 3 (initial program))
        exact fields
      have nextEvaluating : (run (fuel+3) (initial program)).state.control = .evaluate (code.child rest.term) := by
        rw [reached,freed]
      have tailRun := ih (fuel := fuel+3) (code := code.child rest.term) nextEvaluating rfl nextTyped nextContext
        (reached.symm ▸ nextSizes) (reached.symm ▸ nextSlots) (reached.symm ▸ nextCoverage) tailProjected
        restBudget (reached.symm ▸ restWorld) restTotal nextSeparated
      dsimp only at tailRun
      rw [reached] at tailRun
      obtain ⟨tailTicks,tailControl,tailStack,tailPending,tailCells,tailProtected⟩ := tailRun
      have result := run_add 3 rest.ticks state
      dsimp only at result
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · have firstTicks := congrArg Result.steps freed
        change (run 3 state).steps = 3 at firstTicks
        refine (congrArg Result.steps result).trans ?_
        change (run 3 state).steps + (run rest.ticks (run 3 state).state).steps = 3+rest.ticks
        rw [firstTicks,tailTicks]
      · exact (congrArg (fun current : Result => current.state.control) result).trans tailControl
      · exact (congrArg (fun current : Result => current.state.stack) result).trans (tailStack.trans (by rw [freed]))
      · exact (congrArg (fun current : Result => current.state.pending) result).trans (tailPending.trans (by rw [freed]))
      · exact (congrArg (fun current : Result => current.state.heap.cell) result).trans (tailCells.trans (by rw [freed]))
      · intro slot requested uses found wanted
        change .free requested ∉ (run (3+rest.ticks) state).events.filterMap Event.lifecycle?
        rw [result,List.filterMap_append]
        have different : requested ≠ object := by
          intro same
          subst requested
          rw [noLater slot found] at wanted
          cases wanted
        have initialOnly : (run 3 state).events.filterMap Event.lifecycle? = [.free object] := by rw [freed]; rfl
        rw [initialOnly]
        simp only [List.cons_append,List.nil_append,List.mem_cons,not_or]
        exact ⟨by intro same; exact different (SizedBufferHeap.Event.free.inj same),tailProtected slot requested uses found wanted⟩

end CalleeCleanup

private theorem begin_cleanup_call (state : State) (cleanup : CalleeCleanup)
    (evaluating : state.control = .evaluate code)
    (shape : code.term = .app (.strict cleanup.term (.lam false (.buffer count) body)) argument) :
    run 2 state = ⟨⟨state.heap,.evaluate (code.child cleanup.term),
      .strict (code.child (.lam false (.buffer count) body)) :: .function (code.child argument) :: state.stack,
      state.pending⟩,[],2⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,executeLegacy,execute,Option.map_none]
  rfl

private theorem whole_cleanup_separates_argument
    (shape : callee = .seq cleanup rest)
    (separated : OwnerDemandSeparation code callee (.seq argument .pure))
    (restTotal : OwnerDemandWorld.Total code rest) : OwnerDemandSeparation code cleanup argument := by
  intro slot alias object uses stored oldAlias demand
  obtain ⟨others,otherDemand⟩ := restTotal slot object stored
  have calleeUsed : callee.demand slot = some ((uses+others)+1) := by
    rw [shape]
    simp [Control.demand,demand,otherDemand,Nat.add_right_comm]
  have zero := separated slot alias object (uses+others) stored oldAlias calleeUsed
  cases observed : argument.demand alias with
  | none => simp [Control.demand,observed] at zero
  | some amount => simpa [Control.demand,observed] using zero

/-- In a checked computed application, the callee may release any finite
sequence of unrelated Buffers. The original complete projection proves that
every allocation still demanded by the pending argument survives that exact
execution. The actual saved closure and argument enter at their original
types and receipts, without a post-cleanup liveness premise. -/
theorem reachable_cleanup_call_argument (program : Term) (fuel : Nat) (cleanup : CalleeCleanup)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .app (.strict cleanup.term (.lam false (.buffer count) body)) argument)
    (singleBody : lambdaHead body = false)
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some receipt)
    (valid : LocalScopes receipt) (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let state := (run fuel (initial program)).state
    let argumentCode := code.child argument
    let cleanupRun := run cleanup.ticks (run 2 state).state
    let closure := Value.closure false (.buffer count) body code.context code.origins code.values
    let duration := 2+(cleanup.ticks+3)
    let result := run duration state
    result = ⟨⟨cleanupRun.state.heap,.evaluate argumentCode,.argument closure argumentCode.origin :: state.stack,state.pending⟩,
      cleanupRun.events,duration⟩ ∧
    OwnerSizes env result.state.heap.metadata argumentCode meanings ∧
    LoanSlots argumentCode loans result.state.activeStack ∧ LoanCoverage argumentCode loans result.state.activeStack ∧
    ∃ inputType resultType bodyReceipt argumentReceipt,
      LoanClosingTyped env loans false (code.child (.lam false (.buffer count) body)) meanings (.pi false inputType resultType) ∧
      CheckedBufferClosure env loans code count body resourceFuel bodyReceipt ∧
      LoanClosingTyped env loans false argumentCode meanings inputType ∧
      LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans argumentCode.context argumentCode.term = some argumentReceipt ∧
      LoanTyping.ResourceQuantity.LoanBudget argumentCode.context.length loans argumentReceipt ∧
      OwnerDemandWorld result.state.heap.metadata argumentCode argumentReceipt ∧ OwnerDemandWorld.Total argumentCode argumentReceipt ∧
      LoanTyping.Conversion.Conv env (resultType.subst (single (argument.subst meanings))) type := by
  let state := (run fuel (initial program)).state
  let argumentCode := code.child argument
  let duration := 2+(cleanup.ticks+3)
  obtain ⟨calleeReceipt,argumentReceipt,calleeChecked,argumentChecked,wholeShape⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_strict_buffer_call history.wellFormed.admissible (shape ▸ checked)
  obtain ⟨cleanupReceipt,closureReceipt,cleanupChecked,_,calleeShape⟩ :=
    LoanTyping.ResourceQuantity.strict_projection calleeChecked
  obtain ⟨calleeWorld,calleeTotal,argumentSequence,argumentSequenceTotal,separate⟩ :=
    (wholeShape ▸ world).sequence (wholeShape ▸ complete)
  obtain ⟨cleanupWorld,cleanupTotal,_,closureTotal,_⟩ := (calleeShape ▸ calleeWorld).sequence (calleeShape ▸ calleeTotal)
  obtain ⟨pendingWorld,pendingTotal,_,_,_⟩ := argumentSequence.sequence argumentSequenceTotal
  have separated := whole_cleanup_separates_argument calleeShape separate closureTotal
  have calleeBudget := (wholeShape ▸ budget).sequence.1
  rw [calleeShape] at calleeBudget
  have cleanupTyped : ∃ firstType, LoanClosingTyped env loans false (code.child cleanup.term) meanings firstType := by
    obtain ⟨closing,_,source,_⟩ := typed
    rw [shape] at source
    obtain ⟨_,_,_,functionTyped,_,_,_⟩ := source.appView
    obtain ⟨firstType,firstTyped⟩ := functionTyped.strict_first
    exact ⟨firstType.subst meanings,closing,firstType,firstTyped,.refl _⟩
  obtain ⟨_,cleanupCodeTyped⟩ := cleanupTyped
  have setup := begin_cleanup_call state cleanup evaluating shape
  have reached : (run (fuel+2) (initial program)).state = (run 2 state).state := by
    have fields := congrArg Result.state (run_add fuel 2 (initial program))
    exact fields
  let enteredState := (run (fuel+2) (initial program)).state
  have cleanupEvaluating : enteredState.control = .evaluate (code.child cleanup.term) := by
    change (run (fuel+2) (initial program)).state.control = _
    rw [reached,setup]
  have metadata : enteredState.heap.metadata = state.heap.metadata := by
    change (run (fuel+2) (initial program)).state.heap.metadata = _
    rw [reached,setup]
  have frames : readerFrames enteredState.activeStack = readerFrames state.activeStack := by
    change readerFrames (run (fuel+2) (initial program)).state.activeStack = _
    rw [reached,setup]
    rfl
  have cleanupStart : OwnerDemandWorld state.heap.metadata (code.child cleanup.term) cleanupReceipt :=
    ⟨cleanupWorld.live_once,cleanupWorld.exclusive⟩
  obtain ⟨cleanSteps,cleanControl,cleanStack,cleanPending,_,protects⟩ :=
    cleanup.reachable_cleanup_separated program (fuel+2) history cleanupEvaluating rfl cleanupCodeTyped (context.child _)
      (metadata.symm ▸ sizes.child _) ((slots.child _).same_frames frames.symm)
      ((coverage.child _).same_frames frames.symm) cleanupChecked calleeBudget.sequence.1
      (metadata.symm ▸ cleanupStart) cleanupTotal separated
  have argumentStart : OwnerDemandWorld state.heap.metadata argumentCode argumentReceipt :=
    ⟨pendingWorld.live_once,pendingWorld.exclusive⟩
  have pendingStart : OwnerDemandWorld enteredState.heap.metadata argumentCode argumentReceipt :=
    metadata.symm ▸ argumentStart
  have pendingAfter := OwnerDemandWorld.run_without_demanded_free program (fuel+2) cleanup.ticks pendingStart protects
  let cleaned := run cleanup.ticks enteredState
  have afterStack : cleaned.state.stack = .strict (code.child (.lam false (.buffer count) body)) ::
      .function argumentCode :: state.stack := by
    change cleaned.state.stack = _
    refine cleanStack.trans ?_
    change (run (fuel+2) (initial program)).state.stack = _
    rw [reached,setup]
  have afterPending : cleaned.state.pending = state.pending := by
    refine cleanPending.trans ?_
    change (run (fuel+2) (initial program)).state.pending = _
    rw [reached,setup]
  obtain ⟨resumed,input,resultType,bodyReceipt,actualArgumentReceipt,_,lambdaTyped,created,argumentTyped,_,actualChecked,
    actualBudget,actualTotal,_,originalType⟩ := checked_strict_call_to_saved_argument cleaned.state history typed shape
      singleBody checked valid complete budget cleanControl afterStack
  have sameArgument : actualArgumentReceipt = argumentReceipt := Option.some.inj (actualChecked.symm.trans argumentChecked)
  subst actualArgumentReceipt
  have cleanupThenResume := run_add cleanup.ticks 3 enteredState
  dsimp only at cleanupThenResume
  change run (cleanup.ticks+3) enteredState = Result.mk (run 3 cleaned.state).state
    (cleaned.events ++ (run 3 cleaned.state).events) (cleaned.steps+(run 3 cleaned.state).steps) at cleanupThenResume
  rw [resumed,afterPending] at cleanupThenResume
  change cleaned.steps = cleanup.ticks at cleanSteps
  rw [cleanSteps] at cleanupThenResume
  have fullRun := run_add 2 (cleanup.ticks+3) state
  dsimp only at fullRun
  rw [← reached,cleanupThenResume] at fullRun
  have startEvents := congrArg Result.events setup
  have startSteps := congrArg Result.steps setup
  rw [startEvents,startSteps] at fullRun
  have finished : run duration state = ⟨⟨cleaned.state.heap,.evaluate argumentCode,
      .argument (.closure false (.buffer count) body code.context code.origins code.values) argumentCode.origin :: state.stack,
      state.pending⟩,cleaned.events,duration⟩ := by simpa only [List.nil_append,List.append_nil] using fullRun
  have finalSizes := reachable_run_owner_sizes program fuel duration (sizes.child argument)
  have finalFrames : readerFrames (run duration state).state.activeStack = readerFrames state.activeStack := by
    rw [finished]
    rfl
  refine ⟨?_,finalSizes,(slots.child _).same_frames finalFrames.symm,(coverage.child _).same_frames finalFrames.symm,
    input,resultType,bodyReceipt,argumentReceipt,lambdaTyped,created,argumentTyped,actualChecked,actualBudget,?_,actualTotal,originalType⟩
  · dsimp only [cleaned,enteredState] at finished
    rw [reached] at finished
    exact finished
  · change OwnerDemandWorld (run duration state).state.heap.metadata argumentCode argumentReceipt
    rw [finished]
    exact pendingAfter

namespace Examples

private def ownedAfterTwoCleanups : Term :=
  let temporary := Term.buffer (.natural 1)
  let target := Term.buffer (.natural 2)
  let bound := Term.decide (.natural 1) (.natural 2)
  let cleanup := CalleeCleanup.free 1 (.free 2 (.integer 0))
  let release := Term.lam false .i64 (.lam false target (.free (.var 0) (.var 1)))
  let body := Term.load (.var 0) (.natural 1) bound release
  let call := Term.app (.strict cleanup.term (.lam false target body)) (.var 0)
  let written := Term.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 7) bound
  let withTarget := Term.app (.lam false target call) written
  let withSecond := Term.app (.lam false temporary withTarget) (.alloc (.natural 1) (.integer 0))
  .app (.lam false temporary withSecond) (.alloc (.natural 1) (.integer 0))

set_option maxRecDepth 4096 in
/-- Two captured owners are freed during callee evaluation. The pending
argument still owns the third allocation and can read its written cell. -/
theorem computed_callee_frees_two_unrelated_captures :
    LoanTyping.MixedProgram.checkDeclaration 64 128 .empty ⟨.i64,ownedAfterTwoCleanups⟩ =
      some ⟨.i64,ownedAfterTwoCleanups⟩ ∧
    let result := run 80 (initial ownedAfterTwoCleanups)
    observe result = .integer 7 ∧ result.state.heap.metadata.heap.nextObject = 3 ∧
      result.state.heap.metadata.heap.live 0 = false ∧ result.state.heap.metadata.heap.live 1 = false ∧
      result.state.heap.metadata.heap.live 2 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
