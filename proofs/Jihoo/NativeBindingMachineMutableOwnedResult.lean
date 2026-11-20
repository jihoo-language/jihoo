import Jihoo.NativeBindingMachineMutableOwnedCall

/-! A Buffer returned from CODE has a typed source value, an exact allocated
size, and a live physical identity with no reader. A pending application
can consume that result even when its closure retained a different context. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

structure OwnedResult (env : Environment) (heap : SizedBufferHeap.State) (stack : List Frame)
    (object : Nat) (source type : Term) : Prop where
  typed : LoanTyping.HasType env [] [] true source type
  size : OwnerSize env heap object type
  live : heap.heap.live object = true
  noReaders : ¬ ObjectReader object stack

theorem OwnedResult.convert (result : OwnedResult env heap stack object source type)
    (converted : LoanTyping.Conversion.Conv env type other) : OwnedResult env heap stack object source other :=
  ⟨result.typed.convert converted,result.size.convert converted,result.live,result.noReaders⟩

/-- A checked Buffer variable returns the actual physical owner. Source CODE
selects the value, the quantity use derives liveness and loan inactivity,
and the original Buffer annotation determines the result's allocated size. -/
theorem reachable_owned_variable_return (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .var index)
    (typed : LoanClosingTyped env loans false code meanings type)
    (bufferType : LoanTyping.Conversion.Conv env type (.buffer count))
    (context : ValueContext env code meanings) (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata code meanings)
    (coverage : LoanCoverage code loans (run fuel (initial term)).state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial term)).state.heap.metadata code receipt) :
    let state := (run fuel (initial term)).state
    ∃ object, code.values[index]? = some (some (.owner object)) ∧
      step state = some ({state with control := .returned (.owner object)},none) ∧
      OwnedResult env state.heap.metadata state.activeStack object (meanings index) type ∧ receipt.demand index = some 1 ∧
      ∀ alias, alias ≠ index → code.values[alias]? = some (some (.owner object)) → receipt.demand alias = some 0 := by
  let state := (run fuel (initial term)).state
  have ready := initial_run_code_aligned term fuel SizedBufferHeap.empty evaluating
  obtain ⟨value,stored,kind,executed⟩ := canonical_variable_result history evaluating
    (CanonicalView.identity code) typed context ready shape
  obtain ⟨object,rfl⟩ := buffer_kind_is_owner history.wellFormed.admissible (kind.convert bufferType)
  have receiptShape := LoanTyping.ResourceQuantity.raw_variable_use (shape ▸ checked)
  have used : receipt.demand index = some 1 := by simp [receiptShape,Control.demand]
  have live := (world.live_once index object 0 stored used).1
  have inactive : Loans.active code.context.length loans index = false := by
    apply Bool.eq_false_iff.mpr
    intro active
    have zero := budget index active
    rw [used] at zero
    cases zero
  have unborrowed := coverage.inactive stored inactive
  have argument : LoanTyping.HasType env [] [] true (meanings index) type := by
    simpa only [shape,Term.subst] using typed.closed history
  obtain ⟨_,localType,source,converted⟩ := typed
  rw [shape] at source
  have physicalSize := (sizes.typed_variable history source stored).convert converted
  refine ⟨object,stored,executed,⟨argument,physicalSize,live,unborrowed⟩,used,?_⟩
  intro alias distinct previous
  exact world.exclusive index alias object 0 (Ne.symm distinct) stored previous used

/-- The saved closure uses its own original CODE, capture context and body
receipt. A returned owner can cross this real call frame while preserving the
dependent codomain and assigning the sole physical unit to the new binder. -/
theorem saved_closure_owned_result_entry (state : State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (functionTyped : LoanClosingTyped env loans false (capture.child (.lam false domain body)) meanings
      (.pi false inputType resultType))
    (context : ValueContext env capture meanings)
    (sizes : OwnerSizes env state.heap.metadata capture meanings)
    (slots : LoanSlots capture loans (stack ++ state.pending.flatMap Prod.snd))
    (coverage : LoanCoverage capture loans (stack ++ state.pending.flatMap Prod.snd))
    (entered : Loans.Entered capture.context.length loans)
    (argument : OwnedResult env state.heap.metadata (stack ++ state.pending.flatMap Prod.snd) object source inputType)
    (returned : state.control = .returned (.owner object))
    (stackShape : state.stack = .argument (.closure false domain body capture.context capture.origins capture.values) origin :: stack)
    (checked : LoanTyping.ResourceQuantity.projectRaw fuel env loans (⟨domain,false⟩ :: capture.context) body = some receipt)
    (scopeValid : LocalScopes (.scope .linear receipt))
    (budget : LoanTyping.ResourceQuantity.LoanBudget capture.context.length loans (.scope .linear receipt))
    (world : OwnerDemandWorld state.heap.metadata capture (.scope .linear receipt))
    (complete : OwnerDemandWorld.Total capture (.scope .linear receipt))
    (retired : ∀ alias, capture.values[alias]? = some (some (.owner object)) →
      (Control.scope .linear receipt).demand alias = some 0) :
    let next := enter false domain body capture.context capture.origins capture.values origin (some (.owner object))
    let nextMeanings := consValues source meanings
    step state = some (⟨state.heap,.evaluate next,stack,state.pending⟩,some (.legacy (.activate false body origin))) ∧
    LoanClosingTyped env loans false next nextMeanings (resultType.subst (single source)) ∧
    ValueContext env next nextMeanings ∧ OwnerSizes env state.heap.metadata next nextMeanings ∧
    LoanSlots next loans (stack ++ state.pending.flatMap Prod.snd) ∧
    LoanCoverage next loans (stack ++ state.pending.flatMap Prod.snd) ∧
    LoanTyping.ResourceQuantity.projectRaw fuel env loans next.context next.term = some receipt ∧
    LoanTyping.ResourceQuantity.LoanBudget next.context.length loans receipt ∧
    OwnerDemandWorld state.heap.metadata next receipt ∧ OwnerDemandWorld.Total next receipt ∧ receipt.demand 0 = some 1 ∧
    ∀ alias, capture.values[alias]? = some (some (.owner object)) → receipt.demand (alias+1) = some 0 := by
  obtain ⟨_,localType,sourceFunction,closedType⟩ := functionTyped
  obtain ⟨_,bodyType,_,bodyTyped,functionConverted⟩ := sourceFunction.lamView
  have callable : LoanTyping.Conversion.Conv env
      (.pi false (domain.subst meanings) (bodyType.subst (liftSubOne meanings))) (.pi false inputType resultType) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      (functionConverted.substitution meanings history.wellFormed.closed).trans closedType
  obtain ⟨_,annotation,bodyConverted⟩ := callable.pi_injective history.wellFormed.admissible
  have convertedArg := argument.convert annotation.symm
  have kind : ValueKind env (.owner object) (domain.subst meanings) :=
    ⟨.natural (state.heap.metadata.length object),convertedArg.size.realization⟩
  obtain ⟨nextContext,nextSizes⟩ := bind_variable_context context sizes convertedArg.typed kind
    (fun _ same => by cases same; exact convertedArg.size) (by intro _ impossible; cases impossible)
    (by intro _ impossible; cases impossible) body origin
  have bodyResult : LoanTyping.Conversion.Conv env (bodyType.subst (consValues source meanings))
      (resultType.subst (single source)) := by
    simpa only [subst_lift_consValues] using bodyConverted.substitution (single source) history.wellFormed.closed
  have nextTyped : LoanClosingTyped env loans false
      (enter false domain body capture.context capture.origins capture.values origin (some (.owner object)))
      (consValues source meanings) (resultType.subst (single source)) :=
    ⟨nextContext.closing,bodyType,bodyTyped,bodyResult⟩
  have nextSlots := slots.enter entered false domain body origin (some (.owner object))
  have nextCoverage := coverage_enter_unborrowed_owner coverage entered convertedArg.noReaders domain body origin
  have activated := enter_retained_call_step state capture domain body origin (.owner object) returned stackShape
  obtain ⟨nextWorld,nextTotal,one,aliases⟩ :=
    world.enter_linear_result complete scopeValid convertedArg.live retired domain body origin
  exact ⟨activated,nextTyped,nextContext,nextSizes,nextSlots,nextCoverage,checked,budget.scope entered,
    nextWorld,nextTotal,one,aliases⟩

/-- The accepted identity body transfers its parameter back to the caller.
The body's original recursive use receipt supplies the returned object's
ownership and exact size at the original application result type. -/
theorem reachable_named_buffer_identity_return (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .app (.lam false (.buffer count) (.var 0)) (.var owner))
    (typed : LoanClosingTyped env loans false code meanings type)
    (bufferType : LoanTyping.Conversion.Conv env type (.buffer resultCount))
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial term)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial term)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial term)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let state := (run fuel (initial term)).state
    let origin := (code.child (.var owner)).origin
    ∃ object, code.values[owner]? = some (some (.owner object)) ∧
      run 6 state = ⟨{state with control := .returned (.owner object)},[.legacy (.activate false (.var 0) origin)],6⟩ ∧
      OwnedResult env state.heap.metadata state.activeStack object (meanings owner) type := by
  let state := (run fuel (initial term)).state
  let origin := (code.child (.var owner)).origin
  obtain ⟨object,found,call,nextTyped,nextContext,nextSizes,_,nextCoverage,_,_,restChecked,restBudget,nextWorld,_,_,_⟩ :=
    reachable_named_buffer_call_entry term fuel history evaluating shape typed context sizes slots coverage
      entered checked budget world complete
  let body := enter false (.buffer count) (.var 0) code.context code.origins code.values origin (some (.owner object))
  let mid : State := ⟨state.heap,.evaluate body,state.stack,state.pending⟩
  have reached : (run (fuel+5) (initial term)).state = mid := by
    have prefixRun := run_add fuel 5 (initial term)
    dsimp only at prefixRun
    rw [call] at prefixRun
    exact congrArg Result.state prefixRun
  have bodyEvaluating : (run (fuel+5) (initial term)).state.control = .evaluate body := by rw [reached]
  obtain ⟨result,stored,returned,resultTyped,_,_⟩ :=
    reachable_owned_variable_return term (fuel+5) history bodyEvaluating rfl nextTyped bufferType nextContext
      (reached.symm ▸ nextSizes) (reached.symm ▸ nextCoverage) restChecked restBudget (reached.symm ▸ nextWorld)
  have same : object = result := Value.owner.inj (Option.some.inj (Option.some.inj stored))
  subst result
  rw [reached] at returned resultTyped
  refine ⟨object,found,?_,resultTyped⟩
  change run 6 state = _
  rw [run_add 5 1,call]
  dsimp only
  change Result.mk (run 1 mid).state ([.legacy (.activate false (.var 0) origin)] ++ (run 1 mid).events)
    (5+(run 1 mid).steps) = _
  rw [run,returned]
  rfl

namespace Examples

private def returnedBufferArgument : Term :=
  let buffer := Term.buffer (.natural 2)
  let bound := Term.decide (.natural 1) (.natural 2)
  let release := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let read := Term.load (.var 0) (.natural 1) bound release
  let identity := Term.app (.lam false buffer (.var 0)) (.var 0)
  let call := Term.app (.lam false buffer read) identity
  .app (.lam false buffer call)
    (.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 7) bound)

set_option maxRecDepth 4096 in
/-- The original Buffer returns from a named call and becomes the pending
outer closure's argument. Its written cell and physical allocation survive
until that closure's Load callback frees it. -/
theorem owned_result_reenters_saved_closure :
    LoanTyping.MixedProgram.checkDeclaration 48 96 .empty ⟨.i64,returnedBufferArgument⟩ =
      some ⟨.i64,returnedBufferArgument⟩ ∧
    let result := run 50 (initial returnedBufferArgument)
    observe result = .integer 7 ∧ result.state.heap.metadata.heap.nextObject = 1 ∧
      result.state.heap.metadata.heap.live 0 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
