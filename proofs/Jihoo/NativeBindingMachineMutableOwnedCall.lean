import Jihoo.NativeBindingMachineMutableArithmeticReaderHandoff

/-! Calling retained CODE with an existing owner must move the physical
unit to the new parameter, even though the closure captured the old alias.
The original checked call supplies both the argument and body receipts. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity ResourceModes ResourceReplay

theorem raw_variable_use (checked : projectRaw fuel env loans ctx (.var owner) = some receipt) :
    receipt = .use owner := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      simp only [projectRaw] at checked
      obtain ⟨binding,_,selected⟩ := Option.bind_eq_some_iff.mp checked
      split at selected
      · contradiction
      · exact (Option.some.inj selected).symm

/-- The authentic one-argument call projection retains the checked
argument and opens the exact original body under a linear Buffer parameter. -/
theorem projectRaw_buffer_call (admissible : EnvironmentDelta.Admissible env)
    (checked : projectRaw (fuel+3) env loans ctx (.app (.lam false (.buffer count) body) argument) = some receipt) :
    ∃ argumentReceipt bodyReceipt,
      projectRaw (fuel+2) env loans ctx argument = some argumentReceipt ∧
      projectRaw (fuel+2) env loans (⟨.buffer count,false⟩ :: ctx) body = some bodyReceipt ∧
      receipt = .seq (.seq argumentReceipt .pure) (.scope .linear bodyReceipt) := by
  simp only [projectRaw,splitSpine,Op.arity,List.length_cons,List.length_nil,Nat.reduceAdd,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  obtain ⟨⟨head,supplied⟩,splitSpineChecked,checked⟩ := Option.bind_eq_some_iff.mp checked
  cases splitSpineChecked
  obtain ⟨⟨entries,result⟩,replayed,checked⟩ := Option.bind_eq_some_iff.mp checked
  have inferred := (checked_origin replayed).2.2.2
  obtain ⟨signature,headTyped,replaySteps,_⟩ := infer_sound inferred
  split at checked
  · contradiction
  · obtain ⟨opened,openedProof,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨runtime,runtimeProjected,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨bodyReceipt,bodyProjected,same⟩ := Option.bind_eq_some_iff.mp checked
    simp only [openHead] at openedProof
    split at openedProof
    · contradiction
    · obtain ⟨mode,resolved,openedProof⟩ := Option.bind_eq_some_iff.mp openedProof
      have identity : opened = ⟨⟨.buffer count,false⟩ :: ctx,[mode],body⟩ := (Option.some.inj openedProof).symm
      subst opened
      have linear := (ResourceModes.resolve_sound resolved).convertible_buffer_linear admissible (.refl _)
      subst mode
      cases replaySteps with
      | cons normalized _ _ _ next =>
          cases next
          obtain ⟨_,_,_,_,converted⟩ := headTyped.lamView
          have flag := ((converted.trans (Conversion.normalize?_sound normalized)).pi_injective admissible).1
          simp only [flag.symm,Environment.CallReplay.runtimeArguments,List.filterMap_cons,List.filterMap_nil] at runtimeProjected
          obtain ⟨argument,projected,runtimeEq⟩ := Option.bind_eq_some_iff.mp runtimeProjected
          have runtimeShape : runtime = [argument] := (Option.some.inj runtimeEq).symm
          subst runtime
          exact ⟨argument,bodyReceipt,projected,bodyProjected,(Option.some.inj same).symm⟩

/-- The variable argument of a checked Buffer call has exactly its named use. -/
theorem projectRaw_named_buffer_call (admissible : EnvironmentDelta.Admissible env)
    (checked : projectRaw (fuel+3) env loans ctx (.app (.lam false (.buffer count) body) (.var owner)) = some receipt) :
    ∃ bodyReceipt, projectRaw (fuel+2) env loans (⟨.buffer count,false⟩ :: ctx) body = some bodyReceipt ∧
      receipt = .seq (.seq (.use owner) .pure) (.scope .linear bodyReceipt) := by
  obtain ⟨argumentReceipt,bodyReceipt,projected,bodyProjected,rfl⟩ := projectRaw_buffer_call admissible checked
  exact ⟨bodyReceipt,bodyProjected,by rw [raw_variable_use projected]⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

/-- The retained body can install a live owned result under its checked
linear binder. Captured aliases of the result must already have zero demand. -/
theorem OwnerDemandWorld.enter_linear_result
    (bodyWorld : OwnerDemandWorld heap code (.scope .linear receipt))
    (bodyTotal : OwnerDemandWorld.Total code (.scope .linear receipt))
    (scopeValid : LocalScopes (.scope .linear receipt)) (live : heap.heap.live object = true)
    (retired : ∀ alias, code.values[alias]? = some (some (.owner object)) →
      (Control.scope .linear receipt).demand alias = some 0) (domain body origin : Term) :
    let next := enter false domain body code.context code.origins code.values origin (some (.owner object))
    OwnerDemandWorld heap next receipt ∧ OwnerDemandWorld.Total next receipt ∧ receipt.demand 0 = some 1 ∧
      ∀ alias, code.values[alias]? = some (some (.owner object)) → receipt.demand (alias+1) = some 0 := by
  have binderUse : receipt.demand 0 = some 1 := scopeValid.1
  have outer := demand_under_checked_scope scopeValid
  have aliases : ∀ alias, code.values[alias]? = some (some (.owner object)) → receipt.demand (alias+1) = some 0 := by
    intro alias selected
    exact (outer alias).symm.trans (retired alias selected)
  refine ⟨⟨?_,?_⟩,?_,binderUse,aliases⟩
  · intro slot queried amount selected positive
    cases slot with
    | zero =>
        have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj selected))
        rw [binderUse] at positive
        have exactAmount : 1 = amount+1 := Option.some.inj positive
        exact ⟨same ▸ live,by omega⟩
    | succ slot => exact bodyWorld.live_once slot queried amount selected ((outer slot).trans positive)
  · intro slot alias queried amount distinct selected selectedAlias positive
    cases slot with
    | zero =>
        have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj selected))
        subst queried
        cases alias with
        | zero => exact False.elim (distinct rfl)
        | succ alias => exact aliases alias selectedAlias
    | succ slot =>
        cases alias with
        | zero =>
            have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj selectedAlias))
            subst queried
            rw [aliases slot selected] at positive
            cases positive
        | succ alias =>
            have different : slot ≠ alias := fun same => distinct (congrArg Nat.succ same)
            exact (outer alias).symm.trans
              (bodyWorld.exclusive slot alias queried amount different selected selectedAlias ((outer slot).trans positive))
  · intro slot queried selected
    cases slot with
    | zero => exact ⟨1,binderUse⟩
    | succ slot =>
        obtain ⟨amount,prev⟩ := bodyTotal slot queried selected
        exact ⟨amount,(outer slot).symm.trans prev⟩

/-- The current resource sequence moves its argument's sole owner unit to
the new linear binder. Captured aliases retain their runtime identity with
zero demand, and unrelated captures retain their own units. -/
theorem OwnerDemandWorld.enter_linear_owner
    (world : OwnerDemandWorld heap code (.seq before (.scope .linear receipt)))
    (complete : OwnerDemandWorld.Total code (.seq before (.scope .linear receipt)))
    (stored : code.values[owner]? = some (some (.owner object)))
    (used : before.demand owner = some 1) (domain body origin : Term) :
    let next := enter false domain body code.context code.origins code.values origin (some (.owner object))
    OwnerDemandWorld heap next receipt ∧ OwnerDemandWorld.Total next receipt ∧ receipt.demand 0 = some 1 ∧
      ∀ alias, code.values[alias]? = some (some (.owner object)) → receipt.demand (alias+1) = some 0 := by
  obtain ⟨uses,found⟩ := complete owner object stored
  have valid := NativeQuantity.demand_localScopes _ found
  change LocalScopes before ∧ LocalScopes (.scope .linear receipt) at valid
  obtain ⟨argumentWorld,_,bodyWorld,bodyTotal,separate⟩ := world.sequence complete
  have live := (argumentWorld.live_once owner object 0 stored used).1
  exact bodyWorld.enter_linear_result bodyTotal valid.2 live
    (fun alias selected => separate owner alias object 0 stored selected used) domain body origin

theorem buffer_kind_is_owner (admissible : EnvironmentDelta.Admissible env)
    (kind : ValueKind env value (.buffer count)) : ∃ object, value = .owner object := by
  cases value with
  | owner object => exact ⟨object,rfl⟩
  | natural => exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) kind admissible)
  | integer => exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) kind admissible)
  | array => exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) kind admissible)
  | reference =>
      obtain ⟨domain,kind⟩ := kind
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) kind admissible)
  | closure =>
      obtain ⟨domain,body,kind⟩ := kind
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) kind admissible)
  | typeCode =>
      obtain ⟨sort,kind⟩ := kind
      cases sort <;> exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) kind admissible)

/-- The original lambda application supplies its actual argument type
and the dependent result conversion at that argument's source meaning. -/
theorem original_buffer_call_inputs
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .app (.lam false (.buffer count) body) argument) :
    ∃ bodyType,
      LoanTyping.HasType env loans code.context false argument (.buffer count) ∧
      LoanTyping.HasType env loans (⟨.buffer count,false⟩ :: code.context) false body bodyType ∧
      LoanTyping.Conversion.Conv env (bodyType.subst (consValues (argument.subst meanings) meanings)) type := by
  obtain ⟨_,_,source,closedType⟩ := typed
  rw [shape] at source
  obtain ⟨erased,argumentType,result,functionTyped,argumentTyped,_,applicationConverted⟩ := source.appView
  obtain ⟨_,bodyType,_,bodyTyped,functionConverted⟩ := functionTyped.lamView
  obtain ⟨flag,domainConverted,bodyConverted⟩ := functionConverted.pi_injective history.wellFormed.admissible
  subst erased
  have bodyResult := bodyConverted.substitution (consValues (argument.subst meanings) meanings) history.wellFormed.closed
  have applicationResult := (applicationConverted.substitution meanings history.wellFormed.closed).trans closedType
  have originalResult : LoanTyping.Conversion.Conv env (result.subst (consValues (argument.subst meanings) meanings)) type := by
    simpa only [Term.subst_instantiate,subst_lift_consValues] using applicationResult
  exact ⟨bodyType,argumentTyped.convert domainConverted.symm,bodyTyped,bodyResult.trans originalResult⟩

private theorem original_named_buffer_call
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .app (.lam false (.buffer count) body) (.var owner)) :
    ∃ bodyType,
      LoanTyping.HasType env loans code.context false (.var owner) (.buffer count) ∧
      LoanTyping.HasType env loans (⟨.buffer count,false⟩ :: code.context) false body bodyType ∧
      LoanTyping.Conversion.Conv env (bodyType.subst (consValues (meanings owner) meanings)) type := by
  simpa only [Term.subst] using original_buffer_call_inputs history typed shape

/-- A returned argument opens the actual saved closure in a single Mutable
step. The physical heap and any suspended operations retain their state. -/
theorem enter_retained_call_step (state : State) (code : Code) (domain body origin : Term) (value : Value)
    (returned : state.control = .returned value)
    (stackShape : state.stack =
      .argument (.closure false domain body code.context code.origins code.values) origin :: stack) :
    let next := enter false domain body code.context code.origins code.values origin (some value)
    step state = some (⟨state.heap,.evaluate next,stack,state.pending⟩,
      some (.legacy (.activate false body origin))) := by
  simp only [step,returned,stackShape,returnAction,applyValue,executeLegacy,execute,Option.map_some]

private theorem named_call_lookup_steps (state : State)
    (evaluating : state.control = .evaluate code)
    (shape : code.term = .app (.lam false domain body) (.var owner))
    (stored : code.values[owner]? = some (some (.owner object))) :
    let origin := (code.child (.var owner)).origin
    let frame := Frame.argument (.closure false domain body code.context code.origins code.values) origin
    run 4 state = ⟨⟨state.heap,.returned (.owner object),frame :: state.stack,state.pending⟩,[],4⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,returnAction,executeLegacy,execute,
    stored,Option.map_none]
  rfl

theorem coverage_enter_unborrowed_owner (coverage : LoanCoverage code loans stack)
    (entered : Loans.Entered code.context.length loans) (unborrowed : ¬ ObjectReader object stack)
    (domain body origin : Term) :
    LoanCoverage (enter false domain body code.context code.origins code.values origin (some (.owner object))) loans stack := by
  intro slot queried stored present
  cases slot with
  | zero =>
      have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj stored))
      exact False.elim (unborrowed (same.symm ▸ present))
  | succ slot =>
      have active := coverage slot queried stored present
      simpa only [enter,List.length_cons,Loans.active_weaken entered] using active

/-- An accepted direct closure call with an existing Buffer argument reaches its
original body with the same physical allocation in the parameter. This derives
the argument identity, dependent body type, and the exact residual resource
receipt from the single original call, with no required body execution shape. -/
theorem reachable_named_buffer_call_entry (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .app (.lam false (.buffer count) body) (.var owner))
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
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
    let next := enter false (.buffer count) body code.context code.origins code.values origin (some (.owner object))
    let nextMeanings := consValues (meanings owner) meanings
    run 5 state = ⟨⟨state.heap,.evaluate next,state.stack,state.pending⟩,[.legacy (.activate false body origin)],5⟩ ∧
    LoanClosingTyped env loans false next nextMeanings type ∧ ValueContext env next nextMeanings ∧
    OwnerSizes env state.heap.metadata next nextMeanings ∧ LoanSlots next loans state.activeStack ∧
    LoanCoverage next loans state.activeStack ∧ freeGuard state.heap.metadata object = true ∧
    ∃ rest, LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans next.context next.term = some rest ∧
      LoanTyping.ResourceQuantity.LoanBudget next.context.length loans rest ∧ OwnerDemandWorld state.heap.metadata next rest ∧
      OwnerDemandWorld.Total next rest ∧ rest.demand 0 = some 1 ∧
      ∀ alias, code.values[alias]? = some (some (.owner object)) → rest.demand (alias+1) = some 0 := by
  let state := (run fuel (initial term)).state
  let domain := Term.buffer count
  let origin := (code.child (.var owner)).origin
  obtain ⟨bodyType,argumentTyped,bodyTyped,converted⟩ := original_named_buffer_call history typed shape
  have argumentClosing : LoanClosingTyped env loans false (code.child (.var owner)) meanings (domain.subst meanings) :=
    ⟨typed.1,domain,argumentTyped,.refl _⟩
  have aligned := initial_run_code_aligned term fuel SizedBufferHeap.empty evaluating
  obtain ⟨value,found,kind⟩ := (context.child (.var owner)).variable_kind history argumentClosing aligned rfl
  have bufferKind : ValueKind env value (.buffer (count.subst meanings)) := by
    simpa only [domain,Term.subst,substArgs,Op.binders,liftSub] using kind
  obtain ⟨object,rfl⟩ := buffer_kind_is_owner history.wellFormed.admissible bufferKind
  let next := enter false domain body code.context code.origins code.values origin (some (.owner object))
  let nextMeanings := consValues (meanings owner) meanings
  have argumentSource : LoanTyping.HasType env [] [] true (meanings owner) (domain.subst meanings) := by
    simpa only [Code.child,Term.subst] using argumentClosing.closed history
  have argumentSize := sizes.typed_variable history argumentTyped found
  obtain ⟨nextContext,nextSizes⟩ := bind_variable_context context sizes argumentSource kind
    (fun _ same => by cases same; exact argumentSize) (by intro _ impossible; cases impossible)
    (by intro _ impossible; cases impossible) body origin
  have nextTyped : LoanClosingTyped env loans false next nextMeanings type :=
    ⟨nextContext.closing,bodyType,bodyTyped,converted⟩
  obtain ⟨rest,restChecked,receiptShape⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_named_buffer_call history.wellFormed.admissible (shape ▸ checked)
  rw [receiptShape] at budget world complete
  have used : (Control.seq (.use owner) .pure).demand owner = some 1 := by simp [Control.demand]
  have inactive : Loans.active code.context.length loans owner = false := by
    apply Bool.eq_false_iff.mpr
    intro active
    have zero := budget.sequence.1 owner active
    rw [used] at zero
    cases zero
  have unborrowed := coverage.inactive found inactive
  have invariant := initial_run_invariant term fuel
  have freeGuardReady := (invariant.2.free_guard_iff invariant.1).mpr unborrowed
  obtain ⟨nextWorld,nextTotal,one,noAliases⟩ :=
    world.enter_linear_owner complete found used domain body origin
  have nextSlots := slots.enter entered false domain body origin (some (.owner object))
  have nextCoverage := coverage_enter_unborrowed_owner coverage entered unborrowed domain body origin
  have lookedUp := named_call_lookup_steps state evaluating shape found
  dsimp only at lookedUp
  let returned : State := ⟨state.heap,.returned (.owner object),
    .argument (.closure false domain body code.context code.origins code.values) origin :: state.stack,state.pending⟩
  have enteredStep := enter_retained_call_step returned code domain body origin (.owner object) rfl rfl
  have ran : run 5 state =
      ⟨⟨state.heap,.evaluate next,state.stack,state.pending⟩,[.legacy (.activate false body origin)],5⟩ := by
    rw [run_add 4 1,lookedUp]
    dsimp only
    change Result.mk (run 1 returned).state (run 1 returned).events (4+(run 1 returned).steps) = _
    rw [run,enteredStep]
    rfl
  exact ⟨object,found,ran,nextTyped,nextContext,nextSizes,nextSlots,nextCoverage,freeGuardReady,
    rest,restChecked,budget.sequence.2.scope entered,nextWorld,nextTotal,one,noAliases⟩

namespace Examples

private def storedOwnerThroughCall : Term :=
  let buffer := Term.buffer (.natural 2)
  let bound := Term.decide (.natural 1) (.natural 2)
  let release := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let read := Term.load (.var 0) (.natural 1) bound release
  let call := Term.app (.lam false buffer read) (.var 0)
  .app (.lam false buffer call)
    (.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 7) bound)

set_option maxRecDepth 4096 in
/-- The admitted closure passes an already written owner to another actual
closure, whose Load observes the written value and whose callback frees it. -/
theorem owned_call_retains_written_cell :
    LoanTyping.MixedProgram.checkDeclaration 48 96 .empty ⟨.i64,storedOwnerThroughCall⟩ =
      some ⟨.i64,storedOwnerThroughCall⟩ ∧
    let result := run 45 (initial storedOwnerThroughCall)
    observe result = .integer 7 ∧ result.state.heap.metadata.heap.live 0 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
