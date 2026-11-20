import Jihoo.NativeBindingMachineMutableOwnedResult
import Jihoo.NativeBindingMachineMutableReaderReturnDemand
import Jihoo.NativeBindingMachineReaderResume

/-! The original resource projection of a reusable CODE closure authenticates
the retained runtime body and forces every captured owner demand to zero.
Computing a callee through Strict retains that same closure receipt. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity ResourceModes

/-- Recover the original closure body receipt and its resolved binder mode.
The projected scope retains the whole leading lambda telescope. -/
theorem projectRaw_closure_origin
    (checked : projectRaw (fuel+1) env loans ctx (.lam erased domain body) = some closureReceipt) :
    ∃ mode bodyReceipt, ResourceModes.Resolved env loans ctx erased domain mode ∧
      projectRaw fuel env loans (⟨domain,erased⟩ :: ctx) body = some bodyReceipt ∧
      closureReceipt = .closure (.scope mode (functionTail body bodyReceipt)) := by
  simp only [projectRaw,Op.arity,List.length_cons,List.length_nil,Nat.reduceAdd,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  split at checked
  · contradiction
  · obtain ⟨mode,resolved,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨bodyReceipt,bodyProjected,same⟩ := Option.bind_eq_some_iff.mp checked
    exact ⟨mode,bodyReceipt,ResourceModes.resolve_sound resolved,bodyProjected,(Option.some.inj same).symm⟩

/-- A checked Buffer lambda retains its original body projection under the
linear parameter. A further leading lambda keeps its separate telescope rule. -/
theorem projectRaw_buffer_closure_origin (admissible : EnvironmentDelta.Admissible env)
    (singleBody : lambdaHead body = false)
    (checked : projectRaw (fuel+1) env loans ctx (.lam false (.buffer count) body) = some closureReceipt) :
    ∃ bodyReceipt, projectRaw fuel env loans (⟨.buffer count,false⟩ :: ctx) body = some bodyReceipt ∧
      closureReceipt = .closure (.scope .linear bodyReceipt) := by
  obtain ⟨mode,bodyReceipt,resolved,bodyProjected,same⟩ := projectRaw_closure_origin checked
  have linear := resolved.convertible_buffer_linear admissible (.refl _)
  subst mode
  exact ⟨bodyReceipt,bodyProjected,by simpa only [functionTail,singleBody,Bool.false_eq_true,↓reduceIte] using same⟩

/-- A single erased lambda's resource receipt contains the original projected
body and its erased scope. Evidence does not consume a runtime slot. -/
theorem projectRaw_erased_closure_origin
    (singleBody : lambdaHead body = false)
    (checked : projectRaw (fuel+1) env loans ctx (.lam true domain body) = some closureReceipt) :
    ∃ bodyReceipt, projectRaw fuel env loans (⟨domain,true⟩ :: ctx) body = some bodyReceipt ∧
      closureReceipt = .closure (.scope .erased bodyReceipt) := by
  obtain ⟨mode,bodyReceipt,resolved,bodyProjected,same⟩ := projectRaw_closure_origin checked
  cases resolved
  exact ⟨bodyReceipt,bodyProjected,by simpa only [functionTail,singleBody,Bool.false_eq_true,↓reduceIte] using same⟩

theorem strict_projection
    (checked : projectRaw (fuel+1) env loans ctx (.strict first later) = some receipt) :
    ∃ firstReceipt laterReceipt,
      projectRaw fuel env loans ctx first = some firstReceipt ∧ projectRaw fuel env loans ctx later = some laterReceipt ∧
      receipt = .seq firstReceipt (.seq laterReceipt .pure) := by
  simp only [projectRaw,Op.arity,List.length_cons,List.length_nil,Nat.reduceAdd,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte,erasedNode,runtimeFields] at checked
  obtain ⟨indices,selected,checked⟩ := Option.bind_eq_some_iff.mp checked
  cases selected
  have ordered : fields (projectRaw fuel env loans ctx) [first,later] [0,1] = (do
      let left ← projectRaw fuel env loans ctx first
      let right ← projectRaw fuel env loans ctx later
      pure (.seq left (.seq right .pure))) := by
    cases left : projectRaw fuel env loans ctx first <;> cases right : projectRaw fuel env loans ctx later <;>
      simp [fields,fetch,left,right]
  rw [ordered] at checked
  obtain ⟨firstReceipt,firstProjected,afterFirst⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨laterReceipt,laterProjected,same⟩ := Option.bind_eq_some_iff.mp afterFirst
  exact ⟨firstReceipt,laterReceipt,firstProjected,laterProjected,(Option.some.inj same).symm⟩

/-- A full checked application of a computed Strict callee retains the
original head and its actual relevant argument as separate ordered receipts. -/
theorem projectRaw_strict_buffer_call (admissible : EnvironmentDelta.Admissible env)
    (checked : projectRaw (fuel+3) env loans ctx
      (.app (.strict first (.lam false (.buffer count) body)) argument) = some receipt) :
    ∃ calleeReceipt argumentReceipt,
      projectRaw (fuel+2) env loans ctx (.strict first (.lam false (.buffer count) body)) = some calleeReceipt ∧
      projectRaw (fuel+2) env loans ctx argument = some argumentReceipt ∧
      receipt = .seq calleeReceipt (.seq argumentReceipt .pure) := by
  simp only [projectRaw,splitSpine,Op.arity,List.length_cons,List.length_nil,Nat.reduceAdd,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  obtain ⟨⟨head,supplied⟩,splitSpineChecked,checked⟩ := Option.bind_eq_some_iff.mp checked
  cases splitSpineChecked
  obtain ⟨⟨entries,result⟩,replayed,checked⟩ := Option.bind_eq_some_iff.mp checked
  have inferred := (ResourceReplay.checked_origin replayed).2.2.2
  obtain ⟨signature,headTyped,replaySteps,_⟩ := ResourceReplay.infer_sound inferred
  split at checked
  · contradiction
  · obtain ⟨opened,openedProof,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨runtime,runtimeProjected,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨calleeReceipt,calleeProjected,same⟩ := Option.bind_eq_some_iff.mp checked
    simp only [openHead] at openedProof
    cases openedProof
    cases replaySteps with
    | cons normalized _ _ _ next =>
        cases next
        obtain ⟨_,_,_,_,converted⟩ := headTyped.strict_tail.lamView
        have flag := ((converted.trans (Conversion.normalize?_sound normalized)).pi_injective admissible).1
        simp only [flag.symm,Environment.CallReplay.runtimeArguments,List.filterMap_cons,List.filterMap_nil] at runtimeProjected
        obtain ⟨argumentReceipt,argumentProjected,runtimeEq⟩ := Option.bind_eq_some_iff.mp runtimeProjected
        have runtimeShape : runtime = [argumentReceipt] := (Option.some.inj runtimeEq).symm
        subst runtime
        exact ⟨calleeReceipt,argumentReceipt,calleeProjected,argumentProjected,(Option.some.inj same).symm⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

structure CheckedBufferClosure (env : Environment) (loans : Loans.Stack) (capture : Code)
    (count body : Term) (fuel : Nat) (bodyReceipt : Jihoo.Quantity.Control) : Prop where
  bodyProjected : LoanTyping.ResourceQuantity.projectRaw fuel env loans (⟨.buffer count,false⟩ :: capture.context) body =
    some bodyReceipt
  scopeValid : LocalScopes (.scope .linear bodyReceipt)
  captureZero : ∀ index object, capture.values[index]? = some (some (.owner object)) →
    (Control.scope .linear bodyReceipt).demand index = some 0

private theorem captured_scope_zero (demanded : (Control.closure scope).demand index = some uses) :
    scope.demand index = some 0 := by
  simp only [Control.demand] at demanded
  obtain ⟨amount,observed,rest⟩ := Option.bind_eq_some_iff.mp demanded
  split at rest
  · rename_i zero
    exact zero ▸ observed
  · contradiction

/-- Evaluating any checked lambda retains its original dependent body and
the resource projection for the whole telescope. Owners already present in
the capture have zero demand in that reusable scope. -/
theorem checked_lambda_retains_capture (state : State) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : state.control = .evaluate code) (shape : code.term = .lam erased domain body)
    (typed : LoanClosingTyped env loans false code meanings requested)
    (checked : LoanTyping.ResourceQuantity.projectRaw (fuel+1) env loans code.context code.term = some closureReceipt)
    (valid : LocalScopes closureReceipt) (total : OwnerDemandWorld.Total code closureReceipt) :
    let closure := Value.closure erased domain body code.context code.origins code.values
    step state = some ({state with control := .returned closure}, none) ∧
    ValueKind env closure requested ∧
    ∃ mode bodyReceipt bodyType,
      LoanTyping.ResourceModes.Resolved env loans code.context erased domain mode ∧
      LoanTyping.HasType env loans (⟨domain,erased⟩ :: code.context) false body bodyType ∧
      RawLend.Conv env (.pi erased (domain.subst meanings) (bodyType.subst (liftSubOne meanings))) requested ∧
      LoanTyping.ResourceQuantity.projectRaw fuel env loans (⟨domain,erased⟩ :: code.context) body = some bodyReceipt ∧
      closureReceipt = .closure (.scope mode (functionTail body bodyReceipt)) ∧
      LocalScopes (.scope mode (functionTail body bodyReceipt)) ∧
      ∀ index object, code.values[index]? = some (some (.owner object)) →
        (Jihoo.Quantity.Control.scope mode (functionTail body bodyReceipt)).demand index = some 0 := by
  obtain ⟨_,_,source,closed⟩ := typed
  rw [shape] at source checked
  obtain ⟨_,bodyType,_,bodyTyped,principal⟩ := source.lamView
  have converted : RawLend.Conv env (.pi erased (domain.subst meanings) (bodyType.subst (liftSubOne meanings))) requested := by
    have exactType := (principal.substitution meanings history.wellFormed.closed).trans closed
    simpa only [Term.pi,Term.subst,substArgs,Op.binders,liftSub] using exactType
  obtain ⟨mode,bodyReceipt,resolved,bodyProjected,rfl⟩ := LoanTyping.ResourceQuantity.projectRaw_closure_origin checked
  refine ⟨?_,⟨_,_,converted⟩,mode,bodyReceipt,bodyType,resolved,bodyTyped,converted,bodyProjected,rfl,valid,?_⟩
  · simp only [step,evaluating,shape,evaluateAction,executeLegacy,execute,Option.map_none]
  · intro index object stored
    exact captured_scope_zero (total index object stored).choose_spec

/-- Original closure creation determines the body scope. Complete closure
demand for the retained captures supplies the zero demand of each physical
owner, regardless of where the closure is eventually applied. -/
theorem checked_buffer_closure_of_projection (admissible : EnvironmentDelta.Admissible env)
    (singleBody : lambdaHead body = false)
    (checked : LoanTyping.ResourceQuantity.projectRaw (fuel+1) env loans capture.context
      (.lam false (.buffer count) body) = some closureReceipt)
    (valid : LocalScopes closureReceipt) (total : OwnerDemandWorld.Total capture closureReceipt) :
    ∃ bodyReceipt, CheckedBufferClosure env loans capture count body fuel bodyReceipt := by
  obtain ⟨bodyReceipt,bodyProjected,rfl⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_buffer_closure_origin admissible singleBody checked
  exact ⟨bodyReceipt,bodyProjected,valid,fun index object found =>
    captured_scope_zero (total index object found).choose_spec⟩

/-- The checked closure itself provides a capture world for the opened body.
Zero-demand captures need no liveness assumption after evaluating an argument. -/
theorem CheckedBufferClosure.owner_world
    (checked : CheckedBufferClosure env loans capture count body fuel receipt) (heap : SizedBufferHeap.State) :
    OwnerDemandWorld heap capture (.scope .linear receipt) ∧ OwnerDemandWorld.Total capture (.scope .linear receipt) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro index object uses stored positive
    rw [checked.captureZero index object stored] at positive
    cases positive
  · intro index alias object uses separate stored previous positive
    exact checked.captureZero alias object previous
  · intro index object stored
    exact ⟨0,checked.captureZero index object stored⟩

private theorem tail_demand_total
    (complete : OwnerDemandWorld.Total capture (.seq before (.seq rest .pure))) :
    OwnerDemandWorld.Total capture rest := by
  intro index object stored
  obtain ⟨uses,found⟩ := complete index object stored
  simp only [Control.demand] at found
  obtain ⟨_,_,afterPrefix⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨_,observed,_⟩ := Option.bind_eq_some_iff.mp afterPrefix
  obtain ⟨amount,known,_⟩ := Option.bind_eq_some_iff.mp observed
  exact ⟨amount,known⟩

private theorem computed_strict_closure_steps (state : State) (capture argument : Code)
    (count body : Term) (returned : state.control = .returned value)
    (shape : state.stack = .strict (capture.child (.lam false (.buffer count) body)) :: .function argument :: stack) :
    let closure := Value.closure false (.buffer count) body capture.context capture.origins capture.values
    run 3 state = ⟨⟨state.heap,.evaluate argument,.argument closure argument.origin :: stack,state.pending⟩,[],3⟩ := by
  simp only [run,step,returned,shape,returnAction,executeLegacy,execute,evaluateAction,Code.child,Option.map_none]
  rfl

/-- After a computed Strict prefix, the actual function frame retains the
original checked closure and its exact capture receipt while evaluating the
argument. The prefix may have performed effects before returning. -/
theorem checked_strict_callee_to_saved_argument (state : State) (argument : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false capture meanings functionType)
    (sourceShape : capture.term = .strict first (.lam false (.buffer count) body))
    (singleBody : lambdaHead body = false)
    (checked : LoanTyping.ResourceQuantity.projectRaw (fuel+2) env loans capture.context capture.term = some receipt)
    (valid : LocalScopes receipt) (total : OwnerDemandWorld.Total capture receipt)
    (returned : state.control = .returned value)
    (stackShape : state.stack = .strict (capture.child (.lam false (.buffer count) body)) :: .function argument :: stack) :
    let closure := Value.closure false (.buffer count) body capture.context capture.origins capture.values
    run 3 state = ⟨⟨state.heap,.evaluate argument,.argument closure argument.origin :: stack,state.pending⟩,[],3⟩ ∧
      LoanClosingTyped env loans false (capture.child (.lam false (.buffer count) body)) meanings functionType ∧
      ∃ bodyReceipt, CheckedBufferClosure env loans capture count body fuel bodyReceipt := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [sourceShape] at source checked
  obtain ⟨firstReceipt,closureReceipt,_,closureProjected,rfl⟩ :=
    LoanTyping.ResourceQuantity.strict_projection checked
  refine ⟨computed_strict_closure_steps state capture argument count body returned stackShape,
    ⟨closing,localType,source.strict_tail,converted⟩,?_⟩
  exact checked_buffer_closure_of_projection history.wellFormed.admissible singleBody closureProjected
    valid.2.1 (tail_demand_total total)

private theorem strict_call_types
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .app (.strict first (.lam false (.buffer count) body)) argument) :
    ∃ inputType resultType,
      LoanClosingTyped env loans false (code.child (.strict first (.lam false (.buffer count) body))) meanings
        (.pi false inputType resultType) ∧
      LoanClosingTyped env loans false (code.child argument) meanings inputType ∧
      LoanTyping.Conversion.Conv env (resultType.subst (single (argument.subst meanings))) type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨erased,input,result,functionTyped,argumentTyped,_,applicationConverted⟩ := source.appView
  obtain ⟨_,_,_,_,functionConverted⟩ := functionTyped.strict_tail.lamView
  have flags := (functionConverted.pi_injective history.wellFormed.admissible).1
  subst erased
  refine ⟨input.subst meanings,result.subst (liftSubOne meanings),
    ⟨closing,.pi false input result,functionTyped,?_⟩,⟨closing,input,argumentTyped,.refl _⟩,?_⟩
  · simp only [Term.subst,substArgs,Op.binders,liftSub]
    exact .refl _
  · simpa only [Term.subst_instantiate] using
      (applicationConverted.substitution meanings history.wellFormed.closed).trans converted

/-- The original checked application authenticates both the retained callee
and the still-pending argument. Resuming after the Strict effect preserves
their independent receipts, the complete closure capture budget, and the
original dependent application result conversion. -/
theorem checked_strict_call_to_saved_argument (state : State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (sourceShape : code.term = .app (.strict first (.lam false (.buffer count) body)) argument)
    (singleBody : lambdaHead body = false)
    (checked : LoanTyping.ResourceQuantity.projectRaw (fuel+3) env loans code.context code.term = some receipt)
    (valid : LocalScopes receipt) (total : OwnerDemandWorld.Total code receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (returned : state.control = .returned value)
    (stackShape : state.stack = .strict (code.child (.lam false (.buffer count) body)) ::
      .function (code.child argument) :: stack) :
    let closure := Value.closure false (.buffer count) body code.context code.origins code.values
    let argumentCode := code.child argument
    run 3 state = ⟨⟨state.heap,.evaluate argumentCode,.argument closure argumentCode.origin :: stack,state.pending⟩,[],3⟩ ∧
    ∃ inputType resultType bodyReceipt argumentReceipt calleeReceipt,
      LoanClosingTyped env loans false (code.child (.lam false (.buffer count) body)) meanings (.pi false inputType resultType) ∧
      CheckedBufferClosure env loans code count body fuel bodyReceipt ∧
      LoanClosingTyped env loans false argumentCode meanings inputType ∧
      LoanTyping.ResourceQuantity.projectRaw (fuel+2) env loans code.context
        (.strict first (.lam false (.buffer count) body)) = some calleeReceipt ∧
      LoanTyping.ResourceQuantity.projectRaw (fuel+2) env loans argumentCode.context argumentCode.term = some argumentReceipt ∧
      LoanTyping.ResourceQuantity.LoanBudget argumentCode.context.length loans argumentReceipt ∧
      OwnerDemandWorld.Total argumentCode argumentReceipt ∧
      receipt = .seq calleeReceipt (.seq argumentReceipt .pure) ∧
      LoanTyping.Conversion.Conv env (resultType.subst (single (argument.subst meanings))) type := by
  obtain ⟨inputType,resultType,calleeTyped,argumentTyped,originalResult⟩ := strict_call_types history typed sourceShape
  obtain ⟨calleeReceipt,argumentReceipt,calleeChecked,argumentChecked,receiptShape⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_strict_buffer_call history.wellFormed.admissible (sourceShape ▸ checked)
  rw [receiptShape] at valid total budget
  let callee := code.child (.strict first (.lam false (.buffer count) body))
  have calleeTotal : OwnerDemandWorld.Total callee calleeReceipt := by
    intro index object stored
    obtain ⟨uses,found⟩ := total index object stored
    simp only [Control.demand] at found
    obtain ⟨amount,observed,_⟩ := Option.bind_eq_some_iff.mp found
    exact ⟨amount,observed⟩
  obtain ⟨executed,lambdaTyped,bodyReceipt,created⟩ := checked_strict_callee_to_saved_argument state
    (code.child argument) history calleeTyped rfl singleBody calleeChecked valid.1 calleeTotal returned stackShape
  have captureChecked : CheckedBufferClosure env loans code count body fuel bodyReceipt :=
    ⟨created.bodyProjected,created.scopeValid,created.captureZero⟩
  exact ⟨executed,inputType,resultType,bodyReceipt,argumentReceipt,calleeReceipt,lambdaTyped,captureChecked,argumentTyped,
    calleeChecked,argumentChecked,budget.sequence.2.sequence.1,tail_demand_total total,receiptShape,originalResult⟩

/-- Apply the actual saved closure using the certificate from creation.
The closure's checked capture demands reconstruct the body world and all
enclosing loan budgets, even when argument evaluation has changed the heap. -/
theorem saved_checked_buffer_closure_entry (state : State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (functionTyped : LoanClosingTyped env loans false (capture.child (.lam false (.buffer count) body)) meanings
      (.pi false inputType resultType))
    (context : ValueContext env capture meanings) (sizes : OwnerSizes env state.heap.metadata capture meanings)
    (slots : LoanSlots capture loans (stack ++ state.pending.flatMap Prod.snd))
    (coverage : LoanCoverage capture loans (stack ++ state.pending.flatMap Prod.snd))
    (entered : Loans.Entered capture.context.length loans)
    (argument : OwnedResult env state.heap.metadata (stack ++ state.pending.flatMap Prod.snd) object source inputType)
    (returned : state.control = .returned (.owner object))
    (stackShape : state.stack = .argument
      (.closure false (.buffer count) body capture.context capture.origins capture.values) origin :: stack)
    (created : CheckedBufferClosure env loans capture count body fuel receipt) :
    let next := enter false (.buffer count) body capture.context capture.origins capture.values origin (some (.owner object))
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
  obtain ⟨world,total⟩ := created.owner_world state.heap.metadata
  have budget : LoanTyping.ResourceQuantity.LoanBudget capture.context.length loans (.scope .linear receipt) := by
    intro index active
    obtain ⟨object,stored,_⟩ := slots index active
    exact created.captureZero index object stored
  exact saved_closure_owned_result_entry state history functionTyped context sizes slots coverage entered argument returned
    stackShape created.bodyProjected created.scopeValid budget world total (fun alias stored => created.captureZero alias object stored)

private theorem erased_value_context
    (context : ValueContext env capture meanings)
    (closed : LoanTyping.Ghost.Substitution env (⟨domain,true⟩ :: capture.context) [] (consValues source meanings))
    (body origin : Term) :
    ValueContext env (enter true domain body capture.context capture.origins capture.values origin none)
      (consValues source meanings) := by
  refine ⟨closed,⟨?_,?_⟩,?_⟩
  · intro index value stored
    cases index with
    | zero => cases stored
    | succ index => exact context.scalars.1 index value stored
  · intro index value stored
    cases index with
    | zero => cases stored
    | succ index => exact context.scalars.2 index value stored
  · intro index binding value selected stored
    cases index with
    | zero => cases stored
    | succ index =>
      obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
      subst binding
      simpa only [shift_subst_consValues] using context.kinds index previous value found stored

/-- The indexed machine applies the saved erased closure without running the
pending argument. The checked ghost argument closes the original dependent
result, while the original captured owners and active loans retain their
receipts. The proof works with distinct caller and capture contexts. -/
theorem saved_checked_erased_closure_entry (state : State) (capture argument : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (functionTyped : LoanClosingTyped env loans false (capture.child (.lam true domain body)) meanings
      (.pi true inputType resultType))
    (argumentTyped : LoanClosingTyped env argumentLoans true argument argumentMeanings inputType)
    (context : ValueContext env capture meanings)
    (slots : LoanSlots capture loans (stack ++ state.pending.flatMap Prod.snd))
    (coverage : LoanCoverage capture loans (stack ++ state.pending.flatMap Prod.snd))
    (entered : Loans.Entered capture.context.length loans)
    (returned : state.control = .returned (.closure true domain body capture.context capture.origins capture.values))
    (stackShape : state.stack = .function argument :: stack)
    (singleBody : lambdaHead body = false)
    (checked : LoanTyping.ResourceQuantity.projectRaw (fuel+1) env loans capture.context (.lam true domain body) =
      some closureReceipt)
    (valid : LocalScopes closureReceipt) (total : OwnerDemandWorld.Total capture closureReceipt) :
    let source := argument.term.subst argumentMeanings
    let next := enter true domain body capture.context capture.origins capture.values argument.origin none
    let nextMeanings := consValues source meanings
    step state = some (⟨state.heap,.evaluate next,stack,state.pending⟩,
      some (.legacy (.activate true body argument.origin))) ∧
    LoanClosingTyped env loans false next nextMeanings (resultType.subst (single source)) ∧
    ValueContext env next nextMeanings ∧
    LoanSlots next loans (stack ++ state.pending.flatMap Prod.snd) ∧
    LoanCoverage next loans (stack ++ state.pending.flatMap Prod.snd) ∧
    ∃ receipt, LoanTyping.ResourceQuantity.projectRaw fuel env loans next.context next.term = some receipt ∧
      LoanTyping.ResourceQuantity.LoanBudget next.context.length loans receipt ∧
      OwnerDemandWorld state.heap.metadata next receipt ∧ OwnerDemandWorld.Total next receipt := by
  let sourceFunction : Code := ⟨.lam true domain body,capture.context,meanings,capture.values⟩
  let sourceArgument : Code := ⟨argument.term,argument.context,argumentMeanings,argument.values⟩
  have sourceFunctionTyped : LoanSourceTyped env loans false sourceFunction (.pi true inputType resultType) :=
    functionTyped
  have sourceArgumentTyped : LoanSourceTyped env argumentLoans true sourceArgument inputType := argumentTyped
  have opened := (enter_loan_source_typed history sourceFunctionTyped sourceArgumentTyped none).2
  have doesNotOwn : ∀ object, (none : Option Value) ≠ some (.owner object) := by
    intro object different
    cases different
  obtain ⟨receipt,bodyProjected,rfl⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_erased_closure_origin singleBody checked
  have unused index object (stored : capture.values[index]? = some (some (.owner object))) :
      (.scope .erased receipt : Jihoo.Quantity.Control).demand index = some 0 :=
    captured_scope_zero (total index object stored).choose_spec
  have scopedTotal : OwnerDemandWorld.Total capture (.scope .erased receipt) :=
    fun index object stored => ⟨0,unused index object stored⟩
  have scopedWorld : OwnerDemandWorld state.heap.metadata capture (.scope .erased receipt) := by
    refine ⟨?_,?_⟩
    · intro index object uses stored positive
      rw [unused index object stored] at positive
      cases positive
    · intro index alias object uses different stored previous positive
      exact unused alias object previous
  have scopedBudget : LoanTyping.ResourceQuantity.LoanBudget capture.context.length loans (.scope .erased receipt) := by
    intro index active
    obtain ⟨object,stored,_⟩ := slots index active
    exact unused index object stored
  have world := scopedWorld.enter_nonowner_scope (erased := true) scopedTotal (show LocalScopes (.scope .erased receipt) from valid)
    domain body argument.origin doesNotOwn
  refine ⟨?_,opened,erased_value_context context opened.1 body argument.origin,
    slots.enter entered true domain body argument.origin none,
    coverage.enter_nonowner entered true domain body argument.origin none doesNotOwn,
    receipt,bodyProjected,scopedBudget.scope entered,world⟩
  simp only [step,returned,stackShape,returnAction,applyValue,executeLegacy,execute,Option.map_some]

namespace Examples

private def callbackDomain : Term := .pi false .u64 .u64
private def higherOrderBody : Term := .lam false .u64 (.app (.var 1) (.var 0))
private def higherOrderClosure : Term := .lam false callbackDomain higherOrderBody

/-- An admitted higher-order closure retains both original leading binders.
The indexed machine observes the first lambda without opening either body. -/
theorem checked_higher_order_closure_retains_telescope :
    LoanTyping.MixedProgram.checkDeclaration 48 96 .empty
      ⟨.pi false callbackDomain callbackDomain,higherOrderClosure⟩ =
      some ⟨.pi false callbackDomain callbackDomain,higherOrderClosure⟩ ∧
    (run 1 (initial higherOrderClosure)).state.control =
      .returned (.closure false callbackDomain higherOrderBody [] Term.var []) := by
  exact ⟨by cbv,rfl⟩

private def ignoredEvidence : Term :=
  .strict (.arith .add (.integer 9223372036854775807) (.integer 1))
    (.decide (.natural 0) (.natural 1))

private def erasedCall : Term :=
  .app (.lam true (.lt (.natural 0) (.natural 1)) (.integer 7)) ignoredEvidence

/-- The original checker admits the application. Evaluating its erased
evidence would overflow, but the only event is entry into the saved body. -/
theorem checked_erased_call_skips_overflowing_evidence :
    LoanTyping.MixedProgram.checkDeclaration 48 96 .empty ⟨.i64,erasedCall⟩ =
      some ⟨.i64,erasedCall⟩ ∧
    let result := run 12 (initial erasedCall)
    observe result = .integer 7 ∧
      result.events = [.legacy (.activate true (.integer 7) ignoredEvidence)] := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,by cbv⟩

private def effectfulComputedCallee : Term :=
  let buffer := Term.buffer (.natural 2)
  let proof := Term.decide (.natural 1) (.natural 2)
  let release := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let body := Term.load (.var 0) (.natural 1) proof release
  let firstEffect := Term.free (.alloc (.natural 1) (.integer 0)) (.integer 0)
  let computed := Term.strict firstEffect (.lam false buffer body)
  .app (.lam false buffer (.app computed (.var 0)))
    (.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 7) proof)

set_option maxRecDepth 4096 in
/-- The callee first allocates and frees a temporary. It then evaluates the
saved lambda, consumes the written Buffer, and reads and frees that owner. -/
theorem strict_callee_reuses_owned_argument :
    LoanTyping.MixedProgram.checkDeclaration 48 96 .empty ⟨.i64,effectfulComputedCallee⟩ =
      some ⟨.i64,effectfulComputedCallee⟩ ∧
    let result := run 60 (initial effectfulComputedCallee)
    observe result = .integer 7 ∧ result.state.heap.metadata.heap.nextObject = 2 ∧
      result.state.heap.metadata.heap.live 0 = false ∧ result.state.heap.metadata.heap.live 1 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
