import Jihoo.NativeBindingMachineReferenceIndex
import Jihoo.NativeBindingMachineLendValues

/-! Actual scalar/owner continuation bindings are interpreted from the same
complete input Lend and resource projection. Specialized callbacks retain their
checked reads/restores; no generic callback or result-typing oracle is added. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

theorem HasType.explicitLendValueDomains (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body))) type) :
    ∃ ownerType valueType, HasType env [] ctx true owner ownerType ∧
      HasType env [] ctx true (Lending.read owner readerBody) valueType ∧
      Conversion.Conv env first valueType ∧ Conversion.Conv env again (ownerType.rename Nat.succ) := by
  obtain ⟨principal,origin,converted⟩ := typed.lendView
  cases origin with
  | generic owner owned outlived reader continuation allowed =>
      obtain ⟨sort,firstBody,binder,innerTyped,firstConverted⟩ := continuation.lamView
      obtain ⟨flag,firstDomain,innerConverted⟩ := firstConverted.pi_injective wf.admissible
      obtain ⟨innerSort,lastBody,innerBinder,lastTyped,lastConverted⟩ := innerTyped.lamView
      have innerPi := lastConverted.trans innerConverted
      simp only [Term.rename,renameArgs,Op.binders,liftRenaming] at innerPi
      have ownerDomain := (innerPi.pi_injective wf.admissible).2.1
      exact ⟨_,_,owner.ghost [],reader_from_generic_checks wf owner owned reader,firstDomain,ownerDomain⟩
  | dependentCode owner owned binder domain reader outlived first again continuation normalized shifted allowed =>
      exact ⟨_,_,owner.ghost [],reader.ghost [],first,again⟩
  | dependentGhost owner owned binder domain reader outlived first again continuation normalized shifted =>
      exact ⟨_,_,owner.ghost [],reader.ghost [],first,again⟩

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

private theorem bind_value_context (context : ValueContext env code meanings)
    (sizes : OwnerSizes env heap code meanings)
    (argument : LoanTyping.HasType env [] [] true source (domain.subst meanings))
    (kind : ValueKind env value (domain.subst meanings))
    (ownerSize : ∀ object, value = .owner object → OwnerSize env heap object (domain.subst meanings))
    (naturalMeaning : ∀ number, value = .natural number → source = .natural number)
    (integerMeaning : ∀ number, value = .integer number → source = .integer number)
    (body origin : Term) :
    let next := enter false domain body code.context code.origins code.values origin (some value)
    ValueContext env next (consValues source meanings) ∧ OwnerSizes env heap next (consValues source meanings) := by
  constructor
  · refine ⟨context.closing.consValues argument,?_,?_⟩
    · constructor
      · intro index actual stored
        cases index with
        | zero => exact naturalMeaning actual (Option.some.inj (Option.some.inj stored))
        | succ index => exact context.scalars.1 index actual stored
      · intro index actual stored
        cases index with
        | zero => exact integerMeaning actual (Option.some.inj (Option.some.inj stored))
        | succ index => exact context.scalars.2 index actual stored
    · intro index binding actual selected stored
      cases index with
      | zero =>
          simp only [enter,lookup,Option.some.injEq] at selected
          subst binding
          have same : value = actual := Option.some.inj (Option.some.inj stored)
          subst actual
          simpa only [shift_subst_consValues] using kind
      | succ index =>
          obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
          subst binding
          simpa only [shift_subst_consValues] using context.kinds index previous actual found stored
  · intro index binding object selected stored
    cases index with
    | zero =>
        simp only [enter,lookup,Option.some.injEq] at selected
        subst binding
        simpa only [shift_subst_consValues] using ownerSize object (Option.some.inj (Option.some.inj stored))
    | succ index =>
        obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
        subst binding
        simpa only [shift_subst_consValues] using sizes index previous object found stored

private theorem scalar_continuation_context
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans mode code meanings type)
    (context : ValueContext env code meanings) (sizes : OwnerSizes env heap code meanings)
    (shape : code.term = .lend (.var owner) (.lam false domain (.index reference offset evidence))
      (.lam false first (.lam false again body)))
    (stored : code.values[owner]? = some (some (.owner object)))
    (bounded : ValueReduction.signed64 value) (resultOrigin : Term) :
    let next := restoredContinuation code first again body ((Term.var owner).subst code.origins) resultOrigin object (.integer value)
    let nextMeanings := consValues ((Term.var owner).subst meanings) (consValues (.integer value) meanings)
    ValueContext env next nextMeanings ∧ OwnerSizes env heap next nextMeanings ∧
      LoanTyping.HasType env [] [] true (next.term.subst nextMeanings) type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨ownerType,valueType,ownerTyped,readTyped,firstConverted,againConverted⟩ :=
    source.explicitLendValueDomains history.wellFormed
  have closedRead := readTyped.ghostSubstitution history.wellFormed closing
  simp only [Lending.read,Term.subst,substArgs,Op.binders,liftSub] at closedRead
  have readI64 : LoanTyping.Conversion.Conv env .i64 (valueType.subst meanings) := closedRead.principalView
  have firstKind : ValueKind env (.integer value) (first.subst meanings) :=
    readI64.trans (firstConverted.substitution meanings history.wellFormed.closed).symm
  have actual : LoanTyping.HasType env [] [] true (.integer value) .i64 := .integer bounded.1 bounded.2
  have firstTyped := actual.convert firstKind
  have firstContexts := bind_value_context context sizes firstTyped firstKind
    (by intro object same; cases same) (by intro number same; cases same)
    (by intro number same; cases same; rfl) (.lam false again body) resultOrigin
  obtain ⟨firstContext,firstSizes⟩ := firstContexts
  have againClosed : LoanTyping.Conversion.Conv env (again.subst (consValues (.integer value) meanings))
      (ownerType.subst meanings) := by
    simpa only [shift_subst_consValues] using
      againConverted.substitution (consValues (.integer value) meanings) history.wellFormed.closed
  have ownerClosed := (ownerTyped.ghostSubstitution history.wellFormed closing).convert againClosed.symm
  have ownerSize := (sizes.typed_variable history ownerTyped stored).convert againClosed.symm
  have ownerKind : ValueKind env (.owner object) (again.subst (consValues (.integer value) meanings)) :=
    ⟨.natural (heap.length object),ownerSize.realization⟩
  obtain ⟨nextContext,nextSizes⟩ := bind_value_context firstContext firstSizes ownerClosed ownerKind
    (by intro actual same; cases same; exact ownerSize)
    (by intro number same; cases same) (by intro number same; cases same)
    body ((Term.var owner).subst code.origins)
  refine ⟨nextContext,nextSizes,?_⟩
  have closedSource := (show LoanClosingTyped env loans mode code meanings type from
    ⟨closing,localType,by simpa only [shape] using source,converted⟩).closed history
  simp only [shape,Term.subst,substArgs,Op.binders,liftSub] at closedSource
  have finished : LoanTyping.HasType env [] [] true
      (Lending.finish (meanings owner) (body.subst (liftSub 2 meanings)) (.integer value)) type :=
    LoanTyping.actual_scalar_finish history.wellFormed closedSource bounded
  change LoanTyping.HasType env [] [] true
    (body.subst (consValues ((Term.var owner).subst meanings) (consValues (.integer value) meanings))) type
  refine Eq.mpr (congrArg (fun term => LoanTyping.HasType env [] [] true term type)
    (continuation_actual_substitution body ((Term.var owner).subst meanings) (.integer value) meanings)) ?_
  simpa only [Term.subst] using finished

private theorem value_close_five_steps (heap : SizedBufferHeap.State) (code : Code)
    (leased : heap.heap.lease token = some object)
    (first again body ownerOrigin resultOrigin : Term) (result : Value) (name : Option Nat) (stack : List Frame) :
    run 5 ⟨heap,.returned result,
      .lendFinish token object name ownerOrigin resultOrigin (code.child (.lam false first (.lam false again body))) :: stack⟩ =
      ⟨⟨SizedBufferHeap.close heap token,
        .evaluate (restoredContinuation code first again body ownerOrigin resultOrigin object result),stack⟩,
        [.heap (.close token),.activate false (.lam false again body) resultOrigin,.activate false body ownerOrigin],5⟩ := by
  simp only [run,step,action,returnAction,execute,leased,↓reduceIte,evaluateAction,
    Code.child,applyValue,enter,restoredContinuation,Option.map_some]
  rfl

/-- At the actual scalar return boundary the same source/resource check
constructs both continuation bindings, their heap-size context and the exact
closed original result type. The reader closes before either binding. -/
theorem reachable_value_lend_handoff (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (shape : code.term = .lend (.var owner) (.lam false domain (.index reference offset evidence))
      (.lam false first (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+1) env loans code.context code.term = some control)
    (stored : code.values[owner]? = some (some (.owner object)))
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (returned : (run fuel (initial term)).state.control = .returned (.integer value))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst code.origins) resultOrigin
        (code.child (.lam false first (.lam false again body))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let closed := SizedBufferHeap.close heap token
    let next := restoredContinuation code first again body ((Term.var owner).subst code.origins) resultOrigin object (.integer value)
    let nextMeanings := consValues ((Term.var owner).subst meanings) (consValues (.integer value) meanings)
    run 5 (run fuel (initial term)).state =
      ⟨⟨closed,.evaluate next,stack⟩,
        [.heap (.close token),.activate false (.lam false again body) resultOrigin,
          .activate false body ((Term.var owner).subst code.origins)],5⟩ ∧
      ValueContext env next nextMeanings ∧ OwnerSizes env closed next nextMeanings ∧
      LoanTyping.HasType env [] [] true (next.term.subst nextMeanings) type ∧
      LoanSlots next loans stack ∧ ReaderInventory closed (readerFrames stack) ∧
      (closed.heap.live object = true) ∧
      (freeGuard closed object = true ↔ ¬ ObjectReader object stack) ∧
      (∀ index, next.values[index]? = (some (.integer value) :: code.values)[Jihoo.Quantity.openOwner (owner+1) index]?) ∧
      ∃ reader mode rest,
        LoanTyping.ResourceQuantity.projectRaw resourceFuel env (Loans.enter code.context.length owner loans)
          code.context (Lending.read (.var owner) (.index reference offset evidence)) = some reader ∧
        LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans (⟨first,false⟩ :: code.context)
          (body.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
        reader.demand owner = some 0 ∧ (Jihoo.Quantity.Control.scope mode rest).demand owner = some 1 ∧
        control = .seq reader (.scope mode rest) := by
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,name) :: readerFrames stack) at inventory
  have leased := inventory.live _ List.mem_cons_self
  have live := (initial_run_heap_valid term fuel).leased token object leased |>.2
  have remaining := inventory.finish.2
  have valid := SizedBufferHeap.step_valid (initial_run_heap_valid term fuel) (.close leased)
  have closedSizes := sizes.steps (.cons (.close leased) .nil)
  obtain ⟨nextContext,nextSizes,nextTyped⟩ := scalar_continuation_context history typed context closedSizes shape stored
    (initial_run_integer_bound term fuel returned) resultOrigin
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.returned (.integer value),
        .lendFinish token object name ((Term.var owner).subst code.origins) resultOrigin
          (code.child (.lam false first (.lam false again body))) :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  refine ⟨?_,nextContext,nextSizes,nextTyped,
    restored_continuation_loans code slots entered _ _ _ _ _ _ _,remaining,live,
    remaining.free_guard_iff valid,restored_continuation_slots code stored _ _ _ _ _,?_⟩
  · rw [stateShape]
    exact value_close_five_steps _ _ leased _ _ _ _ _ _ _ _
  · rw [shape] at checked
    obtain ⟨outside,sort,resultType,reader,mode,rest,originalScope,readScope,restScope,
      formed,controlScoped,sourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,
      readZero,restOne,same⟩ := LoanTyping.ResourceQuantity.dependent_project_contract checked
    exact ⟨reader,mode,rest,readProjected,restProjected,readZero,restOne,same⟩

end Jihoo.NativeKernel.Environment.BindingMachine
