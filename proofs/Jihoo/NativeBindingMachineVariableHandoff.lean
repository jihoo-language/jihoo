import Jihoo.NativeBindingMachineOutlivedReferences
import Jihoo.NativeBindingMachineLoanScope
import Jihoo.NativeBindingMachineCanonicalHandoff

/-! A source-derived variable result closes the actual Lend reader and enters
the original continuation. Its checked ghost meaning closes the canonical
result binder: scalars retain their observed numeral, while owned values keep
their checked source expression and concrete allocation-size association.
Canonical CODE typing retains the ORIGINAL Lend result type. General resource
and converse physical-loan coverage for an owned result are not claimed. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private theorem actual_explicit_value_finish
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env [] [] true
      (.lend owner (.lam false domain readerBody) (.lam false first (.lam false again body))) type)
    (valueTyped : HasType env [] [] true value first) :
    HasType env [] [] true (Lending.finish owner body value) type := by
  obtain ⟨principal,origin,converted⟩ := typed.lendView
  cases origin with
  | generic ownerTyped owned outlived readerTyped continuationTyped allowed =>
      obtain ⟨sort,firstBody,binder,innerTyped,firstConverted⟩ := continuationTyped.lamView
      have domainConverted := (firstConverted.pi_injective wf.admissible).2.1
      exact (continuation_from_generic_checks wf ownerTyped
        (valueTyped.convert domainConverted) continuationTyped).convert converted
  | dependentGhost ownerTyped owned domainTyped domainConverted readerTyped outlived
      firstConverted againConverted continuationTyped resultConverted removed =>
      have finished := finish_from_specialized_checks wf continuationTyped valueTyped
      exact (finished.convert (result_outside wf resultConverted removed)).convert converted

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

private theorem bind_variable_context (context : ValueContext env code meanings)
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

private theorem variable_handoff_six_steps (heap : SizedBufferHeap.State)
    (current original : Code) (shape : current.term = .var index)
    (stored : current.values[index]? = some (some value))
    (leased : heap.heap.lease token = some object)
    (first again body ownerOrigin resultOrigin : Term) (name : Option Nat) (stack : List Frame) :
    run 6 ⟨heap,.evaluate current,
      .lendFinish token object name ownerOrigin resultOrigin
        (original.child (.lam false first (.lam false again body))) :: stack⟩ =
      ⟨⟨SizedBufferHeap.close heap token,
        .evaluate (restoredContinuation original first again body ownerOrigin resultOrigin object value),stack⟩,
        [.heap (.close token),.activate false (.lam false again body) resultOrigin,
          .activate false body ownerOrigin],6⟩ := by
  simp only [run,step,action,evaluateAction,shape,stored,returnAction,execute,leased,
    ite_true,Code.child,applyValue,enter,restoredContinuation,Option.map_some]
  rfl

/-- One original full Lend/resource query and a currently source-typed
canonical variable construct its actual value and six-step handoff. The
canonical continuation has CODE typing at the ORIGINAL requested Lend type,
constructed value/size contexts and outer ordered source-loan association.
No runtime result typing, selected value, successful close or alias injection
is an input. Owned-result exclusive accounting and converse LoanCoverage
still require general resource/control preservation. -/
theorem reachable_canonical_variable_handoff (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (originalTyped : LoanClosingTyped env originalLoans false original originalMeanings originalType)
    (originalContext : ValueContext env original originalMeanings)
    (originalSizes : OwnerSizes env (run fuel (initial term)).state.heap original originalMeanings)
    (originalScope : LoanScope original originalLoans stack)
    (originalShape : original.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env originalLoans
      original.context original.term = some control)
    (ownerStored : original.values[owner]? = some (some (.owner object)))
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings (first.subst originalMeanings))
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap source meanings)
    (shape : actual.term = .var index)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst original.origins) resultOrigin
        (original.child (.lam false first (.lam false again body))) :: stack) :
    ∃ value, actual.values[index]? = some (some value) ∧
      ValueKind env value (first.subst originalMeanings) ∧
      let valueTerm := meanings (indices index)
      let closed := SizedBufferHeap.close (run fuel (initial term)).state.heap token
      let next := restoredContinuation original first again body
        ((Term.var owner).subst original.origins) resultOrigin object value
      let canonical := canonicalContinuation original owner first body resultOrigin value
      let canonicalMeanings := consValues valueTerm originalMeanings
      LoanTyping.HasType env [] [] true valueTerm (first.subst originalMeanings) ∧
      run 6 (run fuel (initial term)).state =
        ⟨⟨closed,.evaluate next,stack⟩,
          [.heap (.close token),.activate false (.lam false again body) resultOrigin,
            .activate false body ((Term.var owner).subst original.origins)],6⟩ ∧
      CanonicalView next canonical (Jihoo.Quantity.openOwner (owner+1)) ∧
      LoanClosingTyped env originalLoans false canonical canonicalMeanings originalType ∧
      ValueContext env canonical canonicalMeanings ∧ OwnerSizes env closed canonical canonicalMeanings ∧
      LoanScope canonical originalLoans stack ∧ ReaderInventory closed (readerFrames stack) ∧
      SizedBufferHeap.Valid closed ∧ closed.heap.live object = true ∧
      ¬ StateReferenceOccurs token ⟨closed,.evaluate next,stack⟩ ∧
      ∃ rest, LoanTyping.ResourceQuantity.projectRaw resourceFuel env originalLoans
        canonical.context canonical.term = some rest := by
  have allowed := originalTyped.reader_domain_outlived history originalShape
  obtain ⟨value,actualStored,kind,variableStep⟩ := reachable_canonical_variable_kind
    term fuel history evaluating view typed context aligned shape
  have sourceStored := (view.values index).symm.trans actualStored
  have sourceShape : source.term = .var (indices index) := by
    rw [← view.termEq,shape]
    simp only [Term.rename]
  let valueTerm := meanings (indices index)
  have argumentTyped : LoanTyping.HasType env [] [] true valueTerm (first.subst originalMeanings) := by
    simpa only [valueTerm,sourceShape,Term.subst] using typed.closed history
  have naturalMeaning : ∀ number, value = .natural number → valueTerm = .natural number := by
    intro number same
    subst value
    exact context.scalars.1 (indices index) number sourceStored
  have integerMeaning : ∀ number, value = .integer number → valueTerm = .integer number := by
    intro number same
    subst value
    exact context.scalars.2 (indices index) number sourceStored
  have ownerSize : ∀ returnedObject, value = .owner returnedObject →
      OwnerSize env (run fuel (initial term)).state.heap returnedObject (first.subst originalMeanings) := by
    intro returnedObject same
    subst value
    obtain ⟨sourceClosing,sourceType,sourceTyped,sourceConverted⟩ := typed
    rw [sourceShape] at sourceTyped
    exact (sizes.typed_variable history sourceTyped sourceStored).convert sourceConverted
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,name) :: readerFrames stack) at inventory
  obtain ⟨leased,remaining⟩ := inventory.finish
  have closedOriginalSizes := originalSizes.steps (.cons (.close leased) .nil)
  have closedOwnerSize : ∀ returnedObject, value = .owner returnedObject →
      OwnerSize env (SizedBufferHeap.close (run fuel (initial term)).state.heap token)
        returnedObject (first.subst originalMeanings) := by
    intro returnedObject same
    exact (ownerSize returnedObject same).steps (.cons (.close leased) .nil)
  obtain ⟨canonicalContext,canonicalSizes⟩ := bind_variable_context (domain := first)
    (source := valueTerm) (value := value) originalContext closedOriginalSizes
    argumentTyped kind closedOwnerSize naturalMeaning integerMeaning
    (body.rename (Jihoo.Quantity.openOwner (owner+1))) resultOrigin
  obtain ⟨outside,sort,result,reader,mode,rest,originalScoped,readerScoped,restScoped,
    rawSourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,readZero,restOne,same⟩ :=
    LoanTyping.ResourceQuantity.dependent_raw_project_contract (originalShape ▸ checked)
  rw [LoanTyping.ResourceQuantity.restore_body_is_alias] at bodyTyped restProjected
  let canonical := canonicalContinuation original owner first body resultOrigin value
  let canonicalMeanings := consValues valueTerm originalMeanings
  have canonicalTyped : LoanClosingTyped env originalLoans false canonical canonicalMeanings
      (result.subst canonicalMeanings) :=
    ⟨canonicalContext.closing,result,bodyTyped,.refl _⟩
  have closedOriginal := originalTyped.closed history
  simp only [originalShape,Term.subst,substArgs,Op.binders,liftSub] at closedOriginal
  have finished : LoanTyping.HasType env [] [] true
      (Lending.finish (originalMeanings owner) (body.subst (liftSub 2 originalMeanings)) valueTerm) originalType :=
    LoanTyping.actual_explicit_value_finish history.wellFormed closedOriginal argumentTyped
  let next := restoredContinuation original first again body
    ((Term.var owner).subst original.origins) resultOrigin object value
  have actualClosed : LoanTyping.HasType env [] [] true
      (next.term.subst (consValues ((Term.var owner).subst originalMeanings)
        (consValues valueTerm originalMeanings))) originalType := by
    change LoanTyping.HasType env [] [] true
      (body.subst (consValues ((Term.var owner).subst originalMeanings)
        (consValues valueTerm originalMeanings))) originalType
    rw [continuation_actual_substitution]
    simpa only [Term.subst] using finished
  have restoredView := restored_canonical_view original ownerStored first again body resultOrigin value
  have related : ∀ selected,
      consValues ((Term.var owner).subst originalMeanings) (consValues valueTerm originalMeanings) selected =
        consValues valueTerm originalMeanings (Jihoo.Quantity.openOwner (owner+1) selected) := by
    intro selected
    cases selected with
    | zero => simp only [consValues,Term.subst,Jihoo.Quantity.openOwner]
    | succ selected => rfl
  have closedEq := restoredView.closed related
  rw [closedEq] at actualClosed
  have originalConverted := (canonicalTyped.closed history).unique history.wellFormed actualClosed
  have originalCanonical : LoanClosingTyped env originalLoans false canonical canonicalMeanings originalType :=
    ⟨canonicalContext.closing,result,bodyTyped,originalConverted⟩
  have canonicalScope := originalScope.enter false first
    (body.rename (Jihoo.Quantity.openOwner (owner+1))) resultOrigin (some value)
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.evaluate actual,
        .lendFinish token object name ((Term.var owner).subst original.origins) resultOrigin
          (original.child (.lam false first (.lam false again body))) :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  have executed := variable_handoff_six_steps (run fuel (initial term)).state.heap actual original
    shape actualStored leased first again body ((Term.var owner).subst original.origins) resultOrigin name stack
  rw [← stateShape] at executed
  obtain ⟨continuationReady,outerReady⟩ := initial_run_finish_capture_bounds term fuel stackShape
  have valueReady : ValueReferences token value := by
    rcases kind.outlived_shape history.wellFormed.admissible allowed with
      ⟨number,rfl⟩ | ⟨number,rfl⟩ | ⟨returnedObject,rfl⟩
    · exact .natural
    · exact .integer
    · exact .owner
  have nextReady : CodeReferences token next :=
    .retained .owner (.retained valueReady continuationReady)
  have absent : ¬ StateReferenceOccurs token
      ⟨SizedBufferHeap.close (run fuel (initial term)).state.heap token,.evaluate next,stack⟩ := by
    intro occurs
    rcases occurs with occurs | ⟨frame,member,occurs⟩
    · exact nextReady.fresh_absent occurs
    · exact (outerReady.fresh_absent member) occurs
  have valid := SizedBufferHeap.step_valid (initial_run_heap_valid term fuel) (.close leased)
  have live := ((initial_run_heap_valid term fuel).leased token object leased).2
  exact ⟨value,actualStored,kind,argumentTyped,executed,restoredView,originalCanonical,
    canonicalContext,canonicalSizes,canonicalScope,remaining,valid,live,absent,rest,restProjected⟩

end Jihoo.NativeKernel.Environment.BindingMachine
