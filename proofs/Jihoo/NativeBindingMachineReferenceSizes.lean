import Jihoo.NativeBindingMachineCanonicalCaptures
import Jihoo.NativeBindingMachineCanonicalReaderEntry

/-! Retained reference slots interpret actual live Buffer leases and immutable
allocation sizes at their original closed source types. This is a local
context interpretation, not exclusive ownership or an all-control theorem.
Canonical capture coverage supplies source freshness at reader close; source
Lend typing and actual inventory construct the new reference at reader entry. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

theorem ReferenceSize.convert (size : ReferenceSize env heap token type)
    (converted : LoanTyping.Conversion.Conv env type other) : ReferenceSize env heap token other := by
  obtain ⟨object,count,leased,live,length,represented⟩ := size
  exact ⟨object,count,leased,live,length,represented.trans converted⟩

/-- A new lease cannot overwrite an existing live reference token. -/
theorem ReferenceSize.lend (size : ReferenceSize env heap token type)
    (valid : SizedBufferHeap.Valid heap) (object : Nat) :
    ReferenceSize env (SizedBufferHeap.lend heap object) token type := by
  obtain ⟨owner,count,leased,live,length,represented⟩ := size
  have before := (valid.leased token owner leased).1
  have different : token ≠ heap.heap.nextLease := by omega
  refine ⟨owner,count,?_,live,length,represented⟩
  simpa only [SizedBufferHeap.lend,HeapLeases.put,different,ite_false] using leased

theorem ReferenceSize.close (size : ReferenceSize env heap token type)
    (different : token ≠ closing) : ReferenceSize env (SizedBufferHeap.close heap closing) token type := by
  obtain ⟨object,count,leased,live,length,represented⟩ := size
  refine ⟨object,count,?_,live,length,represented⟩
  simpa only [SizedBufferHeap.close,HeapLeases.put,different,ite_false] using leased

def ReferenceSizes (env : Environment) (heap : SizedBufferHeap.State)
    (code : Code) (meanings : Nat → Term) : Prop :=
  ∀ index binding token, lookup code.context index = some binding →
    code.values[index]? = some (some (.reference token)) →
    ReferenceSize env heap token (binding.ty.subst meanings)

theorem ReferenceSizes.initial (env : Environment) (heap : SizedBufferHeap.State) (term : Term) :
    ReferenceSizes env heap (.initial term) Term.var := by
  intro index binding token selected
  cases selected

theorem ReferenceSizes.child (sizes : ReferenceSizes env heap code meanings) (term : Term) :
    ReferenceSizes env heap (code.child term) meanings := sizes

theorem ReferenceSizes.typed_variable (sizes : ReferenceSizes env heap code meanings)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans code.context mode (.var index) type)
    (stored : code.values[index]? = some (some (.reference token))) :
    ReferenceSize env heap token (type.subst meanings) := by
  obtain ⟨binding,selected,converted⟩ := typed.principalView
  exact (sizes index binding token selected stored).convert
    (converted.substitution meanings history.wellFormed.closed)

theorem ReferenceSizes.lend (sizes : ReferenceSizes env heap code meanings)
    (valid : SizedBufferHeap.Valid heap) (object : Nat) :
    ReferenceSizes env (SizedBufferHeap.lend heap object) code meanings := by
  intro index binding token selected stored
  exact (sizes index binding token selected stored).lend valid object

/-- Erased, scalar and owner entries preserve all old reference slots. The
structural premise merely excludes the reference constructor at the new slot. -/
theorem ReferenceSizes.enter_nonreference (sizes : ReferenceSizes env heap code meanings)
    (erased : Bool) (domain body origin source : Term) (argument : Option Value)
    (notReference : ∀ token, argument ≠ some (.reference token)) :
    ReferenceSizes env heap (enter erased domain body code.context code.origins code.values origin argument)
      (consValues source meanings) := by
  intro index binding token selected stored
  cases index with
  | zero => exact False.elim (notReference token (Option.some.inj stored))
  | succ index =>
      obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
      subst binding
      simpa only [shift_subst_consValues] using sizes index previous token found stored

theorem ReferenceSizes.enter_reference (sizes : ReferenceSizes env heap code meanings)
    (reference : ReferenceSize env heap token (domain.subst meanings)) (body origin source : Term) :
    ReferenceSizes env heap (enter false domain body code.context code.origins code.values origin (some (.reference token)))
      (consValues source meanings) := by
  intro index binding actual selected stored
  cases index with
  | zero =>
      simp only [enter,lookup,Option.some.injEq] at selected
      subst binding
      have same : token = actual := Value.reference.inj (Option.some.inj (Option.some.inj stored))
      subst actual
      simpa only [shift_subst_consValues] using reference
  | succ index =>
      obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
      subst binding
      simpa only [shift_subst_consValues] using sizes index previous actual found stored

/-- A reader-entry snapshot predates the closing token, so every retained
reference slot keeps its live lease after that close. -/
theorem ReferenceSizes.close (sizes : ReferenceSizes env heap code meanings)
    (snapshot : CodeReferences closing code) :
    ReferenceSizes env (SizedBufferHeap.close heap closing) code meanings := by
  intro index binding token selected stored
  have before := (ValuesReferences.valueAt snapshot stored).referenceBound
  exact (sizes index binding token selected stored).close (by omega)

/-- Source snapshot freshness is derived from capture coverage and the actual
reachable saved continuation, rather than supplied as a source no-token oracle. -/
theorem ReferenceSizes.close_snapshot (term : Term) (fuel : Nat)
    (sizes : ReferenceSizes env (run fuel (BindingMachine.initial term)).state.heap source meanings)
    (captured : CapturedCanonicalView actual source indices)
    (stackShape : (run fuel (BindingMachine.initial term)).state.stack =
      .lendFinish closing object name origin resultOrigin (actual.child continuation) :: stack) :
    ReferenceSizes env (SizedBufferHeap.close (run fuel (BindingMachine.initial term)).state.heap closing) source meanings := by
  exact sizes.close (captured.initial_finish_snapshot term fuel stackShape).1

/-- The original complete Lend judgment identifies the physical owner's
Buffer length and reference annotation. Actual reader inventory supplies the
new live lease, constructing both the reference and its source binder context.
No selected lease, reference-output certificate or generic reader-body CODE
typing is assumed. General liveness through every control transition is open. -/
theorem reachable_canonical_reader_reference_entry (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (originalView : CapturedCanonicalView actualOriginal original originalIndices)
    (originalTyped : LoanClosingTyped env originalLoans false original originalMeanings originalType)
    (originalContext : ValueContext env original originalMeanings)
    (originalSizes : OwnerSizes env (run fuel (BindingMachine.initial term)).state.heap original originalMeanings)
    (originalReferences : ReferenceSizes env (run fuel (BindingMachine.initial term)).state.heap original originalMeanings)
    (originalScope : LoanScope original originalLoans stack)
    (actualOriginalShape : actualOriginal.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env originalLoans
      original.context original.term = some control)
    (ownerStored : actualOriginal.values[owner]? = some (some (.owner object)))
    (controlShape : (run fuel (BindingMachine.initial term)).state.control =
      .returned (.closure false domain readerBody actualOriginal.context actualOriginal.origins actualOriginal.values))
    (stackShape : (run fuel (BindingMachine.initial term)).state.stack =
      .lendReader token object (some name) ((Term.var owner).subst actualOriginal.origins) readerOrigin
        (actualOriginal.child (.lam false first (.lam false again body))) :: stack) :
    let sourceOwner := originalIndices owner
    let sourceDomain := domain.rename originalIndices
    let sourceReaderBody := readerBody.rename (liftRenaming 1 originalIndices)
    let sourceFirst := first.rename originalIndices
    let sourceLoans := Loans.enter original.context.length sourceOwner originalLoans
    let actualEntered := enter false domain readerBody actualOriginal.context actualOriginal.origins actualOriginal.values
      (.borrow ((Term.var owner).subst actualOriginal.origins)) (some (.reference token))
    let sourceEntered := enter false sourceDomain sourceReaderBody original.context original.origins original.values
      (.borrow ((Term.var sourceOwner).subst original.origins)) (some (.reference token))
    let enteredMeanings := consValues (.borrow ((Term.var sourceOwner).subst originalMeanings)) originalMeanings
    let specialized := original.child (Lending.read (.var sourceOwner) sourceReaderBody)
    let afterStack := .lendFinish token object (some name) ((Term.var owner).subst actualOriginal.origins)
      actualEntered.origin (actualOriginal.child (.lam false first (.lam false again body))) :: stack
    ReferenceSize env (run fuel (BindingMachine.initial term)).state.heap token (sourceDomain.subst originalMeanings) ∧
    ReferenceSizes env (run fuel (BindingMachine.initial term)).state.heap sourceEntered enteredMeanings ∧
    CapturedCanonicalView actualEntered sourceEntered (liftRenaming 1 originalIndices) ∧
    actualEntered.origin = specialized.origin ∧
    LoanClosingTyped env sourceLoans false specialized originalMeanings (sourceFirst.subst originalMeanings) ∧
    LoanTyping.HasType env [] [] true (sourceEntered.term.subst enteredMeanings)
      (sourceFirst.subst originalMeanings) ∧
    ValueContext env sourceEntered enteredMeanings ∧
    OwnerSizes env (run fuel (BindingMachine.initial term)).state.heap sourceEntered enteredMeanings ∧
    LoanScope sourceEntered sourceLoans afterStack ∧
    ReaderInventory (run fuel (BindingMachine.initial term)).state.heap (readerFrames afterStack) ∧
    step (run fuel (BindingMachine.initial term)).state = some
      (⟨(run fuel (BindingMachine.initial term)).state.heap,.evaluate actualEntered,afterStack⟩,
        some (.activate false readerBody (.borrow ((Term.var owner).subst actualOriginal.origins)))) := by
  let sourceOwner := originalIndices owner
  let sourceDomain := domain.rename originalIndices
  let sourceReaderBody := readerBody.rename (liftRenaming 1 originalIndices)
  let sourceFirst := first.rename originalIndices
  let sourceAgain := again.rename (liftRenaming 1 originalIndices)
  let sourceBody := body.rename (liftRenaming 2 originalIndices)
  obtain ⟨leased,live,stepped,enteredView,originEq,substitutionBridge,specializedTyped,allowed,
    bodyClosed,bodyContext,bodySizes,bodyScope,specializedContext,specializedSizes,specializedScope,
    inventory,reader,projected⟩ := reachable_canonical_reader_entry term fuel history originalView.view
    originalTyped originalContext originalSizes originalScope actualOriginalShape checked ownerStored controlShape stackShape
  have originalShape : original.term = .lend (.var sourceOwner) (.lam false sourceDomain sourceReaderBody)
      (.lam false sourceFirst (.lam false sourceAgain sourceBody)) := by
    rw [← originalView.view.termEq,actualOriginalShape]
    simp only [sourceOwner,sourceDomain,sourceReaderBody,sourceFirst,sourceAgain,sourceBody,
      Term.rename,renameArgs,Op.binders,liftRenaming]
  have sourceOwnerStored := (originalView.view.values owner).symm.trans ownerStored
  obtain ⟨closing,localType,sourceTyped,converted⟩ := originalTyped
  rw [originalShape] at sourceTyped
  obtain ⟨ownerType,valueType,sort,ownerTyped,owned,binder,domainConverted,readTyped,outlived⟩ :=
    sourceTyped.explicitLendReaderInputs history.wellFormed
  have ownerSize := originalSizes.typed_variable history ownerTyped sourceOwnerStored
  have domainClosed : LoanTyping.Conversion.Conv env (sourceDomain.subst originalMeanings)
      (.ref (ownerType.subst originalMeanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      domainConverted.substitution originalMeanings history.wellFormed.closed
  have referenceConverted : LoanTyping.Conversion.Conv env
      (.ref (.buffer (.natural ((run fuel (BindingMachine.initial term)).state.heap.length object))))
      (sourceDomain.subst originalMeanings) :=
    (RawLend.Conv.node .ref (.cons ownerSize.realization .nil)).trans domainClosed.symm
  have reference : ReferenceSize env (run fuel (BindingMachine.initial term)).state.heap token
      (sourceDomain.subst originalMeanings) :=
    ⟨object,(run fuel (BindingMachine.initial term)).state.heap.length object,leased,live,rfl,referenceConverted⟩
  have enteredReferences := originalReferences.enter_reference (domain := sourceDomain) reference
    sourceReaderBody (.borrow ((Term.var sourceOwner).subst original.origins))
    (.borrow ((Term.var sourceOwner).subst originalMeanings))
  refine ⟨reference,enteredReferences,⟨enteredView,?_⟩,originEq,specializedTyped,bodyClosed,
    bodyContext,bodySizes,bodyScope,inventory,stepped⟩
  simpa only [BindingMachine.enter] using originalView.captures.cons_cons (some (.reference token))

end Jihoo.NativeKernel.Environment.BindingMachine
