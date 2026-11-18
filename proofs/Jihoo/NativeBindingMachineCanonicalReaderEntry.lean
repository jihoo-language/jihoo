import Jihoo.NativeBindingMachineCanonicalFrameHandoff

/-! Explicit named reader entry retains an arbitrary canonical source snapshot.
The runtime keeps its raw reference binder; the authentic CODE derivation
types the specialized read in the original source context. These are related
by explicit substitution and equal closed origins, without a general CODE
beta rule or arbitrary-input typing for specialized callbacks. Generic computed
callbacks and preservation of this substitution view at every control point
remain separate obligations. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

private theorem reader_specialization_substitution (body : Term) (indices : Nat → Nat) (owner : Nat) :
    body.subst (fun | 0 => .borrow (.var owner) | index+1 => .var (indices index)) =
      Lending.read (.var owner) (body.rename (liftRenaming 1 indices)) := by
  rw [Lending.read,Term.subst_rename]
  congr 1
  funext index
  cases index <;> rfl

/-- The actual returned closure and enclosing named reader frame activate in
one real step. The full canonical Lend/resource query supplies the specialized
CODE read at its original first annotation, while source reference entry
constructs value/size/loan contexts and closed ghost body typing. Actual and
canonical reader names may differ, and neither alias map must be injective. -/
theorem reachable_canonical_reader_entry (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (originalView : CanonicalView actualOriginal original originalIndices)
    (originalTyped : LoanClosingTyped env originalLoans false original originalMeanings originalType)
    (originalContext : ValueContext env original originalMeanings)
    (originalSizes : OwnerSizes env (run fuel (initial term)).state.heap original originalMeanings)
    (originalScope : LoanScope original originalLoans stack)
    (actualOriginalShape : actualOriginal.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env originalLoans
      original.context original.term = some control)
    (ownerStored : actualOriginal.values[owner]? = some (some (.owner object)))
    (controlShape : (run fuel (initial term)).state.control =
      .returned (.closure false domain readerBody actualOriginal.context actualOriginal.origins actualOriginal.values))
    (stackShape : (run fuel (initial term)).state.stack =
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
    (run fuel (initial term)).state.heap.heap.lease token = some object ∧
    (run fuel (initial term)).state.heap.heap.live object = true ∧
    step (run fuel (initial term)).state = some
      (⟨(run fuel (initial term)).state.heap,.evaluate actualEntered,afterStack⟩,
        some (.activate false readerBody (.borrow ((Term.var owner).subst actualOriginal.origins)))) ∧
    CanonicalView actualEntered sourceEntered (liftRenaming 1 originalIndices) ∧
    actualEntered.origin = specialized.origin ∧
    actualEntered.term.subst
      (fun | 0 => .borrow (.var sourceOwner) | index+1 => .var (originalIndices index)) = specialized.term ∧
    LoanClosingTyped env sourceLoans false specialized originalMeanings (sourceFirst.subst originalMeanings) ∧
    LoanTyping.Outlived env (sourceFirst.subst originalMeanings) ∧
    LoanTyping.HasType env [] [] true (sourceEntered.term.subst enteredMeanings)
      (sourceFirst.subst originalMeanings) ∧
    ValueContext env sourceEntered enteredMeanings ∧
    OwnerSizes env (run fuel (initial term)).state.heap sourceEntered enteredMeanings ∧
    LoanScope sourceEntered sourceLoans afterStack ∧
    ValueContext env specialized originalMeanings ∧
    OwnerSizes env (run fuel (initial term)).state.heap specialized originalMeanings ∧
    LoanScope specialized sourceLoans afterStack ∧
    ReaderInventory (run fuel (initial term)).state.heap (readerFrames afterStack) ∧
    ∃ reader, LoanTyping.ResourceQuantity.projectRaw resourceFuel env sourceLoans
      specialized.context specialized.term = some reader := by
  let sourceOwner := originalIndices owner
  let sourceDomain := domain.rename originalIndices
  let sourceReaderBody := readerBody.rename (liftRenaming 1 originalIndices)
  let sourceFirst := first.rename originalIndices
  let sourceAgain := again.rename (liftRenaming 1 originalIndices)
  let sourceBody := body.rename (liftRenaming 2 originalIndices)
  let sourceLoans := Loans.enter original.context.length sourceOwner originalLoans
  let actualEntered := enter false domain readerBody actualOriginal.context actualOriginal.origins actualOriginal.values
    (.borrow ((Term.var owner).subst actualOriginal.origins)) (some (.reference token))
  let sourceEntered := enter false sourceDomain sourceReaderBody original.context original.origins original.values
    (.borrow ((Term.var sourceOwner).subst original.origins)) (some (.reference token))
  let enteredMeanings := consValues (.borrow ((Term.var sourceOwner).subst originalMeanings)) originalMeanings
  let specialized := original.child (Lending.read (.var sourceOwner) sourceReaderBody)
  let afterStack := .lendFinish token object (some name) ((Term.var owner).subst actualOriginal.origins)
    actualEntered.origin (actualOriginal.child (.lam false first (.lam false again body))) :: stack
  have originalShape : original.term = .lend (.var sourceOwner) (.lam false sourceDomain sourceReaderBody)
      (.lam false sourceFirst (.lam false sourceAgain sourceBody)) := by
    rw [← originalView.termEq,actualOriginalShape]
    simp only [sourceOwner,sourceDomain,sourceReaderBody,sourceFirst,sourceAgain,sourceBody,
      Term.rename,renameArgs,Op.binders,liftRenaming]
  have sourceOwnerStored := (originalView.values owner).symm.trans ownerStored
  obtain ⟨outside,sort,result,reader,mode,rest,originalScoped,readerScoped,restScoped,
    rawSourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,readZero,restOne,same⟩ :=
    LoanTyping.ResourceQuantity.dependent_raw_project_contract (originalShape ▸ checked)
  have specializedTyped : LoanClosingTyped env sourceLoans false specialized originalMeanings
      (sourceFirst.subst originalMeanings) :=
    ⟨originalContext.closing,sourceFirst,readTyped,.refl _⟩
  have allowed := originalTyped.reader_domain_outlived history originalShape
  obtain ⟨valueType,outlived,bodyClosed,bodyContext⟩ :=
    value_reader_closing history originalTyped originalContext originalShape token
  have enteredSizes : OwnerSizes env (run fuel (initial term)).state.heap sourceEntered enteredMeanings :=
    originalSizes.enter_reference sourceDomain sourceReaderBody
      (.borrow ((Term.var sourceOwner).subst original.origins))
      (.borrow ((Term.var sourceOwner).subst originalMeanings)) token
  have enteredView : CanonicalView actualEntered sourceEntered (liftRenaming 1 originalIndices) := by
    have entered := originalView.enter false domain readerBody
      (.borrow ((Term.var owner).subst actualOriginal.origins)) (some (.reference token))
    simpa only [actualEntered,sourceEntered,sourceDomain,sourceReaderBody,sourceOwner,
      Term.subst,originalView.origins owner] using entered
  have sourceOrigin : sourceEntered.origin = specialized.origin :=
    reader_entry_origin original (.var sourceOwner) sourceDomain sourceReaderBody token
  have closesRead : sourceEntered.term.subst enteredMeanings = specialized.term.subst originalMeanings :=
    reader_entry_origin ⟨original.term,original.context,originalMeanings,original.values⟩
      (.var sourceOwner) sourceDomain sourceReaderBody token
  have originalClosedBody : LoanTyping.HasType env [] [] true
      (sourceEntered.term.subst enteredMeanings) (sourceFirst.subst originalMeanings) := by
    rw [closesRead]
    exact specializedTyped.closed history
  have substitutionBridge : actualEntered.term.subst
      (fun | 0 => .borrow (.var sourceOwner) | index+1 => .var (originalIndices index)) = specialized.term :=
    reader_specialization_substitution readerBody originalIndices sourceOwner
  have readerScope := originalScope.begin_reader sourceOwnerStored token name
    ((Term.var owner).subst actualOriginal.origins) readerOrigin
    (actualOriginal.child (.lam false first (.lam false again body)))
  have enteredScope := readerScope.enter false sourceDomain sourceReaderBody
    (.borrow ((Term.var sourceOwner).subst original.origins)) (some (.reference token))
  have afterEnteredScope : LoanScope sourceEntered sourceLoans afterStack :=
    enteredScope.reader_body actualEntered.origin
  have afterSpecializedScope : LoanScope specialized sourceLoans afterStack :=
    (readerScope.reader_body actualEntered.origin).child (Lending.read (.var sourceOwner) sourceReaderBody)
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,some name) :: readerFrames stack) at inventory
  have leased := inventory.live _ List.mem_cons_self
  have live := ((initial_run_heap_valid term fuel).leased token object leased).2
  have afterInventory : ReaderInventory (run fuel (initial term)).state.heap (readerFrames afterStack) := inventory
  have stepped : step (run fuel (initial term)).state = some
      (⟨(run fuel (initial term)).state.heap,.evaluate actualEntered,afterStack⟩,
        some (.activate false readerBody (.borrow ((Term.var owner).subst actualOriginal.origins)))) := by
    simp only [step,action,controlShape,stackShape,reader_activation_origin,Option.map_some,execute]
    rfl
  exact ⟨leased,live,stepped,enteredView,enteredView.origin.trans sourceOrigin,substitutionBridge,
    specializedTyped,allowed,originalClosedBody,bodyContext,enteredSizes,afterEnteredScope,
    originalContext.child _,originalSizes.child _,afterSpecializedScope,afterInventory,reader,readProjected⟩

end Jihoo.NativeKernel.Environment.BindingMachine
