import Jihoo.NativeBindingMachineReaderLeaseWorld

/-! A saved continuation's Buffer references survive actual reader execution,
close and both retained binders. The reference and owner-size contexts for
the saved captures are supplied at reader entry. The result slot is derived
from source-variable typing and the original Lend's Outlived restriction. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- The six actual variable handoff transitions construct original-type
canonical CODE and a live reference context. Older captures retain their
leases through the reader interval and close, and source Outlived excludes
a reference in the new result slot. The captured alias view remains available
for later reader frames. The entry token identifies the saved continuation and
outer stack at the finish. -/
theorem reachable_canonical_frame_variable_reference_handoff (term : Term) (entryFuel bodyFuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (originalView : CapturedCanonicalView actualOriginal original originalIndices)
    (originalTyped : LoanClosingTyped env originalLoans false original originalMeanings originalType)
    (originalContext : ValueContext env original originalMeanings)
    (originalSizes : OwnerSizes env (run entryFuel (initial term)).state.heap original originalMeanings)
    (originalReferences : ReferenceSizes env (run entryFuel (initial term)).state.heap original originalMeanings)
    (originalScope : LoanScope original originalLoans stack)
    (actualOriginalShape : actualOriginal.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env originalLoans
      original.context original.term = some control)
    (ownerStored : actualOriginal.values[owner]? = some (some (.owner object)))
    (entryShape : (run entryFuel (initial term)).state.stack =
      .lendReader token object name ((Term.var owner).subst actualOriginal.origins) readerOrigin
        (actualOriginal.child (.lam false first (.lam false again body))) :: stack)
    (evaluating : (run (entryFuel+bodyFuel) (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings
      ((first.rename originalIndices).subst originalMeanings))
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (sizes : OwnerSizes env (run (entryFuel+bodyFuel) (initial term)).state.heap source meanings)
    (shape : actual.term = .var index)
    (finishShape : (run (entryFuel+bodyFuel) (initial term)).state.stack =
      .lendFinish token finalObject finalName finalOrigin resultOrigin finalContinuation :: finalStack) :
    ∃ value, actual.values[index]? = some (some value) ∧
      let valueTerm := meanings (indices index)
      let closed := SizedBufferHeap.close (run (entryFuel+bodyFuel) (initial term)).state.heap token
      let next := restoredContinuation actualOriginal first again body
        ((Term.var owner).subst actualOriginal.origins) resultOrigin object value
      let canonical := canonicalContinuation original (originalIndices owner) (first.rename originalIndices)
        (body.rename (liftRenaming 2 originalIndices)) resultOrigin value
      let canonicalMeanings := consValues valueTerm originalMeanings
      run 6 (run (entryFuel+bodyFuel) (initial term)).state =
        ⟨⟨closed,.evaluate next,stack⟩,
          [.heap (.close token),.activate false (.lam false again body) resultOrigin,
            .activate false body ((Term.var owner).subst actualOriginal.origins)],6⟩ ∧
      CapturedCanonicalView next canonical
        (Jihoo.Quantity.openOwner (originalIndices owner+1) ∘ liftRenaming 2 originalIndices) ∧
      LoanClosingTyped env originalLoans false canonical canonicalMeanings originalType ∧
      ValueContext env canonical canonicalMeanings ∧
      OwnerSizes env closed canonical canonicalMeanings ∧
      ReferenceSizes env closed canonical canonicalMeanings ∧
      LoanScope canonical originalLoans stack ∧ ReaderInventory closed (readerFrames stack) ∧
      ¬ StateReferenceOccurs token ⟨closed,.evaluate next,stack⟩ ∧
      ∃ rest, LoanTyping.ResourceQuantity.projectRaw resourceFuel env originalLoans
        canonical.context canonical.term = some rest := by
  have endpoint : (run (entryFuel+bodyFuel) (initial term)).state =
      (run bodyFuel (run entryFuel (initial term)).state).state := by
    rw [run_add]
  have intervalFinish : (run bodyFuel (run entryFuel (initial term)).state).state.stack =
      .lendFinish token finalObject finalName finalOrigin resultOrigin finalContinuation :: finalStack :=
    endpoint ▸ finishShape
  obtain ⟨objectEq,nameEq,originEq,continuationEq,stackEq⟩ :=
    reachable_reader_finish_snapshot term entryFuel bodyFuel entryShape intervalFinish
  rw [objectEq,nameEq,originEq,continuationEq,stackEq] at intervalFinish finishShape
  obtain ⟨_,_,closedReferences,_,_⟩ := reachable_saved_reference_interval
    term entryFuel bodyFuel originalView originalReferences entryShape intervalFinish
  have endpointSizes := originalSizes.run (state := (run entryFuel (initial term)).state)
    (initial_run_heap_valid term entryFuel) bodyFuel
  rw [← endpoint] at endpointSizes closedReferences
  obtain ⟨value,stored,kind,_,executed,_,canonicalTyped,canonicalContext,canonicalSizes,
      canonicalScope,inventory,_,_,absent,rest,projected⟩ :=
    reachable_canonical_frame_variable_handoff term (entryFuel+bodyFuel) history originalView.view
      originalTyped originalContext endpointSizes originalScope actualOriginalShape checked ownerStored
      evaluating view typed context aligned sizes shape finishShape
  have originalShape : original.term = .lend (.var (originalIndices owner))
      (.lam false (domain.rename originalIndices) (readerBody.rename (liftRenaming 1 originalIndices)))
      (.lam false (first.rename originalIndices)
        (.lam false (again.rename (liftRenaming 1 originalIndices)) (body.rename (liftRenaming 2 originalIndices)))) := by
    rw [← originalView.view.termEq,actualOriginalShape]
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming]
  have allowed := originalTyped.reader_domain_outlived history originalShape
  have notReference : ∀ selected, some value ≠ some (.reference selected) := by
    intro selected same
    have valueReference : value = .reference selected := Option.some.inj same
    rw [valueReference] at kind
    obtain ⟨domain,converted⟩ := kind
    exact allowed.reference_excluded history.wellFormed.admissible converted
  have nextReferences := closedReferences.enter_nonreference false (first.rename originalIndices)
    ((body.rename (liftRenaming 2 originalIndices)).rename (Jihoo.Quantity.openOwner (originalIndices owner+1)))
    resultOrigin (meanings (indices index)) (some value) notReference
  exact ⟨value,stored,executed,originalView.restored ownerStored first again body resultOrigin value,
    canonicalTyped,canonicalContext,canonicalSizes,nextReferences,canonicalScope,inventory,absent,rest,projected⟩

end Jihoo.NativeKernel.Environment.BindingMachine
