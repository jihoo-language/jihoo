import Jihoo.NativeBindingMachineMutableAlignment
import Jihoo.NativeBindingMachineMutableReaderCaptures
import Jihoo.NativeBindingMachineMutableReaderClose
import Jihoo.NativeBindingMachineMutableReferenceOccurs
import Jihoo.NativeBindingMachineOutlivedReferences

/-! Canonical source typing selects the actual variable result of an indexed
reader. The original Lend judgment supplies the policy that prevents its
result, including any nested captures, from containing the closing token. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

/-- An indexed-machine lookup through a canonical alias map returns the value
at the original source type without modifying the heap or either stack. -/
theorem canonical_variable_result
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (shape : actual.term = .var index) :
    ∃ value, actual.values[index]? = some (some value) ∧ ValueKind env value type ∧
      step state = some ({ state with control := .returned value },none) := by
  have sourceShape : source.term = .var (indices index) := by
    rw [← view.termEq,shape]
    simp only [Term.rename]
  obtain ⟨value,stored,kind⟩ := context.variable_kind history typed aligned sourceShape
  have actualStored := (view.values index).trans stored
  refine ⟨value,actualStored,kind,?_⟩
  simp only [step,evaluating,shape,evaluateAction,actualStored,executeLegacy,execute,Option.map_none]

/-- Two indexed transitions return a canonical variable and close the reader.
The original Lend type excludes references in the returned value, while
reader-entry bounds exclude the retiring token from every saved capture. -/
theorem reachable_canonical_lend_variable_nonescape (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (originalTyped : LoanClosingTyped env originalLoans mode original originalMeanings originalType)
    (originalShape : original.term = .lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings (first.subst originalMeanings))
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (shape : actual.term = .var index)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin
        (original.child (.lam false first (.lam false again body))) :: stack) :
    let state := (run fuel (initial term)).state
    let closed := SizedBufferHeap.close state.heap.metadata token
    let continuation := original.child (.lam false first (.lam false again body))
    ∃ value, actual.values[index]? = some (some value) ∧
      ValueKind env value (first.subst originalMeanings) ∧
      let next : State := ⟨⟨closed,state.heap.cell⟩,.evaluate continuation,
        .lendContinuation object origin resultOrigin value :: stack,state.pending⟩
      run 2 state = ⟨next,[.legacy (.heap (.close token))],2⟩ ∧
      ¬ StateReferenceOccurs token next ∧ closed.heap.lease token = none ∧
      (∀ other, other ≠ token → closed.heap.lease other = state.heap.metadata.heap.lease other) ∧
      ReaderInventory closed (readerFrames (stack ++ state.pending.flatMap Prod.snd)) := by
  have allowed := originalTyped.reader_domain_outlived history originalShape
  obtain ⟨value,stored,kind,_⟩ :=
    canonical_variable_result history evaluating view typed context aligned shape
  have resultAbsent := kind.outlived_reference_absent history.wellFormed.admissible allowed token
  obtain ⟨continuationReady,outerReady,pendingReady⟩ := initial_run_finish_capture_bounds term fuel stackShape
  obtain ⟨executed,retired,others,inventory⟩ :=
    reachable_lend_variable_close term fuel evaluating shape stored stackShape
  refine ⟨value,stored,kind,executed,?_,retired,others,inventory⟩
  intro occurs
  rcases occurs with (control | ⟨frame,member,occurs⟩) | pending
  · exact continuationReady.fresh_absent control
  · rcases List.mem_cons.mp member with rfl | member
    · exact resultAbsent occurs
    · exact outerReady.fresh_absent member occurs
  · exact pendingReady.fresh_absent pending

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
