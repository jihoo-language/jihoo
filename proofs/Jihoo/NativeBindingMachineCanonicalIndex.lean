import Jihoo.NativeBindingMachineCanonicalBorrow
import Jihoo.NativeBindingMachineReferenceIndex

/-! Canonical source bounds, physical owner sizes and enclosing reader
authority construct an actual Index execution through a retained owner alias.
The source/runtime map may be noninjective and need not preserve lexical
reader keys. This is a local source/control theorem, not a fundamental theorem
for every control point of an admitted program. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

private theorem canonical_named_index_five_steps (heap : SizedBufferHeap.State)
    (code : Code) (stack : List Frame)
    (shape : code.term = .index (.borrow (.var owner)) (.natural offset) evidence)
    (stored : code.values[owner]? = some (some (.owner object)))
    (found : borrowLease (code.context.length-owner) object stack = some token)
    (leased : heap.heap.lease token = some object)
    (literalBound : offset < 2^64) (readBound : offset < heap.length object) :
    run 5 ⟨heap,.evaluate code,stack⟩ =
      ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),stack⟩,
        [.heap (.read token offset (heap.heap.payload object))],5⟩ := by
  have selected : borrowLease (code.context.length-owner) object
      (.indexReference (code.child (.natural offset)) :: stack) = some token := by
    simpa only [borrowLease,activeLease,readerFor,Frame.reader?,activeOwnerLease,
      readerForOwner,bind,Option.bind,Option.orElse_none] using found
  simp only [Code.child] at selected
  simp only [run,step,action,evaluateAction,shape,Code.child,stored,returnAction,execute,
    literalBound,readBound,leased,ite_true,Option.map_some,selected]
  rfl

/-- Complete source Index typing derives Decide bounds and identifies the
actual allocation length through the canonical owner slot. Canonical loan
authority then selects an actual live lease and constructs the five-step read
and its integer at the original requested type. No numerical guard, actual
loan-slot invariant, allocation snapshot or output oracle is supplied. -/
theorem reachable_canonical_index (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap source meanings)
    (slots : OwnerLoanSlots source loans (run fuel (initial term)).state.stack)
    (shape : actual.term = .index (.borrow (.var owner)) (.natural offset)
      (.decide (.natural offset) (.natural count))) :
    ∃ token object,
      actual.values[owner]? = some (some (.owner object)) ∧
      (run fuel (initial term)).state.heap.length object = count ∧
      (run fuel (initial term)).state.heap.heap.lease token = some object ∧
      (run fuel (initial term)).state.heap.heap.live object = true ∧
      offset < 2^64 ∧ count < 2^64 ∧ offset < count ∧
      LoanTyping.HasType env [] [] false
        (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object))) type ∧
      run 5 (run fuel (initial term)).state =
        ⟨⟨(run fuel (initial term)).state.heap,
          .returned (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object))),
          (run fuel (initial term)).state.stack⟩,
          [.heap (.read token offset ((run fuel (initial term)).state.heap.heap.payload object))],5⟩ := by
  have sourceShape : source.term = .index (.borrow (.var (indices owner))) (.natural offset)
      (.decide (.natural offset) (.natural count)) := by
    rw [← view.termEq,shape]
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming]
  obtain ⟨closing,localType,sourceTyped,converted⟩ := typed
  rw [sourceShape] at sourceTyped
  have permission : Loans.active source.context.length loans (indices owner) = true := by
    obtain ⟨size,reference,offsetTyped,evidence⟩ := sourceTyped.index_inputs
    rcases reference with reference | reference
    all_goals
      obtain ⟨named,namedShape,permission⟩ := reference.code_borrow_named
      have same : indices owner = named := Term.var.inj namedShape
      subst named
      exact permission
  obtain ⟨object,name,sourceStored,present⟩ := slots (indices owner) permission
  have actualStored := (view.values owner).trans sourceStored
  obtain ⟨size,ownerTyped,offsetTyped,evidence⟩ :=
    sourceTyped.named_index_owner history.wellFormed
  obtain ⟨offsetBound,countBound,ordered⟩ := evidence.literal_decide_limits history.wellFormed
  have indexedSize := sizes.typed_variable history ownerTyped sourceStored
  have bufferSize : OwnerSize env (run fuel (initial term)).state.heap object
      (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using indexedSize
  have physical := bufferSize.buffer_length history
  have closedEvidence := evidence.ghostSubstitution history.wellFormed closing
  have evidenceTyped : LoanTyping.HasType env [] [] true
      (.decide (.natural offset) (.natural count)) (.lt (.natural offset) (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using closedEvidence
  have checked := (evidenceTyped.principalView.lt_injective history.wellFormed.admissible).2
  have length : (run fuel (initial term)).state.heap.length object = count :=
    (physical.trans checked.symm).natural_injective history.wellFormed.admissible
  obtain ⟨token,found⟩ := borrowLease_complete present (actual.context.length-owner)
  obtain ⟨frame,member,readerName,descriptor⟩ := borrowLease_sound found
  have leased := initial_run_readers_live term fuel frame member token object (some readerName) descriptor
  have live := ((initial_run_heap_valid term fuel).leased token object leased).2
  have principal : LoanTyping.Conversion.Conv env .i64 localType := sourceTyped.principalView
  have original : LoanTyping.Conversion.Conv env .i64 type := by
    simpa only [Term.subst,substArgs] using
      (principal.substitution meanings history.wellFormed.closed).trans converted
  have bounded := decode_integer_bound ((initial_run_heap_numbers term fuel).payload object)
  have valueTyped : LoanTyping.HasType env [] [] false
      (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object))) type :=
    (LoanTyping.HasType.integer bounded.1 bounded.2).convert original
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.evaluate actual,(run fuel (initial term)).state.stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  refine ⟨token,object,actualStored,length,leased,live,offsetBound,countBound,ordered,valueTyped,?_⟩
  rw [stateShape]
  exact canonical_named_index_five_steps _ actual _ shape actualStored found leased
    offsetBound (by omega)

end Jihoo.NativeKernel.Environment.BindingMachine
