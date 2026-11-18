import Jihoo.NativeBindingMachineCanonicalIndex

/-! Captured comparisons and dependent Buffer reads through canonical owner
aliases. Source slot alignment, value meanings, immutable owner sizes and
physical reader association remain explicit local entry invariants. Numeric
values, bounds, selected leases, successful execution and result typing are
derived, including when the alias map identifies several runtime slots. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

private theorem canonical_natural_slot
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings .u64)
    (context : ValueContext env code meanings) (aligned : CodeAligned code)
    (shape : code.term = .var index) :
    ∃ number, code.values[index]? = some (some (.natural number)) ∧
      meanings index = .natural number ∧ number < 2^64 := by
  obtain ⟨value,stored,kind⟩ := context.variable_kind history typed aligned shape
  obtain ⟨number,rfl⟩ := kind.natural_shape history.wellFormed.admissible
  have meaning := context.scalars.1 index number stored
  have actual : LoanTyping.HasType env [] [] true (.natural number) .u64 := by
    simpa only [shape,Term.subst,meaning] using typed.closed history
  exact ⟨number,stored,meaning,actual.natural_bound⟩

set_option linter.unusedSimpArgs false in
private theorem canonical_dynamic_read_ten_steps (heap : SizedBufferHeap.State)
    (code : Code) (stack : List Frame)
    (shape : code.term = .ifLt (.var index) (.var length) (dynamicRead owner index) no)
    (storedIndex : code.values[index]? = some (some (.natural offset)))
    (storedLength : code.values[length]? = some (some (.natural count)))
    (storedOwner : code.values[owner]? = some (some (.owner object)))
    (found : borrowLease (code.context.length-owner) object stack = some token)
    (leased : heap.heap.lease token = some object) (size : heap.length object = count)
    (compared : offset < count) :
    run 10 ⟨heap,.evaluate code,stack⟩ =
      ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),stack⟩,
        [.heap (.read token offset (heap.heap.payload object))],10⟩ := by
  have selected : ∀ saved : Code, borrowLease (code.context.length-owner) object
      (.indexReference saved :: stack) = some token := by
    intro saved
    simpa only [borrowLease,activeLease,readerFor,Frame.reader?,activeOwnerLease,
      readerForOwner,bind,Option.bind,Option.orElse_none] using found
  simp only [run,step,action,evaluateAction,shape,Code.child,storedIndex,storedLength,storedOwner,
    returnAction,execute,branchCode,dynamicRead,List.getElem?_cons_succ,List.length_cons,
    Nat.add_sub_add_right,selected,leased,size,compared,decide_true,Bool.false_eq_true,
    ↓reduceIte,Option.map_some]
  rfl

set_option linter.unusedSimpArgs false in
private theorem canonical_dynamic_else_five_steps (heap : SizedBufferHeap.State)
    (code : Code) (stack : List Frame)
    (shape : code.term = .ifLt (.var index) (.var length) yes no)
    (storedIndex : code.values[index]? = some (some (.natural offset)))
    (storedLength : code.values[length]? = some (some (.natural count)))
    (compared : ¬ offset < count) :
    run 5 ⟨heap,.evaluate code,stack⟩ = ⟨⟨heap,.evaluate (code.child no),stack⟩,[],5⟩ := by
  simp only [run,step,action,evaluateAction,shape,Code.child,storedIndex,storedLength,
    returnAction,execute,compared,decide_false,Bool.false_eq_true,↓reduceIte,Option.map_some]
  rfl

/-- Canonical source typing supplies captured comparison values and the
erased branch evidence. In bounds it derives a live physical owner, exact
length, runtime-typed integer and ten actual transitions with one read. The
else arm enters its original body in five transitions and retains canonical
typing, value/size/loan contexts and the alias view. No numerical guard,
selected slot value, actual loan-slot invariant or successful run is an input. -/
theorem reachable_canonical_dynamic_index (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap source meanings)
    (entered : Loans.Entered source.context.length loans)
    (slots : OwnerLoanSlots source loans (run fuel (initial term)).state.stack)
    (shape : actual.term = .ifLt (.var index) (.var length) (dynamicRead owner index) no) :
    ∃ offset count,
      actual.values[index]? = some (some (.natural offset)) ∧
      actual.values[length]? = some (some (.natural count)) ∧
      meanings (indices index) = .natural offset ∧ meanings (indices length) = .natural count ∧
      offset < 2^64 ∧ count < 2^64 ∧
      let heap := (run fuel (initial term)).state.heap
      let stack := (run fuel (initial term)).state.stack
      if offset < count then
        ∃ token object,
          actual.values[owner]? = some (some (.owner object)) ∧ heap.length object = count ∧
          heap.heap.lease token = some object ∧ heap.heap.live object = true ∧
          LoanTyping.HasType env [] [] false (.integer (decodeInteger (heap.heap.payload object))) type ∧
          run 10 (run fuel (initial term)).state =
            ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),stack⟩,
              [.heap (.read token offset (heap.heap.payload object))],10⟩
      else
        LoanClosingTyped env loans false (source.child (no.rename indices)) meanings type ∧
        ValueContext env (source.child (no.rename indices)) meanings ∧
        OwnerSizes env heap (source.child (no.rename indices)) meanings ∧
        OwnerLoanSlots (source.child (no.rename indices)) loans stack ∧
        CodeAligned (source.child (no.rename indices)) ∧
        CanonicalView (actual.child no) (source.child (no.rename indices)) indices ∧
        run 5 (run fuel (initial term)).state = ⟨⟨heap,.evaluate (actual.child no),stack⟩,[],5⟩ := by
  have sourceShape : source.term = .ifLt (.var (indices index)) (.var (indices length))
      (dynamicRead (indices owner) (indices index)) (no.rename indices) := by
    rw [← view.termEq,shape]
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,dynamicRead]
  obtain ⟨closing,localType,sourceDerivation,converted⟩ := typed
  have sourceTyped := sourceDerivation
  rw [sourceShape] at sourceTyped
  obtain ⟨result,leftTyped,rightTyped,yesTyped,noTyped⟩ := sourceTyped.ifLt_inputs
  have rebuilt : LoanTyping.HasType env loans source.context false
      (.ifLt (.var (indices index)) (.var (indices length))
        (dynamicRead (indices owner) (indices index)) (no.rename indices)) result :=
    .ifLt leftTyped rightTyped yesTyped noTyped
  have resultConverted := ((rebuilt.unique history.wellFormed sourceTyped).substitution meanings
    history.wellFormed.closed).trans converted
  have leftClosing : LoanClosingTyped env loans false (source.child (.var (indices index))) meanings .u64 :=
    ⟨closing,.u64,leftTyped,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  have rightClosing : LoanClosingTyped env loans false (source.child (.var (indices length))) meanings .u64 :=
    ⟨closing,.u64,rightTyped,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  obtain ⟨offset,indexStored,indexMeaning,indexBound⟩ :=
    canonical_natural_slot history leftClosing (context.child _) (aligned.child _) rfl
  obtain ⟨count,lengthStored,lengthMeaning,lengthBound⟩ :=
    canonical_natural_slot history rightClosing (context.child _) (aligned.child _) rfl
  have actualIndexStored := (view.values index).trans indexStored
  have actualLengthStored := (view.values length).trans lengthStored
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.evaluate actual,(run fuel (initial term)).state.stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  refine ⟨offset,count,actualIndexStored,actualLengthStored,indexMeaning,lengthMeaning,indexBound,lengthBound,?_⟩
  by_cases compared : offset < count
  · simp only [compared,↓reduceIte]
    let branch := branchCode false (source.child (dynamicRead (indices owner) (indices index)))
      (.var (indices index)) (.var (indices length))
    let branchMeanings := consValues (.decide (.natural offset) (.natural count)) meanings
    have proofTyped : LoanTyping.HasType env [] [] true (.decide (.natural offset) (.natural count))
        ((Term.lt (.var (indices index)) (.var (indices length))).subst meanings) := by
      simpa only [Term.subst,substArgs,Op.binders,liftSub,indexMeaning,lengthMeaning] using
        (show LoanTyping.HasType env [] [] true (.decide (.natural offset) (.natural count))
          (.lt (.natural offset) (.natural count)) from .decide indexBound lengthBound compared)
    have branchClosing : LoanTyping.Ghost.Substitution env branch.context [] branchMeanings :=
      closing.consValues proofTyped
    have branchSource : LoanTyping.HasType env loans branch.context false branch.term
        (result.rename Nat.succ) := yesTyped
    have branchSizes : OwnerSizes env (run fuel (initial term)).state.heap branch branchMeanings :=
      sizes.branch false _ _ _ _
    have permission := typed_dynamic_read_permission (code := source) sourceDerivation sourceShape entered
    obtain ⟨object,name,ownerStored,present⟩ := slots (indices owner) permission
    have actualOwnerStored := (view.values owner).trans ownerStored
    obtain ⟨size,ownerTyped,indexTyped,evidence⟩ := branchSource.named_index_owner history.wellFormed
    have shiftedOwner : branch.values[indices owner+1]? = some (some (.owner object)) := by
      simpa only [branch,branchCode,Code.child,List.getElem?_cons_succ] using ownerStored
    have ownerSize := branchSizes.typed_variable history ownerTyped shiftedOwner
    have ownerBufferSize : OwnerSize env (run fuel (initial term)).state.heap object
        (.buffer (size.subst branchMeanings)) := by
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using ownerSize
    have heapSize := ownerBufferSize.buffer_length history
    have evidenceClosed := evidence.ghostSubstitution history.wellFormed branchClosing
    have closedEvidence : LoanTyping.HasType env [] [] true (.decide (.natural offset) (.natural count))
        (.lt (.natural offset) (size.subst branchMeanings)) := by
      simpa only [branchMeanings,Term.subst,substArgs,Op.binders,liftSub,consValues,indexMeaning] using evidenceClosed
    have checkedLength := (closedEvidence.principalView.lt_injective history.wellFormed.admissible).2
    have actualLength : (run fuel (initial term)).state.heap.length object = count :=
      (heapSize.trans checkedLength.symm).natural_injective history.wellFormed.admissible
    obtain ⟨token,found⟩ := borrowLease_complete present (actual.context.length-owner)
    obtain ⟨frame,member,readerName,descriptor⟩ := borrowLease_sound found
    have leased := initial_run_readers_live term fuel frame member token object (some readerName) descriptor
    have live := ((initial_run_heap_valid term fuel).leased token object leased).2
    have principal := sourceTyped.ifLt_index_result history.wellFormed
    have original : LoanTyping.Conversion.Conv env .i64 type := by
      simpa only [Term.subst,substArgs] using
        (principal.substitution meanings history.wellFormed.closed).trans converted
    have bounded := decode_integer_bound ((initial_run_heap_numbers term fuel).payload object)
    have valueTyped : LoanTyping.HasType env [] [] false
        (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object))) type :=
      (LoanTyping.HasType.integer bounded.1 bounded.2).convert original
    refine ⟨token,object,actualOwnerStored,actualLength,leased,live,valueTyped,?_⟩
    rw [stateShape]
    exact canonical_dynamic_read_ten_steps _ actual _ shape actualIndexStored actualLengthStored
      actualOwnerStored found leased actualLength compared
  · simp only [compared,↓reduceIte]
    refine ⟨⟨closing,result,noTyped,resultConverted⟩,context.child _,sizes.child _,slots.child _,
      aligned.child _,view.child no,?_⟩
    rw [stateShape]
    exact canonical_dynamic_else_five_steps _ actual _ shape actualIndexStored actualLengthStored compared

end Jihoo.NativeKernel.Environment.BindingMachine
