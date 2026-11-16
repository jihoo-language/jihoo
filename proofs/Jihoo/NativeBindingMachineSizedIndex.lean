import Jihoo.NativeBindingMachineOwnerSizes

/-! Source evidence connects a compared captured length to the named owner's
actual immutable allocation length. Reachability and the reader inventory
supply the live lease. No allocation snapshot or safe-read oracle is supplied. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

/-- A Borrow cannot masquerade as an Array reference. Full Index inversion
retains the actual owner's Buffer typing and the original bound evidence. -/
theorem HasType.named_index_owner (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.index (.borrow (.var owner)) offset boundEvidence) type) :
    ∃ size, HasType env loans ctx true (.var owner) (.buffer size) ∧
      HasType env loans ctx mode offset .u64 ∧ HasType env loans ctx true boundEvidence (.lt offset size) := by
  obtain ⟨size,reference,indexTyped,evidence⟩ := typed.index_inputs
  rcases reference with reference | reference
  · obtain ⟨ownerType,ownerTyped,converted⟩ := reference.principalView
    exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) converted wf.admissible)
  · obtain ⟨ownerType,ownerTyped,converted⟩ := reference.principalView
    exact ⟨size,ownerTyped.convert (converted.ref_injective wf.admissible),indexTyped,evidence⟩

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

private theorem sized_read_ten_steps (heap : SizedBufferHeap.State) (code : Code) (stack : List Frame)
    (shape : code.term = .ifLt (.var index) (.var length) (dynamicRead owner index) no)
    (storedIndex : code.values[index]? = some (some (.natural offset)))
    (storedLength : code.values[length]? = some (some (.natural count)))
    (storedOwner : code.values[owner]? = some (some (.owner object)))
    (found : activeLease (code.context.length-owner) object stack = some token)
    (leased : heap.heap.lease token = some object) (size : heap.length object = count)
    (compared : offset < count) :
    run 10 ⟨heap,.evaluate code,stack⟩ =
      ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),stack⟩,
        [.heap (.read token offset (heap.heap.payload object))],10⟩ := by
  simp only [run,step,action,evaluateAction,shape,Code.child,storedIndex,storedLength,storedOwner,
    returnAction,execute,branchCode,dynamicRead,List.getElem?_cons_succ,List.length_cons,
    Nat.add_sub_add_right,borrowLease,Option.orElse_some,activeLease,readerFor,Frame.reader?,bind,Option.bind,Option.orElse_none,
    found,leased,size,compared,decide_true,Bool.false_eq_true,↓reduceIte,Option.map_some]
  rfl

/-- Full source bound evidence identifies the real Buffer length. Every
numeric slot, owner identity, lease, bound and result typing is constructed
from the input source/value/size/loan contexts and actual reachability.
Neither an allocation snapshot nor selected runtime values are inputs. -/
theorem reachable_sized_dynamic_index (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (shape : code.term = .ifLt (.var index) (.var length) (dynamicRead owner index) no)
    (entered : Loans.Entered code.context.length loans)
    (slots : LoanSlots code loans (run fuel (initial term)).state.stack) :
    ∃ offset count, meanings index = .natural offset ∧ meanings length = .natural count ∧
      let heap := (run fuel (initial term)).state.heap
      let stack := (run fuel (initial term)).state.stack
      if offset < count then
        ∃ token object,
          code.values[owner]? = some (some (.owner object)) ∧ heap.length object = count ∧
          heap.heap.lease token = some object ∧ heap.heap.live object = true ∧
          LoanTyping.HasType env [] [] true (.integer (decodeInteger (heap.heap.payload object))) type ∧
          run 10 (run fuel (initial term)).state =
            ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),stack⟩,
              [.heap (.read token offset (heap.heap.payload object))],10⟩
      else
        LoanClosingTyped env loans false (code.child no) meanings type ∧
        ValueContext env (code.child no) meanings ∧
        run 5 (run fuel (initial term)).state = ⟨⟨heap,.evaluate (code.child no),stack⟩,[],5⟩ := by
  obtain ⟨offset,count,indexStored,lengthStored,indexMeaning,lengthMeaning,indexBound,lengthBound,selected⟩ :=
    reachable_captured_less_branch term fuel history evaluating typed context shape
  refine ⟨offset,count,indexMeaning,lengthMeaning,?_⟩
  by_cases compared : offset < count
  · simp only [compared,↓reduceIte] at selected ⊢
    obtain ⟨branchTyped,branchContext,branchExecuted⟩ := selected
    let branch := branchCode false (code.child (dynamicRead owner index)) (.var index) (.var length)
    let branchMeanings := consValues (.decide (.natural offset) (.natural count)) meanings
    have branchSizes : OwnerSizes env (run fuel (initial term)).state.heap branch branchMeanings :=
      sizes.branch false _ _ _ _
    obtain ⟨closing,localType,source,converted⟩ := typed
    have permission := typed_dynamic_read_permission source shape entered
    obtain ⟨object,ownerStored,present⟩ := slots owner permission
    obtain ⟨branchClosing,branchLocal,branchSource,branchConverted⟩ := branchTyped
    obtain ⟨size,ownerTyped,indexTyped,evidence⟩ := branchSource.named_index_owner history.wellFormed
    have ownerStoredShift : branch.values[owner+1]? = some (some (.owner object)) := by
      simpa only [branch,branchCode,Code.child,List.getElem?_cons_succ] using ownerStored
    have ownerSize := branchSizes.typed_variable history ownerTyped ownerStoredShift
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
    obtain ⟨token,found⟩ := activeLease_complete present
    obtain ⟨frame,member,descriptor⟩ := activeLease_sound found
    have leased := initial_run_readers_live term fuel frame member token object
      (some (code.context.length-owner)) descriptor
    have live := (initial_run_heap_valid term fuel).leased token object leased |>.2
    have closedIndex := (show LoanClosingTyped env loans false branch branchMeanings type from
      ⟨branchClosing,branchLocal,branchSource,branchConverted⟩).closed history
    simp only [branch,branchCode,Code.child,dynamicRead,Term.subst,substArgs,Op.binders,liftSub] at closedIndex
    have original : LoanTyping.Conversion.Conv env .i64 type := closedIndex.principalView
    have valueTyped := (initial_run_decoded_integer_typed (env := env) term fuel object).convert original
    have stateShape : (run fuel (initial term)).state =
        ⟨(run fuel (initial term)).state.heap,.evaluate code,(run fuel (initial term)).state.stack⟩ := by
      cases state : (run fuel (initial term)).state
      simp_all
    refine ⟨token,object,ownerStored,actualLength,leased,live,valueTyped,?_⟩
    rw [stateShape]
    exact sized_read_ten_steps _ code _ shape indexStored lengthStored ownerStored found leased actualLength compared
  · simpa only [compared,↓reduceIte] using selected

end Jihoo.NativeKernel.Environment.BindingMachine
