import Jihoo.NativeBindingMachineMutableLoad
import Jihoo.NativeBindingMachineMutableAlignment
import Jihoo.NativeLoanNumericProofExecution

/-! The retained U64 index slot agrees with its canonical source meaning.
Closed arithmetic evidence then supplies the physical bound for an owned read. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity

theorem projectRaw_named_load_inactive
    (checked : projectRaw (fuel+2) env loans ctx
      (.load (.var owner) offset evidence continuation) = some resource)
    (budget : LoanBudget ctx.length loans resource) : Loans.active ctx.length loans owner = false := by
  simp only [projectRaw,Op.arity,fields,fetch,
    List.length_cons,List.length_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,
    bind,Option.bind,Nat.reduceAdd,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  cases selected : lookup ctx owner with
  | none => simp [selected] at checked
  | some binding =>
      cases erased : binding.erased with
      | true => simp [selected,erased] at checked
      | false =>
          cases projectedOffset : projectRaw (fuel+1) env loans ctx offset with
          | none => simp [selected,erased,projectedOffset] at checked
          | some index =>
              cases projectedBody : projectRaw (fuel+1) env loans ctx continuation with
              | none => simp [selected,erased,projectedOffset,projectedBody] at checked
              | some tail =>
                  simp [selected,erased,projectedOffset,projectedBody] at checked
                  rw [← checked] at budget
                  apply Bool.eq_false_iff.mpr
                  intro active
                  have zero := budget.sequence.1.sequence.1 owner active
                  simp [Control.demand] at zero

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds
open Semantics.LoanArithmetic (Order Numeric closedProof? closedProof?_order observed_evidence_order
  normalizedWord? observations? observes_added_and_cancelled_bound)

private theorem variable_load_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .load (.var owner) (.var index) evidence
      (.lam false first (.lam false again body)))
    (storedOwner : code.values[owner]? = some (some (.owner object)))
    (storedIndex : code.values[index]? = some (some (.natural offset)))
    (loaded : state.heap.load object offset = some payload) :
    let origin := (code.child (.var owner)).origin
    let value := Term.integer (decodeInteger payload)
    let next := restoredContinuation code first again body origin value object (.integer (decodeInteger payload))
    run 9 state = ⟨⟨state.heap,.evaluate next,state.stack,state.pending⟩,
      [.load object offset payload,.legacy (.activate false (.lam false again body) value),
        .legacy (.activate false body origin)],9⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,storedOwner,storedIndex,executeLegacy,execute,
    Option.map_none,returnAction,resumeBuffer,loaded,applyValue,enter,restoredContinuation,Option.map_some]
  rfl

theorem load_retained_closing (wf : UnifiedProgram.EnvWellFormed env)
    (closing : LoanTyping.Ghost.Substitution env code.context [] meanings)
    (typed : LoanTyping.HasType env loans code.context false
      (.load owner index evidence (.lam false first (.lam false again body))) localType)
    (converted : LoanTyping.Conversion.Conv env (localType.subst meanings) type)
    (observed : ValueReduction.signed64 number) (origin : Term) (object : Nat) :
    LoanClosingTyped env loans false
      (restoredContinuation code first again body origin (.integer number) object (.integer number))
      (consValues (owner.subst meanings) (consValues (.integer number) meanings)) type := by
  obtain ⟨size,ownerTyped,firstDomain,againDomain,bodyTyped⟩ := LoanTyping.load_retained_body wf typed
  have integer : LoanTyping.HasType env [] [] true (.integer number) .i64 :=
    .integer observed.1 observed.2
  have integerType : LoanTyping.Conversion.Conv env .i64 (first.subst meanings) := by
    simpa only [Term.subst,substArgs] using (firstDomain.substitution meanings wf.closed).symm
  have ownerType : LoanTyping.Conversion.Conv env (.buffer (size.subst meanings))
      (again.subst (consValues (.integer number) meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub,shift_subst_consValues] using
      (againDomain.substitution (consValues (.integer number) meanings) wf.closed).symm
  have ownerMeaning : LoanTyping.HasType env [] [] true (owner.subst meanings) (.buffer (size.subst meanings)) := by
    simpa only [Term.buffer,Term.subst,substArgs,Op.binders,liftSub] using ownerTyped.ghostSubstitution wf closing
  have ownerClosed := ownerMeaning.convert ownerType
  refine ⟨(closing.consValues (integer.convert integerType)).consValues ownerClosed,
    localType.rename (fun x => x + 2),bodyTyped,?_⟩
  change LoanTyping.Conversion.Conv env
    ((localType.rename (fun x => x + 2)).subst
      (consValues (owner.subst meanings) (consValues (.integer number) meanings))) type
  rw [Term.subst_rename]
  exact converted

private theorem reachable_typed_variable_load_with_order (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata source meanings)
    (indexErasure : (lookup actual.context index).map (·.erased) =
      (lookup source.context (indices index)).map (·.erased))
    (shape : actual.term = .load (.var owner) (.var index) evidence
      (.lam false first (.lam false again body)))
    (boundSound : ∀ {offset length}, LoanTyping.HasType env [] [] true (evidence.subst (meanings ∘ indices))
      (.lt (.natural offset) length) → Order env (.lt (.natural offset) length))
    (storedOwner : actual.values[owner]? = some (some (.owner object)))
    (live : (run fuel (initial term)).state.heap.metadata.heap.live object = true)
    (coverage : LoanCoverage source loans (run fuel (initial term)).state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context
      source.term = some resource)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans resource) :
    let state := (run fuel (initial term)).state
    ∃ offset,
      actual.values[index]? = some (some (.natural offset)) ∧
      meanings (indices index) = .natural offset ∧ offset < 2^64 ∧
      offset < state.heap.metadata.length object ∧
      let payload := state.heap.cell object offset
      let value := Term.integer (decodeInteger payload)
      let origin := (actual.child (.var owner)).origin
      let next := restoredContinuation actual first again body origin value object (.integer (decodeInteger payload))
      let nextMeanings := consValues (meanings (indices owner)) (consValues value (meanings ∘ indices))
      let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
        (body.rename (liftRenaming 2 indices)) origin value object (.integer (decodeInteger payload))
      let sourceMeanings := consValues (meanings (indices owner)) (consValues value meanings)
      state.heap.load object offset = some payload ∧
      run 9 state = ⟨⟨state.heap,.evaluate next,state.stack,state.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) value),
          .legacy (.activate false body origin)],9⟩ ∧
      CanonicalView next sourceNext (liftRenaming 2 indices) ∧
      LoanClosingTyped env loans false sourceNext sourceMeanings type ∧
      LoanTyping.HasType env [] [] true (next.term.subst nextMeanings) type := by
  let state := (run fuel (initial term)).state
  have invariant := initial_run_invariant term fuel
  have numbers := initial_run_numbers term fuel
  have aligned := initial_run_code_aligned term fuel SizedBufferHeap.empty evaluating
  have sourceShape : source.term = .load (.var (indices owner)) (.var (indices index))
      (evidence.rename indices) ((Term.lam false first (.lam false again body)).rename indices) := by
    rw [← view.termEq,shape]
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming]
  obtain ⟨closing,localType,sourceTyped,resultType⟩ := typed
  rw [sourceShape] at sourceTyped checked
  obtain ⟨size,ownerTyped,indexTyped,bound⟩ := sourceTyped.load_inputs
  obtain ⟨binding,selected,relevant⟩ := loan_code_variable_permission indexTyped
  have actualRelevant : (lookup actual.context index).map (·.erased) = some false := by
    simpa only [selected,Option.map_some,relevant] using indexErasure
  obtain ⟨runtimeBinding,runtimeSelected,runtimeRelevant⟩ :=
    Option.map_eq_some_iff.mp actualRelevant
  have retained : ∃ value, actual.values[index]? = some (some value) := by
    obtain ⟨slot,stored,flag⟩ := SlotsAligned.ready aligned index runtimeBinding runtimeSelected
    cases slot with
    | none => simp [runtimeRelevant] at flag
    | some value => exact ⟨value,stored⟩
  obtain ⟨value,actualIndexStored⟩ := retained
  have sourceIndexStored := (view.values index).symm.trans actualIndexStored
  obtain ⟨inferred,inferredSelected,converted⟩ := indexTyped.principalView
  have same := Option.some.inj (selected.symm.trans inferredSelected)
  subst inferred
  have indexType : LoanTyping.Conversion.Conv env (binding.ty.subst meanings) .u64 := by
    simpa only [Term.subst,substArgs] using
      converted.substitution meanings history.wellFormed.closed
  have indexKind := (context.kinds (indices index) binding value selected sourceIndexStored).convert indexType
  obtain ⟨offset,rfl⟩ := indexKind.natural_shape history.wellFormed.admissible
  have indexMeaning := context.scalars.1 (indices index) offset sourceIndexStored
  have sourceOwnerStored := (view.values owner).symm.trans storedOwner
  have physicalTyped : OwnerSize env state.heap.metadata object (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      sizes.typed_variable history ownerTyped sourceOwnerStored
  have physical := physicalTyped.buffer_length history
  have closedEvidence : LoanTyping.HasType env [] [] true
      (evidence.subst (meanings ∘ indices)) (.lt (.natural offset) (size.subst meanings)) := by
    simpa only [Term.subst_rename,Term.subst,substArgs,Op.binders,liftSub,indexMeaning,Function.comp_def]
      using bound.ghostSubstitution history.wellFormed closing
  have arithmetic := boundSound closedEvidence
  have within : offset < state.heap.metadata.length object := arithmetic.reflect history.wellFormed.admissible
    (Numeric.natural env offset) ((Numeric.natural env (state.heap.metadata.length object)).convert physical)
  have numeric := numbers.legacy.2.1
  change ControlNumbers state.control at numeric
  rw [evaluating] at numeric
  have width := (ValuesNumbers.valueAt (show CodeNumbers actual from numeric) actualIndexStored).naturalBound
  have inactive := LoanTyping.ResourceQuantity.projectRaw_named_load_inactive checked budget
  have guard := (invariant.2.free_guard_iff invariant.1).mpr (coverage.inactive sourceOwnerStored inactive)
  have read : state.heap.load object offset = some (state.heap.cell object offset) := by
    unfold SizedBufferHeap.IndexedState.load
    exact ite_eq_left ⟨live,guard,within⟩
  let integer := decodeInteger (state.heap.cell object offset)
  let origin := (actual.child (.var owner)).origin
  let next := restoredContinuation actual first again body origin (.integer integer) object (.integer integer)
  let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
    (body.rename (liftRenaming 2 indices)) origin (.integer integer) object (.integer integer)
  let nextMeanings := consValues (meanings (indices owner)) (consValues (.integer integer) (meanings ∘ indices))
  let sourceMeanings := consValues (meanings (indices owner)) (consValues (.integer integer) meanings)
  have sourceCallback : LoanTyping.HasType env loans source.context false
      (.load (.var (indices owner)) (.var (indices index)) (evidence.rename indices)
        (.lam false (first.rename indices)
          (.lam false (again.rename (liftRenaming 1 indices)) (body.rename (liftRenaming 2 indices)))))
      localType := by
    simpa only [Term.lam,Term.rename,renameArgs,Op.binders,liftRenaming] using sourceTyped
  have resumed : LoanClosingTyped env loans false sourceNext sourceMeanings type := by
    simpa only [sourceNext,sourceMeanings,Term.subst] using
      load_retained_closing history.wellFormed closing sourceCallback resultType
        (decode_integer_bound (numbers.cells object offset)) origin object
  have nextView : CanonicalView next sourceNext (liftRenaming 2 indices) :=
    (view.enter false first (.lam false again body) (.integer integer)
      (some (.integer integer))).enter false again body origin (some (.owner object))
  refine ⟨offset,actualIndexStored,indexMeaning,width,within,read,
    variable_load_steps state evaluating shape storedOwner actualIndexStored read,nextView,resumed,?_⟩
  change LoanTyping.HasType env [] [] true (next.term.subst nextMeanings) type
  rw [nextView.closed (sourceMeanings := sourceMeanings) (by intro index; cases index with
    | zero => rfl
    | succ index => cases index <;> rfl)]
  exact resumed.closed history

/-- Actual Load through a captured U64 slot. The closed erased proof may
come from a source branch binder, and its operands may themselves convert
to numerals. The actual slot, width, read bound, and callback result typing
follow from the canonical context and the original Loan64 derivation. -/
theorem reachable_typed_variable_load (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata source meanings)
    (indexErasure : (lookup actual.context index).map (·.erased) =
      (lookup source.context (indices index)).map (·.erased))
    (shape : actual.term = .load (.var owner) (.var index) evidence
      (.lam false first (.lam false again body)))
    (decideEvidence : evidence.subst (meanings ∘ indices) = .decide left right)
    (storedOwner : actual.values[owner]? = some (some (.owner object)))
    (live : (run fuel (initial term)).state.heap.metadata.heap.live object = true)
    (coverage : LoanCoverage source loans (run fuel (initial term)).state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context
      source.term = some resource)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans resource) :
    let state := (run fuel (initial term)).state
    ∃ offset,
      actual.values[index]? = some (some (.natural offset)) ∧
      meanings (indices index) = .natural offset ∧ offset < 2^64 ∧
      offset < state.heap.metadata.length object ∧
      let payload := state.heap.cell object offset
      let value := Term.integer (decodeInteger payload)
      let origin := (actual.child (.var owner)).origin
      let next := restoredContinuation actual first again body origin value object (.integer (decodeInteger payload))
      let nextMeanings := consValues (meanings (indices owner)) (consValues value (meanings ∘ indices))
      let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
        (body.rename (liftRenaming 2 indices)) origin value object (.integer (decodeInteger payload))
      let sourceMeanings := consValues (meanings (indices owner)) (consValues value meanings)
      state.heap.load object offset = some payload ∧
      run 9 state = ⟨⟨state.heap,.evaluate next,state.stack,state.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) value),
          .legacy (.activate false body origin)],9⟩ ∧
      CanonicalView next sourceNext (liftRenaming 2 indices) ∧
      LoanClosingTyped env loans false sourceNext sourceMeanings type ∧
      LoanTyping.HasType env [] [] true (next.term.subst nextMeanings) type := by
  apply reachable_typed_variable_load_with_order term fuel history evaluating view typed context sizes
    indexErasure shape _ storedOwner live coverage checked budget
  intro offset length evidenceTyped
  rw [decideEvidence] at evidenceTyped
  have order := observed_evidence_order (values := Term.var) history.wellFormed evidenceTyped (by
    simp only [Semantics.LoanArithmetic.ObservedEvidence,Semantics.LoanArithmetic.ObservedEvidenceUsing])
  simpa only [Term.subst_id] using order

/-- Bounded normalization of the actual closed erased proof supplies the
physical safety guard. The proof can include arithmetic rules and checked
computations. The executable word width follows from the retained slot. -/
theorem reachable_typed_variable_load_from_proof (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata source meanings)
    (indexErasure : (lookup actual.context index).map (·.erased) =
      (lookup source.context (indices index)).map (·.erased))
    (shape : actual.term = .load (.var owner) (.var index) evidence
      (.lam false first (.lam false again body)))
    (observed : closedProof? env observationBudget reductionFuel operandFuel
      (evidence.subst (meanings ∘ indices)) = some residual)
    (storedOwner : actual.values[owner]? = some (some (.owner object)))
    (live : (run fuel (initial term)).state.heap.metadata.heap.live object = true)
    (coverage : LoanCoverage source loans (run fuel (initial term)).state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context
      source.term = some resource)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans resource) :
    let state := (run fuel (initial term)).state
    ∃ offset,
      actual.values[index]? = some (some (.natural offset)) ∧
      meanings (indices index) = .natural offset ∧ offset < 2^64 ∧
      offset < state.heap.metadata.length object ∧
      let payload := state.heap.cell object offset
      let value := Term.integer (decodeInteger payload)
      let origin := (actual.child (.var owner)).origin
      let next := restoredContinuation actual first again body origin value object (.integer (decodeInteger payload))
      let nextMeanings := consValues (meanings (indices owner)) (consValues value (meanings ∘ indices))
      let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
        (body.rename (liftRenaming 2 indices)) origin value object (.integer (decodeInteger payload))
      let sourceMeanings := consValues (meanings (indices owner)) (consValues value meanings)
      state.heap.load object offset = some payload ∧
      run 9 state = ⟨⟨state.heap,.evaluate next,state.stack,state.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) value),
          .legacy (.activate false body origin)],9⟩ ∧
      CanonicalView next sourceNext (liftRenaming 2 indices) ∧
      LoanClosingTyped env loans false sourceNext sourceMeanings type ∧
      LoanTyping.HasType env [] [] true (next.term.subst nextMeanings) type := by
  apply reachable_typed_variable_load_with_order term fuel history evaluating view typed context sizes
    indexErasure shape _ storedOwner live coverage checked budget
  intro offset length evidenceTyped
  exact closedProof?_order history evidenceTyped observed

namespace Examples

set_option maxRecDepth 4096

private def loadUsing (evidence : Term) : Term :=
  .app (.lam false .u64
    (.ifLt (.var 0) (.natural 2)
      (.app (.lam false (.buffer (.natural 2))
        (.load (.var 0) (.var 2) evidence
          (.lam false .i64 (.lam false (.buffer (.natural 2)) (.free (.var 0) (.var 1))))))
        (.alloc (.natural 2) (.integer 17)))
      (.integer 0))) (.natural 1)

private def dynamic_load : Term := loadUsing (.var 1)

theorem dynamic_load_admitted : LoanTyping.MixedProgram.checkDeclaration 32 64 .empty
    ⟨.i64,dynamic_load⟩ = some ⟨.i64,dynamic_load⟩ := by cbv

theorem dynamic_load_reads : (run 60 (initial dynamic_load)).events.filterMap
    (fun event => match event with
      | .load object index value => some (object,index,value)
      | _ => none) = [(0,1,encodeInteger 17)] := by rfl

theorem dynamic_load_returns : observe (run 60 (initial dynamic_load)) = .integer 17 := by rfl

private def computedBound : Term :=
  .ltCancel (.var 2) (.natural 2) (.natural 1)
    (.ltAdd (.var 2) (.natural 2) (.natural 1) (.var 1))

private def branchValues : Nat → Term
  | 1 => .decide (.natural 1) (.natural 2)
  | 2 => .natural 1
  | index => .var index

/-- The accepted Load keeps the original index and really reads the same
cell when its bound is arithmetic evidence using the erased branch slot. -/
theorem computed_load_evidence_reads :
    let term := loadUsing computedBound
    LoanTyping.MixedProgram.checkDeclaration 64 128 .empty ⟨.i64,term⟩ = some ⟨.i64,term⟩ ∧
    (closedProof? .empty 4096 64 64 (computedBound.subst branchValues)).isSome = true ∧
    (run 60 (initial term)).events.filterMap
      (fun event => match event with
        | .load object index value => some (object,index,value)
        | _ => none) = [(0,1,encodeInteger 17)] ∧
    observe (run 60 (initial term)) = .integer 17 := by
  refine ⟨by cbv,?_,rfl,rfl⟩
  let one := Term.natural 1
  let two := Term.natural 2
  let branch := Term.decide one two
  let closed := Term.ltCancel one two one (.ltAdd one two one branch)
  have substitution : computedBound.subst branchValues = closed := by cbv
  have normal : LoanTyping.ProofNormalization.normalize? .empty 4096 64 closed = some closed := by cbv
  have numberOne : normalizedWord? .empty 4096 64 one = some 1 := by cbv
  have numberTwo : normalizedWord? .empty 4096 64 two = some 2 := by cbv
  have proof : (observations? .empty 4096 64 Term.var branch).isSome = true := by cbv
  have observed : (observations? .empty 4096 64 Term.var closed).isSome = true :=
    observes_added_and_cancelled_bound numberOne numberTwo numberOne proof
  rw [substitution]
  unfold closedProof?
  rw [normal]
  change (if (observations? .empty 4096 64 Term.var closed).isSome then some closed else none).isSome = true
  exact congrArg Option.isSome (ite_eq_left observed)


end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
