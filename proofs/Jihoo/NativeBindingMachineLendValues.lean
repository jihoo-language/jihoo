import Jihoo.NativeBindingMachineIndexValues
import Jihoo.NativeBindingMachineLendOrigins

/-! Actual scalar reader values at the type reconstructed from the input Lend
rule, including source-specialized callbacks. No independently typed generic
callback or returned-value certificate is supplied. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

theorem actual_scalar_finish
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env [] [] true
      (.lend owner (.lam false domain (.index reference offset evidence))
        (.lam false first (.lam false again body))) type)
    (bounded : ValueReduction.signed64 value) :
    HasType env [] [] true (Lending.finish owner body (.integer value)) type := by
  obtain ⟨principal,origin,converted⟩ := typed.lendView
  have actual : HasType env [] [] true (.integer value) .i64 := .integer bounded.1 bounded.2
  cases origin with
  | generic ownerTyped owned outlived readerTyped continuationTyped allowed =>
      have readTyped := reader_from_generic_checks wf ownerTyped owned readerTyped
      simp only [Lending.read,Term.subst,substArgs,Op.binders,liftSub] at readTyped
      have readConverted : Conversion.Conv env .i64 _ := readTyped.principalView
      exact (continuation_from_generic_checks wf ownerTyped (actual.convert readConverted) continuationTyped).convert converted
  | dependentGhost ownerTyped owned domainTyped domainConverted readerTyped outlived firstConverted againConverted continuationTyped resultConverted removed =>
      simp only [Lending.read,Term.subst,substArgs,Op.binders,liftSub] at readerTyped
      have readConverted : Conversion.Conv env .i64 _ := readerTyped.principalView
      have finished := finish_from_specialized_checks wf continuationTyped
        (actual.convert (readConverted.trans firstConverted.symm))
      exact (finished.convert (result_outside wf resultConverted removed)).convert converted

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

theorem lend_index_reader_value (term : Term) (fuel object token : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend owner (.lam false domain (.index reference offset evidence))
      (.lam false first (.lam false again body))) :
    ∃ readerType : Term, LoanTyping.Outlived env readerType ∧
      LoanTyping.HasType env [] [] true
        (enter false domain (.index reference offset evidence) code.context code.origins code.values
          (.borrow (owner.subst code.origins)) (some (.reference token))).origin
        (readerType.subst code.origins) ∧
      LoanTyping.HasType env [] [] true
        (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object)))
        (readerType.subst code.origins) := by
  obtain ⟨readerType,originTyped,outlived⟩ := typed_explicit_reader_origin history typed shape token
  have principal : LoanTyping.Conversion.Conv env .i64 (readerType.subst code.origins) := by
    have source := originTyped
    simp only [Code.origin,enter,Term.subst,substArgs,Op.binders,liftSub] at source
    exact source.principalView
  exact ⟨readerType,outlived,originTyped,
    (initial_run_decoded_integer_typed term fuel object).convert principal⟩

/-- This actual reader-return boundary retains its source origin and type.
Heap numeric/lease facts follow from the real prefix. Bounds failure is left
explicit; the general proof/heap fundamental lemma must exclude it beyond
the already constructed literal and comparison-guarded reads. -/
theorem reachable_lend_index_reader (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend owner (.lam false domain (.index reference offset evidence))
      (.lam false first (.lam false again body)))
    (controlShape : (run fuel (initial term)).state.control = .returned (.natural index))
    (stackShape : (run fuel (initial term)).state.stack = .indexOffset readToken ::
      .lendFinish token object name (owner.subst code.origins)
        (enter false domain (.index reference offset evidence) code.context code.origins code.values
          (.borrow (owner.subst code.origins)) (some (.reference token))).origin continuation :: rest)
    (member : frame ∈ .lendFinish token object name (owner.subst code.origins)
      (enter false domain (.index reference offset evidence) code.context code.origins code.values
        (.borrow (owner.subst code.origins)) (some (.reference token))).origin continuation :: rest)
    (descriptor : frame.reader? = some (readToken,readObject,readName)) :
    ∃ readerType : Term, LoanTyping.Outlived env readerType ∧
      LoanTyping.HasType env [] [] true
        (enter false domain (.index reference offset evidence) code.context code.origins code.values
          (.borrow (owner.subst code.origins)) (some (.reference token))).origin
        (readerType.subst code.origins) ∧
      if index < (run fuel (initial term)).state.heap.length readObject then
        ∃ value : Int, LoanTyping.HasType env [] [] true (.integer value) (readerType.subst code.origins) ∧
          step (run fuel (initial term)).state = some
            (⟨(run fuel (initial term)).state.heap,.returned (.integer value),
              (run fuel (initial term)).state.stack.tail⟩,
              some (.heap (.read readToken index ((run fuel (initial term)).state.heap.heap.payload readObject))))
      else step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.fault .indexBounds,
          (run fuel (initial term)).state.stack.tail⟩,none) := by
  obtain ⟨readerType,outlived,originTyped,valueTyped⟩ := lend_index_reader_value term fuel readObject token history typed shape
  have readers := initial_run_readers_live term fuel
  have frameMember : frame ∈ (run fuel (initial term)).state.stack := by
    rw [stackShape]
    exact List.mem_cons_of_mem _ member
  have leased := readers frame frameMember readToken readObject readName descriptor
  refine ⟨readerType,outlived,originTyped,?_⟩
  by_cases bound : index < (run fuel (initial term)).state.heap.length readObject
  · simp only [bound,↓reduceIte]
    refine ⟨_,valueTyped,?_⟩
    simp only [step,action,controlShape,stackShape,returnAction,Option.map_some,execute,leased,bound,ite_true,List.tail_cons]
  · simp only [bound,↓reduceIte]
    simp only [step,action,controlShape,stackShape,returnAction,Option.map_some,execute,leased,bound,ite_false,List.tail_cons]

/-- Close the original continuation body with the actual scalar read value,
not an assumed returned-value type or a raw macro intermediate. The runtime
still retains the original body and its real owner/result value slots. This
proves a valid scalar closing; general runtime control typing remains open. -/
theorem actual_lend_scalar_continuation (term : Term) (fuel object : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend owner (.lam false domain (.index reference offset evidence))
      (.lam false first (.lam false again body))) :
    LoanTyping.HasType env [] [] true
      (Lending.finish (owner.subst code.origins) (body.subst (liftSub 2 code.origins))
        (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object)))) type := by
  have source := typed.closed history
  simp only [Code.origin,shape,Term.subst,substArgs,Op.binders,liftSub] at source
  exact LoanTyping.actual_scalar_finish history.wellFormed source
    (decode_integer_bound ((initial_run_heap_numbers term fuel).payload object))

set_option linter.unusedSimpArgs false in
/-- The original two-binder body is closed by the actual scalar value and
owner provenance. This is ghost binding algebra, not CODE beta execution. -/
theorem continuation_actual_substitution (body owner value : Term) (origins : Nat → Term) :
    body.subst (consValues owner (consValues value origins)) =
      Lending.finish owner (body.subst (liftSub 2 origins)) value := by
  simp only [Lending.finish,Term.subst_comp]
  congr 1
  funext index
  cases index with
  | zero => simp [consValues,liftSub,liftSubOne,single,Term.subst,Term.rename,Term.subst_rename,Term.subst_id,Term.shift_subst_single]
  | succ index =>
      cases index <;> simp [consValues,liftSub,liftSubOne,single,Term.subst,Term.rename,Term.subst_rename,Term.subst_id,Term.shift_subst_single]

theorem actual_lend_scalar_bindings (term : Term) (fuel object : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend owner (.lam false domain (.index reference offset evidence))
      (.lam false first (.lam false again body))) :
    LoanTyping.HasType env [] [] true
      (body.subst (consValues (owner.subst code.origins)
        (consValues (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object))) code.origins))) type := by
  rw [continuation_actual_substitution]
  exact actual_lend_scalar_continuation term fuel object history typed shape

/-- Actual source-body binding and the typed scalar closing hold together.
The actual code/values are retained, and no general CODE substitution or
external typing of the reader's runtime value is assumed. -/
theorem actual_lend_continuation_binding (term : Term) (fuel readObject : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend owner (.lam false domain (.index reference offset evidence))
      (.lam false first (.lam false again body))) (object : Nat) (stack : List Frame) :
    let value := decodeInteger ((run fuel (initial term)).state.heap.heap.payload readObject)
    let resultOrigin := (Lending.read owner (.index reference offset evidence)).subst code.origins
    returnAction (.closure false again body (⟨first,false⟩ :: code.context)
      (consValues resultOrigin code.origins) (some (.integer value) :: code.values))
      (.lendOwnerArgument object (owner.subst code.origins) :: stack) =
      some (.control (.evaluate (enter false again body (⟨first,false⟩ :: code.context)
        (consValues resultOrigin code.origins) (some (.integer value) :: code.values)
        (owner.subst code.origins) (some (.owner object)))) stack
        (some (false,body,owner.subst code.origins))) ∧
      LoanTyping.HasType env [] [] true
        (body.subst (consValues (owner.subst code.origins) (consValues (.integer value) code.origins))) type :=
  ⟨rfl,actual_lend_scalar_bindings term fuel readObject history typed shape⟩

end Jihoo.NativeKernel.Environment.BindingMachine
