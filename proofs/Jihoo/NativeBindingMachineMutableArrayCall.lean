import Jihoo.NativeBindingMachineMutableArrayFrames
import Jihoo.NativeLoanGhostPromotion

/-! Finishing an array argument restores the suspended application frame.
The next machine transition passes the array to the saved closure, whose
dependent source context closes with the actual retained elements. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds

private theorem array_entry_context
    (context : ValueContext env ⟨.lam false domain body,ctx,origins,captured⟩ meanings)
    (typed : LoanTyping.HasType env [] [] true argument (domain.subst meanings))
    (kind : ValueKind env (.array values) (domain.subst meanings)) :
    ValueContext env (enter false domain body ctx origins captured origin (some (.array values)))
      (consValues argument meanings) := by
  refine ⟨context.closing.consValues typed,⟨?_,?_⟩,?_⟩
  · intro index value stored
    cases index with
    | zero => cases stored
    | succ index => exact context.scalars.1 index value stored
  · intro index value stored
    cases index with
    | zero => cases stored
    | succ index => exact context.scalars.2 index value stored
  · intro index binding value selected stored
    cases index with
    | zero =>
        simp only [enter,lookup,Option.some.injEq] at selected
        subst binding
        have same : Value.array values = value := Option.some.inj (Option.some.inj stored)
        subst value
        simpa only [shift_subst_consValues] using kind
    | succ index =>
        obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
        subst binding
        simpa only [shift_subst_consValues] using context.kinds index previous value found stored

/-- The last element and saved array frame determine the exact argument passed
to the real closure. Its dependent result type and retained value context use
that array, while activation keeps the original argument term as provenance. -/
theorem reachable_typed_array_call_entry (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (arrayTyped : LoanClosingTyped env arrayLoans false source arrayMeanings argumentType)
    (functionTyped : LoanClosingTyped env loans false
      ⟨.lam false domain body,ctx,origins,captured⟩ meanings (.pi false argumentType result))
    (context : ValueContext env ⟨.lam false domain body,ctx,origins,captured⟩ meanings)
    (returned : (run fuel (initial term)).state.control = .returned (.integer number))
    (empty : (run fuel (initial term)).state.stack = [])
    (pending : (run fuel (initial term)).state.pending =
      (.arrayElements source [] reversed,
        .argument (.closure false domain body ctx origins captured) argumentOrigin :: stack) :: outer) :
    let state := (run fuel (initial term)).state
    let values := (number :: reversed).reverse
    let argument := Term.elements values.length (values.map Term.integer)
    let next := enter false domain body ctx origins captured argumentOrigin (some (.array values))
    run 2 state = ⟨⟨state.heap,.evaluate next,stack,outer⟩,[.legacy (.activate false body argumentOrigin)],2⟩ ∧
    LoanClosingTyped env loans false next (consValues argument meanings) (result.subst (single argument)) ∧
    ValueContext env next (consValues argument meanings) := by
  let state := (run fuel (initial term)).state
  let values := (number :: reversed).reverse
  let argument := Term.elements values.length (values.map Term.integer)
  let next := enter false domain body ctx origins captured argumentOrigin (some (.array values))
  let restored : State := ⟨state.heap,.returned (.array values),
    .argument (.closure false domain body ctx origins captured) argumentOrigin :: stack,outer⟩
  have resumed : step state = some (restored,none) ∧
      LoanTyping.HasType env [] [] false argument argumentType :=
    reachable_typed_array_resume term fuel history arrayTyped returned empty pending
  obtain ⟨finished,argumentTyped⟩ := resumed
  have applied : step restored = some
      (⟨state.heap,.evaluate next,stack,outer⟩,some (.legacy (.activate false body argumentOrigin))) := by
    simp only [restored,step,returnAction,applyValue,executeLegacy,execute,Option.map_some]
    rfl
  obtain ⟨closing,_,function,coherent⟩ := functionTyped
  obtain ⟨_,bodyType,_,bodyTyped,principal⟩ := function.lamView
  have convertedPi : LoanTyping.Conversion.Conv env
      (.pi false (domain.subst meanings) (bodyType.subst (liftSubOne meanings))) (.pi false argumentType result) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      (principal.substitution meanings history.wellFormed.closed).trans coherent
  obtain ⟨_,domainConverted,bodyConverted⟩ := convertedPi.pi_injective history.wellFormed.admissible
  have closedArgument := (argumentTyped.ghost []).convert domainConverted.symm
  have realized : ValueKind env (.array values) argumentType := by
    have principal : LoanTyping.Conversion.Conv env
        (.array (.natural (values.map Term.integer).length)) argumentType := argumentTyped.principalView
    simpa only [ValueKind,List.length_map] using principal
  change run 2 state = _ ∧ LoanClosingTyped env loans false next (consValues argument meanings)
    (result.subst (single argument)) ∧ ValueContext env next (consValues argument meanings)
  refine ⟨?_,⟨closing.consValues closedArgument,bodyType,bodyTyped,?_⟩,
    array_entry_context context closedArgument (realized.convert domainConverted.symm)⟩
  · simp only [run,finished,applied]
    rfl
  · simpa only [subst_lift_consValues] using
      bodyConverted.substitution (single argument) history.wellFormed.closed

private theorem run_append (first second : Nat) (state : State) :
    run (first+second) state =
      let before := run first state
      let after := run second before.state
      ⟨after.state,before.events ++ after.events,before.steps+after.steps⟩ := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add,run,List.nil_append]
  | succ first ih =>
      simp only [Nat.succ_add,run]
      cases stepped : step state with
      | none =>
          have stopped (fuel : Nat) : run fuel state = ⟨state,[],0⟩ := by
            cases fuel <;> simp only [run,stepped]
          simp only [stopped,List.nil_append,Nat.zero_add]
      | some result =>
          obtain ⟨next,event⟩ := result
          simp only
          rw [ih]
          simp only [List.append_assoc,Nat.add_assoc,Nat.add_comm]

/-- A retained array argument can immediately be indexed using a previously
captured U64. The closure enters with the actual array and its original
captures, then its checked evidence excludes a bounds fault. -/
theorem reachable_typed_array_call_index (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (arrayTyped : LoanClosingTyped env arrayLoans false source arrayMeanings argumentType)
    (functionTyped : LoanClosingTyped env loans false
      ⟨.lam false (.array size) body,ctx,origins,captured⟩ meanings (.pi false argumentType result))
    (context : ValueContext env ⟨.lam false (.array size) body,ctx,origins,captured⟩ meanings)
    (returned : (run fuel (initial term)).state.control = .returned (.integer number))
    (empty : (run fuel (initial term)).state.stack = [])
    (pending : (run fuel (initial term)).state.pending =
      (.arrayElements source [] reversed,
        .argument (.closure false (.array size) body ctx origins captured) argumentOrigin :: stack) :: outer)
    (shape : body = .index (.var 0) (.var (index+1)) evidence)
    (supported :
      let values := (number :: reversed).reverse
      let argument := Term.elements values.length (values.map Term.integer)
      Semantics.LoanArithmetic.Supported (evidence.subst (consValues argument meanings))) :
    let state := (run fuel (initial term)).state
    let values := (number :: reversed).reverse
    let argument := Term.elements values.length (values.map Term.integer)
    ∃ offset value, captured[index]? = some (some (.natural offset)) ∧
      meanings index = .natural offset ∧ offset < values.length ∧ values[offset]? = some value ∧
      run 7 state = ⟨⟨state.heap,.returned (.integer value),stack,outer⟩,
        [.legacy (.activate false body argumentOrigin)],7⟩ ∧
      LoanTyping.HasType env [] [] false (.integer value) (result.subst (single argument)) := by
  let state := (run fuel (initial term)).state
  let values := (number :: reversed).reverse
  let argument := Term.elements values.length (values.map Term.integer)
  let next := enter false (.array size) body ctx origins captured argumentOrigin (some (.array values))
  obtain ⟨entered,typed,enteredContext⟩ := reachable_typed_array_call_entry term fuel history
    arrayTyped functionTyped context returned empty pending
  change run 2 state = ⟨⟨state.heap,.evaluate next,stack,outer⟩,
    [.legacy (.activate false body argumentOrigin)],2⟩ at entered
  have reached : (run (fuel+2) (initial term)).state = ⟨state.heap,.evaluate next,stack,outer⟩ := by
    rw [run_append]
    change (run 2 state).state = _
    exact congrArg Result.state entered
  have evaluated : (run (fuel+2) (initial term)).state.control = .evaluate next := by
    rw [reached]
  have arrayOperand : LoanTyping.HasType env loans next.context false (.var 0) (.array (size.rename Nat.succ)) := by
    change LoanTyping.HasType env loans (⟨.array size,false⟩ :: ctx) false (.var 0) (.array (size.rename Nat.succ))
    have retained : LoanTyping.HasType env loans (⟨.array size,false⟩ :: ctx) false (.var 0)
        ((Term.array size).rename Nat.succ) :=
      LoanTyping.HasType.var (b := ⟨(Term.array size).rename Nat.succ,false⟩) rfl (.inr rfl)
    simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using retained
  have indexed : next.term = .index (.var 0) (.var (index+1)) evidence := shape
  obtain ⟨observedArray,offset,value,storedArray,storedIndex,observedMeaning,bound,read,executed,resultType⟩ :=
    reachable_typed_variable_array_index term (fuel+2) history evaluated typed enteredContext indexed
      arrayOperand supported
  have same : values = observedArray := Value.array.inj (Option.some.inj (Option.some.inj storedArray))
  subst observedArray
  rw [reached] at executed
  refine ⟨offset,value,storedIndex,observedMeaning,bound,read,?_,resultType⟩
  change run (2+5) state = _
  rw [run_append 2 5 state,entered]
  dsimp only
  rw [executed]
  rfl

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
