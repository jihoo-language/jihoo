import Jihoo.NativeBindingMachineMutableNumeric

/-! Indexed Array consumes its actual retained immutable elements. Source
index evidence supplies the bound and array typing fixes the physical length. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def ArrayElements (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool) : Term → Prop
  | .elements count values =>
      values.length = count ∧ values.length < 2^64 ∧
        ∀ value ∈ values, HasType env loans ctx mode value .i64
  | _ => True

theorem HasType.elements_inputs (typed : HasType env loans ctx mode (.elements count values) type) :
    values.length = count ∧ values.length < 2^64 ∧ ∀ value ∈ values, HasType env loans ctx mode value .i64 := by
  suffices view : ∀ {term type}, HasType env loans ctx mode term type → ArrayElements env loans ctx mode term from
    view typed
  intro term type source
  apply HasType.rec (t := source)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun stack context ghost term _ _ => ArrayElements env stack context ghost term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case dataElim => split <;> trivial

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

private theorem literal_elements_tail (heap : SizedBufferHeap.IndexedState) (source : Code)
    (saved : List Frame) (outer : List (BufferFrame × List Frame)) (first : Int) (rest reversed : List Int)
    (firstWidth : ValueReduction.signed64 first) (restWidths : ArrayNumbers rest) :
    run (2*rest.length+2) ⟨heap,.evaluate (source.child (.integer first)),[],
      (.arrayElements source (rest.map Term.integer) reversed,saved) :: outer⟩ =
      ⟨⟨heap,.returned (.array (reversed.reverse ++ first :: rest)),saved,outer⟩,[],2*rest.length+2⟩ := by
  induction rest generalizing first reversed with
  | nil =>
      simp only [run,step,evaluateAction,Code.child,executeLegacy,execute,Option.map_none,
        returnAction,resumeBuffer,firstWidth,↓reduceIte,List.map_nil,List.reverse_cons]
      rfl
  | cons number rest ih =>
      have width := restWidths number List.mem_cons_self
      have tailWidths : ArrayNumbers rest := fun value member => restWidths value (List.mem_cons_of_mem _ member)
      have steps : 2*(number :: rest).length+2 = (2*rest.length+2)+2 := by
        simp only [List.length_cons]
        omega
      rw [steps,run]
      simp only [step,evaluateAction,Code.child,executeLegacy,execute,Option.map_none,firstWidth,↓reduceIte,
        Option.toList,List.nil_append,List.map_cons]
      rw [run]
      simp only [step,returnAction,resumeBuffer,Option.toList,List.nil_append]
      have continued := ih number (first :: reversed) width tailWidths
      dsimp only [Code.child] at continued
      simp only [Code.child]
      rw [continued]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc]

/-- For an arbitrarily long typed literal array, each element is evaluated
and retained in its original position and the requested array type is kept. -/
theorem typed_literal_array (state : State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .elements values.length (values.map Term.integer)) :
    run (2*values.length+1) state = ⟨⟨state.heap,.returned (.array values),state.stack,state.pending⟩,
      [],2*values.length+1⟩ ∧ ValueKind env (.array values) type := by
  obtain ⟨_,_,original,converted⟩ := typed
  rw [shape] at original
  obtain ⟨_,countWidth,entries⟩ := original.elements_inputs
  have width : values.length < 2^64 := by simpa only [List.length_map] using countWidth
  have numbers : ArrayNumbers values := fun number member =>
    (entries (.integer number) (List.mem_map.mpr ⟨number,member,rfl⟩)).integer_bound
  have arrayType : ValueKind env (.array values) type := by
    simpa only [ValueKind,Term.subst,substArgs,Op.binders,liftSub,List.length_map] using
      (original.principalView.substitution meanings history.wellFormed.closed).trans converted
  refine ⟨?_,arrayType⟩
  cases values with
  | nil =>
      simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,run,step,evaluating,shape,beginArray,List.map_nil,
        true_and]
      rfl
  | cons first rest =>
      have lengths : 2*(first :: rest).length = 2*rest.length+2 := by
        simp only [List.length_cons]
        omega
      have eligible : ((first :: rest).map Term.integer).length = (first :: rest).length ∧
          (first :: rest).length < 2^64 := ⟨List.length_map _,width⟩
      have starts : step state = some (⟨state.heap,.evaluate (code.child (.integer first)),[],
          (.arrayElements code (rest.map Term.integer) [],state.stack) :: state.pending⟩,none) := by
        simp only [step,evaluating,shape,beginArray,ite_eq_left eligible]
        rfl
      rw [run,starts,lengths]
      simp only [Option.toList,List.nil_append]
      have firstWidth := numbers first List.mem_cons_self
      have restWidths : ArrayNumbers rest := fun value member => numbers value (List.mem_cons_of_mem _ member)
      rw [literal_elements_tail _ _ _ _ first rest [] firstWidth restWidths]
      rfl

private theorem literal_array_index_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .index (.var slot) (.natural offset) evidence)
    (stored : code.values[slot]? = some (some (.array elements)))
    (width : offset < 2^64)
    (selected : elements[offset]? = some value) :
    run 5 state = ⟨⟨state.heap,.returned (.integer value),state.stack,state.pending⟩,[],5⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,stored,executeLegacy,execute,Option.map_none,
    returnAction,width,↓reduceIte,selected]
  rfl

/-- The original Loan64 Index judgment supplies the literal proof and
result type. The interpreted slot identifies the actual immutable length,
and every reachable array member already has signed I64 width. -/
theorem reachable_typed_array_index (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (shape : code.term = .index (.var slot) (.natural offset)
      (.decide (.natural offset) (.natural count)))
    (stored : code.values[slot]? = some (some (.array elements))) :
    let state := (run fuel (initial term)).state
    elements.length = count ∧ offset < elements.length ∧
    ∃ value, elements[offset]? = some value ∧
      run 5 state = ⟨⟨state.heap,.returned (.integer value),state.stack,state.pending⟩,[],5⟩ ∧
      LoanTyping.HasType env [] [] false (.integer value) type := by
  obtain ⟨closing,_,original,converted⟩ := typed
  rw [shape] at original
  obtain ⟨size,indexed,_,bound⟩ := original.index_inputs
  have sizes : LoanTyping.Conversion.Conv env (.array (.natural elements.length)) (.array (size.subst meanings)) := by
    rcases indexed with array | borrowed
    · obtain ⟨binding,selected,principal⟩ := array.principalView
      have represented := context.kinds slot binding (.array elements) selected stored
      have converted := principal.substitution meanings history.wellFormed.closed
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using represented.trans converted
    · obtain ⟨binding,selected,principal⟩ := borrowed.principalView
      have represented := context.kinds slot binding (.array elements) selected stored
      have converted := principal.substitution meanings history.wellFormed.closed
      have impossible : LoanTyping.Conversion.Conv env (.array (.natural elements.length))
          (.ref (.buffer (size.subst meanings))) := by
        simpa only [Term.subst,substArgs,Op.binders,liftSub] using represented.trans converted
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same)
        impossible history.wellFormed.admissible)
  have physical := sizes.array_injective history.wellFormed.admissible
  have proof : LoanTyping.HasType env [] [] true (.decide (.natural offset) (.natural count))
      (.lt (.natural offset) (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using bound.ghostSubstitution history.wellFormed closing
  have checkedLength := (proof.principalView.lt_injective history.wellFormed.admissible).2
  have length := (physical.trans checkedLength.symm).natural_injective history.wellFormed.admissible
  have limits := bound.literal_decide_limits history.wellFormed
  have within : offset < elements.length := length ▸ limits.2.2
  have selected : elements[offset]? = some elements[offset] := List.getElem?_eq_some_iff.mpr ⟨within,rfl⟩
  have numeric := (initial_run_numbers term fuel).legacy.2.1
  change ControlNumbers _ at numeric
  rw [evaluating] at numeric
  have cells := (ValuesNumbers.valueAt (show CodeNumbers code from numeric) stored).arrayBounds
  have width := cells _ (List.mem_of_getElem? selected)
  have requested : LoanTyping.Conversion.Conv env .i64 type := by
    simpa only [Term.subst,substArgs] using
      (original.principalView.substitution meanings history.wellFormed.closed).trans converted
  exact ⟨length,within,_,selected,literal_array_index_steps _ evaluating shape stored limits.1 selected,
    (LoanTyping.HasType.integer width.1 width.2).convert requested⟩

namespace Examples

set_option maxRecDepth 4096

private def element (fill value : Int) : Term :=
  .free (.alloc (.natural 1) (.integer fill)) (.integer value)

private def elements : Term := .elements 2 [element 11 4,element 22 (-6)]

private def read_array : Term :=
  .app (.lam false (.array (.natural 2))
    (.index (.var 0) (.natural 1) (.decide (.natural 1) (.natural 2)))) elements

theorem array_index_admitted : LoanTyping.MixedProgram.checkDeclaration 40 64 .empty
    ⟨.i64,read_array⟩ = some ⟨.i64,read_array⟩ := by cbv

theorem array_literal_retains_order : observe (run 40 (initial elements)) = .array [4,-6] := by rfl

theorem array_index_returns : observe (run 50 (initial read_array)) = .integer (-6) := by rfl

theorem array_literal_effect_order : (run 50 (initial read_array)).events.filterMap
    (fun event => match event with | .legacy (.heap heap) => some heap | _ => none) =
    [.alloc 0 1 (encodeInteger 11),.free 0,.alloc 1 1 (encodeInteger 22),.free 1] := by rfl

theorem array_index_out_of_bounds :
    observe (run 8 (initial (.index (.elements 0 []) (.natural 0) (.natural 0)))) =
      .fault .indexBounds := by rfl

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
