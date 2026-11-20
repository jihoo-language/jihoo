import Jihoo.NativeBindingMachineMutableArray

/-! A suspended array frame retains its original source and the unvisited
suffix. Each actual resumption either starts the next typed child or returns an
array of the original type, including when its children performed effects. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

/-- The machine has visited as many source terms as it has accumulated values.
The current term accounts for the result that has yet to enter the accumulator. -/
def ArraySource (source : Code) (remaining : List Term) (reversed : List Int) : Prop :=
  ∃ visited current count, source.term = .elements count (visited ++ current :: remaining) ∧
    visited.length = reversed.length

private def FrameSource : BufferFrame → Prop
  | .arrayElements source remaining reversed => ArraySource source remaining reversed
  | _ => True

private def PendingSources (pending : List (BufferFrame × List Frame)) : Prop :=
  ∀ entry ∈ pending, FrameSource entry.1

private theorem PendingSources.cons (sources : PendingSources rest) (source : FrameSource frame) :
    PendingSources ((frame,saved) :: rest) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | member
  · exact source
  · exact sources entry member

private theorem executeLegacy_sources (sources : PendingSources state.pending) (action : Action) :
    PendingSources (executeLegacy state action).1.pending := by
  cases action <;> simp only [executeLegacy]
  all_goals first | exact sources | skip
  case read => split <;> exact sources

private theorem ownedAccessFailure_sources (sources : PendingSources state.pending) (object : Nat) :
    PendingSources (ownedAccessFailure state object).1.pending := by
  simp only [ownedAccessFailure]
  split <;> try split
  all_goals exact sources

private theorem beginArray_sources (sources : PendingSources state.pending)
    (shape : source.term = .elements count elements) :
    PendingSources (beginArray state source count elements).1.pending := by
  simp only [beginArray]
  split
  · cases elements with
    | nil => exact sources
    | cons first rest => exact sources.cons ⟨[],first,count,shape,rfl⟩
  · exact sources

private theorem resumeBuffer_sources (sources : PendingSources state.pending)
    (pending : state.pending = (frame,saved) :: rest) (value : Value) :
    PendingSources (resumeBuffer state frame saved rest value).1.pending := by
  have suspended := sources
  rw [pending] at suspended
  have first := suspended (frame,saved) List.mem_cons_self
  have older : PendingSources rest := fun entry member => suspended entry (List.mem_cons_of_mem _ member)
  cases frame <;> cases value <;> simp only [resumeBuffer]
  all_goals first
    | exact sources
    | exact older
    | exact older.cons True.intro
    | skip
  case value.integer =>
    split
    · exact older
    · exact ownedAccessFailure_sources sources _
  case loadIndex.natural =>
    split
    · exact older.cons True.intro
    · exact ownedAccessFailure_sources sources _
  case loadContinuation.closure =>
    rename_i object origin number erased domain body context origins captured
    cases erased
    · exact executeLegacy_sources
        (state := { state with pending := (.loadOwnerArgument object origin,saved) :: rest })
        (older.cons True.intro) _
    · exact sources
  case loadOwnerArgument.closure =>
    cases ‹Bool›
    · exact executeLegacy_sources (state := { state with pending := rest }) older _
    · exact sources
  case arrayElements.integer =>
    rename_i source remaining reversed number
    cases remaining with
    | nil => exact older
    | cons element unvisited =>
        obtain ⟨visited,current,count,shape,length⟩ := first
        apply older.cons
        refine ⟨visited ++ [current],element,count,?_,?_⟩
        · simpa only [List.append_assoc,List.singleton_append] using shape
        · simp only [List.length_append,List.length_cons,List.length_nil,length] <;> omega

private theorem step_sources (sources : PendingSources state.pending)
    (stepped : step state = some (next,event)) : PendingSources next.pending := by
  cases control : state.control with
  | fault => simp [step,control] at stepped
  | evaluate code =>
      simp only [step,control] at stepped
      split at stepped
      all_goals first
        | solve | cases stepped; exact sources.cons True.intro
        | skip
      · have same := congrArg Prod.fst (Option.some.inj stepped)
        change _ = next at same
        rw [← same]
        exact beginArray_sources sources (by first | assumption | symm; assumption)
      · have same := congrArg Prod.fst (Option.some.inj stepped)
        change _ = next at same
        rw [← same]
        exact executeLegacy_sources sources _
  | returned value =>
      simp only [step,control] at stepped
      cases chosen : returnAction value state.stack with
      | some action =>
          rw [chosen] at stepped
          have same := congrArg Prod.fst (Option.some.inj stepped)
          change _ = next at same
          rw [← same]
          exact executeLegacy_sources sources _
      | none =>
          rw [chosen] at stepped
          cases pending : state.pending with
          | nil => simp [pending] at stepped
          | cons head rest =>
              obtain ⟨frame,saved⟩ := head
              rw [pending] at stepped
              have same := congrArg Prod.fst (Option.some.inj stepped)
              change _ = next at same
              rw [← same]
              exact resumeBuffer_sources sources pending value

private theorem run_sources (fuel : Nat) (sources : PendingSources state.pending) :
    PendingSources (run fuel state).state.pending := by
  induction fuel generalizing state with
  | zero => exact sources
  | succ fuel ih =>
      cases stepped : step state with
      | none => simpa only [run,stepped] using sources
      | some result =>
          obtain ⟨next,event⟩ := result
          simpa only [run,stepped] using ih (step_sources sources stepped)

theorem reachable_array_source (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State)
    (member : (.arrayElements source remaining reversed,saved) ∈ (run fuel (initial term heap)).state.pending) :
    ArraySource source remaining reversed :=
  run_sources fuel (state := initial term heap) (fun _ member => by cases member) _ member

private theorem typed_integer_child {source : Code}
    (closing : LoanTyping.Ghost.Substitution env source.context [] meanings)
    (typed : LoanTyping.HasType env loans source.context false child .i64) :
    LoanClosingTyped env loans false (source.child child) meanings .i64 := by
  refine ⟨closing,_,typed,?_⟩
  simpa only [Term.subst,substArgs] using (RawLend.Conv.refl (env := env) .i64)

/-- Checked array entry starts the first child at I64, retaining every outer
frame while suspending the array's remaining children. -/
theorem typed_array_entry (state : State) (evaluating : state.control = .evaluate source)
    (typed : LoanClosingTyped env loans false source meanings type)
    (shape : source.term = .elements count (first :: remaining)) :
    let child := source.child first
    step state = some (⟨state.heap,.evaluate child,[],
      (.arrayElements source remaining [],state.stack) :: state.pending⟩,none) ∧
    LoanClosingTyped env loans false child meanings .i64 := by
  obtain ⟨closing,_,original,_⟩ := typed
  rw [shape] at original
  obtain ⟨length,width,children⟩ := original.elements_inputs
  have eligible : (first :: remaining).length = count ∧ count < 2^64 := ⟨length,length ▸ width⟩
  exact ⟨by simp only [step,evaluating,shape,beginArray,ite_eq_left eligible],
    typed_integer_child closing (children first List.mem_cons_self)⟩

/-- At a real child return, the saved source gives the next child's typing.
The final child restores the saved frames with a typed array of the original
requested type, using the actual accumulator and signed integer bounds. -/
theorem reachable_typed_array_resume (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false source meanings type)
    (returned : (run fuel (initial term)).state.control = .returned (.integer number))
    (empty : (run fuel (initial term)).state.stack = [])
    (pending : (run fuel (initial term)).state.pending = (.arrayElements source remaining reversed,saved) :: outer) :
    let state := (run fuel (initial term)).state
    match remaining with
    | [] =>
        let values := (number :: reversed).reverse
        step state = some (⟨state.heap,.returned (.array values),saved,outer⟩,none) ∧
        LoanTyping.HasType env [] [] false (.elements values.length (values.map Term.integer)) type
    | next :: rest =>
        let child := source.child next
        step state = some (⟨state.heap,.evaluate child,state.stack,
          (.arrayElements source rest (number :: reversed),saved) :: outer⟩,none) ∧
        LoanClosingTyped env loans false child meanings .i64 := by
  have member : (.arrayElements source remaining reversed,saved) ∈ (run fuel (initial term)).state.pending := by
    rw [pending]
    exact List.mem_cons_self
  obtain ⟨visited,current,count,shape,length⟩ := reachable_array_source term fuel _ member
  obtain ⟨closing,_,original,converted⟩ := typed
  rw [shape] at original
  obtain ⟨_,width,children⟩ := original.elements_inputs
  cases remaining with
  | cons next rest =>
      exact ⟨by simp only [step,returned,empty,returnAction,pending,resumeBuffer],
        typed_integer_child closing
          (children next (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
  | nil =>
      refine ⟨by simp only [step,returned,empty,returnAction,pending,resumeBuffer],?_⟩
      let values := (number :: reversed).reverse
      have numeric := initial_run_numbers term fuel
      have currentWidth := numeric.legacy.2.1
      change ControlNumbers _ at currentWidth
      rw [returned] at currentWidth
      have entry := numeric.pending _ member
      have previousWidths : ArrayNumbers reversed := entry.1.2
      have allWidths : ArrayNumbers values := by
        intro value found
        have found : value ∈ number :: reversed := List.mem_reverse.mp found
        rcases List.mem_cons.mp found with same | previous
        · subst value
          exact (show ValueNumbers (.integer number) from currentWidth).integerBound
        · exact previousWidths value previous
      have sameLength : values.length = (visited ++ [current]).length := by
        simp only [values,List.length_reverse,List.length_cons,List.length_append,List.length_nil,length] <;> omega
      have literals : LoanTyping.HasType env [] [] false
          (.elements values.length (values.map Term.integer)) (.array (.natural values.length)) := by
        have lengthMap : (values.map Term.integer).length = values.length := List.length_map _
        have fits : (values.map Term.integer).length < 2^64 := by
          rw [lengthMap,sameLength]
          exact width
        have each : ∀ value ∈ values.map Term.integer, LoanTyping.HasType env [] [] false value .i64 := by
          intro value mapped
          obtain ⟨integer,originalMember,rfl⟩ := List.mem_map.mp mapped
          have signed := allWidths integer originalMember
          exact .integer signed.1 signed.2
        have formed := LoanTyping.HasType.elements lengthMap fits each
        simpa only [List.length_map] using formed
      have requested : LoanTyping.Conversion.Conv env (.array (.natural values.length)) type := by
        rw [sameLength]
        simpa only [Term.subst,substArgs,Op.binders,liftSub] using
          (original.principalView.substitution meanings history.wellFormed.closed).trans converted
      exact literals.convert requested

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
