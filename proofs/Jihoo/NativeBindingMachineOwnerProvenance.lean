import Jihoo.NativeBindingMachineNumeric

/-! Every owner retained by actual control, frames or recursively captured
closures has an earlier allocation identity. Fresh allocation therefore cannot
alias an old captured owner, even if that old object is already released.
This is provenance, not live/exclusive source ownership or a progress theorem. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

mutual
  inductive ValueOwners (limit : Nat) : Value → Prop where
    | natural : ValueOwners limit (.natural value)
    | integer : ValueOwners limit (.integer value)
    | typeCode : ValueOwners limit (.typeCode source)
    | array : ValueOwners limit (.array elements)
    | reference : ValueOwners limit (.reference token)
    | owner : object < limit → ValueOwners limit (.owner object)
    | closure : ValuesOwners limit captured → ValueOwners limit (.closure erased domain body context origins captured)
  inductive ValuesOwners (limit : Nat) : List (Option Value) → Prop where
    | nil : ValuesOwners limit []
    | erased : ValuesOwners limit values → ValuesOwners limit (none :: values)
    | retained : ValueOwners limit value → ValuesOwners limit values → ValuesOwners limit (some value :: values)
end

theorem ValueOwners.ownerBound (ready : ValueOwners limit (.owner object)) : object < limit := by
  cases ready; assumption

theorem ValueOwners.mono (ready : ValueOwners before value) (grows : before ≤ after) : ValueOwners after value := by
  apply ValueOwners.rec (t := ready)
    (motive_1 := fun value _ => ValueOwners after value)
    (motive_2 := fun values _ => ValuesOwners after values)
  all_goals intros
  all_goals first
    | exact .natural | exact .integer | exact .typeCode | exact .array | exact .reference
    | exact .owner (by omega) | exact .closure (by assumption)
    | exact .nil | exact .erased (by assumption) | exact .retained (by assumption) (by assumption)

theorem ValuesOwners.mono (ready : ValuesOwners before values) (grows : before ≤ after) : ValuesOwners after values := by
  induction values with
  | nil => exact .nil
  | cons value rest ih =>
      cases ready with
      | erased previous => exact .erased (ih previous)
      | retained first previous => exact .retained (first.mono grows) (ih previous)

theorem ValuesOwners.valueAt {index : Nat} (ready : ValuesOwners limit values)
    (found : values[index]? = some (some value)) : ValueOwners limit value := by
  induction values generalizing index with
  | nil => simp at found
  | cons option rest ih =>
      cases ready with
      | erased previous => cases index with
          | zero => cases found
          | succ index => exact ih previous found
      | retained first previous => cases index with
          | zero =>
              simp only [List.getElem?_cons_zero,Option.some.injEq] at found
              subst value
              exact first
          | succ index => exact ih previous found

theorem ValuesOwners.cons (ready : ValuesOwners limit values)
    (argumentReady : ∀ value, argument = some value → ValueOwners limit value) : ValuesOwners limit (argument :: values) := by
  cases argument with
  | none => exact .erased ready
  | some value => exact .retained (argumentReady value rfl) ready

def CodeOwners (limit : Nat) (code : Code) : Prop := ValuesOwners limit code.values

theorem CodeOwners.mono (ready : CodeOwners before code) (grows : before ≤ after) : CodeOwners after code :=
  ValuesOwners.mono ready grows

theorem CodeOwners.branch (ready : CodeOwners limit code) (equal : Bool) (first second : Term) :
    CodeOwners limit (branchCode equal code first second) := .erased ready

def FrameOwners (limit : Nat) : Frame → Prop
  | .function code | .strict code | .addLeft code | .arithmeticLeft _ code |
      .allocateCount code | .free code | .indexReference code => CodeOwners limit code
  | .argument function _ => ValueOwners limit function
  | .branchLeft _ second yes no _ => CodeOwners limit second ∧ CodeOwners limit yes ∧ CodeOwners limit no
  | .branchRight _ _ yes no _ _ => CodeOwners limit yes ∧ CodeOwners limit no
  | .lendOwner reader continuation _ _ => CodeOwners limit reader ∧ CodeOwners limit continuation
  | .lendReader _ object _ _ _ continuation | .lendFinish _ object _ _ _ continuation =>
      object < limit ∧ CodeOwners limit continuation
  | .lendContinuation object _ _ result => object < limit ∧ ValueOwners limit result
  | .lendOwnerArgument object _ => object < limit
  | _ => True

theorem FrameOwners.mono (ready : FrameOwners before frame) (grows : before ≤ after) : FrameOwners after frame := by
  cases frame <;> simp only [FrameOwners] at ready ⊢
  all_goals first
    | trivial | exact ready.mono grows | omega
    | exact ⟨ready.1.mono grows,ready.2.mono grows⟩
    | exact ⟨ready.1.mono grows,ready.2.1.mono grows,ready.2.2.mono grows⟩
    | exact ⟨by omega,ready.2.mono grows⟩

def StackOwners (limit : Nat) (stack : List Frame) : Prop := ∀ frame ∈ stack, FrameOwners limit frame

theorem StackOwners.empty : StackOwners limit [] := by intro frame member; cases member

theorem StackOwners.cons (ready : StackOwners limit rest) (firstReady : FrameOwners limit first) :
    StackOwners limit (first :: rest) := by
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact firstReady
  · exact ready frame member

theorem StackOwners.head (ready : StackOwners limit (first :: rest)) : FrameOwners limit first := ready first List.mem_cons_self

theorem StackOwners.tail (ready : StackOwners limit (first :: rest)) : StackOwners limit rest := by
  intro frame member
  exact ready frame (List.mem_cons_of_mem _ member)

theorem StackOwners.mono (ready : StackOwners before stack) (grows : before ≤ after) : StackOwners after stack := by
  intro frame member
  exact (ready frame member).mono grows

def ControlOwners (limit : Nat) : Control → Prop
  | .evaluate code => CodeOwners limit code
  | .returned value => ValueOwners limit value
  | .fault _ => True

def StateOwners (state : State) : Prop :=
  ControlOwners state.heap.heap.nextObject state.control ∧ StackOwners state.heap.heap.nextObject state.stack

def ActionOwners (limit : Nat) : Action → Prop
  | .control control stack _ => ControlOwners limit control ∧ StackOwners limit stack
  | .allocate _ _ stack | .read _ _ stack => StackOwners limit stack
  | .free object rest stack => object < limit ∧ CodeOwners limit rest ∧ StackOwners limit stack
  | .lend object _ _ reader continuation stack =>
      object < limit ∧ CodeOwners limit reader ∧ CodeOwners limit continuation ∧ StackOwners limit stack
  | .close _ object result _ _ continuation stack =>
      object < limit ∧ ValueOwners limit result ∧ CodeOwners limit continuation ∧ StackOwners limit stack
  | .borrow _ object stack => object < limit ∧ StackOwners limit stack

theorem applyValue_owners (functionReady : ValueOwners limit function)
    (argumentReady : ∀ value, argument = some value → ValueOwners limit value)
    (stackReady : StackOwners limit stack) : ActionOwners limit (applyValue function origin argument stack) := by
  cases functionReady
  all_goals first | exact ⟨True.intro,stackReady⟩ | exact ⟨ValuesOwners.cons (by assumption) argumentReady,stackReady⟩

theorem applyValue_owners_retained (functionReady : ValueOwners limit function) (argumentReady : ValueOwners limit argument)
    (stackReady : StackOwners limit stack) : ActionOwners limit (applyValue function origin (some argument) stack) :=
  applyValue_owners functionReady (by intro value same; cases same; exact argumentReady) stackReady

theorem evaluate_action_owners (codeReady : CodeOwners limit code) (stackReady : StackOwners limit stack) :
    ActionOwners limit (evaluateAction code stack) := by
  fun_cases evaluateAction code stack
  all_goals try simp only [evaluateAction, *]
  all_goals first
    | exact ⟨True.intro,stackReady⟩
    | exact ⟨ValueOwners.natural,stackReady⟩
    | exact ⟨ValueOwners.integer,stackReady⟩
    | exact ⟨ValueOwners.typeCode,stackReady⟩
    | exact ⟨ValueOwners.closure codeReady,stackReady⟩
    | exact ⟨codeReady,stackReady.cons codeReady⟩
    | exact ⟨codeReady,stackReady.cons ⟨codeReady,codeReady⟩⟩
    | exact ⟨codeReady,stackReady.cons ⟨codeReady,codeReady,codeReady⟩⟩
    | exact ⟨ValuesOwners.valueAt codeReady (by assumption),stackReady⟩
    | exact ⟨(ValuesOwners.valueAt codeReady (by assumption)).ownerBound,stackReady⟩

theorem return_action_owners (valueReady : ValueOwners limit value) (stackReady : StackOwners limit stack)
    (computed : returnAction value stack = some result) : ActionOwners limit result := by
  cases stack with
  | nil => cases computed
  | cons frame rest =>
      have frameReady := stackReady.head
      have restReady := stackReady.tail
      simp only [returnAction] at computed
      split at computed
      all_goals have same := Option.some.inj computed
      all_goals rw [← same]
      all_goals clear computed same
      all_goals simp only [FrameOwners] at frameReady
      all_goals first
        | exact ⟨True.intro,restReady⟩
        | exact ⟨True.intro,restReady.cons frameReady⟩
        | exact ⟨frameReady,restReady⟩
        | exact ⟨frameReady,restReady.cons valueReady⟩
        | exact ⟨frameReady,restReady.cons True.intro⟩
        | exact restReady
        | exact ⟨valueReady.ownerBound,frameReady,restReady⟩
        | exact ⟨valueReady.ownerBound,frameReady.1,frameReady.2,restReady⟩
        | exact ⟨frameReady.1,valueReady,frameReady.2,restReady⟩
        | exact ⟨frameReady.1,restReady.cons frameReady.2⟩
        | exact applyValue_owners_retained frameReady valueReady restReady
        | exact applyValue_owners (argument := none) valueReady (by intro candidate same; cases same) restReady
        | exact applyValue_owners_retained valueReady .reference (restReady.cons frameReady)
        | exact applyValue_owners_retained valueReady frameReady.2 (restReady.cons frameReady.1)
        | exact applyValue_owners_retained valueReady (.owner frameReady) restReady
        | skip
      case h_7 => split <;> first | exact ⟨ValueOwners.natural,restReady⟩ | exact ⟨True.intro,restReady⟩
      case h_9 => split <;> first | exact ⟨ValueOwners.integer,restReady⟩ | exact ⟨True.intro,restReady⟩
      case h_14 =>
        rename_i equal left yes no firstOrigin secondOrigin right
        by_cases compared : (if equal then left == right else decide (left < right)) = true
        · simp only [compared,↓reduceIte]
          exact ⟨frameReady.1.branch equal firstOrigin secondOrigin,restReady⟩
        · simp only [compared]
          exact ⟨frameReady.2,restReady⟩
      all_goals split <;> first | exact ⟨ValueOwners.integer,restReady⟩ | exact ⟨True.intro,restReady⟩

theorem action_owners (control : ControlOwners limit state.control) (stack : StackOwners limit state.stack)
    (chosen : action state = some next) : ActionOwners limit next := by
  cases state with
  | mk heap current frames =>
      cases current with
      | evaluate code =>
          have same : evaluateAction code frames = next := Option.some.inj chosen
          rw [← same]
          exact evaluate_action_owners control stack
      | returned value => exact return_action_owners control stack chosen
      | fault reason => cases chosen

theorem execute_owners (ready : ActionOwners heap.heap.nextObject next) : StateOwners (execute heap next).1 := by
  cases next with
  | control control stack activation => exact ready
  | allocate count fill stack =>
      simp only [execute]
      split
      · exact ⟨ValueOwners.owner (Nat.lt_succ_self _),ready.mono (Nat.le_succ _)⟩
      · exact ⟨True.intro,ready⟩
  | free object rest stack =>
      simp only [execute]
      split
      · split
        · exact ready.2
        · exact ⟨True.intro,ready.2.2⟩
      · exact ⟨True.intro,ready.2.2⟩
  | lend object name origin reader continuation stack =>
      simp only [execute]
      split
      · exact ⟨ready.2.1,ready.2.2.2.cons ⟨ready.1,ready.2.2.1⟩⟩
      · exact ⟨True.intro,ready.2.2.2⟩
  | close token object result origin resultOrigin continuation stack =>
      simp only [execute]
      split
      · exact ⟨ready.2.2.1,ready.2.2.2.cons ⟨ready.1,ready.2.1⟩⟩
      · exact ⟨True.intro,ready.2.2.2⟩
  | borrow key object stack =>
      simp only [execute]
      split
      · split
        · exact ⟨ValueOwners.reference,ready.2⟩
        · exact ⟨True.intro,ready.2⟩
      · exact ⟨True.intro,ready.2⟩
  | read token index stack =>
      simp only [execute]
      split
      · split
        · exact ⟨ValueOwners.integer,ready⟩
        · exact ⟨True.intro,ready⟩
      · exact ⟨True.intro,ready⟩

theorem step_owners (ready : StateOwners state) (stepped : step state = some (next,event)) : StateOwners next := by
  obtain ⟨nextAction,chosen,same⟩ := Option.map_eq_some_iff.mp stepped
  simpa only [same] using execute_owners (action_owners ready.1 ready.2 chosen)

theorem run_owners (ready : StateOwners state) (fuel : Nat) : StateOwners (run fuel state).state := by
  induction fuel generalizing state with
  | zero => exact ready
  | succ fuel ih =>
      simp only [run]
      cases observed : step state with
      | none => exact ready
      | some result =>
          obtain ⟨next,event⟩ := result
          exact ih (step_owners ready observed)

/-- All real prefixes, including faults and fuel exhaustion; every nested
closure capture and saved continuation owner is covered. -/
theorem initial_run_owners (term : Term) (fuel : Nat) : StateOwners (run fuel (initial term)).state :=
  run_owners (state := initial term) ⟨ValuesOwners.nil,StackOwners.empty⟩ fuel

inductive OwnerOccurs (object : Nat) : Value → Prop where
  | owner : OwnerOccurs object (.owner object)
  | closure {index : Nat} : captured[index]? = some (some value) → OwnerOccurs object value →
      OwnerOccurs object (.closure erased domain body context origins captured)

theorem OwnerOccurs.before_limit (occurs : OwnerOccurs object value) (ready : ValueOwners limit value) : object < limit := by
  induction occurs with
  | owner => exact ready.ownerBound
  | closure stored inside ih =>
      cases ready with
      | closure captured => exact ih (captured.valueAt stored)

theorem initial_run_captured_owner_bound {index : Nat} (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (stored : code.values[index]? = some (some value)) (occurs : OwnerOccurs object value) :
    object < (run fuel (initial term)).state.heap.heap.nextObject := by
  have ready := (initial_run_owners term fuel).1
  rw [evaluating] at ready
  exact occurs.before_limit (ValuesOwners.valueAt ready stored)

/-- The next allocation identity is absent even inside recursively captured
old closures. This covers dead old owners as well as currently live owners. -/
theorem initial_run_fresh_not_captured {index : Nat} (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (stored : code.values[index]? = some (some value)) :
    ¬ OwnerOccurs (run fuel (initial term)).state.heap.heap.nextObject value := by
  intro occurs
  have before := initial_run_captured_owner_bound term fuel evaluating stored occurs
  omega

private theorem allocation_step_origin (step : SizedBufferHeap.Step before event after)
    (bound : object < after.heap.nextObject) :
    object < before.heap.nextObject ∨ ∃ count fill, event = .alloc object count fill := by
  cases step with
  | alloc =>
      by_cases earlier : object < before.heap.nextObject
      · exact Or.inl earlier
      · have identity : object = before.heap.nextObject := by
          change object < before.heap.nextObject+1 at bound
          omega
        subst object
        exact Or.inr ⟨_,_,rfl⟩
  | free => exact Or.inl bound
  | beginLease => exact Or.inl bound
  | close => exact Or.inl bound
  | read => exact Or.inl bound

private theorem allocation_steps_origin (steps : SizedBufferHeap.Steps before events after)
    (bound : object < after.heap.nextObject) :
    object < before.heap.nextObject ∨ ∃ count fill, SizedBufferHeap.Event.alloc object count fill ∈ events := by
  induction steps with
  | nil => exact Or.inl bound
  | cons step rest ih =>
      rcases ih bound with previous | allocated
      · rcases allocation_step_origin step previous with previous | ⟨count,fill,same⟩
        · exact Or.inl previous
        · exact Or.inr ⟨count,fill,List.mem_cons.mpr (Or.inl same.symm)⟩
      · obtain ⟨count,fill,member⟩ := allocated
        exact Or.inr ⟨count,fill,List.mem_cons_of_mem _ member⟩

private theorem initial_allocation_origin (term : Term) (fuel : Nat)
    (bound : object < (run fuel (initial term)).state.heap.heap.nextObject) :
    ∃ count fill, SizedBufferHeap.Event.alloc object count fill ∈ eventsHeap (run fuel (initial term)).events := by
  have steps := run_heap_steps (state := initial term) SizedBufferHeap.empty_valid fuel
  rcases allocation_steps_origin steps bound with old | allocated
  · change object < 0 at old
    omega
  · exact allocated

private theorem allocation_event_layout (steps : SizedBufferHeap.Steps before events after)
    (member : SizedBufferHeap.Event.alloc object count fill ∈ events) :
    after.length object = count ∧ after.heap.payload object = fill := by
  induction steps with
  | nil => cases member
  | cons step rest ih =>
      rcases List.mem_cons.mp member with same | member
      · cases step with
        | alloc =>
            cases same
            rename_i allocationBase remainingEvents finalHeap
            have bound : allocationBase.heap.nextObject <
                (SizedBufferHeap.allocate allocationBase count fill).heap.nextObject := Nat.lt_succ_self _
            exact ⟨(SizedBufferHeap.lengths_preserved bound rest).2.trans SizedBufferHeap.allocation_length,
              (SizedBufferHeap.payloads_preserved bound rest).trans (by simp [SizedBufferHeap.allocate,HeapLeases.put])⟩
        | free => cases same
        | beginLease => cases same
        | close => cases same
        | read => cases same
      · exact ih member

/-- Every owner recursively captured at an actual evaluation point comes from
a concrete earlier allocation event, with its original length and payload. -/
theorem initial_run_captured_owner_provenance {index : Nat} (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (stored : code.values[index]? = some (some value)) (occurs : OwnerOccurs object value) :
    ∃ count fill,
      SizedBufferHeap.Event.alloc object count fill ∈ eventsHeap (run fuel (initial term)).events ∧
      (run fuel (initial term)).state.heap.length object = count ∧
      (run fuel (initial term)).state.heap.heap.payload object = fill := by
  obtain ⟨count,fill,allocated⟩ := initial_allocation_origin term fuel
    (initial_run_captured_owner_bound term fuel evaluating stored occurs)
  have layout := allocation_event_layout (run_heap_steps (state := initial term) SizedBufferHeap.empty_valid fuel) allocated
  exact ⟨count,fill,allocated,layout⟩

theorem initial_run_returned_owner_provenance (term : Term) (fuel : Nat)
    (returned : (run fuel (initial term)).state.control = .returned value)
    (occurs : OwnerOccurs object value) :
    ∃ count fill,
      SizedBufferHeap.Event.alloc object count fill ∈ eventsHeap (run fuel (initial term)).events ∧
      (run fuel (initial term)).state.heap.length object = count ∧
      (run fuel (initial term)).state.heap.heap.payload object = fill := by
  have ready := (initial_run_owners term fuel).1
  rw [returned] at ready
  obtain ⟨count,fill,allocated⟩ := initial_allocation_origin term fuel (occurs.before_limit ready)
  have layout := allocation_event_layout (run_heap_steps (state := initial term) SizedBufferHeap.empty_valid fuel) allocated
  exact ⟨count,fill,allocated,layout⟩

end Jihoo.NativeKernel.Environment.BindingMachine
