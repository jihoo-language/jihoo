import Jihoo.NativeBindingMachineAlignment

/-! Numeric value, capture, stack and heap interpretation for every actual
machine prefix. Guards and actual heap contents supply bounds; no returned
value typing or successful-evaluation certificate is an input. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

mutual
  inductive ValueNumbers : Value → Prop where
    | natural : value < 2^64 → ValueNumbers (.natural value)
    | integer : ValueReduction.signed64 value → ValueNumbers (.integer value)
    | typeCode : ValueNumbers (.typeCode source)
    | owner : ValueNumbers (.owner object)
    | reference : ValueNumbers (.reference token)
    | closure : ValuesNumbers captured → ValueNumbers (.closure erased domain body context origins captured)
  inductive ValuesNumbers : List (Option Value) → Prop where
    | nil : ValuesNumbers []
    | erased : ValuesNumbers values → ValuesNumbers (none :: values)
    | retained : ValueNumbers value → ValuesNumbers values → ValuesNumbers (some value :: values)
end

def CodeNumbers (code : Code) : Prop := ValuesNumbers code.values

theorem ValueNumbers.naturalBound (bounded : ValueNumbers (.natural value)) : value < 2^64 := by
  cases bounded; assumption

theorem ValueNumbers.integerBound (bounded : ValueNumbers (.integer value)) : ValueReduction.signed64 value := by
  cases bounded; assumption

theorem ValuesNumbers.valueAt {index : Nat} (bounded : ValuesNumbers values)
    (found : values[index]? = some (some value)) : ValueNumbers value := by
  induction values generalizing index with
  | nil => simp at found
  | cons option values ih =>
      cases bounded with
      | erased previous => cases index with
          | zero => cases found
          | succ index => exact ih previous found
      | retained ready previous => cases index with
          | zero =>
              simp only [List.getElem?_cons_zero,Option.some.injEq] at found
              subst value
              exact ready
          | succ index => exact ih previous found

theorem ValuesNumbers.cons (bounded : ValuesNumbers values)
    (argumentBound : ∀ value, argument = some value → ValueNumbers value) : ValuesNumbers (argument :: values) := by
  cases argument with
  | none => exact .erased bounded
  | some value => exact .retained (argumentBound value rfl) bounded

theorem CodeNumbers.child (bounded : CodeNumbers code) (term : Term) : CodeNumbers (code.child term) := bounded

theorem CodeNumbers.branch (bounded : CodeNumbers code) (equal : Bool) (first second : Term) :
    CodeNumbers (branchCode equal code first second) := .erased bounded

/-- This uniform read-only heap stores bounded encoded payloads everywhere,
including old/released identities, and only machine-representable lengths. -/
structure HeapNumbers (heap : SizedBufferHeap.State) : Prop where
  payload : ∀ object, heap.heap.payload object < 2^64
  length : ∀ object, heap.length object * 8 + 8 < 2^64

theorem HeapNumbers.empty : HeapNumbers SizedBufferHeap.empty := by
  constructor
  · intro object
    change (0 : Nat) < 2^64
    decide
  · intro object
    change (8 : Nat) < 2^64
    decide

theorem HeapNumbers.allocate (bounded : HeapNumbers heap)
    (fillBound : ValueReduction.signed64 fill) (fits : count*8+8 < 2^64) :
    HeapNumbers (SizedBufferHeap.allocate heap count (encodeInteger fill)) := by
  constructor
  · intro object
    simp only [SizedBufferHeap.allocate,HeapLeases.put]
    split
    · exact encode_integer_bound fillBound
    · exact bounded.payload object
  · intro object
    simp only [SizedBufferHeap.allocate,HeapLeases.put]
    split
    · exact fits
    · exact bounded.length object

theorem decode_integer_bound (bounded : value < 2^64) : ValueReduction.signed64 (decodeInteger value) := by
  have high : (value : Int) < 2^64 := Int.ofNat_lt.mpr bounded
  have low : (0 : Int) ≤ value := Int.natCast_nonneg value
  constructor <;> dsimp [decodeInteger] <;> omega

def FrameNumbers : Frame → Prop
  | .function code | .strict code | .addLeft code | .arithmeticLeft _ code |
      .allocateCount code | .free code | .indexReference code => CodeNumbers code
  | .argument function _ => ValueNumbers function
  | .addRight left | .allocateFill left => left < 2^64
  | .arithmeticRight _ left => ValueReduction.signed64 left
  | .branchLeft _ second yes no _ => CodeNumbers second ∧ CodeNumbers yes ∧ CodeNumbers no
  | .branchRight _ first yes no _ _ => first < 2^64 ∧ CodeNumbers yes ∧ CodeNumbers no
  | .lendOwner reader continuation _ _ => CodeNumbers reader ∧ CodeNumbers continuation
  | .lendReader _ _ _ _ _ continuation | .lendFinish _ _ _ _ _ continuation => CodeNumbers continuation
  | .lendContinuation _ _ _ result => ValueNumbers result
  | _ => True

def StackNumbers (stack : List Frame) : Prop := ∀ frame ∈ stack, FrameNumbers frame

theorem StackNumbers.empty : StackNumbers [] := by intro frame member; cases member

theorem StackNumbers.cons (stack : StackNumbers rest) (frame : FrameNumbers first) :
    StackNumbers (first :: rest) := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | member
  · exact frame
  · exact stack selected member

theorem StackNumbers.head (stack : StackNumbers (first :: rest)) : FrameNumbers first :=
  stack first List.mem_cons_self

theorem StackNumbers.tail (stack : StackNumbers (first :: rest)) : StackNumbers rest := by
  intro frame member
  exact stack frame (List.mem_cons_of_mem _ member)

def ControlNumbers : Control → Prop
  | .evaluate code => CodeNumbers code
  | .returned value => ValueNumbers value
  | .fault _ => True

def StateNumbers (state : State) : Prop :=
  HeapNumbers state.heap ∧ ControlNumbers state.control ∧ StackNumbers state.stack

def ActionNumbers : Action → Prop
  | .control control stack _ => ControlNumbers control ∧ StackNumbers stack
  | .allocate count fill stack => count < 2^64 ∧ ValueReduction.signed64 fill ∧ StackNumbers stack
  | .read _ index stack => index < 2^64 ∧ StackNumbers stack
  | .free _ rest stack => CodeNumbers rest ∧ StackNumbers stack
  | .lend _ _ _ reader continuation stack => CodeNumbers reader ∧ CodeNumbers continuation ∧ StackNumbers stack
  | .close _ _ result _ _ continuation stack => ValueNumbers result ∧ CodeNumbers continuation ∧ StackNumbers stack
  | .borrow _ _ stack => StackNumbers stack

theorem applyValue_numbers (functionReady : ValueNumbers function)
    (argumentReady : ∀ value, argument = some value → ValueNumbers value)
    (stackReady : StackNumbers stack) : ActionNumbers (applyValue function origin argument stack) := by
  cases functionReady
  all_goals first | exact ⟨True.intro,stackReady⟩ | exact ⟨ValuesNumbers.cons (by assumption) argumentReady,stackReady⟩

theorem applyValue_numbers_retained (functionReady : ValueNumbers function) (argumentReady : ValueNumbers argument)
    (stackReady : StackNumbers stack) : ActionNumbers (applyValue function origin (some argument) stack) :=
  applyValue_numbers functionReady (by intro value same; cases same; exact argumentReady) stackReady

theorem evaluate_action_numbers (codeReady : CodeNumbers code) (stackReady : StackNumbers stack) :
    ActionNumbers (evaluateAction code stack) := by
  fun_cases evaluateAction code stack
  all_goals try simp only [evaluateAction, *]
  all_goals first
    | exact stackReady
    | exact ⟨True.intro,stackReady⟩
    | exact ⟨ValueNumbers.natural (by assumption),stackReady⟩
    | exact ⟨ValueNumbers.integer (by assumption),stackReady⟩
    | exact ⟨ValueNumbers.typeCode,stackReady⟩
    | exact ⟨ValueNumbers.closure codeReady,stackReady⟩
    | exact ⟨codeReady,stackReady.cons codeReady⟩
    | exact ⟨codeReady,stackReady.cons ⟨codeReady,codeReady⟩⟩
    | exact ⟨codeReady,stackReady.cons ⟨codeReady,codeReady,codeReady⟩⟩
    | exact ⟨ValuesNumbers.valueAt codeReady (by assumption),stackReady⟩

theorem return_action_numbers (valueReady : ValueNumbers value) (stackReady : StackNumbers stack)
    (computed : returnAction value stack = some result) : ActionNumbers result := by
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
      all_goals simp only [FrameNumbers] at frameReady
      all_goals first
        | exact ⟨True.intro,restReady⟩
        | exact ⟨True.intro,restReady.cons frameReady⟩
        | exact ⟨frameReady,restReady⟩
        | exact ⟨frameReady,restReady.cons valueReady.naturalBound⟩
        | exact ⟨frameReady,restReady.cons valueReady.integerBound⟩
        | exact ⟨frameReady,restReady.cons valueReady⟩
        | exact ⟨frameReady,restReady.cons True.intro⟩
        | exact ⟨frameReady.1,frameReady.2,restReady⟩
        | exact ⟨valueReady,frameReady,restReady⟩
        | exact ⟨frameReady,valueReady.integerBound,restReady⟩
        | exact ⟨valueReady.naturalBound,restReady⟩
        | exact ⟨frameReady.1,restReady.cons ⟨valueReady.naturalBound,frameReady.2.1,frameReady.2.2⟩⟩
        | exact applyValue_numbers_retained frameReady valueReady restReady
        | exact applyValue_numbers (argument := none) valueReady (by intro candidate same; cases same) restReady
        | exact applyValue_numbers_retained valueReady .reference (restReady.cons frameReady)
        | exact applyValue_numbers_retained valueReady frameReady (restReady.cons True.intro)
        | exact applyValue_numbers_retained valueReady .owner restReady
        | skip
      case h_7 =>
        rename_i left right
        by_cases fit : left + right < 2^64
        · simpa only [fit,↓reduceIte] using (show ActionNumbers (.control (.returned (.natural (left+right))) rest) from
            ⟨ValueNumbers.natural fit,restReady⟩)
        · simpa only [fit,↓reduceIte] using (show ActionNumbers (fault .arithmeticOverflow rest) from ⟨True.intro,restReady⟩)
      case h_9 =>
        rename_i op left right
        by_cases fit : ValueReduction.signed64 (ValueReduction.arithmetic op left right)
        · simpa only [fit,↓reduceIte] using (show ActionNumbers (.control (.returned (.integer (ValueReduction.arithmetic op left right))) rest) from
            ⟨ValueNumbers.integer fit,restReady⟩)
        · simpa only [fit,↓reduceIte] using (show ActionNumbers (fault .arithmeticOverflow rest) from ⟨True.intro,restReady⟩)
      case h_14 =>
        rename_i equal left yes no firstOrigin secondOrigin right
        by_cases compared : (if equal then left == right else decide (left < right)) = true
        · simp only [compared,↓reduceIte]
          exact ⟨frameReady.2.1.branch equal firstOrigin secondOrigin,restReady⟩
        · simp only [compared]
          exact ⟨frameReady.2.2,restReady⟩

theorem action_numbers (control : ControlNumbers state.control) (stack : StackNumbers state.stack)
    (chosen : action state = some next) : ActionNumbers next := by
  cases state with
  | mk heap current frames =>
      cases current with
      | evaluate code =>
          have same : evaluateAction code frames = next := Option.some.inj chosen
          rw [← same]
          exact evaluate_action_numbers control stack
      | returned value => exact return_action_numbers control stack chosen
      | fault reason => cases chosen

theorem execute_numbers (heapReady : HeapNumbers heap) (aligned : ActionNumbers next) :
    StateNumbers (execute heap next).1 := by
  cases next with
  | control control stack activation => exact ⟨heapReady,aligned⟩
  | allocate count fill stack =>
      simp only [execute]
      split
      · rename_i fits
        exact ⟨heapReady.allocate aligned.2.1 fits,ValueNumbers.owner,aligned.2.2⟩
      · exact ⟨heapReady,True.intro,aligned.2.2⟩
  | free object rest stack =>
      simp only [execute]
      split
      · split
        · exact ⟨⟨heapReady.payload,heapReady.length⟩,aligned⟩
        · exact ⟨heapReady,True.intro,aligned.2⟩
      · exact ⟨heapReady,True.intro,aligned.2⟩
  | lend object name origin reader continuation stack =>
      simp only [execute]
      split
      · exact ⟨⟨heapReady.payload,heapReady.length⟩,aligned.1,aligned.2.2.cons aligned.2.1⟩
      · exact ⟨heapReady,True.intro,aligned.2.2⟩
  | close token object result origin resultOrigin continuation stack =>
      simp only [execute]
      split
      · exact ⟨⟨heapReady.payload,heapReady.length⟩,aligned.2.1,aligned.2.2.cons aligned.1⟩
      · exact ⟨heapReady,True.intro,aligned.2.2⟩
  | borrow key object stack =>
      simp only [execute]
      split
      · split
        · exact ⟨heapReady,ValueNumbers.reference,aligned⟩
        · exact ⟨heapReady,True.intro,aligned⟩
      · exact ⟨heapReady,True.intro,aligned⟩
  | read token index stack =>
      simp only [execute]
      split
      · rename_i object leased
        split
        · exact ⟨heapReady,ValueNumbers.integer (decode_integer_bound (heapReady.payload object)),aligned.2⟩
        · exact ⟨heapReady,True.intro,aligned.2⟩
      · exact ⟨heapReady,True.intro,aligned.2⟩

theorem step_numbers (bounded : StateNumbers state) (stepped : step state = some (next,event)) :
    StateNumbers next := by
  obtain ⟨nextAction,chosen,same⟩ := Option.map_eq_some_iff.mp stepped
  simpa only [same] using execute_numbers bounded.1 (action_numbers bounded.2.1 bounded.2.2 chosen)

theorem run_numbers (bounded : StateNumbers state) (fuel : Nat) : StateNumbers (run fuel state).state := by
  induction fuel generalizing state with
  | zero => exact bounded
  | succ fuel ih =>
      simp only [run]
      cases observed : step state with
      | none => exact bounded
      | some result =>
          obtain ⟨next,event⟩ := result
          exact ih (step_numbers bounded observed)

theorem initial_numbers (term : Term) : StateNumbers (initial term) :=
  ⟨HeapNumbers.empty,ValuesNumbers.nil,StackNumbers.empty⟩

/-- Numeric widths and heap payload/length bounds hold at every actual prefix,
including faults and exhausted fuel, through arbitrary computed closures and
nested readers. No source syntax subset or successful-result premise is used. -/
theorem initial_run_numbers (term : Term) (fuel : Nat) : StateNumbers (run fuel (initial term)).state :=
  run_numbers (initial_numbers term) fuel

theorem initial_run_natural_bound (term : Term) (fuel : Nat)
    (returned : (run fuel (initial term)).state.control = .returned (.natural value)) : value < 2^64 := by
  have bounded := (initial_run_numbers term fuel).2.1
  rw [returned] at bounded
  exact ValueNumbers.naturalBound bounded

theorem initial_run_integer_bound (term : Term) (fuel : Nat)
    (returned : (run fuel (initial term)).state.control = .returned (.integer value)) : ValueReduction.signed64 value := by
  have bounded := (initial_run_numbers term fuel).2.1
  rw [returned] at bounded
  exact ValueNumbers.integerBound bounded

theorem initial_run_code_numbers (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code) : CodeNumbers code := by
  have bounded := (initial_run_numbers term fuel).2.1
  simpa only [evaluating,ControlNumbers] using bounded

theorem initial_run_slot_natural_bound {index : Nat} (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (stored : code.values[index]? = some (some (.natural value))) : value < 2^64 :=
  (ValuesNumbers.valueAt (initial_run_code_numbers term fuel evaluating) stored).naturalBound

theorem initial_run_heap_numbers (term : Term) (fuel : Nat) : HeapNumbers (run fuel (initial term)).state.heap :=
  (initial_run_numbers term fuel).1

/-- The native I64 literal typing is constructed from actual reachable heap
contents, not an externally supplied post-value typing certificate. -/
theorem initial_run_decoded_integer_typed (term : Term) (fuel object : Nat) :
    LoanTyping.HasType env [] [] true
      (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object))) .i64 := by
  have bounded := decode_integer_bound ((initial_run_heap_numbers term fuel).payload object)
  exact .integer bounded.1 bounded.2

end Jihoo.NativeKernel.Environment.BindingMachine
