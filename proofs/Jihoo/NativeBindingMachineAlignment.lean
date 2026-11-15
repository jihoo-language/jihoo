import Jihoo.NativeBindingMachineLoanTyping

/-! Captured runtime slots retain their actual source erasure flags throughout
all machine execution, including computed closures and nested readers. This is
a value/context/control-stack invariant, not semantic heap typing of values. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

mutual
  inductive ValueAligned : Value → Prop where
    | natural : ValueAligned (.natural value)
    | integer : ValueAligned (.integer value)
    | typeCode : ValueAligned (.typeCode source)
    | owner : ValueAligned (.owner object)
    | reference : ValueAligned (.reference token)
    | closure : SlotsAligned context captured →
        ValueAligned (.closure erased domain body context origins captured)

  inductive SlotsAligned : Context → List (Option Value) → Prop where
    | nil : SlotsAligned [] []
    | erased : SlotsAligned context values →
        SlotsAligned (⟨domain,true⟩ :: context) (none :: values)
    | retained : ValueAligned value → SlotsAligned context values →
        SlotsAligned (⟨domain,false⟩ :: context) (some value :: values)
end

def CodeAligned (code : Code) : Prop := SlotsAligned code.context code.values

theorem SlotsAligned.ready (aligned : SlotsAligned context values) : Ready context values := by
  induction context generalizing values with
  | nil => cases aligned; exact .empty
  | cons binding context ih =>
      cases aligned with
      | erased previous => exact (ih previous).cons rfl
      | retained value previous => exact (ih previous).cons rfl

theorem SlotsAligned.valueAt {index : Nat} (aligned : SlotsAligned context values)
    (found : values[index]? = some (some value)) : ValueAligned value := by
  induction context generalizing values index with
  | nil => cases aligned; simp at found
  | cons binding context ih =>
      cases aligned with
      | erased previous => cases index with
          | zero => cases found
          | succ index => exact ih previous found
      | retained ready previous => cases index with
          | zero =>
              simp only [List.getElem?_cons_zero,Option.some.injEq] at found
              subst value
              exact ready
          | succ index => exact ih previous found

theorem SlotsAligned.enter {erased : Bool} (aligned : SlotsAligned context values)
    (argumentAligned : ∀ value, argument = some value → ValueAligned value)
    (flag : argument.isNone = erased) :
    SlotsAligned (⟨domain,erased⟩ :: context) (argument :: values) := by
  cases argument with
  | none => have same : erased = true := flag.symm; subst erased; exact .erased aligned
  | some value =>
      have same : erased = false := flag.symm
      subst erased
      exact .retained (argumentAligned value rfl) aligned

theorem CodeAligned.child (aligned : CodeAligned code) (term : Term) : CodeAligned (code.child term) := aligned

theorem CodeAligned.branch (aligned : CodeAligned code) (equal : Bool) (first second : Term) :
    CodeAligned (branchCode equal code first second) := .erased aligned

def RelevantFunction : Value → Prop
  | .closure erased _ _ _ _ _ => erased = false
  | _ => True

def FrameAligned : Frame → Prop
  | .function code | .strict code | .addLeft code | .arithmeticLeft _ code |
      .allocateCount code | .free code | .indexReference code => CodeAligned code
  | .argument function _ => ValueAligned function ∧ RelevantFunction function
  | .branchLeft _ second yes no _ => CodeAligned second ∧ CodeAligned yes ∧ CodeAligned no
  | .branchRight _ _ yes no _ _ => CodeAligned yes ∧ CodeAligned no
  | .lendOwner reader continuation _ _ => CodeAligned reader ∧ CodeAligned continuation
  | .lendReader _ _ _ _ _ continuation | .lendFinish _ _ _ _ _ continuation => CodeAligned continuation
  | .lendContinuation _ _ _ result => ValueAligned result
  | _ => True

def StackAligned (stack : List Frame) : Prop := ∀ frame ∈ stack, FrameAligned frame

theorem StackAligned.empty : StackAligned [] := by intro frame member; cases member

theorem StackAligned.cons (stack : StackAligned rest) (frame : FrameAligned first) :
    StackAligned (first :: rest) := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | member
  · exact frame
  · exact stack selected member

theorem StackAligned.head (stack : StackAligned (first :: rest)) : FrameAligned first :=
  stack first List.mem_cons_self

theorem StackAligned.tail (stack : StackAligned (first :: rest)) : StackAligned rest := by
  intro frame member
  exact stack frame (List.mem_cons_of_mem _ member)

def ControlAligned : Control → Prop
  | .evaluate code => CodeAligned code
  | .returned value => ValueAligned value
  | .fault _ => True

def StateAligned (state : State) : Prop := ControlAligned state.control ∧ StackAligned state.stack

def ActionAligned : Action → Prop
  | .control control stack _ => ControlAligned control ∧ StackAligned stack
  | .free _ rest stack => CodeAligned rest ∧ StackAligned stack
  | .lend _ _ _ reader continuation stack => CodeAligned reader ∧ CodeAligned continuation ∧ StackAligned stack
  | .close _ _ result _ _ continuation stack => ValueAligned result ∧ CodeAligned continuation ∧ StackAligned stack
  | .allocate _ _ stack | .borrow _ _ stack | .read _ _ stack => StackAligned stack

theorem applyValue_aligned (functionReady : ValueAligned function)
    (argumentReady : ∀ value, argument = some value → ValueAligned value)
    (flag : match function with | .closure erased _ _ _ _ _ => argument.isNone = erased | _ => True)
    (stackReady : StackAligned stack) : ActionAligned (applyValue function origin argument stack) := by
  cases functionReady
  all_goals first | exact ⟨True.intro,stackReady⟩ | exact ⟨SlotsAligned.enter (by assumption) argumentReady flag,stackReady⟩

theorem applyValue_retained_aligned (functionReady : ValueAligned function)
    (relevant : RelevantFunction function) (argumentReady : ValueAligned argument)
    (stackReady : StackAligned stack) : ActionAligned (applyValue function origin (some argument) stack) := by
  apply applyValue_aligned functionReady (by intro value same; cases same; exact argumentReady) ?_ stackReady
  cases function <;> simp_all [RelevantFunction]

theorem evaluate_action_aligned (codeReady : CodeAligned code) (stackReady : StackAligned stack) :
    ActionAligned (evaluateAction code stack) := by
  fun_cases evaluateAction code stack
  all_goals try simp only [evaluateAction, *]
  all_goals first
    | exact stackReady
    | exact ⟨True.intro,stackReady⟩
    | exact ⟨ValueAligned.natural,stackReady⟩
    | exact ⟨ValueAligned.integer,stackReady⟩
    | exact ⟨ValueAligned.typeCode,stackReady⟩
    | exact ⟨ValueAligned.closure codeReady,stackReady⟩
    | exact ⟨codeReady,stackReady.cons codeReady⟩
    | exact ⟨codeReady,stackReady.cons ⟨codeReady,codeReady⟩⟩
    | exact ⟨codeReady,stackReady.cons ⟨codeReady,codeReady,codeReady⟩⟩
    | exact ⟨SlotsAligned.valueAt codeReady (by assumption),stackReady⟩

theorem return_action_aligned (valueReady : ValueAligned value) (stackReady : StackAligned stack)
    (computed : returnAction value stack = some result) : ActionAligned result := by
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
      all_goals simp only [FrameAligned] at frameReady
      all_goals first
        | exact restReady
        | exact ⟨True.intro,restReady⟩
        | exact ⟨True.intro,restReady.cons frameReady⟩
        | exact ⟨frameReady,restReady⟩
        | exact ⟨frameReady,restReady.cons True.intro⟩
        | exact ⟨frameReady,restReady.cons ⟨valueReady,rfl⟩⟩
        | exact ⟨frameReady.1,restReady.cons frameReady.2⟩
        | exact ⟨frameReady.1,frameReady.2,restReady⟩
        | exact ⟨valueReady,frameReady,restReady⟩
        | exact applyValue_retained_aligned frameReady.1 frameReady.2 valueReady restReady
        | exact applyValue_aligned (argument := none) valueReady (by intro candidate same; cases same) rfl restReady
        | exact applyValue_retained_aligned valueReady rfl .reference (restReady.cons frameReady)
        | exact applyValue_retained_aligned valueReady rfl frameReady (restReady.cons True.intro)
        | exact applyValue_retained_aligned valueReady rfl .owner restReady
        | skip
      case h_7 =>
        rename_i left right
        by_cases fit : left + right < 2^64
        · simpa only [fit,↓reduceIte] using (show ActionAligned (.control (.returned (.natural (left+right))) rest) from
            ⟨ValueAligned.natural,restReady⟩)
        · simpa only [fit,↓reduceIte] using (show ActionAligned (fault .arithmeticOverflow rest) from ⟨True.intro,restReady⟩)
      case h_9 =>
        rename_i op left right
        by_cases fit : ValueReduction.signed64 (ValueReduction.arithmetic op left right)
        · simpa only [fit,↓reduceIte] using (show ActionAligned (.control (.returned (.integer (ValueReduction.arithmetic op left right))) rest) from
            ⟨ValueAligned.integer,restReady⟩)
        · simpa only [fit,↓reduceIte] using (show ActionAligned (fault .arithmeticOverflow rest) from ⟨True.intro,restReady⟩)
      case h_14 =>
        rename_i equal left yes no firstOrigin secondOrigin right
        by_cases compared : (if equal then left == right else decide (left < right)) = true
        · simp only [compared,↓reduceIte]
          exact ⟨frameReady.1.branch equal firstOrigin secondOrigin,restReady⟩
        · simp only [compared]
          exact ⟨frameReady.2,restReady⟩

theorem action_aligned (aligned : StateAligned state) (chosen : action state = some next) :
    ActionAligned next := by
  cases state with
  | mk heap control stack =>
      cases control with
      | evaluate code =>
          have same : evaluateAction code stack = next := Option.some.inj chosen
          rw [← same]
          exact evaluate_action_aligned aligned.1 aligned.2
      | returned value => exact return_action_aligned aligned.1 aligned.2 chosen
      | fault reason => cases chosen

theorem execute_aligned (aligned : ActionAligned next) : StateAligned (execute heap next).1 := by
  cases next with
  | control control stack activation => exact aligned
  | allocate count fill stack =>
      simp only [execute]
      split
      · exact ⟨ValueAligned.owner,aligned⟩
      · exact ⟨True.intro,aligned⟩
  | free object rest stack =>
      simp only [execute]
      split
      · split
        · exact aligned
        · exact ⟨True.intro,aligned.2⟩
      · exact ⟨True.intro,aligned.2⟩
  | lend object name origin reader continuation stack =>
      simp only [execute]
      split
      · exact ⟨aligned.1,aligned.2.2.cons aligned.2.1⟩
      · exact ⟨True.intro,aligned.2.2⟩
  | close token object result origin resultOrigin continuation stack =>
      simp only [execute]
      split
      · exact ⟨aligned.2.1,aligned.2.2.cons aligned.1⟩
      · exact ⟨True.intro,aligned.2.2⟩
  | borrow key object stack =>
      simp only [execute]
      split
      · split
        · exact ⟨ValueAligned.reference,aligned⟩
        · exact ⟨True.intro,aligned⟩
      · exact ⟨True.intro,aligned⟩
  | read token index stack =>
      simp only [execute]
      split
      · split
        · exact ⟨ValueAligned.integer,aligned⟩
        · exact ⟨True.intro,aligned⟩
      · exact ⟨True.intro,aligned⟩

theorem step_aligned (aligned : StateAligned state) (stepped : step state = some (next,event)) :
    StateAligned next := by
  obtain ⟨nextAction,chosen,same⟩ := Option.map_eq_some_iff.mp stepped
  simpa only [same] using execute_aligned (heap := state.heap) (action_aligned aligned chosen)

theorem run_aligned (aligned : StateAligned state) (fuel : Nat) :
    StateAligned (run fuel state).state := by
  induction fuel generalizing state with
  | zero => exact aligned
  | succ fuel ih =>
      simp only [run]
      cases observed : step state with
      | none => exact aligned
      | some result =>
          obtain ⟨next,event⟩ := result
          exact ih (step_aligned aligned observed)

theorem initial_aligned (term : Term) (heap : SizedBufferHeap.State) : StateAligned (initial term heap) :=
  ⟨SlotsAligned.nil,StackAligned.empty⟩

/-- This uses the actual machine from an empty source context, at every fuel
and with any initial heap. Neither input typing nor successful evaluation is
required for structural slot/erasure preservation. -/
theorem initial_run_aligned (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State) :
    StateAligned (run fuel (initial term heap)).state := run_aligned (initial_aligned term heap) fuel

theorem ValueAligned.captures (aligned : ValueAligned (.closure erased domain body context origins captured)) :
    SlotsAligned context captured := by cases aligned; assumption

theorem initial_run_code_aligned (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State)
    (evaluating : (run fuel (initial term heap)).state.control = .evaluate code) : CodeAligned code := by
  have aligned := (initial_run_aligned term fuel heap).1
  simpa only [evaluating,ControlAligned] using aligned

theorem initial_run_closure_captures (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State)
    (returned : (run fuel (initial term heap)).state.control =
      .returned (.closure erased domain body context origins captured)) : SlotsAligned context captured := by
  have aligned := (initial_run_aligned term fuel heap).1
  rw [returned] at aligned
  exact ValueAligned.captures aligned

/-- Full Loan64 input variable typing and actual reachability construct the
next returned runtime value. Captured-slot readiness is derived from execution,
not supplied independently by the caller. -/
theorem initial_run_code_variable_step (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State)
    (evaluating : (run fuel (initial term heap)).state.control = .evaluate code)
    (typed : LoanTyping.HasType env loans code.context false code.term type)
    (shape : code.term = .var index) :
    ∃ value, ValueAligned value ∧ step (run fuel (initial term heap)).state = some
      (⟨(run fuel (initial term heap)).state.heap,.returned value,
        (run fuel (initial term heap)).state.stack⟩,none) := by
  rw [shape] at typed
  obtain ⟨binding,selected,relevant⟩ := loan_code_variable_permission typed
  have aligned := initial_run_code_aligned term fuel heap evaluating
  obtain ⟨option,stored,flag⟩ := SlotsAligned.ready aligned index binding selected
  cases option with
  | none => simp [relevant] at flag
  | some value =>
      refine ⟨value,SlotsAligned.valueAt aligned stored,?_⟩
      simp only [step,action,evaluating,evaluateAction,shape,stored,Option.map_some,execute,Option.map_none]

end Jihoo.NativeKernel.Environment.BindingMachine
