import Jihoo.NativeBindingMachineReaderState

/-! Every reference token retained by actual control, frames or recursively
captured closures predates the current lease counter. Concrete reader and Index
frame tokens are covered as well. A newly issued reader token is consequently
absent from previously saved values and frames. This is structural provenance,
not reference liveness, source typing or a theorem that reader results cannot
escape with the token they were just given. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

mutual
  inductive ValueReferences (limit : Nat) : Value → Prop where
    | natural : ValueReferences limit (.natural value)
    | integer : ValueReferences limit (.integer value)
    | typeCode : ValueReferences limit (.typeCode source)
    | array : ValueReferences limit (.array elements)
    | owner : ValueReferences limit (.owner object)
    | reference : token < limit → ValueReferences limit (.reference token)
    | closure : ValuesReferences limit captured →
        ValueReferences limit (.closure erased domain body context origins captured)
  inductive ValuesReferences (limit : Nat) : List (Option Value) → Prop where
    | nil : ValuesReferences limit []
    | erased : ValuesReferences limit values → ValuesReferences limit (none :: values)
    | retained : ValueReferences limit value → ValuesReferences limit values →
        ValuesReferences limit (some value :: values)
end

theorem ValueReferences.referenceBound (ready : ValueReferences limit (.reference token)) : token < limit := by
  cases ready; assumption

theorem ValueReferences.mono (ready : ValueReferences before value) (grows : before ≤ after) :
    ValueReferences after value := by
  apply ValueReferences.rec (t := ready)
    (motive_1 := fun value _ => ValueReferences after value)
    (motive_2 := fun values _ => ValuesReferences after values)
  all_goals intros
  all_goals first
    | exact .natural | exact .integer | exact .typeCode | exact .array | exact .owner
    | exact .reference (by omega) | exact .closure (by assumption)
    | exact .nil | exact .erased (by assumption) | exact .retained (by assumption) (by assumption)

theorem ValuesReferences.mono (ready : ValuesReferences before values) (grows : before ≤ after) :
    ValuesReferences after values := by
  induction values with
  | nil => exact .nil
  | cons value rest ih =>
      cases ready with
      | erased previous => exact .erased (ih previous)
      | retained first previous => exact .retained (first.mono grows) (ih previous)

theorem ValuesReferences.valueAt {index : Nat} (ready : ValuesReferences limit values)
    (found : values[index]? = some (some value)) : ValueReferences limit value := by
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

theorem ValuesReferences.cons (ready : ValuesReferences limit values)
    (argumentReady : ∀ value, argument = some value → ValueReferences limit value) :
    ValuesReferences limit (argument :: values) := by
  cases argument with
  | none => exact .erased ready
  | some value => exact .retained (argumentReady value rfl) ready

def CodeReferences (limit : Nat) (code : Code) : Prop := ValuesReferences limit code.values

theorem CodeReferences.mono (ready : CodeReferences before code) (grows : before ≤ after) :
    CodeReferences after code := ValuesReferences.mono ready grows

theorem CodeReferences.branch (ready : CodeReferences limit code) (equal : Bool) (first second : Term) :
    CodeReferences limit (branchCode equal code first second) := .erased ready

def FrameReferences (limit : Nat) : Frame → Prop
  | .function code | .strict code | .addLeft code | .arithmeticLeft _ code |
      .allocateCount code | .free code | .indexReference code => CodeReferences limit code
  | .argument function _ => ValueReferences limit function
  | .branchLeft _ second yes no _ =>
      CodeReferences limit second ∧ CodeReferences limit yes ∧ CodeReferences limit no
  | .branchRight _ _ yes no _ _ => CodeReferences limit yes ∧ CodeReferences limit no
  | .lendOwner reader continuation _ _ => CodeReferences limit reader ∧ CodeReferences limit continuation
  | .lendReader token _ _ _ _ continuation | .lendFinish token _ _ _ _ continuation =>
      token < limit ∧ CodeReferences limit continuation
  | .lendContinuation _ _ _ result => ValueReferences limit result
  | .indexOffset token => token < limit
  | _ => True

theorem FrameReferences.mono (ready : FrameReferences before frame) (grows : before ≤ after) :
    FrameReferences after frame := by
  cases frame <;> simp only [FrameReferences] at ready ⊢
  all_goals first
    | trivial | exact ready.mono grows | omega
    | exact ⟨ready.1.mono grows,ready.2.mono grows⟩
    | exact ⟨ready.1.mono grows,ready.2.1.mono grows,ready.2.2.mono grows⟩
    | exact ⟨by omega,ready.2.mono grows⟩

def StackReferences (limit : Nat) (stack : List Frame) : Prop :=
  ∀ frame ∈ stack, FrameReferences limit frame

theorem StackReferences.empty : StackReferences limit [] := by intro frame member; cases member

theorem StackReferences.cons (ready : StackReferences limit rest) (firstReady : FrameReferences limit first) :
    StackReferences limit (first :: rest) := by
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact firstReady
  · exact ready frame member

theorem StackReferences.head (ready : StackReferences limit (first :: rest)) :
    FrameReferences limit first := ready first List.mem_cons_self

theorem StackReferences.tail (ready : StackReferences limit (first :: rest)) : StackReferences limit rest := by
  intro frame member
  exact ready frame (List.mem_cons_of_mem _ member)

theorem StackReferences.mono (ready : StackReferences before stack) (grows : before ≤ after) :
    StackReferences after stack := by
  intro frame member
  exact (ready frame member).mono grows

def ControlReferences (limit : Nat) : Control → Prop
  | .evaluate code => CodeReferences limit code
  | .returned value => ValueReferences limit value
  | .fault _ => True

def StateReferences (state : State) : Prop :=
  ControlReferences state.heap.heap.nextLease state.control ∧
    StackReferences state.heap.heap.nextLease state.stack

def ActionReferences (limit : Nat) : Action → Prop
  | .control control stack _ => ControlReferences limit control ∧ StackReferences limit stack
  | .allocate _ _ stack | .borrow _ _ stack => StackReferences limit stack
  | .free _ rest stack => CodeReferences limit rest ∧ StackReferences limit stack
  | .lend _ _ _ reader continuation stack =>
      CodeReferences limit reader ∧ CodeReferences limit continuation ∧ StackReferences limit stack
  | .close token _ result _ _ continuation stack =>
      token < limit ∧ ValueReferences limit result ∧ CodeReferences limit continuation ∧ StackReferences limit stack
  | .read token _ stack => token < limit ∧ StackReferences limit stack

theorem applyValue_references (functionReady : ValueReferences limit function)
    (argumentReady : ∀ value, argument = some value → ValueReferences limit value)
    (stackReady : StackReferences limit stack) :
    ActionReferences limit (applyValue function origin argument stack) := by
  cases functionReady
  all_goals first
    | exact ⟨True.intro,stackReady⟩
    | exact ⟨ValuesReferences.cons (by assumption) argumentReady,stackReady⟩

theorem applyValue_references_retained (functionReady : ValueReferences limit function)
    (argumentReady : ValueReferences limit argument) (stackReady : StackReferences limit stack) :
    ActionReferences limit (applyValue function origin (some argument) stack) :=
  applyValue_references functionReady (by intro value same; cases same; exact argumentReady) stackReady

theorem evaluate_action_references (codeReady : CodeReferences limit code)
    (stackReady : StackReferences limit stack) : ActionReferences limit (evaluateAction code stack) := by
  fun_cases evaluateAction code stack
  all_goals try simp only [evaluateAction, *]
  all_goals first
    | exact ⟨True.intro,stackReady⟩
    | exact ⟨ValueReferences.natural,stackReady⟩
    | exact ⟨ValueReferences.integer,stackReady⟩
    | exact ⟨ValueReferences.typeCode,stackReady⟩
    | exact ⟨ValueReferences.closure codeReady,stackReady⟩
    | exact ⟨codeReady,stackReady.cons codeReady⟩
    | exact ⟨codeReady,stackReady.cons ⟨codeReady,codeReady⟩⟩
    | exact ⟨codeReady,stackReady.cons ⟨codeReady,codeReady,codeReady⟩⟩
    | exact ⟨ValuesReferences.valueAt codeReady (by assumption),stackReady⟩
    | exact stackReady

theorem return_action_references (valueReady : ValueReferences limit value)
    (stackReady : StackReferences limit stack) (computed : returnAction value stack = some result) :
    ActionReferences limit result := by
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
      all_goals simp only [FrameReferences] at frameReady
      all_goals first
        | exact ⟨True.intro,restReady⟩
        | exact ⟨True.intro,restReady.cons frameReady⟩
        | exact ⟨frameReady,restReady⟩
        | exact ⟨frameReady,restReady.cons valueReady⟩
        | exact ⟨frameReady,restReady.cons True.intro⟩
        | exact ⟨frameReady,restReady.cons valueReady.referenceBound⟩
        | exact restReady
        | exact ⟨frameReady.1,frameReady.2,restReady⟩
        | exact ⟨frameReady.1,valueReady,frameReady.2,restReady⟩
        | exact ⟨frameReady.1,restReady.cons frameReady.2⟩
        | exact applyValue_references_retained frameReady valueReady restReady
        | exact applyValue_references (argument := none) valueReady (by intro candidate same; cases same) restReady
        | exact applyValue_references_retained valueReady (.reference frameReady.1) (restReady.cons frameReady)
        | exact applyValue_references_retained valueReady frameReady (restReady.cons True.intro)
        | exact applyValue_references_retained valueReady .owner restReady
        | skip
      case h_7 => split <;> first | exact ⟨ValueReferences.natural,restReady⟩ | exact ⟨True.intro,restReady⟩
      case h_9 => split <;> first | exact ⟨ValueReferences.integer,restReady⟩ | exact ⟨True.intro,restReady⟩
      case h_14 =>
        rename_i equal left yes no firstOrigin secondOrigin right
        by_cases compared : (if equal then left == right else decide (left < right)) = true
        · simp only [compared,↓reduceIte]
          exact ⟨frameReady.1.branch equal firstOrigin secondOrigin,restReady⟩
        · simp only [compared]
          exact ⟨frameReady.2,restReady⟩
      all_goals split <;> first | exact ⟨ValueReferences.integer,restReady⟩ | exact ⟨True.intro,restReady⟩

theorem action_references (control : ControlReferences limit state.control)
    (stack : StackReferences limit state.stack) (chosen : action state = some next) :
    ActionReferences limit next := by
  cases state with
  | mk heap current frames =>
      cases current with
      | evaluate code =>
          have same : evaluateAction code frames = next := Option.some.inj chosen
          rw [← same]
          exact evaluate_action_references control stack
      | returned value => exact return_action_references control stack chosen
      | fault reason => cases chosen

theorem execute_references (valid : SizedBufferHeap.Valid heap)
    (ready : ActionReferences heap.heap.nextLease next) : StateReferences (execute heap next).1 := by
  cases next with
  | control control stack activation => exact ready
  | allocate count fill stack =>
      simp only [execute]
      split
      · exact ⟨ValueReferences.owner,ready⟩
      · exact ⟨True.intro,ready⟩
  | free object rest stack =>
      simp only [execute]
      split
      · split
        · exact ready
        · exact ⟨True.intro,ready.2⟩
      · exact ⟨True.intro,ready.2⟩
  | lend object name origin reader continuation stack =>
      simp only [execute]
      split
      · exact ⟨ready.1.mono (Nat.le_succ _),
          (ready.2.2.mono (Nat.le_succ _)).cons ⟨Nat.lt_succ_self _,ready.2.1.mono (Nat.le_succ _)⟩⟩
      · exact ⟨True.intro,ready.2.2⟩
  | close token object result origin resultOrigin continuation stack =>
      simp only [execute]
      split
      · exact ⟨ready.2.2.1,ready.2.2.2.cons ready.2.1⟩
      · exact ⟨True.intro,ready.2.2.2⟩
  | borrow key object stack =>
      simp only [execute]
      split
      · rename_i token selected
        split
        · rename_i leased
          exact ⟨ValueReferences.reference (valid.leased token object leased).1,ready⟩
        · exact ⟨True.intro,ready⟩
      · exact ⟨True.intro,ready⟩
  | read token index stack =>
      simp only [execute]
      split
      · split
        · exact ⟨ValueReferences.integer,ready.2⟩
        · exact ⟨True.intro,ready.2⟩
      · exact ⟨True.intro,ready.2⟩

theorem step_references (valid : SizedBufferHeap.Valid state.heap) (ready : StateReferences state)
    (stepped : step state = some (next,event)) : StateReferences next := by
  obtain ⟨nextAction,chosen,same⟩ := Option.map_eq_some_iff.mp stepped
  simpa only [same] using execute_references valid (action_references ready.1 ready.2 chosen)

theorem run_references (valid : SizedBufferHeap.Valid state.heap) (ready : StateReferences state)
    (fuel : Nat) : StateReferences (run fuel state).state := by
  induction fuel generalizing state with
  | zero => exact ready
  | succ fuel ih =>
      simp only [run]
      cases observed : step state with
      | none => exact ready
      | some result =>
          obtain ⟨next,event⟩ := result
          have nextValid := SizedBufferHeap.steps_valid valid (step_heap_steps valid observed)
          exact ih nextValid (step_references valid ready observed)

/-- All prefixes, including faults and fuel exhaustion. The bound includes
references inside recursively captured closures, saved Code, and concrete
reader/Index frame fields; it makes no current-liveness claim. -/
theorem initial_run_references (term : Term) (fuel : Nat) :
    StateReferences (run fuel (initial term)).state :=
  run_references (state := initial term) SizedBufferHeap.empty_valid
    ⟨ValuesReferences.nil,StackReferences.empty⟩ fuel

inductive ReferenceOccurs (token : Nat) : Value → Prop where
  | reference : ReferenceOccurs token (.reference token)
  | closure {index : Nat} : captured[index]? = some (some value) → ReferenceOccurs token value →
      ReferenceOccurs token (.closure erased domain body context origins captured)

theorem ReferenceOccurs.before_limit (occurs : ReferenceOccurs token value)
    (ready : ValueReferences limit value) : token < limit := by
  induction occurs with
  | reference => exact ready.referenceBound
  | closure stored inside ih =>
      cases ready with
      | closure captured => exact ih (captured.valueAt stored)

theorem ValueReferences.fresh_absent (ready : ValueReferences limit value) : ¬ ReferenceOccurs limit value := by
  intro occurs
  have earlier := occurs.before_limit ready
  omega

def CodeReferenceOccurs (token : Nat) (code : Code) : Prop :=
  ∃ (index : Nat) (value : Value), code.values[index]? = some (some value) ∧ ReferenceOccurs token value

theorem CodeReferenceOccurs.before_limit (occurs : CodeReferenceOccurs token code)
    (ready : CodeReferences limit code) : token < limit := by
  obtain ⟨index,value,stored,inside⟩ := occurs
  exact inside.before_limit (ValuesReferences.valueAt ready stored)

theorem CodeReferences.fresh_absent (ready : CodeReferences limit code) : ¬ CodeReferenceOccurs limit code := by
  intro occurs
  have earlier := occurs.before_limit ready
  omega

def FrameReferenceOccurs (token : Nat) : Frame → Prop
  | .function code | .strict code | .addLeft code | .arithmeticLeft _ code |
      .allocateCount code | .free code | .indexReference code => CodeReferenceOccurs token code
  | .argument function _ => ReferenceOccurs token function
  | .branchLeft _ second yes no _ =>
      CodeReferenceOccurs token second ∨ CodeReferenceOccurs token yes ∨ CodeReferenceOccurs token no
  | .branchRight _ _ yes no _ _ => CodeReferenceOccurs token yes ∨ CodeReferenceOccurs token no
  | .lendOwner reader continuation _ _ => CodeReferenceOccurs token reader ∨ CodeReferenceOccurs token continuation
  | .lendReader selected _ _ _ _ continuation | .lendFinish selected _ _ _ _ continuation =>
      selected = token ∨ CodeReferenceOccurs token continuation
  | .lendContinuation _ _ _ result => ReferenceOccurs token result
  | .indexOffset selected => selected = token
  | _ => False

theorem FrameReferenceOccurs.before_limit (occurs : FrameReferenceOccurs token frame)
    (ready : FrameReferences limit frame) : token < limit := by
  cases frame <;> simp only [FrameReferenceOccurs,FrameReferences] at occurs ready
  all_goals first
    | contradiction
    | exact occurs.before_limit ready
    | omega
    | rcases occurs with first | second
      · exact first.before_limit ready.1
      · exact second.before_limit ready.2
    | rcases occurs with first | second | third
      · exact first.before_limit ready.1
      · exact second.before_limit ready.2.1
      · exact third.before_limit ready.2.2
    | rcases occurs with same | inside
      · omega
      · exact inside.before_limit ready.2

theorem FrameReferences.fresh_absent (ready : FrameReferences limit frame) :
    ¬ FrameReferenceOccurs limit frame := by
  intro occurs
  have earlier := occurs.before_limit ready
  omega

theorem StackReferences.fresh_absent (ready : StackReferences limit stack) (member : frame ∈ stack) :
    ¬ FrameReferenceOccurs limit frame := (ready frame member).fresh_absent

theorem initial_run_captured_reference_bound {index : Nat} (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (stored : code.values[index]? = some (some value)) (occurs : ReferenceOccurs token value) :
    token < (run fuel (initial term)).state.heap.heap.nextLease := by
  have ready := (initial_run_references term fuel).1
  rw [evaluating] at ready
  exact occurs.before_limit (ValuesReferences.valueAt ready stored)

/-- A newly issued reader token is absent from every old recursively captured
value of the current Code, even when previous references have already closed. -/
theorem initial_run_fresh_reference_not_captured {index : Nat} (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (stored : code.values[index]? = some (some value)) :
    ¬ ReferenceOccurs (run fuel (initial term)).state.heap.heap.nextLease value := by
  intro occurs
  have earlier := initial_run_captured_reference_bound term fuel evaluating stored occurs
  omega

theorem initial_run_fresh_reference_not_in_code (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code) :
    ¬ CodeReferenceOccurs (run fuel (initial term)).state.heap.heap.nextLease code := by
  have ready := (initial_run_references term fuel).1
  rw [evaluating] at ready
  exact CodeReferences.fresh_absent ready

/-- This applies before a reader starts: every outer frame, including its saved
closures/Code and its concrete reader/Index token, excludes the future token. -/
theorem initial_run_fresh_reference_not_in_frame (term : Term) (fuel : Nat)
    (member : frame ∈ (run fuel (initial term)).state.stack) :
    ¬ FrameReferenceOccurs (run fuel (initial term)).state.heap.heap.nextLease frame :=
  (initial_run_references term fuel).2.fresh_absent member

theorem initial_run_returned_reference_bound (term : Term) (fuel : Nat)
    (returned : (run fuel (initial term)).state.control = .returned value)
    (occurs : ReferenceOccurs token value) :
    token < (run fuel (initial term)).state.heap.heap.nextLease := by
  have ready := (initial_run_references term fuel).1
  rw [returned] at ready
  exact occurs.before_limit ready

end Jihoo.NativeKernel.Environment.BindingMachine
