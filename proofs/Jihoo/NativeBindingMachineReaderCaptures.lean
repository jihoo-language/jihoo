import Jihoo.NativeBindingMachineReferenceProvenance
import Jihoo.NativeBindingMachineReaderState

/-! A reader's saved continuation and complete outer stack contain only
reference tokens older than that reader's own token. These bounds record the
snapshot at reader entry and survive every actual machine prefix, including
faults and fuel exhaustion. They cover recursive closure captures and concrete
reader/Index frame fields. The current reader result is deliberately separate:
this invariant alone does not prohibit its reference token from escaping. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

def ReaderFrameCaptureBounds (frame : Frame) (outer : List Frame) : Prop :=
  match frame with
  | .lendReader token _ _ _ _ continuation | .lendFinish token _ _ _ _ continuation =>
      CodeReferences token continuation ∧ StackReferences token outer
  | _ => True

def ReaderCaptureBounds : List Frame → Prop
  | [] => True
  | frame :: rest => ReaderCaptureBounds rest ∧ ReaderFrameCaptureBounds frame rest

theorem ReaderCaptureBounds.empty : ReaderCaptureBounds [] := True.intro

theorem ReaderCaptureBounds.tail (captures : ReaderCaptureBounds (frame :: rest)) :
    ReaderCaptureBounds rest := captures.1

theorem ReaderCaptureBounds.cons_nonreader (captures : ReaderCaptureBounds rest)
    (ordinary : frame.reader? = none) : ReaderCaptureBounds (frame :: rest) := by
  refine ⟨captures,?_⟩
  cases frame <;> simp_all [Frame.reader?,ReaderFrameCaptureBounds]

theorem ReaderCaptureBounds.begin_reader (captures : ReaderCaptureBounds stack)
    (continuationReady : CodeReferences token continuation) (outerReady : StackReferences token stack)
    (object : Nat) (name : Option Nat) (origin readerOrigin : Term) :
    ReaderCaptureBounds (.lendReader token object name origin readerOrigin continuation :: stack) :=
  ⟨captures,continuationReady,outerReady⟩

theorem ReaderCaptureBounds.reader_body
    (captures : ReaderCaptureBounds (.lendReader token object name origin readerOrigin continuation :: stack))
    (resultOrigin : Term) :
    ReaderCaptureBounds (.lendFinish token object name origin resultOrigin continuation :: stack) := captures

theorem ReaderCaptureBounds.reader
    (captures : ReaderCaptureBounds (.lendReader token object name origin readerOrigin continuation :: stack)) :
    CodeReferences token continuation ∧ StackReferences token stack := captures.2

theorem ReaderCaptureBounds.finish
    (captures : ReaderCaptureBounds (.lendFinish token object name origin resultOrigin continuation :: stack)) :
    CodeReferences token continuation ∧ StackReferences token stack := captures.2

def ActionReaderCaptureBounds : Action → Prop
  | .control _ stack _ | .allocate _ _ stack | .free _ _ stack |
      .lend _ _ _ _ _ stack | .close _ _ _ _ _ _ stack |
      .borrow _ _ stack | .read _ _ stack => ReaderCaptureBounds stack

theorem applyValue_reader_captures (function : Value) (origin : Term) (argument : Option Value)
    (captures : ReaderCaptureBounds stack) :
    ActionReaderCaptureBounds (applyValue function origin argument stack) := by
  cases function <;> exact captures

theorem evaluate_action_reader_captures (code : Code) (captures : ReaderCaptureBounds stack) :
    ActionReaderCaptureBounds (evaluateAction code stack) := by
  fun_cases evaluateAction code stack
  all_goals try simp only [evaluateAction, *]
  all_goals first
    | exact captures
    | exact captures.cons_nonreader rfl

theorem return_action_reader_captures (value : Value) (captures : ReaderCaptureBounds stack)
    (computed : returnAction value stack = some result) : ActionReaderCaptureBounds result := by
  cases stack with
  | nil => cases computed
  | cons frame rest =>
      have outerCaptures := captures.tail
      simp only [returnAction] at computed
      split at computed
      all_goals have same := Option.some.inj computed
      all_goals rw [← same]
      all_goals clear computed same
      all_goals first
        | exact outerCaptures
        | exact outerCaptures.cons_nonreader rfl
        | exact captures
        | exact applyValue_reader_captures _ _ _ outerCaptures
        | exact applyValue_reader_captures _ _ _ (outerCaptures.cons_nonreader rfl)
        | exact applyValue_reader_captures _ _ _ (captures.reader_body _)
        | skip
      case h_7 => split <;> exact outerCaptures
      case h_9 => split <;> exact outerCaptures
      case h_14 =>
        rename_i equal left yes no firstOrigin secondOrigin right
        by_cases compared : (if equal then left == right else decide (left < right)) = true
        all_goals simp only [compared,↓reduceIte]
        all_goals exact outerCaptures
      all_goals split <;> exact outerCaptures

theorem action_reader_captures (captures : ReaderCaptureBounds state.stack)
    (chosen : action state = some next) : ActionReaderCaptureBounds next := by
  cases state with
  | mk heap control stack =>
      cases control with
      | evaluate code =>
          have same : evaluateAction code stack = next := Option.some.inj chosen
          rw [← same]
          exact evaluate_action_reader_captures code captures
      | returned value => exact return_action_reader_captures value captures chosen
      | fault reason => cases chosen

/-- New Lend snapshots use the old lease counter, so its fresh reader's
continuation and outer frames exclude the token being issued. Existing reader
snapshots remain unchanged below ordinary frames or the newly entered reader. -/
theorem execute_reader_captures (references : ActionReferences heap.heap.nextLease next)
    (captures : ActionReaderCaptureBounds next) : ReaderCaptureBounds (execute heap next).1.stack := by
  cases next with
  | control control stack activation => exact captures
  | allocate count fill stack =>
      simp only [execute]
      split <;> exact captures
  | free object rest stack =>
      simp only [execute]
      split
      · split <;> exact captures
      · exact captures
  | lend object name origin reader continuation stack =>
      simp only [execute]
      split
      · exact ⟨captures,references.2.1,references.2.2⟩
      · exact captures
  | close token object result origin resultOrigin continuation stack =>
      simp only [execute]
      split
      · exact captures.cons_nonreader rfl
      · exact captures
  | borrow key object stack =>
      simp only [execute]
      split
      · split <;> exact captures
      · exact captures
  | read token index stack =>
      simp only [execute]
      split
      · split <;> exact captures
      · exact captures

theorem step_reader_captures (references : StateReferences state)
    (captures : ReaderCaptureBounds state.stack) (stepped : step state = some (next,event)) :
    ReaderCaptureBounds next.stack := by
  obtain ⟨nextAction,chosen,same⟩ := Option.map_eq_some_iff.mp stepped
  simpa only [same] using execute_reader_captures
    (action_references references.1 references.2 chosen) (action_reader_captures captures chosen)

theorem run_reader_captures (valid : SizedBufferHeap.Valid state.heap)
    (references : StateReferences state) (captures : ReaderCaptureBounds state.stack) (fuel : Nat) :
    ReaderCaptureBounds (run fuel state).state.stack := by
  induction fuel generalizing state with
  | zero => exact captures
  | succ fuel ih =>
      simp only [run]
      cases observed : step state with
      | none => exact captures
      | some result =>
          obtain ⟨next,event⟩ := result
          exact ih (SizedBufferHeap.steps_valid valid (step_heap_steps valid observed))
            (step_references valid references observed) (step_reader_captures references captures observed)

/-- Every actual prefix has the reader-entry snapshot bounds. Neither source
typing, successful termination nor a token-free reader result is assumed. -/
theorem initial_run_reader_captures (term : Term) (fuel : Nat) :
    ReaderCaptureBounds (run fuel (initial term)).state.stack :=
  run_reader_captures (state := initial term) SizedBufferHeap.empty_valid
    ⟨ValuesReferences.nil,StackReferences.empty⟩ ReaderCaptureBounds.empty fuel

theorem initial_run_reader_capture_bounds (term : Term) (fuel : Nat)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object name origin readerOrigin continuation :: rest) :
    CodeReferences token continuation ∧ StackReferences token rest := by
  have captures := initial_run_reader_captures term fuel
  rw [stackShape] at captures
  exact captures.reader

/-- Immediately before closing a reader, all saved continuation captures and
outer frame references are strictly older than the closing token. -/
theorem initial_run_finish_capture_bounds (term : Term) (fuel : Nat)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin continuation :: rest) :
    CodeReferences token continuation ∧ StackReferences token rest := by
  have captures := initial_run_reader_captures term fuel
  rw [stackShape] at captures
  exact captures.finish

theorem initial_run_finish_capture_absent (term : Term) (fuel : Nat)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin continuation :: rest) :
    ¬ CodeReferenceOccurs token continuation ∧
      ∀ frame ∈ rest, ¬ FrameReferenceOccurs token frame := by
  obtain ⟨continuationReady,outerReady⟩ := initial_run_finish_capture_bounds term fuel stackShape
  exact ⟨continuationReady.fresh_absent,by intro frame member; exact outerReady.fresh_absent member⟩

theorem initial_run_finish_captured_reference_absent {index : Nat} (term : Term) (fuel : Nat)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin continuation :: rest)
    (stored : continuation.values[index]? = some (some value)) : ¬ ReferenceOccurs token value := by
  have continuationReady := (initial_run_finish_capture_bounds term fuel stackShape).1
  exact (ValuesReferences.valueAt continuationReady stored).fresh_absent

end Jihoo.NativeKernel.Environment.BindingMachine
