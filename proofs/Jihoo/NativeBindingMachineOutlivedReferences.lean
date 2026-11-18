import Jihoo.NativeBindingMachineOutlivedValues
import Jihoo.NativeBindingMachineReaderCaptures

/-! Source-derived Outlived variable results cannot retain a closing reader
token. Saved continuation and outer-stack freshness follow from every actual
prefix. This composes a real variable step and reader close without assuming
the returned value, successful close or a post-state reference interpretation.
Arbitrary reader computations still need the common fundamental theorem. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

def ControlReferenceOccurs (token : Nat) : Control → Prop
  | .evaluate code => CodeReferenceOccurs token code
  | .returned value => ReferenceOccurs token value
  | .fault _ => False

def StateReferenceOccurs (token : Nat) (state : State) : Prop :=
  ControlReferenceOccurs token state.control ∨
    ∃ frame ∈ state.stack, FrameReferenceOccurs token frame

theorem ControlReferenceOccurs.before_limit {currentControl : Control}
    (occurs : ControlReferenceOccurs token currentControl)
    (ready : ControlReferences limit currentControl) : token < limit := by
  cases currentControl with
  | evaluate => exact CodeReferenceOccurs.before_limit occurs ready
  | returned => exact ReferenceOccurs.before_limit occurs ready
  | fault => exact False.elim occurs

theorem StateReferenceOccurs.before_limit (occurs : StateReferenceOccurs token state)
    (ready : StateReferences state) : token < state.heap.heap.nextLease := by
  rcases occurs with occurs | ⟨frame,member,occurs⟩
  · exact occurs.before_limit ready.1
  · exact occurs.before_limit (ready.2 frame member)

theorem ValueKind.outlived_reference_absent (admissible : EnvironmentDelta.Admissible env)
    (kind : ValueKind env value type) (allowed : LoanTyping.Outlived env type) (token : Nat) :
    ¬ ReferenceOccurs token value := by
  rcases kind.outlived_shape admissible allowed with ⟨number,rfl⟩ | ⟨number,rfl⟩ | ⟨object,rfl⟩ | ⟨elements,rfl⟩
  all_goals intro occurs; cases occurs

private theorem variable_reader_close_two_steps (heap : SizedBufferHeap.State) (code : Code)
    (shape : code.term = .var index) (stored : code.values[index]? = some (some value))
    (leased : heap.heap.lease token = some object) (name : Option Nat)
    (origin resultOrigin : Term) (continuation : Code) (stack : List Frame) :
    run 2 ⟨heap,.evaluate code,.lendFinish token object name origin resultOrigin continuation :: stack⟩ =
      ⟨⟨SizedBufferHeap.close heap token,.evaluate continuation,
          .lendContinuation object origin resultOrigin value :: stack⟩,
        [.heap (.close token)],2⟩ := by
  simp only [run,step,action,evaluateAction,shape,stored,returnAction,execute,leased,ite_true,Option.map_some]
  rfl

/-- The original full Lend judgment derives Outlived for its actual first
continuation domain. Canonical source variable typing selects the result;
unconditional reader snapshots exclude the closing token from saved captures.
Two actual transitions return that result and close the reader, leaving no
occurrence of its token anywhere in runtime control or outer frames. -/
theorem reachable_canonical_lend_variable_close (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (originalTyped : LoanClosingTyped env originalLoans mode original originalMeanings originalType)
    (originalShape : original.term = .lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings (first.subst originalMeanings))
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (shape : actual.term = .var index)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin
        (original.child (.lam false first (.lam false again body))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let continuation := original.child (.lam false first (.lam false again body))
    ∃ value, actual.values[index]? = some (some value) ∧
      ValueKind env value (first.subst originalMeanings) ∧
      run 2 (run fuel (initial term)).state =
        ⟨⟨SizedBufferHeap.close heap token,.evaluate continuation,
            .lendContinuation object origin resultOrigin value :: stack⟩,
          [.heap (.close token)],2⟩ ∧
      ¬ StateReferenceOccurs token
        ⟨SizedBufferHeap.close heap token,.evaluate continuation,
          .lendContinuation object origin resultOrigin value :: stack⟩ ∧
      (SizedBufferHeap.close heap token).heap.lease token = none ∧
      ReaderInventory (SizedBufferHeap.close heap token) (readerFrames stack) := by
  have allowed := originalTyped.reader_domain_outlived history originalShape
  obtain ⟨value,stored,kind,next⟩ := reachable_canonical_variable_kind
    term fuel history evaluating view typed context aligned shape
  have resultAbsent := kind.outlived_reference_absent history.wellFormed.admissible allowed token
  obtain ⟨continuationAbsent,outerAbsent⟩ := initial_run_finish_capture_absent term fuel stackShape
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,name) :: readerFrames stack) at inventory
  obtain ⟨leased,remaining⟩ := inventory.finish
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.evaluate actual,
        .lendFinish token object name origin resultOrigin
          (original.child (.lam false first (.lam false again body))) :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  refine ⟨value,stored,kind,?_,?_,?_,remaining⟩
  · rw [stateShape]
    exact variable_reader_close_two_steps _ actual shape stored leased name origin resultOrigin _ stack
  · intro occurs
    rcases occurs with occurs | ⟨frame,member,occurs⟩
    · exact continuationAbsent occurs
    · rcases List.mem_cons.mp member with rfl | member
      · exact resultAbsent occurs
      · exact outerAbsent frame member occurs
  · simp only [SizedBufferHeap.close,HeapLeases.put,ite_true]

end Jihoo.NativeKernel.Environment.BindingMachine
