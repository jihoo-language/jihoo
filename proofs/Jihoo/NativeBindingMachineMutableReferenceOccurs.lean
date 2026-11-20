import Jihoo.NativeBindingMachineMutableReferenceProvenance
import Jihoo.NativeBindingMachineOutlivedReferences

/-! A fresh reader token is absent from both active and suspended control.
The occurrence predicates include closure captures stored in buffer frames
and in the legacy frames saved underneath them. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

def BufferFrameReferenceOccurs (token : Nat) : BufferFrame → Prop
  | .owner offset value | .loadOwner _ offset value =>
      CodeReferenceOccurs token offset ∨ CodeReferenceOccurs token value
  | .index _ value | .loadIndex _ _ value | .usubLeft value |
      .arrayElements value _ _ => CodeReferenceOccurs token value
  | .value _ _ | .loadContinuation _ _ _ | .loadOwnerArgument _ _ |
      .usubRight _ | .refinement => False

def PendingReferenceOccurs (token : Nat) (pending : List (BufferFrame × List Frame)) : Prop :=
  ∃ pair ∈ pending, BufferFrameReferenceOccurs token pair.1 ∨
    ∃ frame ∈ pair.2, FrameReferenceOccurs token frame

def StateReferenceOccurs (token : Nat) (state : State) : Prop :=
  BindingMachine.StateReferenceOccurs token ⟨state.heap.metadata,state.control,state.stack⟩ ∨
    PendingReferenceOccurs token state.pending

theorem BufferFrameReferenceOccurs.before_limit (occurs : BufferFrameReferenceOccurs token frame)
    (ready : BufferFrameReferences limit frame) : token < limit := by
  cases frame <;> simp only [BufferFrameReferenceOccurs,BufferFrameReferences] at occurs ready
  all_goals first
    | contradiction
    | exact occurs.before_limit ready
    | exact occurs.elim (fun left => left.before_limit ready.1) (fun right => right.before_limit ready.2)

theorem PendingReferenceOccurs.before_limit (occurs : PendingReferenceOccurs token pending)
    (ready : PendingReferences limit pending) : token < limit := by
  obtain ⟨pair,member,occurs⟩ := occurs
  obtain ⟨frameReady,stackReady⟩ := ready pair member
  rcases occurs with occurs | ⟨frame,frameMember,occurs⟩
  · exact occurs.before_limit frameReady
  · exact occurs.before_limit (stackReady frame frameMember)

theorem StateReferenceOccurs.before_limit (occurs : StateReferenceOccurs token state)
    (ready : StateReferences state) : token < state.heap.metadata.heap.nextLease := by
  rcases occurs with occurs | occurs
  · exact occurs.before_limit ready.1
  · exact occurs.before_limit ready.2

theorem BufferFrameReferences.fresh_absent (ready : BufferFrameReferences limit frame) :
    ¬ BufferFrameReferenceOccurs limit frame := by
  intro occurs
  exact Nat.lt_irrefl _ (occurs.before_limit ready)

theorem PendingReferences.fresh_absent (ready : PendingReferences limit pending) :
    ¬ PendingReferenceOccurs limit pending := by
  intro occurs
  exact Nat.lt_irrefl _ (occurs.before_limit ready)

theorem StateReferences.fresh_absent (ready : StateReferences state) :
    ¬ StateReferenceOccurs state.heap.metadata.heap.nextLease state := by
  intro occurs
  exact Nat.lt_irrefl _ (occurs.before_limit ready)

/-- Before a reader is opened, its new token is absent from the entire
reachable state, including buffer payloads and their saved legacy stacks. -/
theorem initial_run_fresh_reference_absent (term : Term) (fuel : Nat) :
    let state := (run fuel (initial term)).state
    ¬ StateReferenceOccurs state.heap.metadata.heap.nextLease state :=
  (initial_run_references term fuel).fresh_absent

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
