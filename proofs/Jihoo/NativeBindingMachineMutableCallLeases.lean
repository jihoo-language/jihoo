import Jihoo.NativeBindingMachineMutableCallEntry
import Jihoo.NativeBindingMachineMutableHeapHistory

/-! Call entry preserves the enclosing readers even when its relevant
arguments execute heap operations. The actual trace may contain temporary
leases, and the exact inventory identifies the leases at the boundary. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

private theorem call_reader_frames (heap : SizedBufferHeap.IndexedState) (code caller : Code)
    (supplied : List Term) (stack : List Frame) (pending : List (BufferFrame × List Frame)) :
    readerFrames (callState heap code caller supplied stack pending).activeStack =
      readerFrames (stack ++ pending.flatMap Prod.snd) := by
  induction supplied with
  | nil => rfl
  | cons arg rest ih =>
    simpa only [callState,State.activeStack,functionFrames,List.map_cons,List.cons_append,
      readerFrames,List.filterMap_cons,Frame.reader?] using ih

private theorem same_scope_leases (first : ReaderInventory before frames)
    (second : ReaderInventory after frames) : before.heap.lease = after.heap.lease := by
  have agrees (token object : Nat) :
      before.heap.lease token = some object ↔ after.heap.lease token = some object := by
    constructor
    · intro leased
      obtain ⟨name,reader⟩ := first.covered token object leased
      exact second.live (token,object,name) reader
    · intro leased
      obtain ⟨name,reader⟩ := second.covered token object leased
      exact first.live (token,object,name) reader
  funext token
  cases initial : before.heap.lease token with
  | some object => exact ((agrees token object).mp initial).symm
  | none =>
    cases final : after.heap.lease token with
    | none => rfl
    | some object => exact False.elim (by simpa only [initial,reduceCtorEq] using (agrees token object).mpr final)

/-- Evaluating the call arguments keeps the original enclosing readers and
their exact token-to-owner map at the entered body. The same native machine
run supplies the intervening heap transition history. -/
theorem CallEntry.retains_enclosing_leases
    (entry : CallEntry env loans caller stack pending code supplied opened heap fuel events slots finalHeap finalCode)
    (initial : Invariant (callState heap code caller supplied stack pending)) :
    Invariant (callState finalHeap finalCode caller (supplied.drop slots.length) stack pending) ∧
    SizedBufferHeap.Steps heap.metadata (events.filterMap Event.lifecycle?) finalHeap.metadata ∧
      heap.metadata.heap.lease = finalHeap.metadata.heap.lease := by
  have executed := entry.executes
  have lifecycle := run_lifecycle initial.1 fuel
  rw [executed] at lifecycle
  have after := run_invariant fuel initial
  rw [executed] at after
  have available := initial.2
  have retained := after.2
  rw [call_reader_frames] at available retained
  exact ⟨after,lifecycle,same_scope_leases available retained⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
