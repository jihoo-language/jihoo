import Jihoo.NativeBindingMachineMutableCallEntry
import Jihoo.NativeBindingMachineMutableHeapHistory

/-! Call entry preserves the enclosing readers even when its relevant
arguments execute heap operations. The actual trace may contain temporary
leases, and the exact inventory identifies the leases at the boundary. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

open Jihoo.Quantity NativeQuantity

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

/-- The actual argument trace preserves the captured owner world exactly
when no demanded capture is released. Alias exclusivity and demand counts
refer to the same capture slots before and after the argument run. -/
theorem CallEntry.capture_demand_survives
    (entry : CallEntry env loans caller stack pending code supplied opened heap fuel events slots finalHeap finalCode)
    (initial : Invariant (callState heap code caller supplied stack pending))
    (world : OwnerDemandWorld heap.metadata code receipt) :
    OwnerDemandWorld finalHeap.metadata code receipt ↔
      ∀ index object uses, code.values[index]? = some (some (Value.owner object)) →
        receipt.demand index = some (uses+1) → .free object ∉ events.filterMap Event.lifecycle? := by
  have heapSteps := (entry.retains_enclosing_leases initial).2.1
  have traceFor {index object uses : Nat} (stored : code.values[index]? = some (some (Value.owner object)))
      (demand : receipt.demand index = some (uses+1)) :
      finalHeap.metadata.heap.live object = true ↔ .free object ∉ events.filterMap Event.lifecycle? := by
    have live := (world.live_once index object uses stored demand).1
    have old := initial.1.allocated object live
    exact (lifecycle_owner_live_iff old heapSteps).trans ⟨fun past => past.2,fun kept => ⟨live,kept⟩⟩
  constructor
  · intro after index object uses stored demand
    exact (traceFor stored demand).mp (after.live_once index object uses stored demand).1
  · intro kept
    refine ⟨?_,world.exclusive⟩
    intro index object uses stored demand
    exact ⟨(traceFor stored demand).mpr (kept index object uses stored demand),
      (world.live_once index object uses stored demand).2⟩

/-- Transfer demand from the capture store at the start of the actual
call. The initial world and the release trace derive liveness of captures
at entry. Newly bound owners still require their own checked slot facts. -/
theorem CallEntry.transfers_owner_demand_from_start
    (entry : CallEntry env loans caller stack pending code supplied opened heap fuel events slots finalHeap finalCode)
    (initial : Invariant (callState heap code caller supplied stack pending))
    (world : OwnerDemandWorld heap.metadata code (.scopes opened.modes body))
    (total : OwnerDemandWorld.Total code (.scopes opened.modes body))
    (valid : LocalScopes (.scopes opened.modes body))
    (avoids : ∀ index object uses, code.values[index]? = some (some (Value.owner object)) →
      (.scopes opened.modes body : Jihoo.Quantity.Control).demand index = some (uses+1) →
        .free object ∉ events.filterMap Event.lifecycle?)
    (installed : ∀ (position object : Nat), slots.reverse[position]? = some (some (Value.owner object)) →
      opened.modes[opened.modes.length-position-1]? = some .linear ∧ finalHeap.metadata.heap.live object = true)
    (different : ∀ (position alias object : Nat), slots.reverse[position]? = some (some (Value.owner object)) →
      slots.reverse[alias]? = some (some (Value.owner object)) → position = alias)
    (retired : ∀ (position index object : Nat), slots.reverse[position]? = some (some (Value.owner object)) →
      code.values[index]? = some (some (Value.owner object)) →
        (.scopes opened.modes body : Jihoo.Quantity.Control).demand index = some 0) :
    OwnerDemandWorld finalHeap.metadata finalCode body ∧ OwnerDemandWorld.Total finalCode body :=
  entry.transfers_owner_demand ((entry.capture_demand_survives initial world).mpr avoids)
    total valid installed different retired

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
