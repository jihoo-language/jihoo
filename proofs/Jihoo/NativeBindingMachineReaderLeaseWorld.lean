import Jihoo.NativeBindingMachineReferenceSizes
import Jihoo.NativeBindingMachineRunAlgebra

/-! An active reader protects every older lease through arbitrary actual body
prefixes, including nested readers and partial/fault outcomes. A final active
reader cannot have closed and reopened at an intermediate point. This gives
saved canonical reference contexts an entry-to-body-interval liveness theorem;
it does not construct those contexts from every admitted program or extend the
current Buffer-reference model to other runtime representations. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

private theorem frame_reader_token_bound (ready : FrameReferences limit frame)
    (descriptor : frame.reader? = some (token,object,name)) : token < limit := by
  cases frame <;> simp_all [FrameReferences,Frame.reader?]

private theorem reader_outer_reference_bounds (captures : ReaderFrameCaptureBounds frame stack)
    (descriptor : frame.reader? = some (token,object,name)) : StackReferences token stack := by
  cases frame <;> simp_all [ReaderFrameCaptureBounds,Frame.reader?]

/-- The first active reader has the newest token among current reader frames.
Administrative frames may occur before that reader in the control stack. -/
theorem ReaderCaptureBounds.head_token_bound (captures : ReaderCaptureBounds stack)
    (shape : readerFrames stack = (closing,object,name) :: entries)
    (member : (token,owner,readerName) ∈ readerFrames stack) : token ≤ closing := by
  induction stack with
  | nil => cases shape
  | cons frame rest ih =>
      cases descriptor : frame.reader? with
      | none =>
          have tailShape : readerFrames rest = (closing,object,name) :: entries := by
            simpa only [readerFrames,List.filterMap_cons,descriptor] using shape
          have tailMember : (token,owner,readerName) ∈ readerFrames rest := by
            simpa only [readerFrames,List.filterMap_cons,descriptor] using member
          exact ih captures.tail tailShape tailMember
      | some first =>
          have same : first = (closing,object,name) := by
            have lists : first :: readerFrames rest = (closing,object,name) :: entries := by
              simpa only [readerFrames,List.filterMap_cons,descriptor] using shape
            exact (List.cons.inj lists).1
          subst first
          have outerReady := reader_outer_reference_bounds captures.2 descriptor
          have selected : (token,owner,readerName) ∈ (closing,object,name) :: readerFrames rest := by
            simpa only [readerFrames,List.filterMap_cons,descriptor] using member
          rcases List.mem_cons.mp selected with same | selected
          · have equal : token = closing := congrArg Prod.fst same
            omega
          · obtain ⟨outer,outerMember,outerDescriptor⟩ := List.mem_filterMap.mp selected
            have bound := frame_reader_token_bound (outerReady outer outerMember) outerDescriptor
            omega

/-- Actual steps cannot alter lease slots older than an enclosing reader.
Fresh lease allocation is newer, and any closing reader is at least as new
as the barrier, even if this step closes the barrier itself. -/
theorem step_reader_older_lease (valid : SizedBufferHeap.Valid state.heap)
    (inventory : ReaderInventory state.heap (readerFrames state.stack))
    (captures : ReaderCaptureBounds state.stack)
    (member : (barrier,owner,name) ∈ readerFrames state.stack)
    (older : Nat) (before : older < barrier)
    (stepped : step state = some (next,event)) :
    next.heap.heap.lease older = state.heap.heap.lease older := by
  have barrierLease := inventory.live _ member
  have barrierBound := (valid.leased barrier owner barrierLease).1
  obtain ⟨nextAction,chosen,same⟩ := Option.map_eq_some_iff.mp stepped
  have preserved : (execute state.heap nextAction).1.heap.heap.lease older = state.heap.heap.lease older := by
    cases nextAction with
    | control control stack activation => rfl
    | allocate count fill stack =>
        simp only [execute]
        split <;> rfl
    | free object rest stack =>
        simp only [execute]
        split
        · split <;> rfl
        · rfl
    | lend object name origin reader continuation stack =>
        have different : older ≠ state.heap.heap.nextLease := by omega
        simp only [execute]
        split
        · simp only [SizedBufferHeap.lend,HeapLeases.put,different,ite_false]
        · rfl
    | close closing object result origin resultOrigin continuation stack =>
        obtain ⟨closingName,head⟩ := action_frame_change chosen
        have order := captures.head_token_bound head member
        have different : older ≠ closing := by omega
        simp only [execute]
        split
        · simp only [SizedBufferHeap.close,HeapLeases.put,different,ite_false]
        · rfl
    | borrow key object stack =>
        simp only [execute]
        split
        · split <;> rfl
        · rfl
    | read token index stack =>
        simp only [execute]
        split
        · split <;> rfl
        · rfl
  simpa only [same] using preserved

private theorem lease_counter_step (step : HeapLeases.Step before event after) :
    before.nextLease ≤ after.nextLease := by
  cases step <;> simp_all <;> omega

private theorem lease_counter_steps (steps : HeapLeases.Steps before events after) :
    before.nextLease ≤ after.nextLease := by
  induction steps with
  | nil => exact Nat.le_refl _
  | cons first rest ih => exact Nat.le_trans (lease_counter_step first) ih

/-- Internal backward-use lemma: an already issued token present at the end
cannot be absent now, because expired tokens never reopen. -/
private theorem barrier_present_before_run (valid : SizedBufferHeap.Valid state.heap)
    (old : barrier < state.heap.heap.nextLease)
    (present : (run fuel state).state.heap.heap.lease barrier = some object) :
    ∃ owner, state.heap.heap.lease barrier = some owner := by
  cases current : state.heap.heap.lease barrier with
  | some owner => exact ⟨owner,rfl⟩
  | none =>
      have expired := HeapLeases.expired_steps old current
        (SizedBufferHeap.steps_project (run_heap_steps valid fuel))
      have impossible : some object = none := present.symm.trans expired.2
      cases impossible

private theorem run_older_lease_eq (fuel : Nat) (valid : SizedBufferHeap.Valid state.heap)
    (references : StateReferences state) (captures : ReaderCaptureBounds state.stack)
    (inventory : ReaderInventory state.heap (readerFrames state.stack))
    (old : barrier < state.heap.heap.nextLease)
    (present : (run fuel state).state.heap.heap.lease barrier = some object)
    (older : Nat) (before : older < barrier) :
    (run fuel state).state.heap.heap.lease older = state.heap.heap.lease older := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases observed : step state with
      | none => simp only [run,observed]
      | some result =>
          obtain ⟨next,event⟩ := result
          obtain ⟨owner,leased⟩ := barrier_present_before_run valid old present
          obtain ⟨name,member⟩ := inventory.covered barrier owner leased
          have first := step_reader_older_lease valid inventory captures member older before observed
          have steps := step_heap_steps valid observed
          have nextValid := SizedBufferHeap.steps_valid valid steps
          have nextReferences := step_references valid references observed
          have nextCaptures := step_reader_captures references captures observed
          have nextInventory := step_reader_inventory valid inventory observed
          have monotone := lease_counter_steps (SizedBufferHeap.steps_project steps)
          have nextOld : barrier < next.heap.heap.nextLease := by omega
          have nextPresent : (run fuel next).state.heap.heap.lease barrier = some object := by
            simpa only [run,observed] using present
          have tail := ih nextValid nextReferences nextCaptures nextInventory nextOld nextPresent
          simpa only [run,observed] using tail.trans first

/-- A reader surviving at the final actual prefix protects every older lease
through the entire interval. Intermediate reader presence follows from lease
non-reopening and inventory, rather than an all-prefix success certificate. -/
theorem run_reader_older_leases (fuel : Nat) (valid : SizedBufferHeap.Valid state.heap)
    (references : StateReferences state) (captures : ReaderCaptureBounds state.stack)
    (inventory : ReaderInventory state.heap (readerFrames state.stack))
    (entered : (barrier,owner,name) ∈ readerFrames state.stack)
    (remaining : (barrier,finalOwner,finalName) ∈ readerFrames (run fuel state).state.stack) :
    ∀ older, older < barrier →
      (run fuel state).state.heap.heap.lease older = state.heap.heap.lease older := by
  have old := (valid.leased barrier owner (inventory.live _ entered)).1
  have finalInventory := run_reader_inventory valid inventory fuel
  have present := finalInventory.live _ remaining
  intro older before
  exact run_older_lease_eq fuel valid references captures inventory old present older before

/-- Saved source references remain live through an arbitrary actual reader
body interval and its eventual close. Initial reference interpretation is an
entry invariant; final interpretation, source freshness and every older lease
entry are outputs derived from actual snapshots, inventory and heap steps.
The endpoint reader-frame shape permits partial/fault prefixes and does not
assert successful evaluation of the body or arbitrary source typing. -/
theorem reachable_saved_reference_interval (term : Term) (entryFuel bodyFuel : Nat)
    (captured : CapturedCanonicalView actual source indices)
    (sizes : ReferenceSizes env (run entryFuel (initial term)).state.heap source meanings)
    (entryShape : (run entryFuel (initial term)).state.stack =
      .lendReader barrier object name origin readerOrigin (actual.child continuation) :: entryStack)
    (finishShape : (run bodyFuel (run entryFuel (initial term)).state).state.stack =
      .lendFinish barrier object name origin resultOrigin (actual.child continuation) :: finishStack) :
    let before := (run entryFuel (initial term)).state.heap
    let after := (run bodyFuel (run entryFuel (initial term)).state).state.heap
    (∀ older, older < barrier → after.heap.lease older = before.heap.lease older) ∧
    ReferenceSizes env after source meanings ∧
    ReferenceSizes env (SizedBufferHeap.close after barrier) source meanings ∧
    after.heap.lease barrier = some object ∧
    ReaderInventory (SizedBufferHeap.close after barrier) (readerFrames finishStack) := by
  have valid := initial_run_heap_valid term entryFuel
  have references := initial_run_references term entryFuel
  have captures := initial_run_reader_captures term entryFuel
  have inventory := initial_reader_inventory term entryFuel
  have entered : (barrier,object,name) ∈ readerFrames (run entryFuel (initial term)).state.stack := by
    rw [entryShape]
    exact List.mem_cons_self
  have remaining : (barrier,object,name) ∈
      readerFrames (run bodyFuel (run entryFuel (initial term)).state).state.stack := by
    rw [finishShape]
    exact List.mem_cons_self
  have world := run_reader_older_leases bodyFuel valid references captures inventory entered remaining
  obtain ⟨actualReady,outerReady⟩ := initial_run_reader_capture_bounds term entryFuel entryShape
  have sourceReady : CodeReferences barrier source := captured.references actualReady
  have finalValid := run_heap_valid valid bodyFuel
  have steps := run_heap_steps valid bodyFuel
  have finalSizes : ReferenceSizes env (run bodyFuel (run entryFuel (initial term)).state).state.heap source meanings := by
    intro index binding token selected stored
    obtain ⟨owner,count,leased,live,length,converted⟩ := sizes index binding token selected stored
    have before := (ValuesReferences.valueAt sourceReady stored).referenceBound
    have retained := (world token before).trans leased
    have finalLive := (finalValid.leased token owner retained).2
    have oldOwner := valid.allocated owner live
    have preservedLength := SizedBufferHeap.lengths_preserved oldOwner steps
    exact ⟨owner,count,retained,finalLive,preservedLength.2.trans length,converted⟩
  have finalInventory := run_reader_inventory valid inventory bodyFuel
  rw [finishShape] at finalInventory
  change ReaderInventory _ ((barrier,object,name) :: readerFrames finishStack) at finalInventory
  obtain ⟨leased,closedInventory⟩ := finalInventory.finish
  exact ⟨world,finalSizes,finalSizes.close sourceReady,leased,closedInventory⟩

end Jihoo.NativeKernel.Environment.BindingMachine
