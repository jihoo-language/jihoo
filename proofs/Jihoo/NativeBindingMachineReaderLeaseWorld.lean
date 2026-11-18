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

private abbrev ReaderSnapshot := Nat × Option Nat × Term × Code × List Frame

private def Frame.savedCode? : Frame → Option (Term × Code)
  | .lendReader _ _ _ origin _ continuation
  | .lendFinish _ _ _ origin _ continuation => some (origin,continuation)
  | _ => none

private def readerSnapshot (token : Nat) : List Frame → Option ReaderSnapshot
  | [] => none
  | frame :: outer =>
      match frame.reader? with
      | some (selected,object,name) =>
          if selected = token then
            frame.savedCode?.map (fun (origin,continuation) => (object,name,origin,continuation,outer))
          else readerSnapshot token outer
      | none => readerSnapshot token outer

private def SnapshotChange (token : Nat) (before : List Frame) : Action → Prop
  | .control _ after _ | .allocate _ _ after | .free _ _ after |
      .lend _ _ _ _ _ after | .borrow _ _ after | .read _ _ after =>
      readerSnapshot token before = readerSnapshot token after
  | .close closing _ _ _ _ _ after =>
      closing ≠ token → readerSnapshot token before = readerSnapshot token after

private theorem applyValue_snapshot (function : Value) (origin : Term)
    (argument : Option Value) (stack : List Frame) (token : Nat) :
    SnapshotChange token stack (applyValue function origin argument stack) := by
  cases function <;> rfl

private theorem evaluate_snapshot (code : Code) (stack : List Frame) (token : Nat) :
    SnapshotChange token stack (evaluateAction code stack) := by
  fun_cases evaluateAction code stack
  all_goals try simp only [evaluateAction, *]
  all_goals rfl

private theorem return_snapshot (value : Value) (stack : List Frame) (token : Nat)
    (computed : returnAction value stack = some result) : SnapshotChange token stack result := by
  cases stack with
  | nil => cases computed
  | cons frame rest =>
      simp only [returnAction] at computed
      split at computed
      all_goals have same := Option.some.inj computed
      all_goals rw [← same]
      all_goals clear computed same
      all_goals try { simp only [applyValue] }
      all_goals first | rfl | skip
      all_goals try { split <;> rfl }
      case h_4 => exact applyValue_snapshot _ _ _ _ _
      case h_14 =>
        rename_i equal left yes no firstOrigin secondOrigin right
        by_cases compared : (if equal then left == right else decide (left < right)) = true
        all_goals simp only [compared,↓reduceIte]
        all_goals rfl
      case h_18 =>
        intro different
        simp only [readerSnapshot,Frame.reader?,different,ite_false]
      case h_23 =>
        change readerSnapshot token (frame :: rest) = readerSnapshot token rest
        have noReader : frame.reader? = none := by
          cases frame <;> simp_all [Frame.reader?]
          all_goals rename_i selected object name ownerOrigin readerOrigin continuation impossible
          all_goals exact impossible selected object name ownerOrigin readerOrigin continuation rfl rfl rfl rfl rfl rfl
        simp only [readerSnapshot,noReader]

private theorem action_snapshot (token : Nat) (chosen : action state = some next) :
    SnapshotChange token state.stack next := by
  cases state with
  | mk heap control stack =>
      cases control with
      | evaluate code =>
          have same : evaluateAction code stack = next := Option.some.inj chosen
          rw [← same]
          exact evaluate_snapshot code stack token
      | returned value => exact return_snapshot value stack token chosen
      | fault reason => cases chosen

private theorem execute_snapshot (inventory : ReaderInventory heap (readerFrames before))
    (frameChanged : FrameChange before next) (snapshotChanged : SnapshotChange token before next)
    (old : token < heap.heap.nextLease) (live : (execute heap next).1.heap.heap.lease token = some owner) :
    readerSnapshot token (execute heap next).1.stack = readerSnapshot token before := by
  cases next with
  | control control stack activation => exact snapshotChanged.symm
  | allocate count fill stack =>
      simp only [execute]
      split <;> exact snapshotChanged.symm
  | free object rest stack =>
      simp only [execute]
      split
      · split <;> exact snapshotChanged.symm
      · exact snapshotChanged.symm
  | lend object name readerOrigin reader continuation stack =>
      have different : heap.heap.nextLease ≠ token := by omega
      simp only [execute]
      split
      · simpa only [readerSnapshot,Frame.reader?,different,ite_false] using snapshotChanged.symm
      · exact snapshotChanged.symm
  | close closing object result origin resultOrigin continuation stack =>
      obtain ⟨name,shape⟩ := frameChanged
      have member : (closing,object,name) ∈ readerFrames before := by
        rw [shape]
        exact List.mem_cons_self
      have leased := inventory.live (closing,object,name) member
      change heap.heap.lease closing = some object at leased
      simp only [execute,leased,ite_true] at live ⊢
      have different : closing ≠ token := by
        intro same
        subst closing
        simp [SizedBufferHeap.close,HeapLeases.put] at live
      exact (snapshotChanged different).symm
  | borrow key object stack =>
      simp only [execute]
      split
      · split <;> exact snapshotChanged.symm
      · exact snapshotChanged.symm
  | read token index stack =>
      simp only [execute]
      split
      · split <;> exact snapshotChanged.symm
      · exact snapshotChanged.symm

private theorem step_snapshot (inventory : ReaderInventory state.heap (readerFrames state.stack))
    (old : token < state.heap.heap.nextLease) (live : next.heap.heap.lease token = some object)
    (stepped : step state = some (next,event)) :
    readerSnapshot token next.stack = readerSnapshot token state.stack := by
  obtain ⟨nextAction,chosen,same⟩ := Option.map_eq_some_iff.mp stepped
  have actual : (execute state.heap nextAction).1 = next := congrArg Prod.fst same
  rw [← actual] at live ⊢
  exact execute_snapshot inventory (action_frame_change chosen) (action_snapshot token chosen) old live

private theorem run_snapshot (fuel : Nat) (valid : SizedBufferHeap.Valid state.heap)
    (inventory : ReaderInventory state.heap (readerFrames state.stack))
    (old : token < state.heap.heap.nextLease) (live : (run fuel state).state.heap.heap.lease token = some object) :
    readerSnapshot token (run fuel state).state.stack = readerSnapshot token state.stack := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases observed : step state with
      | none => simp only [run,observed]
      | some result =>
          obtain ⟨next,event⟩ := result
          have steps := step_heap_steps valid observed
          have nextValid := SizedBufferHeap.steps_valid valid steps
          have nextInventory := step_reader_inventory valid inventory observed
          have monotone := lease_counter_steps (SizedBufferHeap.steps_project steps)
          have nextOld : token < next.heap.heap.nextLease := by omega
          have nextLive : (run fuel next).state.heap.heap.lease token = some object := by
            simpa only [run,observed] using live
          obtain ⟨owner,leased⟩ := barrier_present_before_run nextValid nextOld nextLive
          have first := step_snapshot inventory old leased observed
          have tail := ih nextValid nextInventory nextOld nextLive
          simpa only [run,observed] using tail.trans first

/-- If an actual run reaches a finishing reader with the entry token, that
frame retains the same owner, reader name, original owner term, saved code,
and entire outer stack. The reader's result origin is computed on activation. -/
theorem reachable_reader_finish_snapshot (term : Term) (entryFuel bodyFuel : Nat)
    (entryShape : (run entryFuel (initial term)).state.stack =
      .lendReader token owner name origin readerOrigin continuation :: outer)
    (finishShape : (run bodyFuel (run entryFuel (initial term)).state).state.stack =
      .lendFinish token finalOwner finalName finalOrigin resultOrigin finalContinuation :: finalOuter) :
    finalOwner = owner ∧ finalName = name ∧ finalOrigin = origin ∧
      finalContinuation = continuation ∧ finalOuter = outer := by
  have valid := initial_run_heap_valid term entryFuel
  have inventory := initial_reader_inventory term entryFuel
  have entryMember : (token,owner,name) ∈ readerFrames (run entryFuel (initial term)).state.stack := by
    rw [entryShape]
    exact List.mem_cons_self
  have old := (valid.leased token owner (inventory.live _ entryMember)).1
  have finalInventory := run_reader_inventory valid inventory bodyFuel
  have finishMember : (token,finalOwner,finalName) ∈
      readerFrames (run bodyFuel (run entryFuel (initial term)).state).state.stack := by
    rw [finishShape]
    exact List.mem_cons_self
  have saved := run_snapshot bodyFuel valid inventory old (finalInventory.live _ finishMember)
  rw [entryShape,finishShape] at saved
  simpa only [readerSnapshot,Frame.reader?,Frame.savedCode?,eq_self,ite_true,Option.map_some,
    Option.some.injEq,Prod.mk.injEq] using saved

end Jihoo.NativeKernel.Environment.BindingMachine
