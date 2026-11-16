import Jihoo.NativeBindingMachineLoans

/-! Reader frames and actual heap leases stay in correspondence at every
machine prefix, including faults. This invariant concerns the concrete control
stack; source owner-slot alignment and value typing are separate obligations. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

def readerFrames (stack : List Frame) : List (Nat × Nat × Option Nat) :=
  stack.filterMap Frame.reader?

def FrameChange (before : List Frame) : Action → Prop
  | .control _ after _ | .allocate _ _ after | .free _ _ after |
      .lend _ _ _ _ _ after | .borrow _ _ after | .read _ _ after =>
      readerFrames before = readerFrames after
  | .close token object _ _ _ _ after =>
      ∃ name, readerFrames before = (token,object,name) :: readerFrames after

theorem applyValue_frame_change (function : Value) (origin : Term)
    (argument : Option Value) (stack : List Frame) :
    FrameChange stack (applyValue function origin argument stack) := by
  cases function <;> rfl

theorem evaluate_frame_change (code : Code) (stack : List Frame) :
    FrameChange stack (evaluateAction code stack) := by
  fun_cases evaluateAction code stack
  all_goals try simp only [evaluateAction, *]
  all_goals rfl

theorem return_frame_change (value : Value) (stack : List Frame) (result : Action)
    (computed : returnAction value stack = some result) : FrameChange stack result := by
  cases stack with
  | nil => simp [returnAction] at computed
  | cons frame rest =>
      simp only [returnAction] at computed
      split at computed
      all_goals have same := Option.some.inj computed
      all_goals rw [← same]
      all_goals clear computed same
      all_goals try { simp only [applyValue] }
      all_goals first | rfl | exact ⟨_,rfl⟩ | skip
      all_goals try { split <;> rfl }
      case h_4 => exact applyValue_frame_change _ _ _ _
      case h_14 =>
        rename_i equal left yes no firstOrigin secondOrigin right
        by_cases compared : (if equal then left == right else decide (left < right)) = true
        all_goals simp only [compared,↓reduceIte]
        all_goals rfl
      case h_23 =>
        change readerFrames (frame :: rest) = readerFrames rest
        have noReader : frame.reader? = none := by
          cases frame <;> simp_all [Frame.reader?]
          all_goals rename_i token object name ownerOrigin readerOrigin continuation impossible
          all_goals exact impossible token object name ownerOrigin readerOrigin continuation rfl rfl rfl rfl rfl rfl
        simp only [readerFrames,List.filterMap_cons,noReader]

/-- Exact inventory of active leases, with one concrete reader per token. -/
structure ReaderInventory (heap : SizedBufferHeap.State)
    (entries : List (Nat × Nat × Option Nat)) : Prop where
  distinct : (entries.map Prod.fst).Nodup
  live : ∀ entry ∈ entries, heap.heap.lease entry.1 = some entry.2.1
  covered : ∀ token object, heap.heap.lease token = some object →
    ∃ name, (token,object,name) ∈ entries

theorem ReaderInventory.empty : ReaderInventory SizedBufferHeap.empty [] := by
  constructor
  · exact .nil
  · simp
  · intro token object leased
    cases leased

theorem ReaderInventory.begin (valid : SizedBufferHeap.Valid heap)
    (inventory : ReaderInventory heap entries) (object : Nat) (name : Option Nat) :
    ReaderInventory (SizedBufferHeap.lend heap object)
      ((heap.heap.nextLease,object,name) :: entries) := by
  have earlier : ∀ entry ∈ entries, entry.1 < heap.heap.nextLease := by
    intro entry member
    exact (valid.leased _ _ (inventory.live entry member)).1
  constructor
  · simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,inventory.distinct⟩
    intro member
    obtain ⟨entry,member,same⟩ := List.mem_map.mp member
    have := earlier entry member
    omega
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · simp [SizedBufferHeap.lend,HeapLeases.put]
    · have previous := inventory.live entry member
      have different : entry.1 ≠ heap.heap.nextLease := by have := earlier entry member; omega
      simpa [SizedBufferHeap.lend,HeapLeases.put,different] using previous
  · intro token owner leased
    by_cases same : token = heap.heap.nextLease
    · subst token
      have identity : object = owner := by simpa [SizedBufferHeap.lend,HeapLeases.put] using leased
      subst owner
      exact ⟨name,List.mem_cons_self⟩
    · have previous : heap.heap.lease token = some owner := by
        simpa [SizedBufferHeap.lend,HeapLeases.put,same] using leased
      obtain ⟨key,member⟩ := inventory.covered token owner previous
      exact ⟨key,List.mem_cons_of_mem _ member⟩

theorem ReaderInventory.finish
    (inventory : ReaderInventory heap ((token,object,name) :: entries)) :
    heap.heap.lease token = some object ∧
      ReaderInventory (SizedBufferHeap.close heap token) entries := by
  have distinct := List.nodup_cons.mp inventory.distinct
  have different : ∀ entry ∈ entries, entry.1 ≠ token := by
    intro entry member same
    apply distinct.1
    exact List.mem_map.mpr ⟨entry,member,same⟩
  refine ⟨inventory.live _ List.mem_cons_self,distinct.2,?_,?_⟩
  · intro entry member
    simpa [SizedBufferHeap.close,HeapLeases.put,different entry member] using
      inventory.live entry (List.mem_cons_of_mem _ member)
  · intro queried owner leased
    have other : queried ≠ token := by
      intro same
      subst queried
      simp [SizedBufferHeap.close,HeapLeases.put] at leased
    have previous : heap.heap.lease queried = some owner := by
      simpa [SizedBufferHeap.close,HeapLeases.put,other] using leased
    obtain ⟨key,member⟩ := inventory.covered queried owner previous
    rcases List.mem_cons.mp member with same | member
    · have identity : queried = token := congrArg Prod.fst same
      exact False.elim (other identity)
    · exact ⟨key,member⟩

theorem action_frame_change (chosen : action state = some next) :
    FrameChange state.stack next := by
  cases state with
  | mk heap control stack =>
      cases control with
      | evaluate code =>
          have same : evaluateAction code stack = next := Option.some.inj chosen
          rw [← same]
          exact evaluate_frame_change code stack
      | returned value => exact return_frame_change value stack next chosen
      | fault reason => cases chosen

theorem execute_reader_inventory (valid : SizedBufferHeap.Valid heap)
    (inventory : ReaderInventory heap (readerFrames before))
    (changed : FrameChange before next) :
    ReaderInventory (execute heap next).1.heap (readerFrames (execute heap next).1.stack) := by
  cases next with
  | control control stack activation =>
      simpa only [execute,FrameChange] using changed ▸ inventory
  | allocate count fill stack =>
      change readerFrames before = readerFrames stack at changed
      rw [changed] at inventory
      simp only [execute]
      split <;> exact ⟨inventory.distinct,inventory.live,inventory.covered⟩
  | free object rest stack =>
      change readerFrames before = readerFrames stack at changed
      rw [changed] at inventory
      simp only [execute]
      split
      · split <;> exact ⟨inventory.distinct,inventory.live,inventory.covered⟩
      · exact inventory
  | lend object name origin reader continuation stack =>
      change readerFrames before = readerFrames stack at changed
      rw [changed] at inventory
      simp only [execute]
      split
      · exact ReaderInventory.begin valid inventory object name
      · exact inventory
  | close token object result origin resultOrigin continuation stack =>
      obtain ⟨name,changed⟩ := changed
      rw [changed] at inventory
      obtain ⟨leased,remaining⟩ := inventory.finish
      simpa only [execute,leased,ite_true,readerFrames,List.filterMap_cons,Frame.reader?]
        using remaining
  | borrow key object stack =>
      change readerFrames before = readerFrames stack at changed
      rw [changed] at inventory
      simp only [execute]
      split
      · split <;> exact ⟨inventory.distinct,inventory.live,inventory.covered⟩
      · exact inventory
  | read token index stack =>
      change readerFrames before = readerFrames stack at changed
      rw [changed] at inventory
      simp only [execute]
      split
      · split <;> exact ⟨inventory.distinct,inventory.live,inventory.covered⟩
      · exact inventory

theorem step_reader_inventory (valid : SizedBufferHeap.Valid state.heap)
    (inventory : ReaderInventory state.heap (readerFrames state.stack))
    (stepped : step state = some (next,event)) :
    ReaderInventory next.heap (readerFrames next.stack) := by
  obtain ⟨nextAction,chosen,same⟩ := Option.map_eq_some_iff.mp stepped
  simpa only [same] using execute_reader_inventory valid inventory (action_frame_change chosen)

theorem run_reader_inventory (valid : SizedBufferHeap.Valid state.heap)
    (inventory : ReaderInventory state.heap (readerFrames state.stack)) (fuel : Nat) :
    ReaderInventory (run fuel state).state.heap (readerFrames (run fuel state).state.stack) := by
  induction fuel generalizing state with
  | zero => exact inventory
  | succ fuel ih =>
      simp only [run]
      cases observed : step state with
      | none => exact inventory
      | some result =>
          obtain ⟨next,event⟩ := result
          exact ih (SizedBufferHeap.steps_valid valid (step_heap_steps valid observed))
            (step_reader_inventory valid inventory observed)

theorem initial_reader_inventory (term : Term) (fuel : Nat) :
    ReaderInventory (run fuel (initial term)).state.heap
      (readerFrames (run fuel (initial term)).state.stack) :=
  run_reader_inventory SizedBufferHeap.empty_valid ReaderInventory.empty fuel

theorem ReaderInventory.readersLive
    (inventory : ReaderInventory heap (readerFrames stack)) : ReadersLive heap stack := by
  intro frame member token object name descriptor
  exact inventory.live (token,object,name)
    (List.mem_filterMap.mpr ⟨frame,member,descriptor⟩)

theorem ReaderInventory.lease_has_reader
    (inventory : ReaderInventory heap (readerFrames stack))
    (leased : heap.heap.lease token = some object) :
    ∃ frame ∈ stack, ∃ name, frame.reader? = some (token,object,name) := by
  obtain ⟨name,member⟩ := inventory.covered token object leased
  obtain ⟨frame,member,descriptor⟩ := List.mem_filterMap.mp member
  exact ⟨frame,member,name,descriptor⟩

/-- Every real reader still owns its live lease at every reachable prefix;
no per-Borrow reader invariant is provided by the caller. -/
theorem initial_run_readers_live (term : Term) (fuel : Nat) :
    ReadersLive (run fuel (initial term)).state.heap (run fuel (initial term)).state.stack :=
  (initial_reader_inventory term fuel).readersLive

/-- A completed computation has no outstanding leases. This is lease
accounting only; ownership accounting for allocated objects is separate. -/
theorem initial_run_empty_stack_no_leases (term : Term) (fuel : Nat)
    (empty : (run fuel (initial term)).state.stack = []) (token : Nat) :
    (run fuel (initial term)).state.heap.heap.lease token = none := by
  cases leased : (run fuel (initial term)).state.heap.heap.lease token with
  | none => rfl
  | some object =>
      obtain ⟨frame,member,_⟩ := (initial_reader_inventory term fuel).lease_has_reader leased
      rw [empty] at member
      cases member

/-- In a reachable reader return, the close precondition is derived from the
actual execution prefix. Inner and outer readers have distinct tokens. -/
theorem initial_run_finish_reader (term : Term) (fuel : Nat)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin continuation :: rest) (result : Value) :
    execute (run fuel (initial term)).state.heap
      (.close token object result origin resultOrigin continuation rest) =
      (⟨SizedBufferHeap.close (run fuel (initial term)).state.heap token,.evaluate continuation,
        .lendContinuation object origin resultOrigin result :: rest⟩,some (.heap (.close token))) ∧
    ReadersLive (SizedBufferHeap.close (run fuel (initial term)).state.heap token)
      (.lendContinuation object origin resultOrigin result :: rest) := by
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,name) :: readerFrames rest) at inventory
  obtain ⟨leased,remaining⟩ := inventory.finish
  constructor
  · simp only [execute,leased,ite_true]
  · exact ReaderInventory.readersLive
      (stack := .lendContinuation object origin resultOrigin result :: rest) remaining

theorem initial_run_typed_borrow (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (slots : LoanSlots code loans (run fuel (initial term)).state.stack)
    (typed : LoanTyping.HasType env loans code.context false code.term type)
    (shape : code.term = .borrow owner) :
    ∃ token object,
      (run fuel (initial term)).state.heap.heap.lease token = some object ∧
      (run fuel (initial term)).state.heap.heap.live object = true ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.returned (.reference token),
          (run fuel (initial term)).state.stack⟩,none) := by
  obtain ⟨token,object,leased,live,executes⟩ := typed_borrow_executes
    (initial_run_heap_valid term fuel) (initial_run_readers_live term fuel) slots typed shape
  refine ⟨token,object,leased,live,?_⟩
  simp only [step,action,evaluating,Option.map_some,executes]

end Jihoo.NativeKernel.Environment.BindingMachine
