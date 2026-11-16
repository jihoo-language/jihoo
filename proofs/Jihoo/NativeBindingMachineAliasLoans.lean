import Jihoo.NativeBindingMachineReaderState

/-! Runtime owner aliases share the authorization of an actual enclosing named
reader of the same object. Exact lexical matches retain priority; fallback
consults only named reader frames, never continuation frames or heap-only
leases. Execution checks the selected lease; reachability proves it live. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

theorem readerForOwner_sound (found : readerForOwner object frame = some token) :
    ∃ name, frame.reader? = some (token,object,some name) := by
  cases descriptor : frame.reader? with
  | none => simp [readerForOwner,descriptor] at found
  | some entry =>
      rcases entry with ⟨candidate,owner,name⟩
      cases name with
      | none => simp [readerForOwner,descriptor] at found
      | some name =>
          simp only [readerForOwner,descriptor,bind,Option.bind] at found
          split at found
          · rename_i sameOwner
            subst owner
            cases found
            exact ⟨name,rfl⟩
          · contradiction

theorem readerForOwner_complete
    (found : frame.reader? = some (token,object,some name)) :
    readerForOwner object frame = some token := by
  simp [readerForOwner,found]

theorem activeOwnerLease_sound (found : activeOwnerLease object stack = some token) :
    ∃ frame ∈ stack, ∃ name, frame.reader? = some (token,object,some name) := by
  induction stack with
  | nil => simp [activeOwnerLease] at found
  | cons frame rest ih =>
      cases first : readerForOwner object frame with
      | none =>
          obtain ⟨selected,member,name,descriptor⟩ :=
            ih (by simpa only [activeOwnerLease,first,Option.orElse_none] using found)
          exact ⟨selected,List.mem_cons_of_mem _ member,name,descriptor⟩
      | some candidate =>
          have same : candidate = token := by
            simpa only [activeOwnerLease,first,Option.orElse_some,Option.some.injEq] using found
          subst candidate
          obtain ⟨name,descriptor⟩ := readerForOwner_sound first
          exact ⟨frame,List.mem_cons_self,name,descriptor⟩

theorem activeOwnerLease_complete (present : ReaderPresent name object stack) :
    ∃ token, activeOwnerLease object stack = some token := by
  induction stack with
  | nil => obtain ⟨frame,member,_⟩ := present; cases member
  | cons frame rest ih =>
      cases first : readerForOwner object frame with
      | some token => exact ⟨token,by simp only [activeOwnerLease,first,Option.orElse_some]⟩
      | none =>
          obtain ⟨selected,member,token,descriptor⟩ := present
          rcases List.mem_cons.mp member with rfl | member
          · rw [readerForOwner_complete descriptor] at first
            cases first
          · obtain ⟨token,found⟩ := ih ⟨selected,member,token,descriptor⟩
            exact ⟨token,by simpa only [activeOwnerLease,first,Option.orElse_none] using found⟩

/-- A matching outer lexical reader keeps its token even when a nearer reader
lends the same object through another alias. -/
theorem borrowLease_exact (found : activeLease key object stack = some token) :
    borrowLease key object stack = some token := by
  simp only [borrowLease,found,Option.orElse_some]

theorem borrowLease_sound (found : borrowLease key object stack = some token) :
    ∃ frame ∈ stack, ∃ name, frame.reader? = some (token,object,some name) := by
  cases exactName : activeLease key object stack with
  | none =>
      exact activeOwnerLease_sound
        (by simpa only [borrowLease,exactName,Option.orElse_none] using found)
  | some candidate =>
      have same : candidate = token := by
        simpa only [borrowLease,exactName,Option.orElse_some,Option.some.injEq] using found
      subst candidate
      obtain ⟨frame,member,descriptor⟩ := activeLease_sound exactName
      exact ⟨frame,member,key,descriptor⟩

/-- Any actual enclosing named reader for this object supplies a token, even
when the retained runtime alias has a different lexical key. -/
theorem borrowLease_complete (present : ReaderPresent name object stack) (key : Nat) :
    ∃ token, borrowLease key object stack = some token := by
  cases exactName : activeLease key object stack with
  | none =>
      obtain ⟨token,found⟩ := activeOwnerLease_complete present
      exact ⟨token,by simpa only [borrowLease,exactName,Option.orElse_none] using found⟩
  | some token => exact ⟨token,borrowLease_exact exactName⟩

theorem borrowLease_no_reader (absent : ∀ name, ¬ ReaderPresent name object stack) :
    borrowLease key object stack = none := by
  cases found : borrowLease key object stack with
  | none => rfl
  | some token =>
      obtain ⟨frame,member,name,descriptor⟩ := borrowLease_sound found
      exact False.elim (absent name ⟨frame,member,token,descriptor⟩)

/-- Aliasing cannot manufacture reader scope after all named readers for the
object have left the actual control stack. -/
theorem borrow_without_reader_faults (heap : SizedBufferHeap.State)
    (absent : ∀ name, ¬ ReaderPresent name object stack) :
    execute heap (.borrow key object stack) = (⟨heap,.fault .inactiveBorrow,stack⟩,none) := by
  simp only [execute,borrowLease_no_reader absent]

/-- Actual reachability supplies validity and live-lease correspondence. The
local owner slot and enclosing reader may use different lexical names. -/
theorem reachable_alias_borrow_executes (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .borrow (.var index))
    (stored : code.values[index]? = some (some (.owner object)))
    (present : ReaderPresent name object (run fuel (initial term)).state.stack) :
    ∃ token,
      (run fuel (initial term)).state.heap.heap.lease token = some object ∧
      (run fuel (initial term)).state.heap.heap.live object = true ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.returned (.reference token),
          (run fuel (initial term)).state.stack⟩,none) := by
  obtain ⟨token,found⟩ := borrowLease_complete present (code.context.length-index)
  obtain ⟨frame,member,name,descriptor⟩ := borrowLease_sound found
  have leased := initial_run_readers_live term fuel frame member token object (some name) descriptor
  have live := ((initial_run_heap_valid term fuel).leased token object leased).2
  refine ⟨token,leased,live,?_⟩
  simp only [step,action,evaluating,Option.map_some,evaluateAction,shape,stored,
    execute,found,leased,ite_true]

end Jihoo.NativeKernel.Environment.BindingMachine
