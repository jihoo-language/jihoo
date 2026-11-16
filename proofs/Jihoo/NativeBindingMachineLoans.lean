import Jihoo.NativeBindingMachineHeap
import Jihoo.NativeLoanPermissions
import Jihoo.NativeLoanMixedProgram

/-! A bridge from the full Loan64 source permission to actual machine Borrow.
Runtime slots identify the owner and real reader frames identify its lease.
Neither successful Borrow execution nor a returned-value typing certificate is
an input. General preservation of these runtime invariants remains separate. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

def ReaderPresent (key object : Nat) (stack : List Frame) : Prop :=
  ∃ frame ∈ stack, ∃ token, frame.reader? = some (token,object,some key)

def ReadersLive (heap : SizedBufferHeap.State) (stack : List Frame) : Prop :=
  ∀ frame ∈ stack, ∀ token object name, frame.reader? = some (token,object,name) →
    heap.heap.lease token = some object

theorem ReadersLive.begin_reader (valid : SizedBufferHeap.Valid heap)
    (readers : ReadersLive heap stack) (object : Nat) (name : Option Nat)
    (origin readerOrigin : Term) (continuation : Code) :
    ReadersLive (SizedBufferHeap.lend heap object)
      (.lendReader heap.heap.nextLease object name origin readerOrigin continuation :: stack) := by
  intro frame member token owner key descriptor
  rcases List.mem_cons.mp member with rfl | member
  · simp only [Frame.reader?,Option.some.injEq,Prod.mk.injEq] at descriptor
    obtain ⟨rfl,rfl,rfl⟩ := descriptor
    simp only [SizedBufferHeap.lend,HeapLeases.put,ite_true]
  · have leased := readers frame member token owner key descriptor
    have earlier := (valid.leased token owner leased).1
    have different : token ≠ heap.heap.nextLease := by omega
    simpa [SizedBufferHeap.lend,HeapLeases.put,different] using leased

theorem ReadersLive.reader_body (readers : ReadersLive heap
    (.lendReader token object name origin readerOrigin continuation :: stack)) (resultOrigin : Term) :
    ReadersLive heap (.lendFinish token object name origin resultOrigin continuation :: stack) := by
  intro frame member queried owner key descriptor
  rcases List.mem_cons.mp member with rfl | member
  · exact readers _ List.mem_cons_self queried owner key descriptor
  · exact readers _ (List.mem_cons_of_mem _ member) queried owner key descriptor

/-- Distinct outstanding reader tokens survive closing the finished reader.
The close guard follows from the frame invariant, rather than being assumed. -/
theorem ReadersLive.finish_reader
    (readers : ReadersLive heap (.lendFinish token object name origin resultOrigin continuation :: stack))
    (distinct : ∀ frame ∈ stack, ∀ other owner key,
      frame.reader? = some (other,owner,key) → other ≠ token) (result : Value) :
    execute heap (.close token object result origin resultOrigin continuation stack) =
      (⟨SizedBufferHeap.close heap token,.evaluate continuation,
        .lendContinuation object origin resultOrigin result :: stack⟩,some (.heap (.close token))) ∧
    ReadersLive (SizedBufferHeap.close heap token)
      (.lendContinuation object origin resultOrigin result :: stack) := by
  have leased := readers _ List.mem_cons_self token object name rfl
  constructor
  · simp only [execute,leased,ite_true]
  · intro frame member other owner key descriptor
    rcases List.mem_cons.mp member with rfl | member
    · cases descriptor
    · have live := readers _ (List.mem_cons_of_mem _ member) other owner key descriptor
      have different := distinct frame member other owner key descriptor
      simpa [SizedBufferHeap.close,HeapLeases.put,different] using live

theorem readerFor_sound (found : readerFor key object frame = some token) :
    frame.reader? = some (token,object,some key) := by
  cases descriptor : frame.reader? with
  | none => simp [readerFor,descriptor] at found
  | some entry =>
      rcases entry with ⟨candidate,owner,name⟩
      cases name with
      | none => simp [readerFor,descriptor] at found
      | some name =>
          simp only [readerFor,descriptor,bind,Option.bind] at found
          split at found
          · rename_i sameOwner
            obtain ⟨rfl,rfl⟩ := sameOwner
            cases found
            rfl
          · contradiction

theorem readerFor_complete (found : frame.reader? = some (token,object,some key)) :
    readerFor key object frame = some token := by
  simp [readerFor,found]

theorem activeLease_sound (found : activeLease key object stack = some token) :
    ∃ frame ∈ stack, frame.reader? = some (token,object,some key) := by
  induction stack with
  | nil => simp [activeLease] at found
  | cons frame rest ih =>
      cases first : readerFor key object frame with
      | none =>
          obtain ⟨selected,member,descriptor⟩ := ih (by simpa only [activeLease,first,Option.orElse_none] using found)
          exact ⟨selected,List.mem_cons_of_mem _ member,descriptor⟩
      | some candidate =>
          have same : candidate = token := by simpa only [activeLease,first,Option.orElse_some,Option.some.injEq] using found
          subst candidate
          exact ⟨frame,List.mem_cons_self,readerFor_sound first⟩

theorem activeLease_complete (present : ReaderPresent key object stack) :
    ∃ token, activeLease key object stack = some token := by
  induction stack with
  | nil => obtain ⟨frame,member,_⟩ := present; cases member
  | cons frame rest ih =>
      cases first : readerFor key object frame with
      | some token => exact ⟨token,by simp only [activeLease,first,Option.orElse_some]⟩
      | none =>
          obtain ⟨selected,member,token,descriptor⟩ := present
          rcases List.mem_cons.mp member with rfl | member
          · rw [readerFor_complete descriptor] at first
            cases first
          · obtain ⟨token,found⟩ := ih ⟨selected,member,token,descriptor⟩
            exact ⟨token,by simpa only [activeLease,first,Option.orElse_none] using found⟩

/-- Active source names refer to concrete owner slots and lexical reader
frames. This invariant does not mention the Borrow interpreter or its guard. -/
def LoanSlots (code : Code) (loans : Loans.Stack) (stack : List Frame) : Prop :=
  ∀ index, Loans.active code.context.length loans index = true →
    ∃ object, code.values[index]? = some (some (.owner object)) ∧
      ReaderPresent (code.context.length-index) object stack

theorem typed_borrow_executes
    (valid : SizedBufferHeap.Valid heap) (liveReaders : ReadersLive heap stack)
    (slots : LoanSlots code loans stack)
    (typed : LoanTyping.HasType env loans code.context false code.term type)
    (shape : code.term = .borrow owner) :
    ∃ token object, heap.heap.lease token = some object ∧ heap.heap.live object = true ∧
      execute heap (evaluateAction code stack) = (⟨heap,.returned (.reference token),stack⟩,none) := by
  rw [shape] at typed
  obtain ⟨index,rfl,permitted⟩ := typed.code_borrow_named
  obtain ⟨object,stored,present⟩ := slots index permitted
  obtain ⟨token,found⟩ := activeLease_complete present
  obtain ⟨frame,member,descriptor⟩ := activeLease_sound found
  have leased := liveReaders frame member token object (some (code.context.length-index)) descriptor
  exact ⟨token,object,leased,(valid.leased token object leased).2,
    by simp only [evaluateAction,shape,stored,execute,found,leased,ite_true]⟩

theorem closed_lease_cannot_be_read (heap : SizedBufferHeap.State) (token index : Nat) (stack : List Frame) :
    execute (SizedBufferHeap.close heap token) (.read token index stack) =
      (⟨SizedBufferHeap.close heap token,.fault .closedLease,stack⟩,none) := by
  simp only [execute,SizedBufferHeap.close,HeapLeases.put,ite_true]

theorem continuation_is_not_a_reader (object : Nat) (ownerOrigin resultOrigin : Term) (result : Value) :
    (Frame.lendContinuation object ownerOrigin resultOrigin result).reader? = none := rfl

theorem owner_argument_is_not_a_reader (object : Nat) (ownerOrigin : Term) :
    (Frame.lendOwnerArgument object ownerOrigin).reader? = none := rfl

end Jihoo.NativeKernel.Environment.BindingMachine
