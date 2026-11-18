import Jihoo.NativeBindingMachineCanonicalBorrow

/-! Ordered source-loan occurrences retain their concrete reader identities.
Equal source frames, including frames identified by canonical alias rebasing,
remain separate list occurrences. Source authority can therefore be popped at
reader return without selecting the closing reader anew for every outer loan.
This relation does not type returned values or prove references cannot escape
inside arbitrary closures; those remain separate fundamental obligations. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

structure LoanReader where
  token : Nat
  object : Nat
  name : Nat
  deriving DecidableEq

def namedReader : Nat × Nat × Option Nat → Option LoanReader
  | (token,object,some name) => some ⟨token,object,name⟩
  | _ => none

def namedReaders (stack : List Frame) : List LoanReader :=
  (readerFrames stack).filterMap namedReader

theorem namedReaders_member (member : reader ∈ namedReaders stack) :
    (reader.token,reader.object,some reader.name) ∈ readerFrames stack := by
  obtain ⟨entry,entryMember,selected⟩ := List.mem_filterMap.mp member
  rcases entry with ⟨token,object,name⟩
  cases name with
  | none => cases selected
  | some name =>
      have same : (⟨token,object,name⟩ : LoanReader) = reader := Option.some.inj selected
      subst reader
      exact entryMember

def LoanPair (code : Code) (loan : Loans.Frame) (reader : LoanReader) : Prop :=
  ∃ index, loan.indexAt code.context.length = some index ∧
    code.values[index]? = some (some (.owner reader.object))

/-- Positional two-list pairing. It deliberately preserves duplicate source
frames instead of assigning a token to the source frame's structural value. -/
inductive LoanPairs (code : Code) : Loans.Stack → List LoanReader → Prop where
  | nil : LoanPairs code [] []
  | cons (loan : Loans.Frame) (reader : LoanReader)
      {loans : Loans.Stack} {readers : List LoanReader} :
      LoanPair code loan reader → LoanPairs code loans readers →
      LoanPairs code (loan :: loans) (reader :: readers)

theorem LoanPairs.member (paired : LoanPairs code loans readers) (member : loan ∈ loans) :
    ∃ reader ∈ readers, LoanPair code loan reader := by
  induction paired with
  | nil => cases member
  | cons first reader matched rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨reader,List.mem_cons_self,matched⟩
      · obtain ⟨selected,selectedMember,paired⟩ := ih member
        exact ⟨selected,List.mem_cons_of_mem _ selectedMember,paired⟩

theorem LoanPairs.entered (paired : LoanPairs code loans readers) :
    Loans.Entered code.context.length loans := by
  intro loan member
  obtain ⟨reader,_,index,found,_⟩ := paired.member member
  exact (Loans.Frame.indexAt_some.mp found).1

theorem LoanPairs.child (paired : LoanPairs code loans readers) (term : Term) :
    LoanPairs (code.child term) loans readers := by
  induction paired with
  | nil => exact .nil
  | cons loan reader matched rest ih => exact .cons loan reader matched ih

/-- The same concrete reader identities survive an ordinary source binder. -/
theorem LoanPairs.enter (paired : LoanPairs code loans readers)
    (erased : Bool) (domain body origin : Term) (argument : Option Value) :
    LoanPairs (enter erased domain body code.context code.origins code.values origin argument)
      loans readers := by
  induction paired with
  | nil => exact .nil
  | cons loan reader matched rest ih =>
      obtain ⟨index,found,stored⟩ := matched
      obtain ⟨before,same⟩ := Loans.Frame.indexAt_some.mp found
      refine .cons loan reader ⟨index+1,?_,stored⟩ ih
      apply Loans.Frame.indexAt_some.mpr
      simp only [BindingMachine.enter,List.length_cons]
      constructor <;> omega

/-- Rebasing changes only source snapshots. Noninjective aliases may identify
their owner slots while each occurrence keeps its original reader identity. -/
theorem LoanPairs.canonical (view : CanonicalView actual source indices)
    (paired : LoanPairs actual loans readers) :
    LoanPairs source (Loans.rebase actual.context.length source.context.length indices loans) readers := by
  induction paired with
  | nil => exact .nil
  | cons loan reader matched rest ih =>
      obtain ⟨index,found,stored⟩ := matched
      simp only [Loans.rebase,List.filterMap_cons,found,Option.map_some]
      refine .cons _ reader ⟨indices index,?_,(view.values index).symm.trans stored⟩ ih
      simp [Loans.Frame.indexAt]

def LoanScope (code : Code) (loans : Loans.Stack) (stack : List Frame) : Prop :=
  ∃ readers, LoanPairs code loans readers ∧ readers.Sublist (namedReaders stack)

theorem LoanScope.initial (term : Term) : LoanScope (.initial term) [] [] :=
  ⟨[],.nil,.slnil⟩

theorem LoanScope.entered (scope : LoanScope code loans stack) :
    Loans.Entered code.context.length loans := by
  obtain ⟨readers,paired,_⟩ := scope
  exact paired.entered

theorem LoanScope.child (scope : LoanScope code loans stack) (term : Term) :
    LoanScope (code.child term) loans stack := by
  obtain ⟨readers,paired,ordered⟩ := scope
  exact ⟨readers,paired.child term,ordered⟩

/-- Administrative control changes need only preserve the existing concrete
reader projection; no Borrow interpreter or successful lookup is mentioned. -/
theorem LoanScope.same_readers (scope : LoanScope code loans before)
    (same : readerFrames before = readerFrames after) : LoanScope code loans after := by
  obtain ⟨readers,paired,ordered⟩ := scope
  refine ⟨readers,paired,?_⟩
  change readers.Sublist ((readerFrames after).filterMap namedReader)
  rw [← same]
  exact ordered

/-- Saved code may run under additional enclosing readers while retaining its
original reader identities and source permissions. -/
theorem LoanScope.extend (scope : LoanScope code loans before)
    (extension : (readerFrames before).Sublist (readerFrames after)) : LoanScope code loans after := by
  obtain ⟨readers,paired,ordered⟩ := scope
  exact ⟨readers,paired,ordered.trans (extension.filterMap namedReader)⟩

theorem LoanScope.cons_frame (scope : LoanScope code loans stack) (frame : Frame) :
    LoanScope code loans (frame :: stack) :=
  scope.extend ((List.sublist_cons_self frame stack).filterMap Frame.reader?)

theorem LoanScope.enter (scope : LoanScope code loans stack)
    (erased : Bool) (domain body origin : Term) (argument : Option Value) :
    LoanScope (enter erased domain body code.context code.origins code.values origin argument) loans stack := by
  obtain ⟨readers,paired,ordered⟩ := scope
  exact ⟨readers,paired.enter erased domain body origin argument,ordered⟩

theorem LoanScope.canonical (view : CanonicalView actual source indices)
    (scope : LoanScope actual loans stack) :
    LoanScope source (Loans.rebase actual.context.length source.context.length indices loans) stack := by
  obtain ⟨readers,paired,ordered⟩ := scope
  exact ⟨readers,paired.canonical view,ordered⟩

/-- The ordered association supplies the local owner/reader authority used by
the canonical Borrow and Index theorems. Runtime lexical names may differ. -/
theorem LoanScope.ownerLoanSlots (scope : LoanScope code loans stack) :
    OwnerLoanSlots code loans stack := by
  intro index active
  obtain ⟨loan,member,before,same⟩ := Loans.active_iff.mp active
  obtain ⟨readers,paired,ordered⟩ := scope
  obtain ⟨reader,readerMember,other,found,stored⟩ := paired.member member
  have sourceFound := Loans.Frame.indexAt_some.mpr ⟨before,same⟩
  have equal : index = other := Option.some.inj (sourceFound.symm.trans found)
  subst other
  have observed := namedReaders_member (ordered.subset readerMember)
  obtain ⟨frame,frameMember,descriptor⟩ := List.mem_filterMap.mp observed
  exact ⟨reader.object,reader.name,stored,frame,frameMember,reader.token,descriptor⟩

/-- Entry pairs the NEW source occurrence with the NEW concrete named reader;
outer equal-owner loans retain their distinct original list positions. -/
theorem LoanScope.begin_reader (scope : LoanScope code loans stack)
    (stored : code.values[owner]? = some (some (.owner object)))
    (token name : Nat) (origin readerOrigin : Term) (continuation : Code) :
    LoanScope code (Loans.enter code.context.length owner loans)
      (.lendReader token object (some name) origin readerOrigin continuation :: stack) := by
  obtain ⟨readers,paired,ordered⟩ := scope
  refine ⟨⟨token,object,name⟩ :: readers,.cons _ _ ⟨owner,?_,stored⟩ paired,?_⟩
  · simp [Loans.Frame.indexAt]
  · change (⟨token,object,name⟩ :: readers).Sublist (⟨token,object,name⟩ :: namedReaders stack)
    exact ordered.cons_cons _

theorem LoanScope.reader_body (scope : LoanScope code loans
    (.lendReader token object name origin readerOrigin continuation :: stack)) (resultOrigin : Term) :
    LoanScope code loans (.lendFinish token object name origin resultOrigin continuation :: stack) := scope

/-- Pop source and runtime reader heads together. Ordering prevents an outer
source occurrence from remaining attached to the removed runtime head. -/
theorem LoanScope.pop (scope : LoanScope code (loan :: loans) before)
    (shape : readerFrames before = (token,object,some name) :: readerFrames after) :
    LoanScope code loans after := by
  obtain ⟨readers,paired,ordered⟩ := scope
  cases paired with
  | cons first reader matched rest =>
      refine ⟨_,rest,?_⟩
      change (reader :: _).Sublist ((readerFrames before).filterMap namedReader) at ordered
      rw [shape] at ordered
      change (reader :: _).Sublist (⟨token,object,name⟩ :: namedReaders after) at ordered
      exact ordered.of_cons_cons

/-- Actual reader inventory supplies all retained linked leases. Successful
Borrow execution and post-value typing are not premises. -/
theorem LoanScope.live_links (scope : LoanScope code loans stack)
    (inventory : ReaderInventory heap (readerFrames stack)) :
    ∃ readers, LoanPairs code loans readers ∧ readers.Sublist (namedReaders stack) ∧
      ∀ reader ∈ readers, heap.heap.lease reader.token = some reader.object := by
  obtain ⟨readers,paired,ordered⟩ := scope
  refine ⟨readers,paired,ordered,?_⟩
  intro reader member
  exact inventory.live _ (namedReaders_member (ordered.subset member))

/-- Closing an actual named reader constructs the outer source association
and preserves every retained linked lease. Token distinctness derives that
none of those links can be the closed token, even when objects/names coincide.
No post-close authority or close-success certificate is supplied. -/
theorem LoanScope.finish (scope : LoanScope code (loan :: loans)
    (.lendFinish token object (some name) origin resultOrigin continuation :: stack))
    (inventory : ReaderInventory heap (readerFrames
      (.lendFinish token object (some name) origin resultOrigin continuation :: stack)))
    (result : Value) :
    execute heap (.close token object result origin resultOrigin continuation stack) =
      (⟨SizedBufferHeap.close heap token,.evaluate continuation,
        .lendContinuation object origin resultOrigin result :: stack⟩,some (.heap (.close token))) ∧
    LoanScope code loans stack ∧
    ReaderInventory (SizedBufferHeap.close heap token) (readerFrames stack) ∧
    ∃ readers, LoanPairs code loans readers ∧ readers.Sublist (namedReaders stack) ∧
      ∀ reader ∈ readers, reader.token ≠ token ∧
        (SizedBufferHeap.close heap token).heap.lease reader.token = some reader.object := by
  have remainingScope := scope.pop (after := stack) rfl
  change ReaderInventory heap ((token,object,some name) :: readerFrames stack) at inventory
  obtain ⟨leased,remaining⟩ := inventory.finish
  obtain ⟨readers,paired,ordered,live⟩ := remainingScope.live_links remaining
  refine ⟨?_,remainingScope,remaining,readers,paired,ordered,?_⟩
  · simp only [execute,leased,ite_true]
  · intro reader member
    refine ⟨?_,live reader member⟩
    intro same
    apply (List.nodup_cons.mp inventory.distinct).1
    exact List.mem_map.mpr
      ⟨(reader.token,reader.object,some reader.name),namedReaders_member (ordered.subset member),same⟩

end Jihoo.NativeKernel.Environment.BindingMachine
