import Jihoo.NativeBindingMachineCanonicalVariables
import Jihoo.NativeBindingMachineAliasLoans
import Jihoo.NativeBindingMachineSizedBorrow

/-! Canonical source loans authorize Borrow through actual retained owner
aliases. Canonical and runtime lexical keys may differ, and the alias map may
be noninjective. Actual reader scope and immutable allocation sizes supply the
returned reference's lease and exact dependent type. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

/-- Source permissions identify physical owner slots and an enclosing named
reader. Canonical aliases need not retain that reader's runtime lexical key. -/
def OwnerLoanSlots (code : Code) (loans : Loans.Stack) (stack : List Frame) : Prop :=
  ∀ index, Loans.active code.context.length loans index = true →
    ∃ object name, code.values[index]? = some (some (.owner object)) ∧ ReaderPresent name object stack

theorem LoanSlots.ownerLoanSlots (slots : LoanSlots code loans stack) :
    OwnerLoanSlots code loans stack := by
  intro index permission
  obtain ⟨object,stored,present⟩ := slots index permission
  exact ⟨object,code.context.length-index,stored,present⟩

theorem OwnerLoanSlots.initial (term : Term) : OwnerLoanSlots (.initial term) [] [] := by
  intro index permission
  cases permission

theorem OwnerLoanSlots.child (slots : OwnerLoanSlots code loans stack) (term : Term) :
    OwnerLoanSlots (code.child term) loans stack := slots

/-- Rebasing source loans through a canonical alias map preserves physical
reader authority even when several actual slots become one source slot. -/
theorem OwnerLoanSlots.canonical (view : CanonicalView actual source indices)
    (slots : OwnerLoanSlots actual loans stack) :
    OwnerLoanSlots source (Loans.rebase actual.context.length source.context.length indices loans) stack := by
  intro index permission
  obtain ⟨selected,selectedMember,before,same⟩ := Loans.active_iff.mp permission
  obtain ⟨frame,frameMember,mapped⟩ := List.mem_filterMap.mp selectedMember
  obtain ⟨owner,found,equality⟩ := Option.map_eq_some_iff.mp mapped
  cases equality
  have same : index = indices owner := by simpa only [Nat.sub_self,Nat.add_zero] using same
  have allowed : Loans.active actual.context.length loans owner = true :=
    Loans.active_iff.mpr ⟨frame,frameMember,Loans.Frame.indexAt_some.mp found⟩
  obtain ⟨object,name,stored,present⟩ := slots owner allowed
  refine ⟨object,name,?_,present⟩
  rw [same]
  exact (view.values owner).symm.trans stored

/-- Ordinary captured bindings preserve the owner association without any
equality between canonical source keys and runtime reader keys. -/
theorem OwnerLoanSlots.enter (slots : OwnerLoanSlots code loans stack)
    (entered : Loans.Entered code.context.length loans)
    (erased : Bool) (domain body argumentOrigin : Term) (argument : Option Value) :
    OwnerLoanSlots (enter erased domain body code.context code.origins code.values argumentOrigin argument)
      loans stack := by
  intro index active
  change Loans.active (code.context.length+1) loans index = true at active
  cases index with
  | zero =>
      obtain ⟨frame,member,before,same⟩ := Loans.active_iff.mp active
      have previous := entered frame member
      omega
  | succ index =>
      have permission : Loans.active code.context.length loans index = true := by
        simpa only [Loans.active_weaken entered] using active
      obtain ⟨object,name,stored,present⟩ := slots index permission
      exact ⟨object,name,by simpa only [BindingMachine.enter,List.getElem?_cons_succ] using stored,present⟩

/-- A canonical source owner can acquire the reader recorded under an actual
alias's name. The source and runtime names are independent. -/
theorem OwnerLoanSlots.begin_reader (slots : OwnerLoanSlots code loans stack)
    (stored : code.values[owner]? = some (some (.owner object)))
    (token name : Nat) (origin readerOrigin : Term) (continuation : Code) :
    OwnerLoanSlots code (Loans.enter code.context.length owner loans)
      (.lendReader token object (some name) origin readerOrigin continuation :: stack) := by
  intro index active
  rw [Loans.active_enter,Bool.or_eq_true] at active
  rcases active with same | previous
  · have identity : owner = index := by simpa only [beq_iff_eq] using same
    subst index
    exact ⟨object,name,stored,_,List.mem_cons_self,token,rfl⟩
  · obtain ⟨object,name,stored,frame,member,token,descriptor⟩ := slots index previous
    exact ⟨object,name,stored,frame,List.mem_cons_of_mem _ member,token,descriptor⟩

theorem OwnerLoanSlots.reader_body (slots : OwnerLoanSlots code loans
    (.lendReader token object name origin readerOrigin continuation :: stack)) (resultOrigin : Term) :
    OwnerLoanSlots code loans
      (.lendFinish token object name origin resultOrigin continuation :: stack) := by
  intro index permission
  obtain ⟨owner,key,stored,frame,member,selected,descriptor⟩ := slots index permission
  refine ⟨owner,key,stored,?_⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨_,List.mem_cons_self,selected,descriptor⟩
  · exact ⟨frame,List.mem_cons_of_mem _ member,selected,descriptor⟩

/-- Source Borrow permission chooses the canonical owner slot. Its saved
value and actual enclosing reader construct a real step through any alias;
no separate runtime-slot loan invariant is required. -/
theorem reachable_canonical_borrow (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (slots : OwnerLoanSlots source loans (run fuel (initial term)).state.stack)
    (shape : actual.term = .borrow (.var index)) :
    ∃ token object,
      actual.values[index]? = some (some (.owner object)) ∧
      (run fuel (initial term)).state.heap.heap.lease token = some object ∧
      (run fuel (initial term)).state.heap.heap.live object = true ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.returned (.reference token),
          (run fuel (initial term)).state.stack⟩,none) := by
  have sourceShape : source.term = .borrow (.var (indices index)) := by
    rw [← view.termEq,shape]
    simp only [rename_borrow,Term.rename]
  obtain ⟨closing,localType,sourceTyped,converted⟩ := typed
  rw [sourceShape] at sourceTyped
  obtain ⟨named,namedShape,permission⟩ := sourceTyped.code_borrow_named
  have same : indices index = named := Term.var.inj namedShape
  subst named
  obtain ⟨object,name,stored,present⟩ := slots (indices index) permission
  have actualStored := (view.values index).trans stored
  obtain ⟨token,leased,live,next⟩ :=
    reachable_alias_borrow_executes term fuel evaluating shape actualStored present
  exact ⟨token,object,actualStored,leased,live,next⟩

/-- Canonical source allocation sizes realize the actual Borrow result at
the original closed requested type, including dependent result conversions.
No actual owner, selected lease, read guard or output interpretation is an
input, and canonical/runtime name equality is unnecessary. -/
theorem reachable_canonical_sized_borrow (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap source meanings)
    (slots : OwnerLoanSlots source loans (run fuel (initial term)).state.stack)
    (shape : actual.term = .borrow (.var index)) :
    ∃ token, ReferenceSize env (run fuel (initial term)).state.heap token type ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.returned (.reference token),
          (run fuel (initial term)).state.stack⟩,none) := by
  obtain ⟨token,object,actualStored,leased,live,next⟩ :=
    reachable_canonical_borrow term fuel evaluating view typed slots shape
  have sourceStored := (view.values index).symm.trans actualStored
  have sourceShape : source.term = .borrow (.var (indices index)) := by
    rw [← view.termEq,shape]
    simp only [rename_borrow,Term.rename]
  obtain ⟨closing,localType,sourceTyped,converted⟩ := typed
  rw [sourceShape] at sourceTyped
  obtain ⟨ownerType,ownerTyped,referenceConverted⟩ := sourceTyped.principalView
  obtain ⟨bound,count,length,bufferConverted⟩ :=
    sizes.typed_variable history ownerTyped sourceStored
  have closedReference : LoanTyping.Conversion.Conv env (.ref (ownerType.subst meanings)) type := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      (referenceConverted.substitution meanings history.wellFormed.closed).trans converted
  have actualReference : LoanTyping.Conversion.Conv env (.ref (.buffer (.natural count))) type :=
    (RawLend.Conv.node .ref (.cons bufferConverted .nil)).trans closedReference
  exact ⟨token,⟨object,count,leased,live,length,actualReference⟩,next⟩

end Jihoo.NativeKernel.Environment.BindingMachine
