import Jihoo.NativeBindingMachineSizedIndex

/-! A source-authorized Borrow returns a reference to a live concrete Buffer
whose actual allocation length realizes its exact closed source type. Static
size interpretation supplies lengths; reader inventory supplies authority. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

/-- Current heap realization of a reference, including its live lease and the
actual dependent Buffer length. It does not grant a deallocation capability. -/
def ReferenceSize (env : Environment) (heap : SizedBufferHeap.State) (token : Nat) (type : Term) : Prop :=
  ∃ object count, heap.heap.lease token = some object ∧ heap.heap.live object = true ∧
    heap.length object = count ∧ LoanTyping.Conversion.Conv env (.ref (.buffer (.natural count))) type

/-- All guard, owner and type witnesses are derived from source typing,
constructed owner sizes, source loan slots and actual reachability. No stored
owner, output reference typing or successful Borrow is a caller certificate. -/
theorem reachable_sized_borrow (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (shape : code.term = .borrow (.var owner))
    (slots : LoanSlots code loans (run fuel (initial term)).state.stack) :
    ∃ token, ReferenceSize env (run fuel (initial term)).state.heap token type ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.returned (.reference token),
          (run fuel (initial term)).state.stack⟩,none) := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨named,namedShape,permission⟩ := source.code_borrow_named
  have same : owner = named := Term.var.inj namedShape
  subst named
  obtain ⟨object,stored,present⟩ := slots owner permission
  obtain ⟨ownerType,ownerTyped,referenceConverted⟩ := source.principalView
  obtain ⟨bound,count,length,bufferConverted⟩ := sizes.typed_variable history ownerTyped stored
  have closedReference : LoanTyping.Conversion.Conv env (.ref (ownerType.subst meanings)) type := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      (referenceConverted.substitution meanings history.wellFormed.closed).trans converted
  have actualReference : LoanTyping.Conversion.Conv env (.ref (.buffer (.natural count))) type :=
    (RawLend.Conv.node .ref (.cons bufferConverted .nil)).trans closedReference
  obtain ⟨token,found⟩ := activeLease_complete present
  obtain ⟨frame,member,descriptor⟩ := activeLease_sound found
  have leased := initial_run_readers_live term fuel frame member token object
    (some (code.context.length-owner)) descriptor
  have live := (initial_run_heap_valid term fuel).leased token object leased |>.2
  refine ⟨token,⟨object,count,leased,live,length,actualReference⟩,?_⟩
  simp only [step,action,evaluating,evaluateAction,shape,stored,execute,found,leased,ite_true,Option.map_some]

end Jihoo.NativeKernel.Environment.BindingMachine
