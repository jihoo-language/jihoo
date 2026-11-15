import Jihoo.NativeBindingMachineReaderResume
import Jihoo.NativeBindingMachineNumeric

/-! Fresh owned reader results: source-derived literal widths, checked linear
first-result mode, actual allocation identity/length and distinct ownership at
the retained continuation. No returned-value typing or success oracle is used.
General source/control/resource interpretation remains an open obligation. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def ScalarLiteralBounds : Term → Prop
  | .natural value => value < 2^64
  | .integer value => ValueReduction.signed64 value
  | _ => True

private theorem literal_bounds (typed : HasType env loans ctx mode term type) : ScalarLiteralBounds term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term _ _ => ScalarLiteralBounds term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case dataElim => split <;> trivial

theorem HasType.natural_bound (typed : HasType env loans ctx mode (.natural value) type) : value < 2^64 :=
  literal_bounds typed

theorem HasType.integer_bound (typed : HasType env loans ctx mode (.integer value) type) :
    ValueReduction.signed64 value := literal_bounds typed

private def AllocationInputs (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool) : Term → Prop
  | .alloc count fill => HasType env loans ctx mode count .u64 ∧ HasType env loans ctx mode fill .i64
  | _ => True

theorem HasType.alloc_inputs (typed : HasType env loans ctx mode (.alloc count fill) type) :
    HasType env loans ctx mode count .u64 ∧ HasType env loans ctx mode fill .i64 := by
  have general : ∀ {term type}, HasType env loans ctx mode term type → AllocationInputs env loans ctx mode term := by
    intro term type source
    apply HasType.rec (t := source)
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun stack context ghost term _ _ => AllocationInputs env stack context ghost term)
      (motive_3 := fun _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ => True)
    all_goals intros
    all_goals first | trivial | assumption | skip
    case dataElim => split <;> trivial
  exact general typed

namespace ResourceModes

/-- Successful normalization preserves Buffer's rigid head, even with a
computed dependent size. An abstract-kind fallback cannot classify this head. -/
theorem Resolved.buffer_linear (resolved : Resolved env loans ctx false (.buffer size) mode) :
    mode = .linear := by
  cases resolved with
  | head normalized known =>
      obtain ⟨children,shape,related⟩ := (Conversion.normalize?_forward normalized).rigid_shape rfl rfl
      cases related with
      | cons first rest =>
          cases rest
          rw [shape] at known
          simpa only [ContextModes.head,NativeQuantity.binderMode,Bool.false_eq_true,↓reduceIte,Option.some.injEq] using known.symm
  | abstract normalized spine =>
      obtain ⟨children,shape,related⟩ := (Conversion.normalize?_forward normalized).rigid_shape rfl rfl
      cases related with
      | cons first rest =>
          cases rest
          rw [shape] at spine
          cases spine

end ResourceModes

namespace ResourceQuantity
open Jihoo.Quantity
variable {control : Control}

/-- The same checked Lend supplies two separate exact-once obligations. The
first mode is derived from its Buffer annotation, not an ownership oracle. -/
theorem dependent_buffer_first_contract
    (checked : project (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody)
        (.lam false (.buffer size) (.lam false again body))) = some control) :
    ∃ reader rest,
      projectRaw fuel env (Loans.enter ctx.length owner loans) ctx (Lending.read (.var owner) readerBody) = some reader ∧
      projectRaw fuel env loans (⟨.buffer size,false⟩ :: ctx)
        (body.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      reader.demand owner = some 0 ∧ rest.demand 0 = some 1 ∧ rest.demand (owner+1) = some 1 ∧
      (∀ events, Finishes rest events → events.count 0 = 1 ∧ events.count (owner+1) = 1) ∧
      (∀ events, Prefix rest events → events.count 0 ≤ 1 ∧ events.count (owner+1) ≤ 1) := by
  obtain ⟨outside,sort,resultType,reader,mode,rest,originalScope,readScope,restScope,
    formed,controlScoped,sourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,
    readZero,restOne,same⟩ := dependent_project_contract checked
  have modeSame := resolved.buffer_linear
  subst mode
  have firstOne : rest.demand 0 = some 1 := (NativeQuantity.demand_localScopes _ restOne).1
  have ownerOne : rest.demand (owner+1) = some 1 := Jihoo.Quantity.scopes_outer (modes := [.linear]) restOne
  exact ⟨reader,rest,readProjected,restProjected,readZero,firstOne,ownerOne,
    fun events run => ⟨run.count_eq firstOne,run.count_eq ownerOne⟩,
    fun events run => ⟨run.count_le firstOne,run.count_le ownerOne⟩⟩

end ResourceQuantity
end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- The actual resource check's specialized reader supplies the declared first
result type as well as both literal widths, using the same source closing. -/
theorem LoanSourceTyped.allocating_first
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend (.var owner) (.lam false domain (.alloc (.natural count) (.integer fill)))
      (.lam false first (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.project (fuel+1) env loans code.context code.term = some control) :
    count < 2^64 ∧ ValueReduction.signed64 fill ∧
      LoanTyping.Conversion.Conv env (.buffer (.natural count)) (first.subst code.origins) := by
  rw [shape] at checked
  obtain ⟨outside,sort,resultType,reader,mode,rest,originalScope,readScope,restScope,
    formed,controlScoped,sourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,
    readZero,restOne,same⟩ := LoanTyping.ResourceQuantity.dependent_project_contract checked
  have allocationTyped : LoanTyping.HasType env [] [] true (.alloc (.natural count) (.integer fill))
      (first.subst code.origins) := by
    have closed := readTyped.ghostSubstitution history.wellFormed typed.1
    simpa only [Lending.read,Term.subst,substArgs,Op.binders,liftSub] using closed
  exact ⟨allocationTyped.alloc_inputs.1.natural_bound,allocationTyped.alloc_inputs.2.integer_bound,
    allocationTyped.principalView⟩

/-- Semantic interpretation of an actual Buffer value at its closed source
type: a live concrete owner with the source length, modulo Loan64 conversion.
It does not assert an exclusive capability or type arbitrary captured values. -/
def BufferValue (env : Environment) (heap : SizedBufferHeap.State) (value : Value) (type : Term) : Prop :=
  ∃ object count, value = .owner object ∧ heap.heap.live object = true ∧ heap.length object = count ∧
    LoanTyping.Conversion.Conv env (.buffer (.natural count)) type

theorem BufferValue.allocate
    (converted : LoanTyping.Conversion.Conv env (.buffer (.natural count)) type) :
    BufferValue env (SizedBufferHeap.allocate heap count fill) (.owner heap.heap.nextObject) type := by
  exact ⟨heap.heap.nextObject,count,rfl,by simp [SizedBufferHeap.allocate,HeapLeases.put],
    SizedBufferHeap.allocation_length,converted⟩

theorem freeGuard_of_unborrowed (unborrowed : HeapLeases.Unborrowed heap.heap object) :
    freeGuard heap object = true := by
  apply List.all_eq_true.mpr
  intro token member
  exact decide_eq_true (unborrowed token)

/-- Allocation cannot alias an existing leased owner; no earlier lease can
authorize a read of the newly returned object. -/
theorem allocated_reader_fresh (valid : SizedBufferHeap.Valid heap)
    (leased : heap.heap.lease token = some object) (count fill : Nat) :
    heap.heap.nextObject ≠ object ∧
      HeapLeases.Unborrowed (SizedBufferHeap.allocate heap count fill).heap heap.heap.nextObject ∧
      freeGuard (SizedBufferHeap.allocate heap count fill) heap.heap.nextObject = true := by
  have old := valid.allocated object (valid.leased token object leased).2
  have fresh : heap.heap.nextObject ≠ object := by omega
  have unborrowed : HeapLeases.Unborrowed (SizedBufferHeap.allocate heap count fill).heap heap.heap.nextObject := by
    intro queried present
    have live := (valid.leased queried heap.heap.nextObject present).2
    have allocated := valid.allocated _ live
    omega
  exact ⟨fresh,unborrowed,freeGuard_of_unborrowed unborrowed⟩

set_option linter.unusedSimpArgs false in
private theorem allocate_reader_five_steps (heap : SizedBufferHeap.State) (code : Code)
    (shape : code.term = .alloc (.natural count) (.integer fill))
    (countBound : count < 2^64) (fillBound : ValueReduction.signed64 fill)
    (stack : List Frame) :
    run 5 ⟨heap,.evaluate code,stack⟩ =
      if count*8+8 < 2^64 then
        ⟨⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.returned (.owner heap.heap.nextObject),stack⟩,
          [.heap (.alloc heap.heap.nextObject count (encodeInteger fill))],5⟩
      else ⟨⟨heap,.fault .allocationOverflow,stack⟩,[],5⟩ := by
  simp only [run,step,action,evaluateAction,shape,returnAction,execute,Code.child,
    countBound,fillBound,↓reduceIte,Option.map_some]
  split <;> simp_all only [↓reduceIte] <;> rfl

/-- Source typing constructs scalar widths and the exact Buffer interpretation
of a successful allocating reader. Reachability constructs freshness, liveness,
lease preservation and the Free guard. Byte-size overflow is reported explicitly.
No allocation/owner-slot association or output-value certificate is an input. -/
theorem reachable_allocating_reader (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend owner (.lam false domain (.alloc (.natural count) (.integer fill)))
      (.lam false first (.lam false again body)))
    (evaluating : (run fuel (initial term)).state.control = .evaluate
      (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
        (.borrow (owner.subst code.origins)) (some (.reference token))))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name (owner.subst code.origins)
        (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
          (.borrow (owner.subst code.origins)) (some (.reference token))).origin continuation :: stack) :
    let heap := (run fuel (initial term)).state.heap
    ∃ readerType,
      LoanTyping.Outlived env readerType ∧ count < 2^64 ∧ ValueReduction.signed64 fill ∧
      heap.heap.nextObject ≠ object ∧
      if count*8+8 < 2^64 then
        BufferValue env (SizedBufferHeap.allocate heap count (encodeInteger fill))
          (.owner heap.heap.nextObject) (readerType.subst code.origins) ∧
        (SizedBufferHeap.allocate heap count (encodeInteger fill)).heap.lease token = some object ∧
        freeGuard (SizedBufferHeap.allocate heap count (encodeInteger fill)) heap.heap.nextObject = true ∧
        run 5 (run fuel (initial term)).state =
          ⟨⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.returned (.owner heap.heap.nextObject),
            (run fuel (initial term)).state.stack⟩,
            [.heap (.alloc heap.heap.nextObject count (encodeInteger fill))],5⟩
      else run 5 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,(run fuel (initial term)).state.stack⟩,[],5⟩ := by
  obtain ⟨readerType,originTyped,outlived⟩ := typed_explicit_reader_origin history typed shape token
  have allocationTyped : LoanTyping.HasType env [] [] true (.alloc (.natural count) (.integer fill))
      (readerType.subst code.origins) := by
    simpa only [Code.origin,enter,Term.subst,substArgs,Op.binders,liftSub] using originTyped
  have countBound := allocationTyped.alloc_inputs.1.natural_bound
  have fillBound := allocationTyped.alloc_inputs.2.integer_bound
  have converted : LoanTyping.Conversion.Conv env (.buffer (.natural count)) (readerType.subst code.origins) :=
    allocationTyped.principalView
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  have leased := inventory.live _ (List.mem_filterMap.mpr ⟨_,List.mem_cons_self,rfl⟩)
  have fresh := allocated_reader_fresh (initial_run_heap_valid term fuel) leased count (encodeInteger fill)
  have readerCodeShape : (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
      (.borrow (owner.subst code.origins)) (some (.reference token))).term = .alloc (.natural count) (.integer fill) := rfl
  have executed := allocate_reader_five_steps (run fuel (initial term)).state.heap _ readerCodeShape countBound fillBound
    (run fuel (initial term)).state.stack
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,
        .evaluate (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
          (.borrow (owner.subst code.origins)) (some (.reference token))),
        (run fuel (initial term)).state.stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  rw [← stateShape] at executed
  refine ⟨readerType,outlived,countBound,fillBound,fresh.1,?_⟩
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte] at executed ⊢
    exact ⟨BufferValue.allocate converted,leased,fresh.2.2,executed⟩
  · simpa only [fits,↓reduceIte] using executed

end Jihoo.NativeKernel.Environment.BindingMachine
