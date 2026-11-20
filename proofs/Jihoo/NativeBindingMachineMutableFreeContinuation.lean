import Jihoo.NativeLoanLoadCallbackResources
import Jihoo.NativeLoanBorrowedBudget

/-! Free transfers the exact checked residual demand and original closing
to its successor. An admitted Store/Load callback supplies the input world
from actual execution, without an assumed liveness, guard, or tail proof. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity
variable {control : Control}

private theorem free_variable_any
    (checked : projectRaw fuel env loans ctx (.free (.var owner) tail) = some control) :
    ∃ tailFuel rest,
      projectRaw tailFuel env loans ctx tail = some rest ∧
      control = .seq (.use owner) (.seq rest .pure) := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [projectRaw,Op.arity,runtimeFields,erasedNode,fields,fetch] at checked
      | succ fuel =>
          obtain ⟨_,rest,_,_,recursive,shape⟩ := projectRaw_free_variable checked
          exact ⟨fuel+1,rest,recursive,shape⟩

theorem projectRaw_free_tail_receipt
    (checked : projectRaw fuel env loans ctx (.free (.var owner) tail) = some control)
    (used : control.demand owner = some 1) :
    ∃ tailFuel rest,
      projectRaw tailFuel env loans ctx tail = some rest ∧
      control = .seq (.use owner) (.seq rest .pure) ∧ rest.demand owner = some 0 ∧
      (∀ events, Jihoo.Quantity.Prefix rest events → events.count owner = 0) := by
  obtain ⟨tailFuel,rest,recursive,shape⟩ := free_variable_any checked
  have zero : rest.demand owner = some 0 := by
    rw [shape] at used
    cases tailDemand : rest.demand owner with
    | none => simp [Control.demand,tailDemand,bind,Option.bind] at used
    | some count =>
        simp [Control.demand,tailDemand,bind,Option.bind] at used
        have countZero : count = 0 := by omega
        simp [countZero]
  exact ⟨tailFuel,rest,recursive,shape,zero,fun _ observed => by
    have le := observed.count_le zero
    omega⟩

theorem projectRaw_free_callback_body
    (checked : projectRaw fuel env loans ctx (.free (.var owner) tail) = some control) :
    reclose (functionTail (.free (.var owner) tail) control) = control := by
  obtain ⟨_,rest,_,rfl⟩ := free_variable_any checked
  rfl

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

theorem run_add (first second : Nat) (state : State) :
    run (first+second) state =
      let before := run first state
      let after := run second before.state
      ⟨after.state,before.events ++ after.events,before.steps+after.steps⟩ := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add,run,List.nil_append]
  | succ count ih =>
      simp only [Nat.succ_add,run]
      cases selected : step state with
      | none =>
          have stopped (remaining : Nat) : run remaining state = ⟨state,[],0⟩ := by
            cases remaining <;> simp only [run,selected]
          simp only [stopped,List.nil_append,Nat.zero_add]
      | some transition =>
          obtain ⟨next,event⟩ := transition
          simp only
          rw [ih]
          simp only [List.append_assoc,Nat.add_assoc,Nat.add_comm]

private theorem raw_free_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .free (.var owner) tail)
    (stored : code.values[owner]? = some (some (.owner object)))
    (live : state.heap.metadata.heap.live object = true)
    (guard : freeGuard state.heap.metadata object = true) :
    let retired : SizedBufferHeap.IndexedState :=
      ⟨SizedBufferHeap.release state.heap.metadata object,state.heap.cell⟩
    run 3 state = ⟨⟨retired,.evaluate (code.child tail),state.stack,state.pending⟩,
      [.legacy (.heap (.free object))],3⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,stored,executeLegacy,execute,
    returnAction,live,guard,↓reduceIte,Option.map_none,Option.map_some]
  rfl

/-- For a typed variable Free at a reachable Mutable control point, the
exact loan budget and physical reader inventory supply its dynamic guard.
The actual successor retains the full original tail type and context. -/
theorem reachable_typed_variable_free (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .free (.var owner) tail)
    (typed : LoanClosingTyped env loans false code meanings type)
    (values : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata code meanings)
    (coverage : LoanCoverage code loans (run fuel (initial term)).state.activeStack)
    (stored : code.values[owner]? = some (some (.owner object)))
    (live : (run fuel (initial term)).state.heap.metadata.heap.live object = true)
    (checked : LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans code.context
      (.free (.var owner) tail) = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (one : receipt.demand owner = some 1) :
    let before := (run fuel (initial term)).state
    let result := run 3 before
    let after := result.state
    let next := code.child tail
    after.control = .evaluate next ∧ after.stack = before.stack ∧ after.pending = before.pending ∧
      after.heap.metadata.heap.live object = false ∧
      after.heap.metadata.length object = before.heap.metadata.length object ∧
      result.events = [.legacy (.heap (.free object))] ∧ result.steps = 3 ∧
      LoanClosingTyped env loans false next meanings type ∧ ValueContext env next meanings ∧
      OwnerSizes env after.heap.metadata next meanings ∧ LoanCoverage next loans after.activeStack ∧
      ∃ tailFuel residual,
        LoanTyping.ResourceQuantity.projectRaw tailFuel env loans next.context tail = some residual ∧
        LoanTyping.ResourceQuantity.LoanBudget next.context.length loans residual ∧
        residual.demand owner = some 0 ∧
        (∀ events, Jihoo.Quantity.Prefix residual events → events.count owner = 0) := by
  let before := (run fuel (initial term)).state
  obtain ⟨tailFuel,residual,tailProjected,receiptShape,zero,noUse⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_free_tail_receipt checked one
  have inactive : Loans.active code.context.length loans owner = false := by
    cases active : Loans.active code.context.length loans owner
    · rfl
    · have used := budget owner active
      rw [one] at used
      cases used
  have inventory := initial_run_invariant term fuel
  have guard := (inventory.2.free_guard_iff inventory.1).mpr (coverage.inactive stored inactive)
  have ran := raw_free_steps before evaluating shape stored live guard
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  have successor : LoanClosingTyped env loans false (code.child tail) meanings type :=
    ⟨closing,localType,source.free_tail,converted⟩
  have nextSizes := (reachable_run_owner_sizes term fuel 3 sizes).child tail
  have tailBudget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans residual := by
    rw [receiptShape] at budget
    exact budget.sequence.2.sequence.1
  dsimp only at ran ⊢
  rw [ran] at nextSizes ⊢
  exact ⟨rfl,rfl,rfl,by simp [SizedBufferHeap.release,HeapLeases.put],rfl,rfl,rfl,successor,
    values.child tail,nextSizes,coverage.child tail,tailFuel,residual,tailProjected,tailBudget,zero,noUse⟩

/-- An admitted Store/Load callback starting with Free executes the complete
22-step allocation, update, read, and release prefix. Its arbitrary checked
tail retains the original type, and the released owner has zero remaining
source demand. Neither the Free guard nor any tail judgment is a premise. -/
theorem checked_closed_store_load_free_continuation
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (accepted : LoanTyping.MixedProgram.checkDeclaration fuel quantityFuel env source =
      some ⟨type,storeLoadWith count offset fill value
        (.lam false first (.lam false again (.free (.var 0) tail)))⟩)
    (sorted : LoanTyping.Checker.sort fuel env [] [] type = some (.type level))
    (fits : count*8+8 < 2^64) :
    let program := storeLoadWith count offset fill value
      (.lam false first (.lam false again (.free (.var 0) tail)))
    let code := storeLoadEntry count offset fill value first again (.free (.var 0) tail)
    let next := code.child tail
    let result := run 22 (initial program)
    result.steps = 22 ∧ result.state.control = .evaluate next ∧
      result.state.stack = [] ∧ result.state.pending = [] ∧
      result.state.heap.metadata.heap.live 0 = false ∧ result.state.heap.metadata.length 0 = count ∧
      result.events.filterMap Event.lifecycle? =
        [.alloc 0 count (encodeInteger fill), .free 0] ∧
      LoanClosingTyped env [] false next code.origins type ∧ ValueContext env next code.origins ∧
      OwnerSizes env result.state.heap.metadata next code.origins ∧
      ∃ tailFuel residual,
        LoanTyping.ResourceQuantity.projectRaw tailFuel env [] next.context tail = some residual ∧
        residual.demand 0 = some 0 ∧
        (∀ events, Jihoo.Quantity.Prefix residual events → events.count 0 = 0) := by
  let program := storeLoadWith count offset fill value
    (.lam false first (.lam false again (.free (.var 0) tail)))
  let code := storeLoadEntry count offset fill value first again (.free (.var 0) tail)
  let entry := run 19 (initial program)
  obtain ⟨entered,emptyStack,emptyPending,_,_,typed,values,sizes,bodyFuel,receipt,bodyChecked,entryBudget,_⟩ :=
    checked_closed_store_load_entry_resources history accepted sorted fits
  obtain ⟨steps,_,_,_,live,length,events,_,_,_⟩ := check_closed_store_load_entry history accepted sorted fits
  change LoanTyping.ResourceQuantity.projectRaw bodyFuel env [] code.context (.free (.var 0) tail) =
    some receipt at bodyChecked
  rw [LoanTyping.ResourceQuantity.projectRaw_free_callback_body bodyChecked] at entryBudget
  change entry.state.stack = [] at emptyStack
  change entry.state.pending = [] at emptyPending
  have emptyPhysical : entry.state.activeStack = [] := by
    simp only [State.activeStack,emptyStack,emptyPending,List.flatMap_nil,List.nil_append]
  have coverage : LoanCoverage code [] entry.state.activeStack := by
    rw [emptyPhysical]
    rintro index object stored ⟨frame,member,token,name,descriptor⟩
    cases member
  have stored : code.values[0]? = some (some (.owner 0)) := rfl
  obtain ⟨afterFree,stack,pending,dead,sameLength,freeEvents,freeSteps,tailTyped,tailValues,tailSizes,
      _,tailFuel,residual,tailChecked,_,zero,noUse⟩ :=
    reachable_typed_variable_free program 19 entered rfl typed values sizes coverage stored live bodyChecked
      (LoanTyping.ResourceQuantity.LoanBudget.empty _ _) entryBudget
  have completed := run_add 19 3 (initial program)
  change run 22 (initial program) =
    ⟨(run 3 entry.state).state,entry.events ++ (run 3 entry.state).events,
      entry.steps + (run 3 entry.state).steps⟩ at completed
  change entry.events.filterMap Event.lifecycle? = _ at events
  change entry.steps = 19 at steps
  change (run 3 entry.state).events = _ at freeEvents
  change (run 3 entry.state).steps = 3 at freeSteps
  change (run 3 entry.state).state.stack = entry.state.stack at stack
  change (run 3 entry.state).state.pending = entry.state.pending at pending
  change (run 3 entry.state).state.heap.metadata.length 0 = entry.state.heap.metadata.length 0 at sameLength
  change entry.state.heap.metadata.length 0 = count at length
  dsimp only
  rw [completed]
  refine ⟨by rw [steps,freeSteps],afterFree,stack.trans emptyStack,pending.trans emptyPending,
    dead,sameLength.trans length,?_,tailTyped,tailValues,tailSizes,tailFuel,residual,tailChecked,zero,noUse⟩
  change (entry.events ++ (run 3 entry.state).events).filterMap Event.lifecycle? = _
  rw [List.filterMap_append,events,freeEvents]
  rfl

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
