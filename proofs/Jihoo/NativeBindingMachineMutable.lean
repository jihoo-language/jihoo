import Jihoo.NativeBindingMachineBufferStore

/-! The binding-retaining evaluator with indexed Buffer contents. Store
evaluates the owner, index and value in order. The ordinary continuation stack
is saved across those operands. Borrow searches the full stack, including
the enclosing readers saved by Store, and Index observes the indexed cells. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds
variable {resource : Jihoo.Quantity.Control}

inductive StoreFrame where
  | owner (index value : Code)
  | index (object : Nat) (value : Code)
  | value (object index : Nat)

structure State where
  heap : SizedBufferHeap.IndexedState
  control : BindingMachine.Control
  stack : List BindingMachine.Frame
  pending : List (StoreFrame × List BindingMachine.Frame)

def State.activeStack (state : State) : List BindingMachine.Frame :=
  state.stack ++ state.pending.flatMap Prod.snd

inductive Event where
  | legacy (event : BindingMachine.Event)
  | store (object index value : Nat)

def initial (term : Term) (heap : SizedBufferHeap.State := SizedBufferHeap.empty) : State :=
  ⟨⟨heap,fun object _ => heap.heap.payload object⟩,.evaluate (.initial term),[],[]⟩

private def fail (state : State) (reason : Fault) (stack : List BindingMachine.Frame) : State × Option Event :=
  ({ state with control := .fault reason, stack },none)

def executeLegacy (state : State) (action : BindingMachine.Action) : State × Option Event :=
  match action with
  | .borrow key object stack =>
      let allFrames := stack ++ state.pending.flatMap Prod.snd
      let borrowed := BindingMachine.execute state.heap.metadata (.borrow key object allFrames)
      ({ state with control := borrowed.1.control, stack },borrowed.2.map .legacy)
  | .read token index stack =>
      match state.heap.read token index with
      | some value =>
          ({ state with control := .returned (.integer (decodeInteger value)), stack },
            some (.legacy (.heap (.read token index value))))
      | none =>
          fail state (if (state.heap.metadata.heap.lease token).isSome then .indexBounds else .closedLease) stack
  | _ =>
      let next := BindingMachine.execute state.heap.metadata action
      let cell := match next.2 with
        | some (.heap (.alloc object _ fill)) => HeapLeases.put state.heap.cell object (fun _ => fill)
        | _ => state.heap.cell
      (⟨⟨next.1.heap,cell⟩,next.1.control,next.1.stack,state.pending⟩,next.2.map .legacy)

private def resumeStore (state : State) (frame : StoreFrame) (saved : List BindingMachine.Frame)
    (rest : List (StoreFrame × List BindingMachine.Frame)) (value : Value) : State × Option Event :=
  match frame,value with
  | .owner offset fill,.owner object =>
      ({ state with control := .evaluate offset, pending := (.index object fill,saved) :: rest },none)
  | .index object fill,.natural offset =>
      ({ state with control := .evaluate fill, pending := (.value object offset,saved) :: rest },none)
  | .value object offset,.integer number =>
      let payload := encodeInteger number
      match state.heap.store object offset payload with
      | some heap => (⟨heap,.returned (.owner object),saved,rest⟩,some (.store object offset payload))
      | none =>
          let old := state.heap.metadata
          if !old.heap.live object then fail state .deadOwner []
          else if !freeGuard old object then fail state .borrowedOwner []
          else fail state .indexBounds []
  | _,_ => fail state .wrongValue []

def step (state : State) : Option (State × Option Event) :=
  match state.control with
  | .evaluate code =>
      match code.term with
      | .store owner index value _ =>
          some (⟨state.heap,.evaluate (code.child owner),[],
            (.owner (code.child index) (code.child value),state.stack) :: state.pending⟩,none)
      | _ => some (executeLegacy state (evaluateAction code state.stack))
  | .returned value =>
      match returnAction value state.stack with
      | some action => some (executeLegacy state action)
      | none => match state.pending with
        | [] => none
        | (frame,saved) :: rest => some (resumeStore state frame saved rest value)
  | .fault _ => none

structure Result where
  state : State
  events : List Event
  steps : Nat

def run : Nat → State → Result
  | 0,state => ⟨state,[],0⟩
  | fuel+1,state =>
      match step state with
      | none => ⟨state,[],0⟩
      | some (next,event) =>
          let result := run fuel next
          ⟨result.state,event.toList ++ result.events,result.steps+1⟩

def observe (result : Result) : Observation :=
  let state := result.state
  match state.control with
  | .fault reason => .fault reason
  | _ =>
      if state.pending.isEmpty then
        BindingMachine.observe ⟨⟨state.heap.metadata,state.control,state.stack⟩,[],result.steps⟩
      else .fuel

/-- Store entry keeps every enclosing legacy frame visible to Borrow. -/
theorem store_entry_frames (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .store owner index value evidence) :
    let next : State := ⟨state.heap,.evaluate (code.child owner),[],
      (.owner (code.child index) (code.child value),state.stack) :: state.pending⟩
    step state = some (next,none) ∧ next.activeStack = state.activeStack := by
  simp [step,evaluating,shape,State.activeStack]

/-- The final Store transition writes the exact indexed cell and returns its
owner to the saved continuation. Earlier and enclosing readers remain visible. -/
theorem pending_store_executes (state : State)
    (returned : state.control = .returned (.integer value)) (empty : state.stack = [])
    (pending : state.pending = (.value object index,saved) :: rest)
    (written : state.heap.store object index (encodeInteger value) = some heap) :
    let next : State := ⟨heap,.returned (.owner object),saved,rest⟩
    step state = some (next,some (.store object index (encodeInteger value))) ∧
      next.activeStack = state.activeStack := by
  simp [step,returned,empty,returnAction,pending,resumeStore,written,State.activeStack]

private def withOuter (outer : List Frame) : Action → Action
  | .control control stack activation => .control control (stack ++ outer) activation
  | .allocate count fill stack => .allocate count fill (stack ++ outer)
  | .free object rest stack => .free object rest (stack ++ outer)
  | .lend object name origin reader continuation stack =>
      .lend object name origin reader continuation (stack ++ outer)
  | .close token object result origin resultOrigin continuation stack =>
      .close token object result origin resultOrigin continuation (stack ++ outer)
  | .borrow key object stack => .borrow key object (stack ++ outer)
  | .read token index stack => .read token index (stack ++ outer)

private theorem frameChange_withOuter {action : Action} (outer : List Frame) (change : FrameChange stack action) :
    FrameChange (stack ++ outer) (withOuter outer action) := by
  cases action <;> simp only [withOuter,FrameChange,readerFrames,List.filterMap_append] at change ⊢
  all_goals try rw [change]
  case close =>
    obtain ⟨name,shape⟩ := change
    exact ⟨name,by rw [shape]; rfl⟩

private theorem executeLegacy_projection (state : State) (action : Action) :
    let original := execute state.heap.metadata (withOuter (state.pending.flatMap Prod.snd) action)
    (executeLegacy state action).1.heap.metadata = original.1.heap ∧
      (executeLegacy state action).1.activeStack = original.1.stack := by
  cases action with
  | control => exact ⟨rfl,rfl⟩
  | allocate =>
      simp only [executeLegacy,withOuter,execute]
      split <;> exact ⟨rfl,rfl⟩
  | free =>
      simp only [executeLegacy,withOuter,execute]
      split
      · split <;> exact ⟨rfl,rfl⟩
      · exact ⟨rfl,rfl⟩
  | lend =>
      simp only [executeLegacy,withOuter,execute]
      split <;> exact ⟨rfl,rfl⟩
  | close =>
      simp only [executeLegacy,withOuter,execute]
      split <;> exact ⟨rfl,rfl⟩
  | borrow =>
      simp only [executeLegacy,withOuter,execute]
      split
      · split <;> exact ⟨rfl,rfl⟩
      · exact ⟨rfl,rfl⟩
  | read token index stack =>
      cases payload : state.heap.read token index <;>
        cases leased : state.heap.metadata.heap.lease token <;>
        simp [executeLegacy,withOuter,execute,State.activeStack,payload,leased,fail]
      all_goals split <;> simp

/-- Allocation and lease metadata match the complete physical reader stack. -/
def Invariant (state : State) : Prop :=
  SizedBufferHeap.Valid state.heap.metadata ∧ ReaderInventory state.heap.metadata (readerFrames state.activeStack)

private theorem executeLegacy_invariant (state : State) (action : Action)
    (invariant : Invariant state) (changed : FrameChange state.stack action) :
    Invariant (executeLegacy state action).1 := by
  obtain ⟨metadata,stack⟩ := executeLegacy_projection state action
  have adjusted := frameChange_withOuter (state.pending.flatMap Prod.snd) changed
  unfold Invariant
  rw [metadata,stack]
  exact ⟨SizedBufferHeap.steps_valid invariant.1 (execute_heap_steps invariant.1 _),
    execute_reader_inventory invariant.1 invariant.2 adjusted⟩

private theorem resumeStore_invariant (state : State) (invariant : Invariant state)
    (empty : state.stack = []) (pending : state.pending = (frame,saved) :: rest) (value : Value) :
    Invariant (resumeStore state frame saved rest value).1 := by
  have old : ReaderInventory state.heap.metadata (readerFrames (saved ++ rest.flatMap Prod.snd)) := by
    simpa [State.activeStack,empty,pending] using invariant.2
  cases frame <;> cases value <;> simp only [resumeStore,fail]
  all_goals first
    | exact ⟨invariant.1,by simpa [State.activeStack,empty,pending] using old⟩
    | skip
  split
  · rename_i heap written
    have unchanged := (SizedBufferHeap.IndexedState.store_spec invariant.1 written).2.2.2.1
    exact ⟨unchanged ▸ invariant.1,unchanged ▸ old⟩
  · split
    · exact ⟨invariant.1,by simpa [State.activeStack,pending] using old⟩
    · split <;> exact ⟨invariant.1,by simpa [State.activeStack,pending] using old⟩

/-- Every extended step preserves valid allocation metadata and the exact
inventory of outstanding reader leases, including across Store operands. -/
theorem step_invariant (invariant : Invariant state) (stepped : step state = some (next,event)) :
    Invariant next := by
  cases control : state.control with
  | fault => simp [step,control] at stepped
  | evaluate code =>
      simp only [step,control] at stepped
      split at stepped
      · cases stepped
        exact ⟨invariant.1,by simpa [State.activeStack] using invariant.2⟩
      · have same := congrArg Prod.fst (Option.some.inj stepped)
        change _ = next at same
        rw [← same]
        exact executeLegacy_invariant _ _ invariant (evaluate_frame_change _ _)
  | returned value =>
      simp only [step,control] at stepped
      cases chosen : returnAction value state.stack with
      | some action =>
          rw [chosen] at stepped
          have same := congrArg Prod.fst (Option.some.inj stepped)
          change _ = next at same
          rw [← same]
          exact executeLegacy_invariant _ _ invariant (return_frame_change _ _ _ chosen)
      | none =>
          have empty : state.stack = [] := by
            cases shape : state.stack with
            | nil => rfl
            | cons frame rest => simp [shape,returnAction] at chosen
          rw [chosen] at stepped
          cases pending : state.pending with
          | nil => simp [pending] at stepped
          | cons head rest =>
              obtain ⟨frame,saved⟩ := head
              rw [pending] at stepped
              have same := congrArg Prod.fst (Option.some.inj stepped)
              change _ = next at same
              rw [← same]
              exact resumeStore_invariant state invariant empty pending value

theorem run_invariant (fuel : Nat) (invariant : Invariant state) : Invariant (run fuel state).state := by
  induction fuel generalizing state with
  | zero => exact invariant
  | succ fuel ih =>
      cases stepped : step state with
      | none => simpa only [run,stepped] using invariant
      | some result =>
          obtain ⟨next,event⟩ := result
          simpa only [run,stepped] using ih (step_invariant invariant stepped)

theorem initial_run_invariant (term : Term) (fuel : Nat) : Invariant (run fuel (initial term)).state :=
  run_invariant fuel ⟨SizedBufferHeap.empty_valid,ReaderInventory.empty⟩

private theorem literal_store_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .store (.var owner) (.natural offset) (.integer value) evidence)
    (stored : code.values[owner]? = some (some (.owner object)))
    (offsetWidth : offset < 2^64) (valueWidth : ValueReduction.signed64 value)
    (written : state.heap.store object offset (encodeInteger value) = some heap) :
    run 7 state =
      ⟨⟨heap,.returned (.owner object),state.stack,state.pending⟩,[.store object offset (encodeInteger value)],7⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,stored,executeLegacy,execute,
    Option.map_none,returnAction,resumeStore,offsetWidth,valueWidth,ite_true,written]
  rfl

/-- A typed literal Store with an actual owner slot constructs the complete
seven-transition execution. The loan budget and coverage discharge the
physical write guard, and the result has the original Buffer type. -/
theorem typed_literal_store (state : State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (invariant : Invariant state) (evaluating : state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (sizes : OwnerSizes env state.heap.metadata source meanings)
    (shape : actual.term = .store (.var owner) (.natural offset) (.integer value)
      (.decide (.natural offset) (.natural count)))
    (stored : actual.values[owner]? = some (some (.owner object)))
    (live : state.heap.metadata.heap.live object = true)
    (coverage : LoanCoverage source loans state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context
      source.term = some resource)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans resource) :
    ∃ heap,
      run 7 state = ⟨⟨heap,.returned (.owner object),state.stack,state.pending⟩,
        [.store object offset (encodeInteger value)],7⟩ ∧
      heap.metadata = state.heap.metadata ∧ heap.metadata.length object = count ∧
      LoanTyping.Conversion.Conv env (.buffer (.natural count)) type ∧
      decodeInteger (heap.cell object offset) = value ∧
      ∀ token index, heap.read token index = state.heap.read token index := by
  obtain ⟨heap,written,metadata,length,offsetWidth,valueWidth,result,cell,_⟩ :=
    canonical_store_cell history state.heap invariant.1 invariant.2 view typed sizes shape stored live coverage checked budget
  exact ⟨heap,literal_store_steps state evaluating shape stored offsetWidth valueWidth written,
    metadata,metadata ▸ length,result,cell,SizedBufferHeap.IndexedState.store_keeps_reader invariant.1 written⟩

namespace Examples

set_option maxRecDepth 4096

private def buffer (length : Nat) : Term := .buffer (.natural length)
private def bound (index length : Nat) : Term := .decide (.natural index) (.natural length)
private def read (reference : Term) (index length : Nat) : Term := .index reference (.natural index) (bound index length)
private def release (length : Nat) : Term :=
  .lam false .i64 (.lam false (buffer length) (.free (.var 0) (.var 1)))

private def store_then_read : Term :=
  .lend (.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 7) (bound 1 2))
    (.lam false (.ref (buffer 2)) (.strict (read (.var 0) 0 2) (read (.var 0) 1 2))) (release 2)

theorem store_then_read_admitted : LoanTyping.MixedProgram.checkDeclaration 32 64 .empty
    ⟨.i64,store_then_read⟩ = some ⟨.i64,store_then_read⟩ := by cbv

theorem store_then_read_returns : observe (run 40 (initial store_then_read)) = .integer 7 := by rfl

private def memoryEvents (events : List Event) : List Event :=
  events.filter fun event => match event with | .legacy (.activate _ _ _) => false | _ => true

theorem store_then_read_events : memoryEvents (run 40 (initial store_then_read)).events =
    [.legacy (.heap (.alloc 0 2 (encodeInteger 3))),.store 0 1 (encodeInteger 7),.legacy (.heap (.beginLease 0 0)),
      .legacy (.heap (.read 0 0 (encodeInteger 3))),.legacy (.heap (.read 0 1 (encodeInteger 7))),
      .legacy (.heap (.close 0)),.legacy (.heap (.free 0))] := by rfl

-- Borrow inside the fill expression requires searching below a pending Store.
private def outer_reader : Term :=
  .app (.lam false (buffer 1) (.lend (.var 0)
    (.lam false (.ref (buffer 1)) (.free
      (.store (.alloc (.natural 1) (.integer 0)) (.natural 0) (read (.borrow (.var 1)) 0 1) (bound 0 1))
      (.integer 5))) (release 1))) (.alloc (.natural 1) (.integer 7))

theorem outer_reader_admitted : LoanTyping.MixedProgram.checkDeclaration 32 64 .empty
    ⟨.i64,outer_reader⟩ = some ⟨.i64,outer_reader⟩ := by cbv

theorem outer_reader_store_returns : observe (run 45 (initial outer_reader)) = .integer 5 := by rfl

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
