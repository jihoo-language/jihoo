import Jihoo.NativeBindingMachineMutable

/-! The indexed machine agrees with the read-only machine until the latter
selects one of the extended operations. An old heap embeds with the original
object's payload at every index. The correspondence includes faults, step
counts, and the complete event sequence. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

def embedReadOnly (state : BindingMachine.State) : State :=
  ⟨⟨state.heap, fun object _ => state.heap.heap.payload object⟩, state.control, state.stack, []⟩

def embedReadOnlyTransition (transition : BindingMachine.State × Option BindingMachine.Event) :
    State × Option Event :=
  (embedReadOnly transition.1, transition.2.map .legacy)

def embedReadOnlyResult (result : BindingMachine.Result) : Result :=
  ⟨embedReadOnly result.state, result.events.map .legacy, result.steps⟩

private theorem put_uniform (payload : Nat → Nat) (object value : Nat) :
    HeapLeases.put (fun queried (_ : Nat) => payload queried) object (fun _ => value) =
      fun queried _ => HeapLeases.put payload object value queried := by
  funext queried index
  by_cases hits : queried = object <;> simp [HeapLeases.put, hits]

/-- Each ordinary action preserves the uniform embedding and emits the
same event. In particular, an allocation initializes all indexed cells and
a borrowed read retrieves the original payload. -/
theorem executeLegacy_embedReadOnly (state : BindingMachine.State) (action : Action) :
    executeLegacy (embedReadOnly state) action =
      embedReadOnlyTransition (BindingMachine.execute state.heap action) := by
  cases action with
  | control next stack activation => cases activation <;> rfl
  | allocate count fill stack =>
      by_cases fits : count * 8 + 8 < (2 ^ 64 : Nat)
      · simp [executeLegacy, embedReadOnlyTransition, embedReadOnly, BindingMachine.execute,
          fits, SizedBufferHeap.allocate, put_uniform]
      · simp [executeLegacy, embedReadOnlyTransition, embedReadOnly, BindingMachine.execute, fits]
  | free object rest stack =>
      by_cases live : state.heap.heap.live object <;> by_cases free : freeGuard state.heap object <;>
        simp [executeLegacy, embedReadOnlyTransition, embedReadOnly, BindingMachine.execute, live, free,
          SizedBufferHeap.release]
  | lend object name origin reader continuation stack =>
      by_cases live : state.heap.heap.live object <;>
        simp [executeLegacy, embedReadOnlyTransition, embedReadOnly, BindingMachine.execute, live, SizedBufferHeap.lend]
  | close token object result origin resultOrigin continuation stack =>
      by_cases leased : state.heap.heap.lease token = some object <;>
        simp [executeLegacy, embedReadOnlyTransition, embedReadOnly, BindingMachine.execute, leased, SizedBufferHeap.close]
  | borrow key object stack =>
      cases found : borrowLease key object stack with
      | none => simp [executeLegacy, embedReadOnlyTransition, embedReadOnly, BindingMachine.execute, found]
      | some token =>
          by_cases leased : state.heap.heap.lease token = some object <;>
            simp [executeLegacy, embedReadOnlyTransition, embedReadOnly, BindingMachine.execute, found, leased]
  | read token index stack =>
      cases leased : state.heap.heap.lease token with
      | none =>
          simp [executeLegacy, embedReadOnlyTransition, embedReadOnly, BindingMachine.execute,
            SizedBufferHeap.IndexedState.read, leased]
          rfl
      | some object =>
          by_cases fits : index < state.heap.length object
          · simp [executeLegacy, embedReadOnlyTransition, embedReadOnly, BindingMachine.execute,
              SizedBufferHeap.IndexedState.read, leased, fits]
          · simp [executeLegacy, embedReadOnlyTransition, embedReadOnly, BindingMachine.execute,
              SizedBufferHeap.IndexedState.read, leased, fits]
            rfl

def LegacyControl (state : BindingMachine.State) : Prop :=
  match state.control with
  | .evaluate code =>
      (∀ owner index value evidence, code.term ≠ .store owner index value evidence) ∧
      (∀ owner index evidence continuation, code.term ≠ .load owner index evidence continuation) ∧
      (∀ left right evidence, code.term ≠ .usub left right evidence) ∧
      (∀ predicate witness evidence, code.term ≠ .pack predicate witness evidence) ∧
      (∀ refinement, code.term ≠ .witness refinement) ∧
      (∀ count elements, code.term ≠ .node (.elements count) elements)
  | _ => True

/-- An old transition agrees with the indexed transition outside the
additional operations. Each operation may occur in suspended code. -/
theorem step_embedReadOnly (state : BindingMachine.State) (ordinary : LegacyControl state) :
    step (embedReadOnly state) = (BindingMachine.step state).map embedReadOnlyTransition := by
  cases state with
  | mk heap control stack =>
      cases control with
      | evaluate code =>
          simp only [step, embedReadOnly, BindingMachine.step, BindingMachine.action, Option.map_some]
          split
          · rename_i owner index value evidence shape
            exact False.elim (ordinary.1 owner index value evidence shape)
          · rename_i owner index evidence continuation shape
            exact False.elim (ordinary.2.1 owner index evidence continuation shape)
          · rename_i left right evidence shape
            exact False.elim (ordinary.2.2.1 left right evidence shape)
          · rename_i predicate witness evidence shape
            exact False.elim (ordinary.2.2.2.1 predicate witness evidence shape)
          · rename_i refinement shape
            exact False.elim (ordinary.2.2.2.2.1 refinement shape)
          · rename_i count elements shape
            exact False.elim (ordinary.2.2.2.2.2 count elements shape)
          · exact congrArg some (executeLegacy_embedReadOnly ⟨heap,.evaluate code,stack⟩ (evaluateAction code stack))
      | returned value =>
          cases chosen : returnAction value stack with
          | none => simp [step, embedReadOnly, BindingMachine.step, BindingMachine.action, chosen]
          | some action =>
              simpa only [step, embedReadOnly, BindingMachine.step, BindingMachine.action, chosen, Option.map_some]
                using congrArg some (executeLegacy_embedReadOnly ⟨heap,.returned value,stack⟩ action)
      | fault reason => rfl

/-- The bounded old execution steps through ordinary control. Its final state
may select a newer operation when the fuel ends before that step. -/
def ReadOnlyPrefix : Nat → BindingMachine.State → Prop
  | 0, _ => True
  | fuel + 1, state => LegacyControl state ∧
      match BindingMachine.step state with
      | none => True
      | some (next, _) => ReadOnlyPrefix fuel next

private theorem event_toList_embed (event : Option BindingMachine.Event) :
    (event.map Event.legacy).toList = event.toList.map Event.legacy := by
  cases event <;> rfl

/-- Every such old prefix gives exact agreement of the final state,
the full trace, and the number of executed transitions. -/
theorem run_embedReadOnly (fuel : Nat) (state : BindingMachine.State) (readOnly : ReadOnlyPrefix fuel state) :
    run fuel (embedReadOnly state) = embedReadOnlyResult (BindingMachine.run fuel state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      obtain ⟨ordinary, after⟩ := readOnly
      rw [run, BindingMachine.run, step_embedReadOnly state ordinary]
      cases chosen : BindingMachine.step state with
      | none => rfl
      | some transition =>
          obtain ⟨next, event⟩ := transition
          rw [chosen] at after
          simp only [Option.map_some, embedReadOnlyTransition]
          rw [ih next after]
          simp only [embedReadOnlyResult, event_toList_embed, List.map_append]

/-- The indexed evaluator produces the same externally visible observation
on every embedded old result, including its faults and exhausted prefixes. -/
theorem observe_embedReadOnly (result : BindingMachine.Result) :
    observe (embedReadOnlyResult result) = BindingMachine.observe result := by
  obtain ⟨⟨heap,control,stack⟩,events,steps⟩ := result
  cases control with
  | fault reason => cases stack <;> rfl
  | evaluate code => rfl
  | returned value => rfl

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
