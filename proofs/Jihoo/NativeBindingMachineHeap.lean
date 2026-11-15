import Jihoo.NativeBindingMachine

/-! Every finite machine prefix produces genuine existing heap transitions,
including prefixes ending in faults or fuel exhaustion. No successful-result
or supplied post-state heap invariant is assumed. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

theorem freeGuard_unborrowed (valid : SizedBufferHeap.Valid heap)
    (checked : freeGuard heap object = true) : HeapLeases.Unborrowed heap.heap object := by
  intro token present
  have bound := (valid.leased token object present).1
  have guard := List.all_eq_true.mp checked token (List.mem_range.mpr bound)
  exact (of_decide_eq_true guard) present

theorem encode_decode_integer (bounded : ValueReduction.signed64 value) :
    decodeInteger (encodeInteger value) = value := by
  have nonnegative : 0 ≤ value + 2^63 := by rcases bounded with ⟨low,high⟩; omega
  simp only [decodeInteger,encodeInteger,Int.toNat_of_nonneg nonnegative]
  omega

theorem encode_integer_bound (bounded : ValueReduction.signed64 value) :
    encodeInteger value < 2^64 := by
  have nonnegative : 0 ≤ value + 2^63 := by rcases bounded with ⟨low,high⟩; omega
  have high : value + 2^63 < 2^64 := by rcases bounded with ⟨low,high⟩; omega
  exact (Int.toNat_lt nonnegative).mpr high

theorem execute_heap_steps (valid : SizedBufferHeap.Valid heap) (next : Action) :
    SizedBufferHeap.Steps heap (eventHeap (execute heap next).2) (execute heap next).1.heap := by
  cases next with
  | control control stack activation =>
      cases activation <;> simp only [execute,Option.map_none,Option.map_some,eventHeap]
      all_goals exact .nil
  | allocate count fill stack =>
      simp only [execute]
      split
      · exact .cons .alloc .nil
      · exact .nil
  | free object rest stack =>
      simp only [execute]
      split
      · rename_i live
        split
        · rename_i guarded
          exact .cons (.free live (freeGuard_unborrowed valid guarded)) .nil
        · exact .nil
      · exact .nil
  | lend object name origin reader continuation stack =>
      simp only [execute]
      split
      · rename_i live
        exact .cons (.beginLease live) .nil
      · exact .nil
  | close token object result origin resultOrigin continuation stack =>
      simp only [execute]
      split
      · rename_i present
        exact .cons (.close present) .nil
      · exact .nil
  | borrow key object stack =>
      simp only [execute]
      split
      · split <;> exact .nil
      · exact .nil
  | read token index stack =>
      simp only [execute]
      split
      · rename_i object present
        split
        · rename_i bound
          exact .cons (.read present bound) .nil
        · exact .nil
      · exact .nil

theorem step_heap_steps (valid : SizedBufferHeap.Valid state.heap)
    (stepped : step state = some (next,event)) :
    SizedBufferHeap.Steps state.heap (eventHeap event) next.heap := by
  obtain ⟨nextAction,chosen,same⟩ := Option.map_eq_some_iff.mp stepped
  simpa only [same] using execute_heap_steps valid nextAction

private theorem heap_steps_append (first : SizedBufferHeap.Steps before firstEvents middle)
    (second : SizedBufferHeap.Steps middle secondEvents after) :
    SizedBufferHeap.Steps before (firstEvents ++ secondEvents) after := by
  induction first with
  | nil => exact second
  | cons step rest ih => exact .cons step (ih second)

theorem eventsHeap_append (before after : List Event) :
    eventsHeap (before ++ after) = eventsHeap before ++ eventsHeap after := by
  simp only [eventsHeap,List.filterMap_append]

theorem eventsHeap_option (event : Option Event) : eventsHeap event.toList = eventHeap event := by
  cases event with
  | none => rfl
  | some event => cases event <;> rfl

/-- This holds for every fuel and every outcome, including reported faults.
The evaluator actually produces the complete event prefix and final state. -/
theorem run_heap_steps (valid : SizedBufferHeap.Valid state.heap) (fuel : Nat) :
    SizedBufferHeap.Steps state.heap (eventsHeap (run fuel state).events) (run fuel state).state.heap := by
  induction fuel generalizing state with
  | zero => exact .nil
  | succ fuel ih =>
      simp only [run]
      cases observed : step state with
      | none => exact .nil
      | some result =>
          obtain ⟨next,event⟩ := result
          have first := step_heap_steps valid observed
          have rest := ih (SizedBufferHeap.steps_valid valid first)
          simpa only [eventsHeap_append,eventsHeap_option] using heap_steps_append first rest

theorem run_heap_valid (valid : SizedBufferHeap.Valid state.heap) (fuel : Nat) :
    SizedBufferHeap.Valid (run fuel state).state.heap :=
  SizedBufferHeap.steps_valid valid (run_heap_steps valid fuel)

theorem initial_run_heap_valid (term : Term) (fuel : Nat) :
    SizedBufferHeap.Valid (run fuel (initial term)).state.heap :=
  run_heap_valid SizedBufferHeap.empty_valid fuel

end Jihoo.NativeKernel.Environment.BindingMachine
