import Jihoo.NativeBindingMachineHeap

/-! Projection equations for actual fuel-bounded execution. These avoid
repeated expansion of the state/event/step fields of the same suffix run. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

theorem observe_run_zero (state : State) : observe (run 0 state) = observe ⟨state,[],0⟩ := rfl

theorem observe_run_succ (fuel : Nat) (state : State) :
    observe (run (fuel+1) state) = match step state with
      | none => observe ⟨state,[],0⟩
      | some (next,_) => observe (run fuel next) := by
  simp only [run]
  cases step state <;> rfl

theorem state_run_zero (state : State) : (run 0 state).state = state := rfl

theorem state_run_succ (fuel : Nat) (state : State) :
    (run (fuel+1) state).state = match step state with
      | none => state
      | some (next,_) => (run fuel next).state := by
  simp only [run]
  cases step state <;> rfl

theorem events_run_zero (state : State) : (run 0 state).events = [] := rfl

theorem events_run_succ (fuel : Nat) (state : State) :
    (run (fuel+1) state).events = match step state with
      | none => []
      | some (next,event) => event.toList ++ (run fuel next).events := by
  simp only [run]
  cases step state <;> rfl

theorem heap_events_run_zero (state : State) : eventsHeap (run 0 state).events = [] := rfl

theorem heap_events_run_succ (fuel : Nat) (state : State) :
    eventsHeap (run (fuel+1) state).events = match step state with
      | none => []
      | some (next,event) => eventHeap event ++ eventsHeap (run fuel next).events := by
  cases observed : step state with
  | none => simp only [events_run_succ,observed,eventsHeap,List.filterMap_nil]
  | some result =>
      obtain ⟨next,event⟩ := result
      simp only [events_run_succ,observed,eventsHeap_append,eventsHeap_option]

end Jihoo.NativeKernel.Environment.BindingMachine
