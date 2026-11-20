import Jihoo.NativeCorePureComputationNormal

/-! A shared native Core visit charges the checking meter without editing
the arena. The failed tick is included in the retained state. -/
namespace Jihoo.NativeKernel.NativeCoreMeteredVisit

open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreTransformExact (State)
open NativeCoreUnsignedCancellation (tick)

def charge (limit depth : Nat) (state : State) (root : Nat) : Outcome Unit :=
  let visited := tick state.arena limit depth state.steps root
  ⟨{state with steps := visited.2}, visited.1.mapError .tick⟩

theorem charge_progress (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (charge limit depth state root) := by
  unfold charge tick
  by_cases over : limit < state.steps+1
  · simp only [over,ite_true,Except.mapError]
    exact ⟨.refl _,Nat.le_succ _,fun room => Nat.succ_le_succ room,by intro _ _ failed; cases failed⟩
  have within := Nat.le_of_not_gt over
  by_cases deep : depth = 0
  · simp only [over,deep,ite_false,ite_true,Except.mapError]
    exact ⟨.refl _,Nat.le_succ _,fun _ => Nat.le_trans within (Nat.le_succ _),by intro _ _ failed; cases failed⟩
  by_cases missing : state.arena.size ≤ root
  · simp only [over,deep,missing,ite_false,ite_true,Except.mapError]
    exact ⟨.refl _,Nat.le_succ _,fun _ => Nat.le_trans within (Nat.le_succ _),by intro _ _ failed; cases failed⟩
  simp only [over,deep,missing,ite_false,Except.mapError]
  exact ⟨.refl _,Nat.le_succ _,fun _ => Nat.le_trans within (Nat.le_succ _),fun _ _ _ => within⟩

end Jihoo.NativeKernel.NativeCoreMeteredVisit
