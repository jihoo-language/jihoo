import Jihoo.NativeBindingMachineMutableDemandSequence
import Jihoo.NativeBindingMachineMutableLoadOwnerDemand

/-! Exact demand availability survives Free and Load. It supplements the
physical owner world when sequencing effects or starting a named reader. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds

theorem OwnerDemandWorld.Total.free_tail
    (complete : OwnerDemandWorld.Total code (.seq (.use owner) (.seq residual .pure))) :
    OwnerDemandWorld.Total (code.child tail) residual := by
  intro index object selected
  obtain ⟨uses,observed⟩ := complete index object selected
  cases queried : residual.demand index
  · simp [Jihoo.Quantity.Control.demand,queried,bind,Option.bind] at observed
  · exact ⟨_,rfl⟩

theorem OwnerDemandWorld.Total.load_handoff
    (complete : OwnerDemandWorld.Total code current)
    (indexValue : code.values[offset]? = some (some (.natural position)))
    (demand : LoanTyping.ResourceQuantity.LoadDemand current entered owner offset)
    (first again body origin : Term) (object : Nat) (integer : Int) :
    let next := restoredContinuation code first again body origin (.integer integer) object (.integer integer)
    OwnerDemandWorld.Total next entered := by
  dsimp only
  intro index queried stored
  cases index with
  | zero => exact ⟨1,demand.returned⟩
  | succ previous =>
      cases previous with
      | zero => cases stored
      | succ capture =>
          by_cases consumed : capture = owner
          · subst capture
            exact ⟨0,demand.consumed⟩
          · have notOffset : capture ≠ offset := by
              intro same
              subst capture
              change code.values[offset]? = _ at stored
              rw [indexValue] at stored
              cases stored
            obtain ⟨uses,observed⟩ := complete capture queried stored
            exact ⟨uses,(demand.retained capture consumed notOffset).symm.trans observed⟩

theorem OwnerDemandWorld.Total.store_load_entry {receipt : Jihoo.Quantity.Control}
    (unit : receipt.demand 0 = some 1) :
    OwnerDemandWorld.Total (storeLoadEntry count offset fill value first again body) receipt := by
  intro index object selected
  cases index with
  | zero => exact ⟨1,unit⟩
  | succ index => cases index <;> cases selected

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
