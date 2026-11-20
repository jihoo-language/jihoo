import Jihoo.NativeBindingMachineMutableCheckedClosure
import Jihoo.NativeLoanCallBindingStores

/-! The ownership world of a full entered call uses the final de Bruijn
order of its runtime slots. Checked scopes allocate exactly one unit per
linear binder, including binders whose value was held in an intermediate
closure while the rest of the application was pending. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

open Jihoo.Quantity NativeQuantity
open LoanTyping.ResourceQuantity (scopes_bound_demand)

private theorem scopes_outer_exact (valid : LocalScopes (.scopes modes body)) (index : Nat) :
    (Jihoo.Quantity.Control.scopes modes body).demand index = body.demand (index+modes.length) := by
  induction modes generalizing index with
  | nil => rfl
  | cons mode rest ih =>
    have inner : LocalScopes (.scopes rest body) := by
      cases mode
      · exact valid.2
      · exact valid.2
      · exact valid
      · exact valid
    change (Control.scope mode (.scopes rest body)).demand index = _
    have scopeValid : LocalScopes (.scope mode (.scopes rest body)) := valid
    rw [demand_under_checked_scope scopeValid index,ih inner]
    congr 1
    simp only [List.length_cons]
    omega

/-- Entering the entire checked telescope installs one unit for every new
physical owner. Captured aliases of those owners keep a zero receipt, and
other captured owners retain exactly the authority of the original call.
The machine's actual final slot list is an input to this local handoff. -/
theorem OwnerDemandWorld.opened_telescope
    {boundValues : List (Option Value)} {capture entered : Code}
    (world : OwnerDemandWorld heap capture (.scopes modes body))
    (total : OwnerDemandWorld.Total capture (.scopes modes body))
    (valid : LocalScopes (.scopes modes body))
    (values : entered.values = boundValues ++ capture.values)
    (order : modes.length = boundValues.length)
    (installed : ∀ (position object : Nat), boundValues[position]? = some (some (Value.owner object)) →
      modes[modes.length-position-1]? = some .linear ∧ heap.heap.live object = true)
    (different : ∀ (position alias object : Nat), boundValues[position]? = some (some (Value.owner object)) →
      boundValues[alias]? = some (some (Value.owner object)) → position = alias)
    (retired : ∀ (position index object : Nat), boundValues[position]? = some (some (Value.owner object)) →
      capture.values[index]? = some (some (Value.owner object)) → (.scopes modes body : Jihoo.Quantity.Control).demand index = some 0) :
    OwnerDemandWorld heap entered body ∧ OwnerDemandWorld.Total entered body := by
  have boundSlot {position object} (inside : position < boundValues.length)
      (found : entered.values[position]? = some (some (.owner object))) :
      boundValues[position]? = some (some (.owner object)) := by
    simpa only [values,List.getElem?_append_left inside] using found
  have captureSlot {position object} (outside : ¬position < boundValues.length)
      (found : entered.values[position]? = some (some (.owner object))) :
      capture.values[position-boundValues.length]? = some (some (.owner object)) := by
    simpa only [values,List.getElem?_append,outside,ite_false] using found
  have newDemand {position object} (stored : boundValues[position]? = some (some (.owner object))) :
      body.demand position = some 1 ∧ heap.heap.live object = true := by
    have inside := (List.getElem?_eq_some_iff.mp stored).1
    obtain ⟨linear,alive⟩ := installed position object stored
    have one := scopes_bound_demand valid linear (Or.inl rfl)
    have index : modes.length-(modes.length-position-1)-1 = position := by omega
    exact ⟨by simpa only [index,ite_eq_left rfl,ite_true] using one,alive⟩
  have oldDemand (position : Nat) (outside : ¬position < boundValues.length) :
      body.demand position = (.scopes modes body : Jihoo.Quantity.Control).demand (position-boundValues.length) := by
    have shift := scopes_outer_exact valid (position-boundValues.length)
    have index : position-boundValues.length+modes.length = position := by omega
    simpa only [index] using shift.symm
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro index object uses stored positive
    by_cases inside : index < boundValues.length
    · obtain ⟨used,live⟩ := newDemand (boundSlot inside stored)
      have count := Option.some.inj (positive.symm.trans used)
      exact ⟨live,by omega⟩
    · exact world.live_once _ object uses (captureSlot inside stored) ((oldDemand index inside).symm.trans positive)
  · intro index alias object uses distinct stored aliased positive
    by_cases first : index < boundValues.length
    · have new := boundSlot first stored
      by_cases second : alias < boundValues.length
      · exact False.elim (distinct (different index alias object new (boundSlot second aliased)))
      · exact (oldDemand alias second).trans (retired index _ object new (captureSlot second aliased))
    · have previous := captureSlot first stored
      by_cases second : alias < boundValues.length
      · have unused := (oldDemand index first).trans (retired alias _ object (boundSlot second aliased) previous)
        rw [unused] at positive
        cases positive
      · have indices : index-boundValues.length ≠ alias-boundValues.length := by omega
        exact (oldDemand alias second).trans (world.exclusive _ _ object uses indices previous
          (captureSlot second aliased) ((oldDemand index first).symm.trans positive))
  · intro index object stored
    by_cases inside : index < boundValues.length
    · exact ⟨1,(newDemand (boundSlot inside stored)).1⟩
    · obtain ⟨uses,observed⟩ := total _ object (captureSlot inside stored)
      exact ⟨uses,(oldDemand index inside).trans observed⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
