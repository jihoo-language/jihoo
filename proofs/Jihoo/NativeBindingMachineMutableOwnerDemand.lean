import Jihoo.NativeBindingMachineMutableFreeContinuation
import Jihoo.NativeBindingMachineCapturedOwnerHandoff

/-! A demanded owner slot identifies a live physical allocation, with unit
demand and no competing alias. Free preserves this invariant for the exact
source receipt of its continuation. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

structure OwnerDemandWorld (heap : SizedBufferHeap.State) (code : Code) (receipt : Jihoo.Quantity.Control) : Prop where
  live_once : ∀ index object uses, code.values[index]? = some (some (.owner object)) →
    receipt.demand index = some (uses+1) → heap.heap.live object = true ∧ uses = 0
  exclusive : ExclusiveOwnerDemand code receipt

theorem OwnerDemandWorld.initial (heap : SizedBufferHeap.State) (term : Term) (receipt : Jihoo.Quantity.Control) :
    OwnerDemandWorld heap (.initial term) receipt := by
  constructor
  · intro _ _ _ stored
    cases stored
  · intro _ _ _ _ _ stored
    cases stored

private theorem free_other_demand (other : index ≠ owner) :
    (Control.seq (.use owner) (.seq residual .pure)).demand index = residual.demand index := by
  cases observed : residual.demand index <;> simp [Control.demand,Ne.symm other,observed,bind,Option.bind]

/-- Consuming one slot removes all future demand for its physical owner,
including through retained aliases. Other positive demands keep their
original identities and their linear unit. -/
theorem OwnerDemandWorld.release
    (world : OwnerDemandWorld heap code (.seq (.use owner) (.seq residual .pure)))
    (stored : code.values[owner]? = some (some (.owner object)))
    (used : (Control.seq (.use owner) (.seq residual .pure)).demand owner = some 1)
    (zero : residual.demand owner = some 0) :
    OwnerDemandWorld (SizedBufferHeap.release heap object) (code.child tail) residual := by
  have past (index positive : Nat) (demanded : residual.demand index = some (positive+1)) :
      index ≠ owner ∧ (Control.seq (.use owner) (.seq residual .pure)).demand index = some (positive+1) := by
    have different : index ≠ owner := by
      intro same
      subst index
      rw [zero] at demanded
      cases demanded
    exact ⟨different,(free_other_demand different).trans demanded⟩
  constructor
  · intro index current uses found demanded
    obtain ⟨different,original⟩ := past index uses demanded
    obtain ⟨live,unit⟩ := world.live_once index current uses found original
    have separate : current ≠ object := by
      intro same
      subst current
      have unused := world.exclusive owner index object 0 (Ne.symm different) stored found used
      rw [original] at unused
      cases unused
    exact ⟨by simp [SizedBufferHeap.release,HeapLeases.put,separate,live],unit⟩
  · intro index alias current uses different found aliased demanded
    by_cases consumes : alias = owner
    · exact consumes.symm ▸ zero
    · have ⟨_,original⟩ := past index uses demanded
      rw [← free_other_demand (residual := residual) consumes]
      exact world.exclusive index alias current uses different found aliased original

theorem OwnerDemandWorld.store_load_entry {heap : SizedBufferHeap.State} {receipt : Jihoo.Quantity.Control}
    (live : heap.heap.live 0 = true) (one : receipt.demand 0 = some 1) :
    OwnerDemandWorld heap (storeLoadEntry count offset fill value first again body) receipt := by
  have sole (index object : Nat)
      (found : (storeLoadEntry count offset fill value first again body).values[index]? = some (some (.owner object))) :
      index = 0 ∧ object = 0 := by
    cases index with
    | zero =>
        exact ⟨rfl,(Value.owner.inj (Option.some.inj (Option.some.inj found))).symm⟩
    | succ index => cases index <;> cases found
  constructor
  · intro index object uses found demanded
    obtain ⟨rfl,rfl⟩ := sole index object found
    rw [one] at demanded
    have exactUse : 1 = uses+1 := Option.some.inj demanded
    exact ⟨live,by omega⟩
  · intro index alias object uses different found other _
    exact False.elim (different ((sole index object found).1.trans (sole alias object other).1.symm))

private theorem free_lifecycle_result
    (step : SizedBufferHeap.Steps before [.free object] after) :
    after = SizedBufferHeap.release before object := by
  cases step with
  | cons first rest =>
      cases rest
      cases first
      rfl

/-- The current owner-demand world supplies liveness. The actual Free
step establishes the same invariant for the new checked receipt and
the successor heap, while keeping the original type and value context. -/
theorem reachable_free_preserves_owner_demand (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .free (.var owner) tail)
    (typed : LoanClosingTyped env loans false code meanings type)
    (values : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata code meanings)
    (coverage : LoanCoverage code loans (run fuel (initial term)).state.activeStack)
    (stored : code.values[owner]? = some (some (.owner object)))
    (checked : LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans code.context
      (.free (.var owner) tail) = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (one : receipt.demand owner = some 1)
    (world : OwnerDemandWorld (run fuel (initial term)).state.heap.metadata code receipt) :
    let before := (run fuel (initial term)).state
    let result := run 3 before
    let next := code.child tail
    result.state.control = .evaluate next ∧
      result.state.heap.metadata.heap.live object = false ∧ result.events = [.legacy (.heap (.free object))] ∧
      LoanClosingTyped env loans false next meanings type ∧ ValueContext env next meanings ∧
      OwnerSizes env result.state.heap.metadata next meanings ∧ LoanCoverage next loans result.state.activeStack ∧
      ∃ tailFuel residual,
        LoanTyping.ResourceQuantity.projectRaw tailFuel env loans next.context tail = some residual ∧
        LoanTyping.ResourceQuantity.LoanBudget next.context.length loans residual ∧
        residual.demand owner = some 0 ∧ OwnerDemandWorld result.state.heap.metadata next residual := by
  let before := (run fuel (initial term)).state
  have live := (world.live_once owner object 0 stored one).1
  obtain ⟨entered,_,_,dead,_,events,_,typedTail,tailValues,tailSizes,tailCoverage,_⟩ :=
    reachable_typed_variable_free term fuel evaluating shape typed values sizes coverage stored live checked budget one
  obtain ⟨tailFuel,residual,recursive,receiptShape,zero,_⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_free_tail_receipt checked one
  have lifecycle := run_lifecycle (state := before) (initial_run_invariant term fuel).1 3
  change (run 3 before).events = _ at events
  rw [events] at lifecycle
  change SizedBufferHeap.Steps before.heap.metadata [.free object] (run 3 before).state.heap.metadata at lifecycle
  have retired := free_lifecycle_result lifecycle
  rw [receiptShape] at world budget one
  have newWorld := world.release (tail := tail) stored one zero
  rw [← retired] at newWorld
  exact ⟨entered,dead,events,typedTail,tailValues,tailSizes,tailCoverage,tailFuel,residual,
    recursive,budget.sequence.2.sequence.1,zero,newWorld⟩

/-- The admitted Store/Load program supplies the ownership invariant
without incoming captured-owner premises. Its source receipt identifies
the sole physical owner in the actual entered callback. -/
theorem checked_closed_store_load_owner_demand
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (accepted : LoanTyping.MixedProgram.checkDeclaration fuel quantityFuel env source =
      some ⟨type,storeLoadWith count offset fill value (.lam false first (.lam false again body))⟩)
    (sorted : LoanTyping.Checker.sort fuel env [] [] type = some (.type level))
    (fits : count*8+8 < 2^64) :
    let result := run 19 (initial (storeLoadWith count offset fill value (.lam false first (.lam false again body))))
    let code := storeLoadEntry count offset fill value first again body
    result.state.control = .evaluate code ∧
      ∃ bodyFuel receipt,
        LoanTyping.ResourceQuantity.projectRaw bodyFuel env [] code.context code.term = some receipt ∧
        let effective := reclose (functionTail body receipt)
        effective.demand 0 = some 1 ∧ OwnerDemandWorld result.state.heap.metadata code effective := by
  obtain ⟨entered,_,_,physical,_,_,_,_,bodyFuel,receipt,bodyChecked,one,_⟩ :=
    checked_closed_store_load_entry_resources history accepted sorted fits
  obtain ⟨object,_,identity,live,_,_⟩ := physical
  have same := Value.owner.inj identity
  subst object
  exact ⟨entered,bodyFuel,receipt,bodyChecked,one,OwnerDemandWorld.store_load_entry live one⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
