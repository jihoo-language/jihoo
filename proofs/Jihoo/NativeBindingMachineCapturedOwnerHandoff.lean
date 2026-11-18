import Jihoo.NativeBindingMachineCanonicalCaptures

/-! A checked reader can return an existing captured Buffer. The original
resource receipt pays for the captured variable, and the continuation must use
the new result binding while the retained old slot has zero residual demand. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity
variable {control : Control}

private theorem projected_variable_use
    (checked : projectRaw (fuel+1) env loans ctx (.var index) = some control) :
    control = .use index := by
  simp only [projectRaw] at checked
  obtain ⟨binding,_,result⟩ := Option.bind_eq_some_iff.mp checked
  split at result
  · contradiction
  · exact (Option.some.inj result).symm

/-- Specializing a reader whose body is an outer variable exposes exactly
that capture's ownership use. The complete Lend receipt excludes both active
loans and the owner currently being lent, and transfers the capture's unit
budget to the new Buffer result binding. -/
theorem projectRaw_lend_captured_buffer
    (checked : projectRaw (fuel+2) env loans ctx (.lend (.var owner)
      (.lam false domain (.var (captured+1)))
      (.lam false (.buffer length) (.lam false again body))) = some control)
    (budget : LoanBudget ctx.length loans control)
    (entered : Loans.Entered ctx.length loans)
    (once : control.demand captured = some 1) :
    captured ≠ owner ∧ Loans.active ctx.length loans captured = false ∧
    ∃ rest, projectRaw (fuel+1) env loans (⟨.buffer length,false⟩ :: ctx)
        (body.rename (Jihoo.Quantity.openOwner (owner+1))) = some rest ∧
      LoanBudget (ctx.length+1) loans rest ∧
      rest.demand 0 = some 1 ∧ rest.demand (captured+1) = some 0 ∧
      control = .seq (.use captured) (.scope .linear rest) := by
  obtain ⟨outside,sort,result,reader,mode,rest,originalScoped,readerScoped,restScoped,
    sourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,
    readZero,ownerOne,rfl⟩ := dependent_raw_project_contract checked
  have capturedProjected : projectRaw (fuel+1) env (Loans.enter ctx.length owner loans) ctx
      (.var captured) = some reader := by
    simpa only [Lending.read,Term.subst,single] using readProjected
  have readIsUse := projected_variable_use capturedProjected
  rw [readIsUse] at readZero budget once
  have different : captured ≠ owner := by
    intro same
    rw [same] at readZero
    simp [Control.demand] at readZero
  have parts := budget.sequence
  have inactive : Loans.active ctx.length loans captured = false := by
    apply Bool.eq_false_iff.mpr
    intro active
    have zero := parts.1 captured active
    simp [Control.demand] at zero
  have linear := resolved.buffer_linear
  subst mode
  have firstOne : rest.demand 0 = some 1 := (NativeQuantity.demand_localScopes _ ownerOne).1
  have residual : rest.demand (captured+1) = some 0 := by
    change (some (if captured = captured then 1 else 0)).bind
      (fun used => ((Control.scope .linear rest).demand captured).bind
        (fun remaining => some (used+remaining))) = some 1 at once
    simp only [Option.bind_some] at once
    simp only [Control.demand,firstOne] at once
    cases demand : rest.demand (captured+1) with
    | none => simp [demand] at once
    | some count =>
        have zero : count = 0 := by simpa [demand] using once
        exact congrArg some zero
  rw [restore_body_is_alias] at restProjected
  exact ⟨different,inactive,rest,restProjected,parts.2.scope entered,firstOne,residual,
    by rw [readIsUse]⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- A demanded physical owner has one source slot authorized to consume it.
Retained aliases of that object have zero demand in the same receipt. -/
def ExclusiveOwnerDemand (code : Code) (control : Jihoo.Quantity.Control) : Prop :=
  ∀ index alias object uses, index ≠ alias →
    code.values[index]? = some (some (.owner object)) →
    code.values[alias]? = some (some (.owner object)) →
    control.demand index = some (uses+1) → control.demand alias = some 0

/-- The saved source coverage and the exact reader receipt rule out returning
any object with an outer reader. The result binding has the only continuing
unit of demand for that physical allocation, even though the machine retains
the older alias. Other objects preserve their exclusive demand. -/
theorem captured_owner_handoff_coverage
    (originalCoverage : LoanCoverage original loans stack)
    (exclusive : ExclusiveOwnerDemand original control)
    (entered : Loans.Entered original.context.length loans)
    (storedOwner : original.values[owner]? = some (some (.owner object)))
    (storedCapture : original.values[captured]? = some (some (.owner returned)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (fuel+2) env loans original.context
      (.lend (.var owner) (.lam false domain (.var (captured+1)))
        (.lam false (.buffer length) (.lam false again body))) = some control)
    (budget : LoanTyping.ResourceQuantity.LoanBudget original.context.length loans control)
    (once : control.demand captured = some 1) (resultOrigin : Term) :
    let next := canonicalContinuation original owner (.buffer length) body resultOrigin (.owner returned)
    returned ≠ object ∧ ¬ ObjectReader returned stack ∧ LoanCoverage next loans stack ∧
    ∃ rest, LoanTyping.ResourceQuantity.projectRaw (fuel+1) env loans next.context next.term = some rest ∧
      LoanTyping.ResourceQuantity.LoanBudget next.context.length loans rest ∧ rest.demand 0 = some 1 ∧
      ExclusiveOwnerDemand next rest := by
  obtain ⟨different,inactive,rest,projected,restBudget,firstOne,residual,controlShape⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_lend_captured_buffer checked budget entered once
  have noReader := originalCoverage.inactive storedCapture inactive
  have differentObject : returned ≠ object := by
    intro same
    rw [same] at storedCapture
    have zero := exclusive captured owner object 0 different storedCapture storedOwner once
    rw [LoanTyping.ResourceQuantity.projectRaw_lend_owner_demand checked] at zero
    contradiction
  have coverage : LoanCoverage
      (canonicalContinuation original owner (.buffer length) body resultOrigin (.owner returned)) loans stack := by
    intro index queried stored present
    cases index with
    | zero =>
        have same : returned = queried := Value.owner.inj (Option.some.inj (Option.some.inj stored))
        exact False.elim (noReader (same ▸ present))
    | succ index =>
        have active := originalCoverage index queried stored present
        simpa only [canonicalContinuation,enter,List.length_cons,Loans.active_weaken entered] using active
  have shifted (index : Nat) (other : index ≠ captured) :
      control.demand index = rest.demand (index+1) := by
    simp [controlShape,Jihoo.Quantity.Control.demand,firstOne,Ne.symm other]
  have oldAliases (index : Nat) (stored : original.values[index]? = some (some (.owner returned))) :
      rest.demand (index+1) = some 0 := by
    by_cases same : index = captured
    · subst index
      exact residual
    · rw [← shifted index same]
      exact exclusive captured index returned 0 (Ne.symm same) storedCapture stored once
  refine ⟨differentObject,noReader,coverage,rest,projected,restBudget,firstOne,?_⟩
  intro index alias queried uses unequal storedIndex storedAlias used
  cases index with
  | zero =>
      have identity : returned = queried := Value.owner.inj (Option.some.inj (Option.some.inj storedIndex))
      subst queried
      cases alias with
      | zero => contradiction
      | succ other => exact oldAliases other storedAlias
  | succ index =>
      cases alias with
      | zero =>
          have identity : returned = queried := Value.owner.inj (Option.some.inj (Option.some.inj storedAlias))
          subst queried
          have zero := oldAliases index storedIndex
          rw [used] at zero
          exact False.elim (Nat.succ_ne_zero uses (Option.some.inj zero))
      | succ alias =>
          have otherIndex : index ≠ captured := by
            intro same
            subst index
            rw [used] at residual
            exact Nat.succ_ne_zero uses (Option.some.inj residual)
          by_cases same : alias = captured
          · subst alias
            exact residual
          · rw [← shifted alias same]
            have differentSlots : index ≠ alias := fun equal => unequal (congrArg Nat.succ equal)
            exact exclusive index alias queried uses differentSlots storedIndex storedAlias
              ((shifted index otherIndex).trans used)

/-- From an actual reader activation, the captured variable returns its existing
owner in seven transitions through close and the saved continuation. The same
source receipt gives the continuation's loan budget and exclusive owner demand. -/
theorem reachable_canonical_captured_owner_handoff (term : Term) (fuel : Nat)
    (view : CapturedCanonicalView actual original indices)
    (shape : actual.term = .lend (.var owner) (.lam false domain (.var (captured+1)))
      (.lam false (.buffer length) (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans original.context
      original.term = some control)
    (budget : LoanTyping.ResourceQuantity.LoanBudget original.context.length loans control)
    (once : control.demand (indices captured) = some 1)
    (exclusive : ExclusiveOwnerDemand original control)
    (coverage : LoanCoverage original loans stack) (scope : LoanScope original loans stack)
    (storedOwner : actual.values[owner]? = some (some (.owner object)))
    (storedCapture : actual.values[captured]? = some (some (.owner returned)))
    (controlShape : (run fuel (initial term)).state.control =
      .returned (.closure false domain (.var (captured+1)) actual.context actual.origins actual.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object name ((Term.var owner).subst actual.origins) readerOrigin
        (actual.child (.lam false (.buffer length) (.lam false again body))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let ownerOrigin := (Term.var owner).subst actual.origins
    let resultOrigin := (enter false domain (.var (captured+1)) actual.context actual.origins actual.values
      (.borrow ownerOrigin) (some (.reference token))).origin
    let actualNext := restoredContinuation actual (.buffer length) again body
      ownerOrigin resultOrigin object (.owner returned)
    let next := canonicalContinuation original (indices owner) (.buffer (length.rename indices))
      (body.rename (liftRenaming 2 indices)) resultOrigin (.owner returned)
    run 7 (run fuel (initial term)).state =
      ⟨⟨SizedBufferHeap.close heap token,.evaluate actualNext,stack⟩,
        [.activate false (.var (captured+1)) (.borrow ownerOrigin),.heap (.close token),
          .activate false (.lam false again body) resultOrigin,.activate false body ownerOrigin],7⟩ ∧
    CapturedCanonicalView actualNext next (Jihoo.Quantity.openOwner (indices owner+1) ∘ liftRenaming 2 indices) ∧
    returned ≠ object ∧ ¬ ObjectReader returned stack ∧ LoanCoverage next loans stack ∧
    ∃ rest, LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans next.context next.term = some rest ∧
      LoanTyping.ResourceQuantity.LoanBudget next.context.length loans rest ∧ rest.demand 0 = some 1 ∧
      ExclusiveOwnerDemand next rest := by
  let heap := (run fuel (initial term)).state.heap
  let ownerOrigin := (Term.var owner).subst actual.origins
  let resultOrigin := (enter false domain (.var (captured+1)) actual.context actual.origins actual.values
    (.borrow ownerOrigin) (some (.reference token))).origin
  have originalShape : original.term = .lend (.var (indices owner))
      (.lam false (domain.rename indices) (.var (indices captured+1)))
      (.lam false (.buffer (length.rename indices))
        (.lam false (again.rename (liftRenaming 1 indices)) (body.rename (liftRenaming 2 indices)))) := by
    rw [← view.view.termEq,shape]
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming]
    rfl
  have transferred := captured_owner_handoff_coverage coverage exclusive scope.entered
    ((view.view.values owner).symm.trans storedOwner) ((view.view.values captured).symm.trans storedCapture)
    (originalShape ▸ checked) budget once resultOrigin
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory heap ((token,object,name) :: readerFrames stack) at inventory
  have leased := inventory.live _ List.mem_cons_self
  change heap.heap.lease token = some object at leased
  have stateShape : (run fuel (initial term)).state = ⟨heap,
      .returned (.closure false domain (.var (captured+1)) actual.context actual.origins actual.values),
      .lendReader token object name ownerOrigin readerOrigin
        (actual.child (.lam false (.buffer length) (.lam false again body))) :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all [heap,ownerOrigin]
  refine ⟨?_,?_,transferred⟩
  · rw [stateShape]
    simp only [run,step,action,returnAction,execute,evaluateAction,
      enter,List.getElem?_cons_succ,storedCapture,Code.child,applyValue,restoredContinuation,
      Option.map_some,leased,ite_true]
    rfl
  · simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
      view.restored storedOwner (.buffer length) again body resultOrigin (.owner returned)

end Jihoo.NativeKernel.Environment.BindingMachine
