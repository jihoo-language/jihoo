import Jihoo.NativeBindingMachineMutableClosedStoreLoad
import Jihoo.NativeLoanTypeUniqueness

/-! An admitted closed Store/Load program starts its actual callback with a
typed retained context. The written owner and observed integer both come from
the evaluator; the callback body can be any accepted dependent CODE term. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds

private theorem entry_context (metadata : SizedBufferHeap.State)
    (closing : LoanTyping.Ghost.Substitution env (storeLoadEntry count offset fill value first again body).context []
      (storeLoadEntry count offset fill value first again body).origins)
    (owner : OwnerSize env metadata 0 (again.subst (single (.integer value))))
    (integer : LoanTyping.Conversion.Conv env .i64 first) :
    let code := storeLoadEntry count offset fill value first again body
    ValueContext env code code.origins ∧ OwnerSizes env metadata code code.origins := by
  let code := storeLoadEntry count offset fill value first again body
  have headType : (again.rename Nat.succ).subst code.origins = again.subst (single (.integer value)) := by
    change (again.rename Nat.succ).subst (consValues (storeArgument count offset fill value)
      (consValues (.integer value) Term.var)) = _
    rw [shift_subst_consValues]
    rfl
  have secondType : ((first.rename Nat.succ).rename Nat.succ).subst code.origins = first := by
    change ((first.rename Nat.succ).rename Nat.succ).subst (consValues (storeArgument count offset fill value)
      (consValues (.integer value) Term.var)) = _
    rw [shift_subst_consValues,shift_subst_consValues,Term.subst_id]
  have headOwner : OwnerSize env metadata 0 ((again.rename Nat.succ).subst code.origins) := by
    rw [headType]
    exact owner
  have kinds : ∀ index binding actual, lookup code.context index = some binding →
      code.values[index]? = some (some actual) → ValueKind env actual (binding.ty.subst code.origins) := by
    intro index binding actual found stored
    cases index with
    | zero =>
        have bindingShape : binding = ⟨again.rename Nat.succ,false⟩ := (Option.some.inj found).symm
        have valueShape : actual = .owner 0 := (Option.some.inj (Option.some.inj stored)).symm
        subst binding actual
        exact ⟨_,headOwner.realization⟩
    | succ index =>
        cases index with
        | zero =>
            have bindingShape : binding = ⟨(first.rename Nat.succ).rename Nat.succ,false⟩ := (Option.some.inj found).symm
            have valueShape : actual = .integer value := (Option.some.inj (Option.some.inj stored)).symm
            subst binding actual
            exact secondType.symm ▸ integer
        | succ index => cases found
  have scalars : ScalarSlots code code.origins := by
    constructor
    · intro index number stored
      cases index with
      | zero => cases stored
      | succ index => cases index <;> cases stored
    · intro index number stored
      cases index with
      | zero => cases stored
      | succ index =>
          cases index with
          | zero =>
              have same : value = number := Value.integer.inj (Option.some.inj (Option.some.inj stored))
              exact congrArg Term.integer same
          | succ index => cases stored
  refine ⟨⟨closing,scalars,kinds⟩,?_⟩
  intro index binding object found stored
  cases index with
  | zero =>
      have bindingShape : binding = ⟨again.rename Nat.succ,false⟩ := (Option.some.inj found).symm
      have objectShape : object = 0 := (Value.owner.inj (Option.some.inj (Option.some.inj stored))).symm
      subst binding object
      exact headOwner
  | succ index => cases index <;> cases stored

/-- The actual checked expanded declaration supplies the callback's CODE
typing, and its 19-step prefix supplies the retained value and owner heap.
No typing, value interpretation or resource liveness of the entered callback
is supplied by the caller. -/
theorem checked_closed_store_load_entry
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.MixedProgram.DeclarationChecked env source
      ⟨type,storeLoadWith count offset fill value (.lam false first (.lam false again body))⟩)
    (formed : LoanTyping.HasType env [] [] true type (.univ level))
    (fits : count*8+8 < 2^64) :
    let result := run 19 (initial (storeLoadWith count offset fill value (.lam false first (.lam false again body))))
    let code := storeLoadEntry count offset fill value first again body
    result.steps = 19 ∧ result.state.control = .evaluate code ∧ result.state.stack = [] ∧ result.state.pending = [] ∧
      result.state.heap.metadata.heap.live 0 = true ∧ result.state.heap.metadata.length 0 = count ∧
      result.events.filterMap Event.lifecycle? = [.alloc 0 count (encodeInteger fill)] ∧
      LoanClosingTyped env [] false code code.origins type ∧ ValueContext env code code.origins ∧
      OwnerSizes env result.state.heap.metadata code code.origins := by
  let result := run 19 (initial (storeLoadWith count offset fill value (.lam false first (.lam false again body))))
  let code := storeLoadEntry count offset fill value first again body
  obtain ⟨sort,declared,typed,_⟩ := checked.valid.typing
  have correctSort := declared.sort_unique history.wellFormed (second := .type level) formed
  rw [correctSort] at typed
  change LoanTyping.HasType env [] [] false
    (.load (storeArgument count offset fill value) (.natural offset) (.decide (.natural offset) (.natural count))
      (.lam false first (.lam false again body))) type at typed
  obtain ⟨_,storeTyped,offsetTyped,bound⟩ := typed.load_inputs
  obtain ⟨_,allocTyped,_,valueTyped,_,_⟩ := storeTyped.store_inputs
  obtain ⟨countTyped,fillTyped⟩ := allocTyped.alloc_inputs
  have valueWidth := valueTyped.integer_bound
  have limits := bound.literal_decide_limits history.wellFormed
  obtain ⟨steps,entered,emptyStack,emptyPending,live,length,events⟩ := store_load_entry_steps count offset fill value
    first again body countTyped.natural_bound offsetTyped.natural_bound fillTyped.integer_bound valueWidth limits.2.2 fits
  obtain ⟨ownerCount,ownerTyped,integerDomain,ownerDomain,bodyTyped⟩ :=
    LoanTyping.load_retained_body history.wellFormed typed
  obtain ⟨_,allocationTyped,_,_,_,storeType⟩ := ownerTyped.store_inputs
  have closedOwnerType := (ownerDomain.substitution (single (.integer value)) history.wellFormed.closed).symm
  have ownerDomainConverted : LoanTyping.Conversion.Conv env (.buffer ownerCount)
      (again.subst (single (.integer value))) := by
    simpa only [Term.buffer,Term.subst,substArgs,Op.binders,liftSub,Term.shift_subst_single] using closedOwnerType
  have ownerGhost := (ownerTyped.ghost []).convert ownerDomainConverted
  have firstGhost : LoanTyping.HasType env [] [] true (.integer value) (first.subst Term.var) := by
    rw [Term.subst_id]
    exact (LoanTyping.HasType.integer valueWidth.1 valueWidth.2).convert integerDomain.symm
  have empty : LoanTyping.Ghost.Substitution env [] [] Term.var := by intro index binding found; cases found
  have closing : LoanTyping.Ghost.Substitution env code.context [] code.origins :=
    (empty.consValues firstGhost).consValues ownerGhost
  have typedBody : LoanClosingTyped env [] false code code.origins type := by
    refine ⟨closing,_,bodyTyped,?_⟩
    rw [Term.subst_rename]
    change LoanTyping.Conversion.Conv env (type.subst Term.var) type
    rw [Term.subst_id]
    exact .refl _
  have kind := allocationTyped.principalView.trans (storeType.trans ownerDomainConverted)
  have valid := (initial_run_invariant (storeLoadWith count offset fill value (.lam false first (.lam false again body))) 19).1
  have owner : OwnerSize env result.state.heap.metadata 0 (again.subst (single (.integer value))) :=
    ⟨valid.allocated 0 live,count,length,kind⟩
  obtain ⟨valueContext,ownerSizes⟩ := entry_context result.state.heap.metadata closing owner integerDomain.symm
  refine ⟨steps,entered,emptyStack,emptyPending,live,length,?_,typedBody,valueContext,ownerSizes⟩
  change result.events.filterMap Event.lifecycle? = _
  change result.events = _ at events
  rw [events]
  rfl

/-- Executable declaration admission and sort inference supply both input
judgments for the exact callback entry. -/
theorem check_closed_store_load_entry
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (accepted : LoanTyping.MixedProgram.checkDeclaration fuel quantityFuel env source =
      some ⟨type,storeLoadWith count offset fill value (.lam false first (.lam false again body))⟩)
    (sorted : LoanTyping.Checker.sort fuel env [] [] type = some (.type level))
    (fits : count*8+8 < 2^64) :
    let result := run 19 (initial (storeLoadWith count offset fill value (.lam false first (.lam false again body))))
    let code := storeLoadEntry count offset fill value first again body
    result.steps = 19 ∧ result.state.control = .evaluate code ∧ result.state.stack = [] ∧ result.state.pending = [] ∧
      result.state.heap.metadata.heap.live 0 = true ∧ result.state.heap.metadata.length 0 = count ∧
      result.events.filterMap Event.lifecycle? = [.alloc 0 count (encodeInteger fill)] ∧
      LoanClosingTyped env [] false code code.origins type ∧ ValueContext env code code.origins ∧
      OwnerSizes env result.state.heap.metadata code code.origins :=
  checked_closed_store_load_entry history (LoanTyping.MixedProgram.checkDeclaration_sound accepted)
    (LoanTyping.Checker.sort_sound sorted) fits

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
