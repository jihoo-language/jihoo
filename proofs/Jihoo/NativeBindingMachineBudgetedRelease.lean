import Jihoo.NativeBindingMachineLoanCoverage

/-! The same original quantity receipt's enclosing-reader budget derives a
physical Free guard for an arbitrary old owner. Freshness and no-reader or
successful-operation premises are absent. Global construction of the converse
loan association through arbitrary calls remains an explicit obligation. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

private theorem restored_integer_coverage (coverage : LoanCoverage code loans stack)
    (entered : Loans.Entered code.context.length loans) (absent : ¬ ObjectReader object stack)
    (first again body ownerOrigin resultOrigin : Term) (value : Int) :
    LoanCoverage (restoredContinuation code first again body ownerOrigin resultOrigin object (.integer value)) loans stack := by
  intro index queried stored present
  cases index with
  | zero =>
      have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj stored))
      exact False.elim (absent (same ▸ present))
  | succ index =>
      cases index with
      | zero => cases stored
      | succ index =>
          have active := coverage index queried stored present
          have deeper : Loans.Entered (code.context.length+1) loans := by
            intro frame member
            have previous := entered frame member
            omega
          simpa only [restoredContinuation,enter,List.length_cons,Loans.active_weaken deeper,Loans.active_weaken entered] using active

/-- Nine actual transitions close, bind both aliases, release and return the
observed scalar at the original source result type. Quantity budgets and the
converse loan association exclude every enclosing reader of this OLD owner.
No allocation age, birth prefix, output typing or successful suffix is assumed. -/
theorem reachable_raw_budgeted_scalar_release (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (shape : code.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1)))))
    (scalar : LoanTyping.ScalarReadShape readerBody)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some control)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans control)
    (coverage : LoanCoverage code loans stack)
    (stored : code.values[owner]? = some (some (.owner object)))
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = owner+2)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (returned : (run fuel (initial term)).state.control = .returned (.integer value))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst code.origins) resultOrigin
        (code.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let closed := SizedBufferHeap.close heap token
    let released := SizedBufferHeap.release closed object
    let next := restoredContinuation code first again (.free (.var releaseIndex) (.var 1))
      ((Term.var owner).subst code.origins) resultOrigin object (.integer value)
    let nextMeanings := consValues ((Term.var owner).subst meanings) (consValues (.integer value) meanings)
    freeGuard closed object = true ∧ released.heap.live object = false ∧
    LoanTyping.HasType env [] [] true (.integer value) type ∧
    OwnerSizes env released next nextMeanings ∧ LoanSlots next loans stack ∧ LoanCoverage next loans stack ∧
    ReaderInventory released (readerFrames stack) ∧ SizedBufferHeap.Valid released ∧
    run 9 (run fuel (initial term)).state =
      ⟨⟨released,.returned (.integer value),stack⟩,
        [.heap (.close token),.activate false (.lam false again (.free (.var releaseIndex) (.var 1))) resultOrigin,
          .activate false (.free (.var releaseIndex) (.var 1)) ((Term.var owner).subst code.origins),.heap (.free object)],9⟩ ∧
    ∃ rest,
      LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans (⟨first,false⟩ :: code.context)
        ((Term.var 1).subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      LoanTyping.ResourceQuantity.LoanBudget (code.context.length+1) loans rest ∧ rest.demand (owner+1) = some 0 := by
  have inactive := LoanTyping.ResourceQuantity.projectRaw_lend_inactive (shape ▸ checked) budget
  have absent := coverage.inactive stored inactive
  have tailBudget := LoanTyping.ResourceQuantity.projectRaw_lend_free_tail_budget (shape ▸ checked) budget entered selectedAlias
  have handoff := reachable_raw_scalar_value_lend_handoff term fuel code history typed context sizes shape scalar checked
    stored slots entered returned stackShape
  dsimp only at handoff
  obtain ⟨executed,nextContext,nextSizes,nextTyped,nextSlots,inventory,live,guard,aliases,resource⟩ := handoff
  have guarded := guard.mpr absent
  have closedValid := run_heap_valid (state := (run fuel (initial term)).state)
    (initial_run_heap_valid term fuel) 5
  rw [executed] at closedValid
  have freeStep := SizedBufferHeap.Step.free live (freeGuard_unborrowed closedValid guarded)
  have releasedValid := SizedBufferHeap.step_valid closedValid freeStep
  have releasedSizes := nextSizes.steps (.cons freeStep .nil)
  have releasedInventory : ReaderInventory
      (SizedBufferHeap.release (SizedBufferHeap.close (run fuel (initial term)).state.heap token) object)
      (readerFrames stack) := ⟨inventory.distinct,inventory.live,inventory.covered⟩
  have original := nextTyped
  simp only [restoredContinuation,enter,Term.subst,substArgs,Op.binders,liftSub,consValues] at original
  have valueTyped := original.free_tail
  have four := release_alias_return_four_steps (SizedBufferHeap.close (run fuel (initial term)).state.heap token)
    code first again ((Term.var owner).subst code.origins) resultOrigin object owner releaseIndex value stack
    stored selectedAlias live guarded
  dsimp only at four
  have composed := run_add 5 4 (run fuel (initial term)).state
  dsimp only at composed
  rw [executed] at composed
  dsimp only at composed
  rw [four] at composed
  refine ⟨guarded,?_,valueTyped,releasedSizes,nextSlots,
    restored_integer_coverage coverage entered absent _ _ _ _ _ _,releasedInventory,releasedValid,?_,tailBudget⟩
  · simp only [SizedBufferHeap.release,HeapLeases.put,ite_true]
  · simpa only [List.cons_append,List.nil_append,Nat.reduceAdd] using composed

end Jihoo.NativeKernel.Environment.BindingMachine
