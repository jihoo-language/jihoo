import Jihoo.NativeBindingMachineCanonicalHandoff
import Jihoo.NativeLoanScalarFreeAliases

/-! Canonical resource authority is used at the actual aliased Free boundary.
The original check derives which owner alias can be released. Scalar return
and source tail typing/budgets follow from that same input, not output oracles. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

theorem reachable_canonical_scalar_release (term : Term) (fuel : Nat) (code : Code)
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
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (returned : (run fuel (initial term)).state.control = .returned (.integer value))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst code.origins) resultOrigin
        (code.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let closed := SizedBufferHeap.close heap token
    let released := SizedBufferHeap.release closed object
    let actual := restoredContinuation code first again (.free (.var releaseIndex) (.var 1))
      ((Term.var owner).subst code.origins) resultOrigin object (.integer value)
    let source := canonicalContinuation code owner first (.free (.var releaseIndex) (.var 1)) resultOrigin (.integer value)
    let tail := source.child (.var 0)
    let sourceMeanings := consValues (.integer value) meanings
    (releaseIndex = 0 ∨ releaseIndex = owner+2) ∧
    freeGuard closed object = true ∧ released.heap.live object = false ∧
    LoanTyping.HasType env [] [] false (.integer value) type ∧
    LoanClosingTyped env loans false tail sourceMeanings type ∧ OwnerSizes env released tail sourceMeanings ∧
    LoanCoverage tail loans stack ∧ ReaderInventory released (readerFrames stack) ∧ SizedBufferHeap.Valid released ∧
    CanonicalView (actual.child (.var 1)) tail (Jihoo.Quantity.openOwner (owner+1)) ∧
    run 9 (run fuel (initial term)).state =
      ⟨⟨released,.returned (.integer value),stack⟩,
        [.heap (.close token),.activate false (.lam false again (.free (.var releaseIndex) (.var 1))) resultOrigin,
          .activate false (.free (.var releaseIndex) (.var 1)) ((Term.var owner).subst code.origins),.heap (.free object)],9⟩ ∧
    ∃ rest, LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans tail.context tail.term = some rest ∧
      LoanTyping.ResourceQuantity.LoanBudget tail.context.length loans rest ∧ rest.demand (owner+1) = some 0 := by
  have selectedAlias := LoanTyping.ResourceQuantity.projectRaw_scalar_free_alias (shape ▸ checked)
  have handoff := reachable_canonical_scalar_handoff term fuel code history typed context sizes shape scalar checked
    budget coverage stored slots entered returned stackShape
  dsimp only at handoff
  obtain ⟨executed,view,sourceTyped,sourceContext,sourceSizes,sourceSlots,sourceCoverage,inventory,live,rest,restProjected,restBudget⟩ := handoff
  have globalPrefix := run_add fuel 5 (initial term)
  dsimp only at globalPrefix
  rw [executed] at globalPrefix
  have reachedState := congrArg (fun result => result.state) globalPrefix
  have reachedHeap := congrArg State.heap reachedState
  have covered : LoanCoverage
      (canonicalContinuation code owner first (.free (.var releaseIndex) (.var 1)) resultOrigin (.integer value))
      loans (run (fuel+5) (initial term)).state.stack := by
    rw [reachedState]
    exact sourceCoverage
  have actualStored :
      (restoredContinuation code first again (.free (.var releaseIndex) (.var 1))
        ((Term.var owner).subst code.origins) resultOrigin object (.integer value)).values[releaseIndex]? = some (some (.owner object)) := by
    rcases selectedAlias with rfl | rfl
    · rfl
    · simpa only [restoredContinuation,enter,List.getElem?_cons_succ] using stored
  have guarded := reachable_canonical_free_guard term (fuel+5) view rfl actualStored restProjected restBudget covered
  rw [reachedHeap] at guarded
  have closedValid := run_heap_valid (state := (run fuel (initial term)).state) (initial_run_heap_valid term fuel) 5
  rw [executed] at closedValid
  have freeStep := SizedBufferHeap.Step.free live (freeGuard_unborrowed closedValid guarded)
  have releasedValid := SizedBufferHeap.step_valid closedValid freeStep
  have releasedSizes := (sourceSizes.steps (.cons freeStep .nil)).child (.var 0)
  have releasedInventory : ReaderInventory
      (SizedBufferHeap.release (SizedBufferHeap.close (run fuel (initial term)).state.heap token) object)
      (readerFrames stack) := ⟨inventory.distinct,inventory.live,inventory.covered⟩
  have sourceShape :
      (canonicalContinuation code owner first (.free (.var releaseIndex) (.var 1)) resultOrigin (.integer value)).term =
      .free (.var (Jihoo.Quantity.openOwner (owner+1) releaseIndex)) (.var 0) := by
    simp only [canonicalContinuation,enter,Term.rename,renameArgs,Op.binders,liftRenaming,Jihoo.Quantity.openOwner]
  have sourceClosed := sourceTyped.closed history
  simp only [sourceShape,Term.subst,substArgs,Op.binders,liftSub,consValues] at sourceClosed
  have valueTyped := sourceClosed.free_tail
  have bounded := initial_run_integer_bound term fuel returned
  have runtimeTyped : LoanTyping.HasType env [] [] false (.integer value) type :=
    (LoanTyping.HasType.integer bounded.1 bounded.2).convert valueTyped.principalView
  obtain ⟨closing,localType,localTyped,converted⟩ := sourceTyped
  rw [sourceShape] at localTyped
  have tailTyped : LoanClosingTyped env loans false
      ((canonicalContinuation code owner first (.free (.var releaseIndex) (.var 1)) resultOrigin (.integer value)).child (.var 0))
      (consValues (.integer value) meanings) type := ⟨closing,localType,localTyped.free_tail,converted⟩
  have four := release_alias_return_four_steps (SizedBufferHeap.close (run fuel (initial term)).state.heap token)
    code first again ((Term.var owner).subst code.origins) resultOrigin object owner releaseIndex value stack
    stored selectedAlias live guarded
  dsimp only at four
  have composed := run_add 5 4 (run fuel (initial term)).state
  dsimp only at composed
  rw [executed] at composed
  dsimp only at composed
  rw [four] at composed
  have tailBudget := LoanTyping.ResourceQuantity.projectRaw_lend_free_tail_budget (shape ▸ checked) budget entered selectedAlias
  have tailView := view.child (.var 1)
  simp only [Term.rename,Jihoo.Quantity.openOwner] at tailView
  simp only [Term.subst,single] at tailBudget
  refine ⟨selectedAlias,guarded,?_,runtimeTyped,tailTyped,releasedSizes,sourceCoverage.child _,releasedInventory,releasedValid,
    tailView,?_,tailBudget⟩
  · simp only [SizedBufferHeap.release,HeapLeases.put,ite_true]
  · simpa only [List.cons_append,List.nil_append,Nat.reduceAdd] using composed

end Jihoo.NativeKernel.Environment.BindingMachine
