import Jihoo.NativeRetainedCallBodies
import Jihoo.NativeCallResourceContractExamples

namespace Jihoo.NativeKernel.Environment.CodeRetentionExamples
open CodeKinds ContextQuantity CallReplay NativeQuantity Jihoo.Quantity
open CallResourceContractExamples ContextReplayExamples ClosingTelescopeExamples

/-- The actual source body of the admitted owner-consuming call retains code
typing under its original two binders. No beta-reduct checker is run. -/
theorem actual_owned_body_code_typed :
    ∃ result, HasType .empty ownedOpened.context false ownedBody result := by
  obtain ⟨head,supplied,entries,result,opened,body,bodyType,split,sourceTyped,replayed,
      openedHead,formed,bodyTyped,projected,bodyContract,arguments⟩ :=
    checked_app_retained_body_contracts (fuel := 127) owned_full_call_resource_admitted
  have knownSplit : splitSpine 127 ownedCall [] = some (ownedFunction,[allocated,.natural 7]) := by cbv
  change splitSpine 127 ownedCall [] = some (head,supplied) at split
  rw [knownSplit] at split
  cases Option.some.inj split
  have knownOpened : openHead 127 .empty [] ownedFunction [allocated,.natural 7] = some ownedOpened := by cbv
  rw [knownOpened] at openedHead
  cases Option.some.inj openedHead
  exact ⟨bodyType,bodyTyped⟩

/-- An erased extra binding cannot turn the retained source body into ghost
code or erase its owner binding. The inserted annotation is arbitrary. -/
theorem actual_owned_body_under_erased_binding (annotation : Term) :
    ∃ result : Term, HasType .empty (⟨annotation,true⟩ :: ownedOpened.context) false
      (ownedBody.rename Nat.succ) (result.rename Nat.succ) := by
  obtain ⟨result,typed⟩ := actual_owned_body_code_typed
  exact ⟨result,typed.modeWeaken UnifiedProgram.EnvWellFormed.empty annotation true⟩

/-- Runtime owner lookup remains non-erased beneath the new erased binding. -/
theorem owner_lookup_retains_flag (annotation : Term) :
    lookup (⟨annotation,true⟩ :: ownedOpened.context) 2 = some ⟨owner,false⟩ := by
  cbv

def outerArrayMotive : Term := .lam false .u64 (.array (.var 1))

/-- The view result may depend on an arbitrary outer length while excluding
the removed motive binder. No constant or bounded array length is assumed. -/
theorem outer_array_view_policy : ViewMotiveAllowed .empty false true outerArrayMotive := by
  exact Or.inr (Or.inr ⟨false,.u64,.array (.var 1),.refl _,by cbv⟩)

theorem outer_array_view_policy_renamed :
    ViewMotiveAllowed .empty false true (.lam false .u64 (.array (.var 7))) := by
  simpa [outerArrayMotive,Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming] using
    outer_array_view_policy.renaming (fun x => x + 6) UnifiedProgram.EnvWellFormed.empty.closed

theorem array_motive_binder_dependency_rejected :
    viewRepresentation 128 1 (.array (.var 0)) = false := by cbv

/-- Existing alias-bearing positive-kind source code also retains its code
mode under an arbitrary inserted binding. -/
theorem aliased_kind_source_under_binding (annotation : Term) (erased : Bool) :
    HasType InferredKindExamples.aliasEnvironment [⟨annotation,erased⟩] false
      (InferredKindExamples.aliasSourceFunction.rename Nat.succ)
      (InferredKindExamples.aliasSourceSignature.rename Nat.succ) := by
  apply HasType.modeWeaken InferredKindExamples.alias_history.wellFormed
  exact Checker.check_sound (by cbv : Checker.check 64 InferredKindExamples.aliasEnvironment [] false
    InferredKindExamples.aliasSourceFunction InferredKindExamples.aliasSourceSignature = true)

end Jihoo.NativeKernel.Environment.CodeRetentionExamples
