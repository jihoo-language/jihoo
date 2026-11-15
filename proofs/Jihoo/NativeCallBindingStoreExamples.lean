import Jihoo.NativeCallStorePermissions
import Jihoo.NativeCodeRetentionExamples
import Jihoo.NativeInferredKindCoverageBoundary
import Jihoo.NativeCodeBetaBoundary

namespace Jihoo.NativeKernel.Environment.CallBindingStoreExamples
open CodeKinds ContextQuantity CallReplay NativeQuantity Jihoo.Quantity
open CallResourceContractExamples ContextReplayExamples ClosingTelescopeExamples

/-- The owner and scalar are the actual original source arguments, in their
exact right-to-left source binding slots. -/
theorem actual_owned_exact_store :
    Ghost.Substitution .empty ownedOpened.context []
      (pushValues Term.var [allocated,.natural 7]) := by
  obtain ⟨head,supplied,entries,result,opened,body,bodyType,actualSignature,middle,
      leading,trailing,split,replayed,inferred,openedHead,formed,retained,projected,bodyContract,
      store,closedBody,aligned,left,right,entriesSplit,arguments⟩ :=
    checked_app_typed_binding_store (fuel := 127) empty_history owned_full_call_resource_admitted
  have knownSplit : splitSpine 127 ownedCall [] = some (ownedFunction,[allocated,.natural 7]) := by cbv
  change splitSpine 127 ownedCall [] = some (head,supplied) at split
  rw [knownSplit] at split
  cases Option.some.inj split
  have knownOpened : openHead 127 .empty [] ownedFunction [allocated,.natural 7] = some ownedOpened := by cbv
  rw [knownOpened] at openedHead
  cases Option.some.inj openedHead
  simpa only [ownedOpened,List.length_cons,List.length_nil,List.take_succ_cons,List.take_zero] using store

theorem actual_owned_store_slots :
    pushValues Term.var [allocated,.natural 7] 0 = .natural 7 ∧
      pushValues Term.var [allocated,.natural 7] 1 = allocated := by
  constructor <;> rfl

theorem actual_owned_closed_body_typed :
    ∃ bodyType : Term, HasType .empty [] true
      (ownedBody.subst (pushValues Term.var [allocated,.natural 7]))
      (bodyType.subst (pushValues Term.var [allocated,.natural 7])) := by
  obtain ⟨bodyType,typed⟩ := CodeRetentionExamples.actual_owned_body_code_typed
  exact ⟨bodyType,typed.ghostSubstitution empty_history.wellFormed actual_owned_exact_store⟩

/-- The raw checker counterexample has no displayed inferred kind witness,
yet its authentic actual replay supplies its exact typed argument store.
This type-only endpoint assumes neither kind realization nor its completeness. -/
theorem non_displayed_inferred_kind_has_typed_store :
    Ghost.Substitution InferredKindCoverageBoundary.environment [⟨.univ 0,false⟩] []
      (pushValues Term.var [InferredKindCoverageBoundary.argument]) := by
  have telescope : Telescope InferredKindCoverageBoundary.environment []
      (.pi false (.univ 0) .u64) 1 [⟨.univ 0,false⟩] .u64 :=
    .cons (Checker.binder_sound (by cbv : Checker.binder 64 InferredKindCoverageBoundary.environment
      [] false (.univ 0) = some (.type 1))) .nil
  have source : HasType InferredKindCoverageBoundary.environment [] false
      InferredKindCoverageBoundary.consumer (.pi false (.univ 0) .u64) :=
    Checker.infer_sound (by cbv : Checker.infer 64 InferredKindCoverageBoundary.environment [] false
      InferredKindCoverageBoundary.consumer = some (.pi false (.univ 0) .u64))
  have closing : Ghost.Substitution InferredKindCoverageBoundary.environment [] [] Term.var := by
    intro index binding found
    simp [lookup] at found
  exact (telescope.close_typed_checkedCall InferredKindCoverageBoundary.authentic_history .nil closing source
    (by simpa only [Term.subst_id] using InferredKindCoverageBoundary.actual_raw_checked_call_accepted)
    (by rfl)).2.1

/-- The typed store faithfully closes this original code body even though
rechecking an unrestricted raw syntactic beta reduct rejects. This does not
identify that raw beta rule with native memory-touching argument evaluation. -/
theorem retained_code_beta_boundary :
    (∃ bodyType, HasType .empty [] true CodeBetaBoundary.rawBeta bodyType) ∧
      Checker.check 64 .empty [] false CodeBetaBoundary.rawBeta .u64 = false := by
  constructor
  · obtain ⟨head,supplied,entries,result,opened,body,bodyType,actualSignature,middle,
        leading,trailing,split,replayed,inferred,openedHead,formed,retained,projected,bodyContract,
        store,closedBody,aligned,left,right,entriesSplit,arguments⟩ :=
      checked_app_typed_binding_store (fuel := 127) empty_history CodeBetaBoundary.source_resource_check_accepted
    have knownSplit : splitSpine 127 CodeBetaBoundary.sourceCall [] =
        some (CodeBetaBoundary.outerFunction,[CodeBetaBoundary.ownerValue]) := by cbv
    change splitSpine 127 CodeBetaBoundary.sourceCall [] = some (head,supplied) at split
    rw [knownSplit] at split
    cases Option.some.inj split
    have knownOpened : openHead 127 .empty [] CodeBetaBoundary.outerFunction [CodeBetaBoundary.ownerValue] =
        some ⟨[⟨CodeBetaBoundary.ownerType,false⟩],[.linear],CodeBetaBoundary.typedBody⟩ := by cbv
    rw [knownOpened] at openedHead
    cases Option.some.inj openedHead
    refine ⟨bodyType.subst (pushValues Term.var [CodeBetaBoundary.ownerValue]),?_⟩
    simpa [CodeBetaBoundary.typedBody,CodeBetaBoundary.rawBeta,CodeBetaBoundary.typeConsumer,
      Term.subst,substArgs,Op.binders,liftSub,liftSubOne,Term.rename,renameArgs,pushValues,consValues] using closedBody
  · exact CodeBetaBoundary.raw_syntactic_beta_code_recheck_rejected

def computedHead : Term := .ifLt (.natural 0) (.natural 1)
  (.lam false .u64 (.var 0)) (.lam false .u64 (.var 0))
def computedCall : Term := .app computedHead (.natural 7)

theorem actual_computed_call_admitted : checkResource 128 .empty computedCall = true := by cbv

/-- An unopened computed callee leaves its application in the actual replay
remainder and has an empty source store. No dynamic lambda body is fabricated. -/
theorem actual_computed_call_remaining_trace :
    ∃ signature entries result,
      Checker.infer 127 .empty [] false computedHead = some signature ∧
      CallReplay.Steps .empty [] false signature [.natural 7] entries result ∧
      Ghost.Substitution .empty [] [] Term.var := by
  obtain ⟨head,supplied,entries,result,opened,body,bodyType,actualSignature,middle,
      leading,trailing,split,replayed,inferred,openedHead,formed,retained,projected,bodyContract,
      store,closedBody,aligned,left,right,entriesSplit,arguments⟩ :=
    checked_app_typed_binding_store (fuel := 127) empty_history actual_computed_call_admitted
  have knownSplit : splitSpine 127 computedCall [] = some (computedHead,[.natural 7]) := by cbv
  change splitSpine 127 computedCall [] = some (head,supplied) at split
  rw [knownSplit] at split
  cases Option.some.inj split
  have knownOpened : openHead 127 .empty [] computedHead [.natural 7] = some ⟨[],[],computedHead⟩ := by cbv
  rw [knownOpened] at openedHead
  cases Option.some.inj openedHead
  cases left
  exact ⟨actualSignature,trailing,result,inferred,right,store⟩

def ghostEntries : List Argument :=
  [⟨false,.pi false .u64 (.univ 0),computedScalarFamily⟩,
    ⟨true,.u64,ghostIndex⟩,⟨false,.u64,.natural 7⟩]

/-- The same erased ghost-only argument has its exact source slot and actual
domain conversion; the permission theorem grants code access only when its
original erased flag is false. -/
theorem erased_ghost_slot_alignment :
    TypedSourceSlots .empty indexedIdentityContext
      (pushValues Term.var [computedScalarFamily,ghostIndex,.natural 7]) ghostEntries ∧
      Checker.infer 64 .empty [] false ghostIndex = none := by
  constructor
  · have closing : Ghost.Substitution .empty [] [] Term.var := by
      intro index binding found
      simp [lookup] at found
    apply indexed_identity_telescope.checkedCall_source_slots empty_history .nil closing
      (Checker.check_sound indexed_identity_checked) (fuel := 64)
    · simpa only [Term.subst_id] using (by cbv : CallReplay.checked 64 .empty [] false indexedIdentity
        [computedScalarFamily,ghostIndex,.natural 7] = some (ghostEntries,.u64))
    · rfl
  · exact ghost_index_has_no_code_inference

end Jihoo.NativeKernel.Environment.CallBindingStoreExamples
