import Jihoo.NativeCallResourceContracts
import Jihoo.NativeInferredKindExamples

namespace Jihoo.NativeKernel.Environment.CallResourceContractExamples
open ContextQuantity CallReplay ContextReplayExamples ClosingTelescopeExamples InferredKindExamples
open Jihoo.Quantity NativeQuantity

def ownedFunction : Term := .lam false owner (.lam false .u64 (.free (.var 1) (.var 0)))
def ownedBody : Term := .free (.var 1) (.var 0)
def ownedCall : Term := .app (.app ownedFunction allocated) (.natural 7)
def ownedEntries : List Argument := [⟨false,owner,allocated⟩,⟨false,.u64,.natural 7⟩]
def ownedOpened : Opened := ⟨[⟨.u64,false⟩,⟨owner,false⟩],[.linear,.unrestricted],ownedBody⟩

theorem same_unified_owned_full_call :
    (UnifiedProgram.checkProgram 64 128 [⟨.u64,ownedCall⟩] []).isSome = true := by cbv

theorem owned_full_call_resource_admitted : checkResource 128 .empty ownedCall = true := by cbv

/-- The same accepted call supplies actual owner-body exact use and argument
resource safety. No independent function/body resource check is an input. -/
theorem actual_owned_call_body_contract :
    ∃ body, projectRaw 127 .empty ownedOpened.context ownedBody = some body ∧
      BodyContract [.linear,.unrestricted] body ∧
      (Control.scopes [.unrestricted] body).demand 0 = some 1 ∧
      ResourceSafe .empty allocated := by
  obtain ⟨head,supplied,entries,result,opened,runtime,body,split,replayed,guarded,openedHead,mapped,bodyProjected,bodyContract,arguments⟩ :=
    checked_app_contracts (fuel := 127) owned_full_call_resource_admitted
  have knownSplit : splitSpine 127 ownedCall [] = some (ownedFunction,[allocated,.natural 7]) := by cbv
  change splitSpine 127 ownedCall [] = some (head,supplied) at split
  rw [knownSplit] at split
  simp only [Option.some.injEq,Prod.mk.injEq] at split
  obtain ⟨rfl,rfl⟩ := split
  have knownReplay : CallReplay.checked 127 .empty [] false ownedFunction [allocated,.natural 7] = some (ownedEntries,.u64) := by cbv
  simp only [knownReplay,Option.some.injEq,Prod.mk.injEq] at replayed
  obtain ⟨rfl,rfl⟩ := replayed
  have knownOpened : openHead 127 .empty [] ownedFunction [allocated,.natural 7] = some ownedOpened := by cbv
  simp only [knownOpened,Option.some.injEq] at openedHead
  subst opened
  refine ⟨body,bodyProjected,bodyContract,bodyContract.1.1,?_⟩
  exact runtime_arguments_resourceSafe mapped arguments
    (by simp [runtimeArguments,ownedEntries])

theorem owned_partial_factory_rejected :
    checkResource 128 .empty (.app ownedFunction allocated) = false := by cbv

def ghostIndex : Term := .strict (.borrow allocated) (.natural 0)
def erasedCall : Term := applications indexedIdentity
  [computedScalarFamily,ghostIndex,.natural 7]

/-- A genuinely erased U64 index can contain ghost-only borrowing. The actual
runtime erasure list, rather than an assumed all-code child list, is required. -/
theorem ghost_index_has_no_code_inference : Checker.infer 64 .empty [] false ghostIndex = none := by cbv

theorem same_unified_ghost_only_erased_index :
    (UnifiedProgram.checkProgram 64 128 [⟨.u64,erasedCall⟩] []).isSome = true := by cbv

theorem erased_index_not_a_runtime_argument :
    runtimeArguments [⟨false,.pi false .u64 (.univ 0),computedScalarFamily⟩,
      ⟨true,.u64,ghostIndex⟩,⟨false,.u64,.natural 7⟩] = [computedScalarFamily,.natural 7] := rfl

end Jihoo.NativeKernel.Environment.CallResourceContractExamples
