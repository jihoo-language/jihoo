import Jihoo.NativeClosingTelescopeExamples

/-! A finite check on the boundary between raw ghost beta reduction and runtime
CODE rechecking. Strict is internal Core syntax. The native runtime retains
memory-touching arguments, and native Core normalizes away nontrapping Strict
prefixes; its behavior is not identified with unrestricted syntactic beta. -/
namespace Jihoo.NativeKernel.Environment.CodeBetaBoundary

def ownerType : Term := .buffer (.natural 2)
def ownerValue : Term := .strict ownerType (.alloc (.natural 2) (.integer 0))
def typeConsumer : Term := .lam false (.univ 0) (.natural 0)
def typedBody : Term := .app typeConsumer (.strict (.var 0) .u64)
def outerFunction : Term := .lam false ownerType typedBody
def sourceCall : Term := .app outerFunction ownerValue
def rawBeta : Term := .app typeConsumer (.strict ownerValue .u64)

theorem same_unified_source_accepted :
    (UnifiedProgram.checkProgram 64 128 [⟨.u64,sourceCall⟩] []).isSome = true := by cbv

theorem independent_checker_source_accepted :
    Checker.check 64 .empty [] false sourceCall .u64 = true := by cbv

theorem raw_syntactic_beta_code_recheck_rejected :
    Checker.check 64 .empty [] false rawBeta .u64 = false := by cbv

theorem raw_syntactic_beta_program_recheck_rejected :
    (UnifiedProgram.checkProgram 64 128 [⟨.u64,rawBeta⟩] []).isSome = false := by cbv

theorem exposed_strict_kind_gate_rejected :
    Checker.applicationOK 64 .empty false (.univ 0) (.strict ownerValue .u64) = false := by cbv

theorem source_resource_check_accepted : ContextQuantity.checkResource 128 .empty sourceCall = true := by cbv

theorem raw_syntactic_beta_resource_recheck_rejected : ContextQuantity.checkResource 128 .empty rawBeta = false := by cbv

theorem raw_ghost_beta_forward : EnvironmentDelta.Forward .empty sourceCall rawBeta := by
  apply EnvironmentDelta.Forward.acu
  apply ACU.MixedRed.compute
  simpa [sourceCall,rawBeta,outerFunction,typedBody,typeConsumer,ownerValue,ownerType,
    Term.subst,substArgs,Op.binders,liftSub,liftSubOne,single,Term.rename,renameArgs] using
    ACU.Computes.beta false ownerType typedBody ownerValue

theorem raw_ghost_beta_original_type_preserved : HasType .empty [] true rawBeta .u64 :=
  (Checker.check_sound independent_checker_source_accepted).ghostForward
    ClosingTelescopeExamples.empty_history raw_ghost_beta_forward

end Jihoo.NativeKernel.Environment.CodeBetaBoundary
