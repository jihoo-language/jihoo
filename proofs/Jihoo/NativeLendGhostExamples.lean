import Jihoo.NativeLendGhostChecking
import Jihoo.NativeLendPolicyExamples

namespace Jihoo.NativeKernel.Environment.Lending.GhostExamples

private def buffer : Term := .buffer (.natural 2)
private def ownerContext : Context := [⟨buffer,false⟩]
private def scalarReader : Term := .lam false (.ref buffer)
  (.index (.var 0) (.natural 0) (.decide (.natural 0) (.natural 2)))
private def scalarContinuation : Term :=
  .lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))

theorem scalar_specialized_checks :
    inferDependentGhost? 24 empty ownerContext (.var 0) scalarReader scalarContinuation = some .i64 := by cbv

theorem scalar_forward_original_type :
    ∃ output, EnvironmentDelta.Forward empty (desugar (.var 0) scalarReader scalarContinuation) output ∧
      HasType empty ownerContext true output .i64 :=
  inferDependentGhost?_sound UnifiedProgram.EnvWellFormed.empty scalar_specialized_checks

private def count (owner : Term) : Term := .free owner (.natural 0)
private def readValue : Term := count (.deref (.var 0))
private def readerPredicate : Term := .lam false .u64 (.eq (.var 0) (count (.deref (.var 1))))
private def dependentReader : Term := .lam false (.ref buffer)
  (.pack readerPredicate readValue (.refl readValue))
private def originalPredicate : Term := .lam false .u64 (.eq (.var 0) (count (.var 1)))
private def dependentContinuation : Term := .lam false (.refine originalPredicate)
  (.lam false buffer (.free (.var 0) (.witness (.var 1))))

/-- The reader result genuinely mentions its bound reference. Specialization
and Deref(Borrow(owner)) conversion align it with the original-owner predicate. -/
theorem dependent_specialized_checks :
    inferDependentGhost? 32 empty ownerContext (.var 0) dependentReader dependentContinuation =
      some .u64 := by cbv

theorem dependent_forward_original_type :
    ∃ output, EnvironmentDelta.Forward empty
        (desugar (.var 0) dependentReader dependentContinuation) output ∧
      HasType empty ownerContext true output .u64 :=
  inferDependentGhost?_sound UnifiedProgram.EnvWellFormed.empty dependent_specialized_checks

private def constantReader : Term := .lam false (.ref buffer) (.natural 0)
private def escapingContinuation : Term :=
  .lam false .u64 (.lam false buffer (.refl (.var 1)))

/-- A result depending on the temporary result binder cannot be shifted out. -/
theorem result_scope_escape_rejected :
    inferDependentGhost? 24 empty ownerContext (.var 0) constantReader escapingContinuation = none := by cbv

theorem unnamed_owner_rejected :
    inferDependentGhost? 24 empty [] (.alloc (.natural 2) (.integer 0))
      scalarReader scalarContinuation = none := by cbv

end Jihoo.NativeKernel.Environment.Lending.GhostExamples
