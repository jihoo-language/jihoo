import Jihoo.NativeLendGhostChecking
import Jihoo.NativeLendPolicyExamples
import Jihoo.NativeLendGhostRule

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

private def allocatedOwner : Term := .alloc (.natural 2) (.integer 0)

/-- A value owner takes the generic native path. Its callbacks have the
actual independent result types checked by that path. -/
theorem generic_ghost_derivation : GhostDerivation empty []
    (.lend allocatedOwner scalarReader scalarContinuation) .i64 := by
  apply GhostDerivation.generic (ownerType := buffer) (valueType := .i64)
  · exact .alloc (.natural (by decide)) (.integer (by decide) (by decide))
  · exact .buffer (.refl _)
  · exact ⟨.i64,.refl _,rfl⟩
  · exact Checker.check_sound (by cbv : Checker.check 24 empty [] true scalarReader
      (.pi false (.ref buffer) (Term.i64.rename Nat.succ)) = true)
  · exact Checker.check_sound (by cbv : Checker.check 24 empty [] true scalarContinuation
      (.pi false .i64 ((Term.pi false buffer (Term.i64.rename Nat.succ)).rename Nat.succ)) = true)

theorem generic_ghost_original_type :
    ∃ output, EnvironmentDelta.Forward empty
      (desugar allocatedOwner scalarReader scalarContinuation) output ∧
      HasType empty [] true output .i64 :=
  generic_ghost_derivation.sound UnifiedProgram.EnvWellFormed.empty

theorem allocated_owner_uses_generic_path :
    dependent? allocatedOwner scalarReader scalarContinuation = none := by decide

end Jihoo.NativeKernel.Environment.Lending.GhostExamples
