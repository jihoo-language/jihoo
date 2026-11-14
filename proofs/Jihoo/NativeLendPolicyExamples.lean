import Jihoo.NativeLendSyntax
import Jihoo.NativeContextQuantity

/-! Loan/specialization boundaries that the future integrated Lend rule must
preserve. In particular giving the same owner back is aliasing, not permission
to consume both its old and its returned spelling. No native Lend typing rule
or complete code-substitution theorem is assumed here. -/
namespace Jihoo.NativeKernel.Environment.Lending.Examples

open Loans

theorem nested_owner_queries :
    active 4 [⟨3,1⟩,⟨1,0⟩] 2 = true ∧
    active 4 [⟨3,1⟩,⟨1,0⟩] 3 = true ∧
    active 4 [⟨3,1⟩,⟨1,0⟩] 1 = false := by decide

theorem exit_revokes_only_inner :
    active 3 (exit [⟨3,1⟩,⟨1,0⟩]) 2 = true ∧
    active 3 (exit [⟨3,1⟩,⟨1,0⟩]) 1 = false := by decide

theorem future_snapshot_inactive :
    active 2 [⟨3,0⟩] 0 = false := by decide

/-- Merely appending a binder may expose an invalid future snapshot. Such
states are excluded by the Entered premise of the weakening theorem. -/
theorem entered_premise_is_needed :
    active 0 [⟨1,0⟩] 0 = false ∧ active 1 [⟨1,0⟩] 0 = true := by decide

private def buffer : Term := .buffer (.natural 2)
private def reader : Term := .lam false (.ref buffer) (.natural 0)
private def continuation : Term :=
  .lam false .u64 (.lam false buffer (.free (.var 0) (.natural 0)))

/-- The two uses are aliases of the same original owner after specialization. -/
theorem returned_owner_aliases_original :
    restore (.var 0) .u64 (.free (.var 0) (.free (.var 2) (.natural 0))) =
      .lam false .u64 (.free (.var 1) (.free (.var 1) (.natural 0))) := by cbv

private def duplicated : Term := .lam false buffer
  (restore (.var 0) .u64 (.free (.var 0) (.free (.var 2) (.natural 0))))
private def duplicateType : Term := .pi false buffer (.pi false .u64 .u64)

/-- Ordinary typing alone allows both frees; the real current resource gate
rejects the specialized continuation's duplicated owner demand. -/
theorem alias_duplicate_typed : HasType empty [] false duplicated duplicateType :=
  Checker.check_sound (by cbv : Checker.check 24 empty [] false duplicated duplicateType = true)

theorem alias_duplicate_resource_rejected :
    ContextQuantity.checkClosed 24 64 empty duplicated duplicateType = false := by cbv

private def single : Term := .lam false buffer
  (restore (.var 0) .u64 (.free (.var 0) (.natural 0)))

theorem returned_owner_consumed_once :
    ContextQuantity.checkClosed 24 64 empty single duplicateType = true := by cbv

/-- This is the native syntactic dependent-path boundary, not a claim that
all ghost typing must fail after replacing a named owner with a value. -/
theorem dependent_path_requires_named_owner :
    (dependent? (.var 0) reader continuation).isSome = true ∧
    dependent? (.alloc (.natural 2) (.integer 0)) reader continuation = none := by decide

theorem ghosts_need_no_live_frame :
    borrowAllowed true 0 [] (.alloc (.natural 2) (.integer 0)) = true ∧
    borrowAllowed false 0 [] (.alloc (.natural 2) (.integer 0)) = false := by decide

end Jihoo.NativeKernel.Environment.Lending.Examples
