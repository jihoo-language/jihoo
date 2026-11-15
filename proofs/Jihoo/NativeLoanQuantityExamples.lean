import Jihoo.NativeLoanQuantity
import Jihoo.NativeLoanCheckerExamples

namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity.Examples
open Jihoo.Quantity NativeQuantity CheckerExamples

theorem dependent_closed_call_admitted : checkClosed 64 128 empty closedCall .i64 = true := by cbv

theorem generic_allocated_owner_admitted :
    checkClosed 64 128 empty (.lend allocatedOwner reader continuation) .i64 = true := by cbv

def originalContinuation : Term := .lam false .i64 (.lam false buffer (.free (.var 2) (.var 1)))
def originalAlias : Term := .lend (.var 0) reader originalContinuation
def closeOwner (body : Term) : Term := .app (.lam false buffer body) allocatedOwner

/-- The original owner and returned owner are the same identity, so consuming
the original spelling is admitted after the actual native restoration. -/
theorem original_owner_alias_admitted : checkClosed 64 128 empty (closeOwner originalAlias) .i64 = true := by cbv

def bothContinuation : Term := .lam false .i64
  (.lam false buffer (.free (.var 0) (.free (.var 2) (.var 1))))
def bothAliases : Term := .lend (.var 0) reader bothContinuation

theorem both_aliases_still_type_check : Checker.check 64 empty [] ownerContext false bothAliases .i64 = true := by cbv

/-- Both names collapse before demand is computed, exposing the duplicate. -/
theorem both_owner_aliases_rejected : checkClosed 64 128 empty (closeOwner bothAliases) .i64 = false := by cbv

def consumingReader : Term := .lam false (.ref buffer) (.free (.var 1) (.integer 0))
def consumingReaderSource : Term := .lend (.var 0) consumingReader continuation

theorem consuming_reader_still_type_checks :
    Checker.check 64 empty [] ownerContext false consumingReaderSource .i64 = true := by cbv

theorem reader_owner_consumption_rejected :
    checkClosed 64 128 empty (closeOwner consumingReaderSource) .i64 = false := by cbv

def firstOwner : Term := .buffer (.natural 0)
def allocatingReader : Term := .lam false (.ref buffer) (.alloc (.natural 0) (.integer (-1)))
def ownedResultContinuation : Term := .lam false firstOwner
  (.lam false buffer (.free (.var 1) (.free (.var 0) (.integer 7))))
def ownedResultSource : Term := .lend (.var 0) allocatingReader ownedResultContinuation

theorem distinct_first_owned_result_admitted :
    checkClosed 64 128 empty (closeOwner ownedResultSource) .i64 = true := by cbv

theorem first_owned_result_mode_is_linear :
    ResourceModes.resolve 64 empty [] ownerContext false firstOwner = some .linear := by cbv

def droppedFirstContinuation : Term := .lam false firstOwner (.lam false buffer (.free (.var 0) (.integer 7)))
def droppedFirstSource : Term := .lend (.var 0) allocatingReader droppedFirstContinuation

theorem dropped_owned_first_still_type_checks :
    Checker.check 64 empty [] ownerContext false droppedFirstSource .i64 = true := by cbv

theorem dropped_owned_first_rejected : checkClosed 64 128 empty (closeOwner droppedFirstSource) .i64 = false := by cbv

def duplicatedFirstContinuation : Term := .lam false firstOwner
  (.lam false buffer (.free (.var 1) (.free (.var 1) (.free (.var 0) (.integer 7)))))
def duplicatedFirstSource : Term := .lend (.var 0) allocatingReader duplicatedFirstContinuation

theorem duplicated_owned_first_rejected :
    checkClosed 64 128 empty (closeOwner duplicatedFirstSource) .i64 = false := by cbv

theorem borrow_rejected_after_exit :
    (project 64 empty [] ownerContext (.borrow (.var 0))).isSome = false := by cbv

theorem borrow_admitted_inside_reader :
    project 64 empty (Loans.enter ownerContext.length 0 []) ownerContext (.borrow (.var 0)) = some .pure := by cbv

def computedReader : Term := .ifLt (.natural 0) (.natural 1) reader reader
def computedContinuation : Term := .ifEq (.natural 0) (.natural 0) continuation continuation

theorem computed_generic_callbacks_admitted : checkClosed 64 128 empty
    (closeOwner (.lend (.var 0) computedReader computedContinuation)) .i64 = true := by cbv

theorem nested_lend_under_strict_admitted :
    checkClosed 64 128 empty (.strict (.natural 0) closedCall) .i64 = true := by cbv

def ghostLendIndex : Term := .lend allocatedOwner
  (.lam false (.ref buffer) (.natural 0)) (.lam false .u64 (.lam false buffer (.natural 0)))
def familyContext : Context := [⟨.pi false .u64 (.univ 0),false⟩]

/-- The abstract family observer checks its genuine erased U64 Lend index
through the complete Loan64 checker, with no old sixty-rule fallback. -/
theorem abstract_family_with_ghost_lend_index : ResourceModes.resolve 64 empty [] familyContext false
    (.app (.var 0) ghostLendIndex) = some .unrestricted := by cbv

theorem ghost_lend_index_really_typed : Checker.check 64 empty [] [] true ghostLendIndex .u64 = true := by cbv

def hiddenUnscopedAgain : Term := .app (.lam true .u64 buffer) (.var 99)
def hiddenScopeSource : Term := .lend (.var 0) reader
  (.lam false .i64 (.lam false hiddenUnscopedAgain (.free (.var 0) (.var 1))))

theorem typing_does_not_supply_original_annotation_scope :
    Checker.check 64 empty [] [] false (closeOwner hiddenScopeSource) .i64 = true := by cbv

theorem original_annotation_scope_guard_rejects :
    NativeKernel.scopeCheck 0 (closeOwner hiddenScopeSource) = false := by cbv

theorem unscoped_again_resource_entry_rejects :
    checkClosed 64 128 empty (closeOwner hiddenScopeSource) .i64 = false := by cbv

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity.Examples
