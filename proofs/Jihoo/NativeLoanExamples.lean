import Jihoo.NativeLoanPermissions
import Jihoo.NativeLoanSubstitution

namespace Jihoo.NativeKernel.Environment.LoanTyping.Examples

private def buffer : Term := .buffer (.natural 2)
private def ownerContext : Context := [⟨buffer,false⟩]
private def readerBody : Term :=
  .index (.var 0) (.natural 0) (.decide (.natural 0) (.natural 2))
private def reader : Term := .lam false (.ref buffer) readerBody
private def continuationBody : Term := .free (.var 0) (.var 1)
private def continuation : Term := .lam false .i64 (.lam false buffer continuationBody)
private def source : Term := .lend (.var 0) reader continuation

private theorem owner_typed : Environment.HasType empty ownerContext false (.var 0) buffer :=
  Checker.check_sound (by cbv : Checker.check 24 empty ownerContext false (.var 0) buffer = true)

/-- The reader's actual snapshot authorizes the named owner's code borrow. -/
theorem active_code_borrow : HasType empty (Loans.enter ownerContext.length 0 [])
    ownerContext false (.borrow (.var 0)) (.ref buffer) :=
  .codeBorrowOwned (ofEnvironment owner_typed.ghost) (.buffer (.refl _)) (by decide)

private theorem specialized_reader_typed :
    HasType empty (Loans.enter ownerContext.length 0 []) ownerContext false
      (Lending.read (.var 0) readerBody) .i64 := by
  have shape : Lending.read (.var 0) readerBody = .index (.borrow (.var 0)) (.natural 0)
      (.decide (.natural 0) (.natural 2)) := by cbv
  rw [shape]
  exact .borrowedIndex active_code_borrow (ofEnvironment (.natural (by decide)))
    (ofEnvironment (.decide (by decide) (by decide) (by decide)))

/-- This uses code borrowing inside the reader and the popped stack inside
its continuation, with the owner returned as its original variable. -/
theorem dependent_code_lend : HasType empty [] ownerContext false source .i64 := by
  apply HasType.lendDependentCode (T := buffer) (A := .i64)
    (result := .i64) (normal := .i64) (sort := .type 0)
  · exact ofEnvironment owner_typed
  · exact .buffer (.refl _)
  · exact binder_ofEnvironment (Checker.binder_sound
      (by cbv : Checker.binder 24 empty ownerContext false (.ref buffer) = some (.type 0)))
  · exact .refl _
  · exact specialized_reader_typed
  · exact ⟨.i64,.refl _,rfl⟩
  · exact .refl _
  · have same : buffer.rename Nat.succ = buffer := by cbv
    rw [same]
    exact .refl _
  · exact ofEnvironment (Checker.check_sound
      (by cbv : Checker.check 24 empty ownerContext false
        (Lending.restore (.var 0) .i64 continuationBody) (.pi false .i64 .i64) = true))
  · exact .refl _
  · cbv
  · exact Or.inr (nonFunctionHead_full (by decide))

theorem lend_ghost_promotion : HasType empty [] ownerContext true source .i64 :=
  dependent_code_lend.ghost []

theorem pop_revokes_code_borrow :
    ¬ HasType empty (Loans.exit (Loans.enter ownerContext.length 0 []))
      ownerContext false (.borrow (.var 0)) type := HasType.no_code_borrow_without_reader

/-- The default executable gate is deliberately unchanged at this stage. -/
theorem default_checker_not_yet_extended :
    Checker.check 24 empty ownerContext false source .i64 = false := by cbv

private def allocatedOwner : Term := .alloc (.natural 2) (.integer 0)

theorem closed_code_function : HasType empty [] [] false
    (.lam false buffer source) (.pi false buffer .i64) :=
  .lam (binder_ofEnvironment (Checker.binder_sound
    (by cbv : Checker.binder 24 empty [] false buffer = some (.type 0)))) dependent_code_lend

theorem closed_code_application : HasType empty [] [] false
    (.app (.lam false buffer source) allocatedOwner) .i64 := by
  have allocated : HasType empty [] [] false allocatedOwner buffer :=
    ofEnvironment (Checker.check_sound
      (by cbv : Checker.check 24 empty [] false allocatedOwner buffer = true))
  have allowed : applicationAllowed empty false buffer allocatedOwner :=
    Or.inr ⟨buffer,.refl _,by cbv,Or.inl rfl⟩
  have applied := HasType.app closed_code_function allocated allowed
  change HasType empty [] [] false (.app (.lam false buffer source) allocatedOwner)
    (Term.i64.subst (single allocatedOwner)) at applied
  have same : Term.i64.subst (single allocatedOwner) = .i64 := by cbv
  exact same ▸ applied

/-- Ghost closing may replace the source's named owner by an allocating term.
This theorem deliberately does not claim raw effectful CODE substitution. -/
theorem arbitrary_owner_ghost_instantiation : HasType empty [] [] true
    (source.subst (single allocatedOwner)) .i64 := by
  have allocated : HasType empty [] [] true allocatedOwner buffer :=
    ofEnvironment (Checker.check_sound
      (by cbv : Checker.check 24 empty [] true allocatedOwner buffer = true))
  have specialized := dependent_code_lend.ghostInstantiate UnifiedProgram.EnvWellFormed.empty allocated
  have same : Term.i64.subst (single allocatedOwner) = .i64 := by cbv
  exact same ▸ specialized

theorem ghost_weakening_under_new_binder : HasType empty []
    (⟨Term.u64,false⟩ :: ownerContext) true (source.rename Nat.succ) .i64 := by
  have weakened := dependent_code_lend.ghostWeaken UnifiedProgram.EnvWellFormed.empty .u64 false
  have same : Term.i64.rename Nat.succ = .i64 := by cbv
  exact same ▸ weakened

end Jihoo.NativeKernel.Environment.LoanTyping.Examples
