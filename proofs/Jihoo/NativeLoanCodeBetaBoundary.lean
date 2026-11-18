import Jihoo.NativeBindingMachineAliasReborrowBoundary
import Jihoo.NativeLoanAtomicEvaluation
import Jihoo.NativeLoanCodeRenaming

/-! Raw substitution can replace the named owner needed by Loan64's CODE
borrowing rule. The typed source machine instead retains the owner binding. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def IndexReceiver (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (mode : Bool) : Term → Prop
  | .index receiver _ _ => ∃ type, HasType env loans ctx mode receiver type
  | _ => True

/-- Both array and borrowed-buffer indexing type the actual receiver in the
same mode and loan context, even under arbitrary result conversion. -/
theorem HasType.index_receiver (typed : HasType env loans ctx mode (.index receiver offset evidence) type) :
    ∃ receiverType, HasType env loans ctx mode receiver receiverType := by
  suffices view : ∀ {term type}, HasType env loans ctx mode term type →
      IndexReceiver env loans ctx mode term from view typed
  intro term type typed
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun loans ctx mode term _ _ => IndexReceiver env loans ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case index => exact ⟨_,by assumption⟩
  case borrowedIndex => exact ⟨_,by assumption⟩
  case dataElim => split <;> trivial

namespace CodeBetaBoundary

def allocated : Term := .alloc (.natural 1) (.integer 7)

def reader (owner : Term) : Term :=
  .lam false (.ref BindingMachine.AliasReborrowBoundary.buffer)
    (.index (.borrow owner) (.natural 0) (.decide (.natural 0) (.natural 1)))

def body : Term := .lend (.var 0) (reader (.var 1)) BindingMachine.AliasReborrowBoundary.release

def source : Term :=
  .app (.lam false BindingMachine.AliasReborrowBoundary.buffer body) allocated

def rawBeta : Term :=
  .lend allocated (reader allocated) BindingMachine.AliasReborrowBoundary.release

theorem source_admitted : MixedProgram.checkDeclaration 256 512 .empty
    ⟨.i64,source⟩ = some ⟨.i64,source⟩ := by cbv

/-- No CODE type can be assigned to the raw reduct. Generic Lend would need a
CODE derivation for its reader, which tries to borrow a nonvariable owner. -/
theorem raw_beta_code_untypable : ¬ HasType env loans ctx false rawBeta type := by
  intro typed
  obtain ⟨_,origin,_⟩ := typed.lendView
  cases origin with
  | generic _ _ _ readerTyped _ _ =>
      obtain ⟨_,_,_,readerBody,_⟩ := readerTyped.lamView
      obtain ⟨_,borrowed⟩ := readerBody.index_receiver
      obtain ⟨_,named,_⟩ := borrowed.code_borrow_named
      cases named

/-- Actual Loan64 typing and a genuine beta root give a counterexample to
unconditional original-type CODE preservation by raw beta. -/
theorem raw_beta_counterexample :
    HasType .empty [] [] false source .i64 ∧
    Atomic.Root source rawBeta ∧ ¬ HasType .empty [] [] false rawBeta .i64 := by
  refine ⟨Checker.check_sound (fuel := 256) (by cbv),?_,raw_beta_code_untypable⟩
  have contracted : body.subst (single allocated) = rawBeta := by cbv
  rw [← contracted]
  exact .beta false BindingMachine.AliasReborrowBoundary.buffer body allocated

/-- The same admitted source executes through a retained owner binding and
then performs the authorized read, loan close and release. -/
theorem retained_beta_execution :
    BindingMachine.observe (BindingMachine.run 100 (BindingMachine.initial source)) = .integer 7 ∧
    BindingMachine.eventsHeap (BindingMachine.run 100 (BindingMachine.initial source)).events =
      [.alloc 0 1 (BindingMachine.encodeInteger 7),.beginLease 0 0,
        .read 0 0 (BindingMachine.encodeInteger 7),.close 0,.free 0] := by cbv; exact ⟨rfl,trivial⟩

-- A variable argument allows beta while preserving an enclosing loan. The
-- reader sees its named owner at index 2 before beta and at index 1 afterward.
private def outerContext : Context :=
  [⟨.u64,false⟩,⟨BindingMachine.AliasReborrowBoundary.buffer,false⟩]

private def outerLoans : Loans.Stack := Loans.enter outerContext.length 1 []

private def readOuter (owner : Nat) : Term :=
  .index (.borrow (.var owner)) (.natural 0) (.decide (.natural 0) (.natural 1))

example : HasType .empty outerLoans outerContext false (readOuter 1) .i64 := by
  have admitted : Checker.check 256 .empty outerLoans outerContext false
      (.app (.lam false .u64 (readOuter 2)) (.var 0)) .i64 = true := by cbv
  have entered : Loans.Entered outerContext.length outerLoans :=
    Loans.entered_enter (by simp [Loans.Entered])
  have selected : lookup outerContext 0 = some ⟨.u64,false⟩ := by cbv
  have contracted : (readOuter 2).subst (single (.var 0)) = readOuter 1 := by cbv
  rw [← contracted]
  exact (Checker.check_sound admitted).codeVariableBeta UnifiedProgram.EnvWellFormed.empty entered selected

end CodeBetaBoundary
end Jihoo.NativeKernel.Environment.LoanTyping
