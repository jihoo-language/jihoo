import Jihoo.NativeBindingMachineAllocatedDynamicRelease

/-! A closed full-checker/resource admission instantiates the general thirty-
step theorem. Only the caller prefix is computed; the read/release/result follow
from the semantic theorem and constructed scalar/owner contexts. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.AllocatedDynamicExamples
open CodeKinds

def body : Term := allocatedDynamicBody (.ref (.buffer (.var 3))) .i64 (.buffer (.var 4)) (.integer (-1)) 2 3 0
def ownerFunction : Term := .lam false (.buffer (.var 2)) body
def allocation : Term := .alloc (.var 2) (.var 0)
def callerBody : Term := .app ownerFunction allocation
def function : Term := .lam false .u64 (.lam false .u64 (.lam false .i64 callerBody))
def signature : Term := .pi false .u64 (.pi false .u64 (.pi false .i64 .i64))
def program : Term := .app (.app (.app function (.natural 2)) (.natural 1)) (.integer 7)

def firstEntry : Code := enter false .u64 (.lam false .u64 (.lam false .i64 callerBody)) [] Term.var [] (.natural 2) (some (.natural 2))
def secondEntry : Code := enter false .u64 (.lam false .i64 callerBody) firstEntry.context firstEntry.origins firstEntry.values
  (.natural 1) (some (.natural 1))
def entry : Code := enter false .i64 callerBody secondEntry.context secondEntry.origins secondEntry.values
  (.integer 7) (some (.integer 7))
def functionCode : Code := entry.child ownerFunction
def allocationCode : Code := entry.child allocation

theorem program_admitted : LoanTyping.ResourceQuantity.checkClosed 128 256 .empty program .i64 = true := by cbv

private theorem functionTyped : LoanClosingTyped .empty [] false (.initial function) Term.var signature :=
  .initial (LoanTyping.Checker.check_sound
    (show LoanTyping.Checker.check 128 .empty [] [] false function signature = true by cbv))

private theorem secondTyped : LoanClosingTyped .empty [] false firstEntry firstEntry.origins
    (.pi false .u64 (.pi false .i64 .i64)) := by
  have first := enter_natural_closing LoanTyping.MixedProgram.History.empty functionTyped (by decide : 2 < 2^64) (.natural 2)
  simpa only [signature,function,firstEntry,Code.initial,enter,Term.subst,substArgs,Op.binders,liftSub,single] using first

private theorem thirdTyped : LoanClosingTyped .empty [] false secondEntry secondEntry.origins (.pi false .i64 .i64) := by
  have second := enter_natural_closing LoanTyping.MixedProgram.History.empty secondTyped (by decide : 1 < 2^64) (.natural 1)
  simpa only [secondEntry,firstEntry,enter,Term.subst,substArgs,Op.binders,liftSub] using second

private theorem entryContext : ValueContext .empty entry entry.origins := by
  have first := (ValueContext.initial .empty function).enter_natural LoanTyping.MixedProgram.History.empty
    functionTyped (by decide : 2 < 2^64) (.natural 2)
  have second := first.enter_natural LoanTyping.MixedProgram.History.empty secondTyped (by decide : 1 < 2^64) (.natural 1)
  have third := second.enter_integer LoanTyping.MixedProgram.History.empty thirdTyped
    (by decide : ValueReduction.signed64 7) (.integer 7)
  exact third

private theorem entrySizes (heap : SizedBufferHeap.State) : OwnerSizes .empty heap entry entry.origins := by
  have first := (OwnerSizes.initial .empty heap function).enter_natural .u64 (.lam false .u64 (.lam false .i64 callerBody)) (.natural 2) 2
  have second := first.enter_natural .u64 (.lam false .i64 callerBody) (.natural 1) 1
  exact second.enter_integer .i64 callerBody (.integer 7) 7

private theorem allocationTyped : LoanClosingTyped .empty [] false allocationCode entry.origins (.buffer (.natural 2)) := by
  refine ⟨entryContext.closing,.buffer (.var 2),?_,?_⟩
  · exact LoanTyping.Checker.check_sound
      (show LoanTyping.Checker.check 64 .empty [] allocationCode.context false allocationCode.term (.buffer (.var 2)) = true by cbv)
  · simpa only [entry,secondEntry,firstEntry,enter,Term.subst,substArgs,Op.binders,liftSub,consValues] using
      (show LoanTyping.Conversion.Conv .empty (.buffer (.natural 2)) (.buffer (.natural 2)) from .refl _)

private theorem ownerFunctionTyped : LoanClosingTyped .empty [] false functionCode entry.origins
    (.pi false (.buffer (.natural 2)) .i64) := by
  refine ⟨entryContext.closing,.pi false (.buffer (.var 2)) .i64,?_,?_⟩
  · exact LoanTyping.Checker.check_sound
      (show LoanTyping.Checker.check 128 .empty [] functionCode.context false functionCode.term
        (.pi false (.buffer (.var 2)) .i64) = true by cbv)
  · simpa only [entry,secondEntry,firstEntry,enter,Term.subst,substArgs,Op.binders,liftSub,consValues] using
      (show LoanTyping.Conversion.Conv .empty (.pi false (.buffer (.natural 2)) .i64)
        (.pi false (.buffer (.natural 2)) .i64) from .refl _)

def functionControl : Jihoo.Quantity.Control :=
  (LoanTyping.ResourceQuantity.project 256 .empty [] functionCode.context ownerFunction).getD .trap
private theorem projected : LoanTyping.ResourceQuantity.project 256 .empty [] functionCode.context ownerFunction = some functionControl := by cbv
private theorem reached : (run 18 (initial program)).state.control = .evaluate allocationCode := by cbv
private theorem saved : (run 18 (initial program)).state.stack =
    [.argument (.closure false (.buffer (.var 2)) body functionCode.context functionCode.origins functionCode.values)
      allocationCode.origin] := by cbv

/-- The final value comes from the general actual allocation/read/release
proof, rather than an output or execution-success certificate. -/
theorem program_releases_and_returns : observe (run 48 (initial program)) = .integer 7 := by
  have slots : LoanSlots functionCode [] [] := by
    intro index active
    cases active
  have entered : Loans.Entered functionCode.context.length [] := by intro frame member; cases member
  have result := reachable_allocated_dynamic_release (resourceFuel := 251)
    (readerDomain := .ref (.buffer (.var 3))) (first := .i64) (again := .buffer (.var 4)) (no := .integer (-1))
    (index := 2) (length := 3) (releaseIndex := 0) (argumentOrigin := allocationCode.origin)
    program 18 .empty reached allocationTyped (entryContext.child allocation) rfl ownerFunctionTyped
    (entryContext.child ownerFunction) ((entrySizes _).child ownerFunction) slots entered projected (Or.inl rfl) saved
  obtain ⟨count,fill,countMeaning,fillMeaning,result⟩ := result
  have countSame : count = 2 := by cases countMeaning; rfl
  have fillSame : fill = 7 := by cases fillMeaning; rfl
  subst count
  subst fill
  have fits : 2*8+8 < 2^64 := by decide
  simp only [fits,↓reduceIte] at result
  obtain ⟨offset,indexMeaning,lengthMeaning,result⟩ := result
  have indexSame : offset = 1 := by cases indexMeaning; rfl
  subst offset
  have ordered : 1 < 2 := by decide
  simp only [ordered,↓reduceIte] at result
  obtain ⟨typed,dead,valid,inventory,executed⟩ := result
  have composed := run_add 18 30 (initial program)
  dsimp only at composed
  rw [executed] at composed
  simpa only [observe] using congrArg observe composed

end Jihoo.NativeKernel.Environment.BindingMachine.AllocatedDynamicExamples
