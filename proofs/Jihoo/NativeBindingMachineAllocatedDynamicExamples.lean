import Jihoo.NativeBindingMachineMixedLiteralRelease

/-! One authentic mixed declaration admission instantiates the general scalar
entry and dependent reader/release composition. The intermediate source checks,
contexts and pending frame are all derived; final execution is not computed. -/
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

def functionControl : Jihoo.Quantity.Control :=
  (LoanTyping.ResourceQuantity.project 256 .empty [] functionCode.context ownerFunction).getD .trap

def callControl : Jihoo.Quantity.Control :=
  (LoanTyping.ResourceQuantity.project 256 .empty [] entry.context callerBody).getD .trap

private theorem mixedAccepted : LoanTyping.MixedProgram.checkDeclaration 128 259 .empty
    ⟨signature,function⟩ = some
      ⟨ScalarCalls.signature,ScalarCalls.function
        (ScalarCalls.dynamicCall (.buffer (.var 2)) (.ref (.buffer (.var 3))) .i64 (.buffer (.var 4)) (.integer (-1)) 0)⟩ := by cbv

/-- Scalar and owner contexts, body resource receipts, the call frame and the
final actual value all come from the same mixed declaration admission. -/
theorem program_releases_and_returns : observe (run 48 (initial program)) = .integer 7 := by
  have result := ScalarCalls.admitted_literal_release (resourceFuel := 251)
    LoanTyping.MixedProgram.History.empty mixedAccepted
    (by decide : 2 < 2^64) (by decide : 1 < 2^64) (by decide : ValueReduction.signed64 7) (Or.inl rfl)
  have fits : 2*8+8 < 2^64 := by decide
  have ordered : 1 < 2 := by decide
  simp only [fits,ordered,↓reduceIte] at result
  exact result.2.2.1

end Jihoo.NativeKernel.Environment.BindingMachine.AllocatedDynamicExamples
