import Jihoo.NativeBindingMachineReturnedBufferCompletion

/-! A closed accepted application of the general returned-Buffer completion
theorem. Entry typing/resource projection and the actual fourteen-step caller
prefix are checked here; scalar return uses the general thirty-two-step proof.
This is a concrete application, not the missing general admission theorem. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.ReturnedBufferCompletionExamples
open CodeKinds
def buffer : Term := .buffer (.natural 2)
def oldAllocation : Term := .alloc (.natural 2) (.integer (-3))
def allocation : Term := .alloc (.natural 2) (.integer 7)
def body : Term := returnedBufferRead (.ref buffer) 1 2 .i64 buffer returnedReadRelease
def continuation : Term := .lam false buffer (.lam false buffer body)
def source : Term := .lend (.var 0) (.lam false (.ref buffer) allocation) continuation
def program : Term := .app (.lam false buffer source) oldAllocation
def entry : Code := enter false buffer source [] Term.var [] oldAllocation (some (.owner 0))
theorem program_admitted : LoanTyping.ResourceQuantity.checkClosed 128 256 .empty program .i64 = true := by cbv
private theorem entryTyped : LoanSourceTyped .empty [] false entry .i64 := by
  have emptySub : LoanTyping.Ghost.Substitution .empty [] [] Term.var := by
    intro index binding selected
    cases selected
  have oldTyped : LoanTyping.HasType .empty [] [] true oldAllocation buffer :=
    .alloc (.natural (by decide)) (.integer (by decide) (by decide))
  have domainTyped : LoanTyping.HasType .empty [] [] true oldAllocation (buffer.subst Term.var) := by
    simpa only [Term.subst_id] using oldTyped
  refine ⟨emptySub.consValues (erased := false) domainTyped,.i64,?_,?_⟩
  · exact LoanTyping.Checker.check_sound (show LoanTyping.Checker.check 128 .empty [] entry.context false entry.term .i64 = true by cbv)
  · simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv .empty .i64 .i64 from .refl _)
def resourceControl : Jihoo.Quantity.Control :=
  (LoanTyping.ResourceQuantity.project 256 .empty [] entry.context entry.term).getD .trap
private theorem projected : LoanTyping.ResourceQuantity.project 256 .empty [] entry.context entry.term = some resourceControl := by cbv
private theorem reached : (run 14 (initial program)).state.control = .evaluate
    (enter false (.ref buffer) allocation entry.context entry.origins entry.values
      (.borrow ((Term.var 0).subst entry.origins)) (some (.reference 0))) := by cbv
private theorem saved : (run 14 (initial program)).state.stack =
    [.lendFinish 0 0 (some 1) ((Term.var 0).subst entry.origins)
      (enter false (.ref buffer) allocation entry.context entry.origins entry.values
        (.borrow ((Term.var 0).subst entry.origins)) (some (.reference 0))).origin
      (entry.child continuation)] := by cbv
theorem program_completes : observe (run 46 (initial program)) = .integer 7 := by
  have result := reachable_returned_buffer_completion (owner := 0) (object := 0) (token := 0)
    (name := some 1) (stack := []) (resourceFuel := 255) program 14 entry .empty entryTyped rfl projected reached saved
  have fits : 2*8+8 < 2^64 := by decide
  simp only [fits,↓reduceIte] at result
  obtain ⟨typed,guard,executed⟩ := result
  have absent : ¬ ObjectReader 0 [] := by
    rintro ⟨frame,member,token,name,descriptor⟩
    cases member
  have guarded := guard.mpr absent
  simp only [guarded,↓reduceIte] at executed
  have composed := run_add 14 32 (initial program)
  dsimp only at composed
  rw [executed] at composed
  simpa only [observe] using congrArg observe composed
end Jihoo.NativeKernel.Environment.BindingMachine.ReturnedBufferCompletionExamples
