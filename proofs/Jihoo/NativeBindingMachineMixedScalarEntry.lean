import Jihoo.NativeBindingMachineCallDynamicRelease

/-! Recover all scalar-entry source/value/size/loan contexts and the actual
fifteen-step prefix from one authentic mixed declaration check. The body is
arbitrary original syntax; no intermediate typing/check or success is assumed. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.MixedProgram

theorem checkDeclaration_expanded_check
    (accepted : checkDeclaration fuel quantityFuel env source = some expanded) :
    checkExpanded fuel quantityFuel env expanded = true := by
  unfold checkDeclaration at accepted
  cases typeExpanded : GlobalEnvironment.expand fuel env.globals source.type with
  | none => simp [typeExpanded] at accepted
  | some type =>
      simp only [typeExpanded,Bind.bind,Option.bind] at accepted
      cases valueExpanded : GlobalEnvironment.expand fuel env.globals source.value with
      | none => simp [valueExpanded] at accepted
      | some value =>
          simp only [valueExpanded] at accepted
          split at accepted
          · rename_i checked
            cases accepted
            exact checked
          · contradiction

end Jihoo.NativeKernel.Environment.LoanTyping.MixedProgram

namespace Jihoo.NativeKernel.Environment.BindingMachine.ScalarCalls
open CodeKinds

def signature : Term := .pi false .u64 (.pi false .u64 (.pi false .i64 .i64))
def function (body : Term) : Term := .lam false .u64 (.lam false .u64 (.lam false .i64 body))
def program (body : Term) (count offset : Nat) (fill : Int) : Term :=
  .app (.app (.app (function body) (.natural count)) (.natural offset)) (.integer fill)
def first (body : Term) (count : Nat) : Code :=
  enter false .u64 (.lam false .u64 (.lam false .i64 body)) [] Term.var [] (.natural count) (some (.natural count))
def second (body : Term) (count offset : Nat) : Code :=
  enter false .u64 (.lam false .i64 body) (first body count).context (first body count).origins (first body count).values
    (.natural offset) (some (.natural offset))
def entry (body : Term) (count offset : Nat) (fill : Int) : Code :=
  enter false .i64 body (second body count offset).context (second body count offset).origins (second body count offset).values
    (.integer fill) (some (.integer fill))

private theorem sorted : LoanTyping.Checker.sort 128 env [] [] signature = some (.type 0) := by
  cbv

private theorem fifteen_steps (body : Term) (count offset : Nat) (fill : Int)
    (countBound : count < 2^64) (offsetBound : offset < 2^64) (fillBound : ValueReduction.signed64 fill) :
    run 15 (initial (program body count offset fill)) =
      ⟨⟨SizedBufferHeap.empty,.evaluate (entry body count offset fill),[]⟩,
        [.activate false (.lam false .u64 (.lam false .i64 body)) (.natural count),
          .activate false (.lam false .i64 body) (.natural offset),.activate false body (.integer fill)],15⟩ := by
  simp only [run,initial,program,function,step,action,evaluateAction,returnAction,applyValue,execute,
    Code.initial,Code.child,Code.origin,Term.subst_id,first,second,entry,enter,Option.map_some,countBound,offsetBound,fillBound,↓reduceIte]
  rfl

/-- Exact computational mode and resource receipt from the original mixed
checker, retaining its resource fuel rather than choosing a second query. -/
theorem admitted_function
    (accepted : LoanTyping.MixedProgram.checkDeclaration 128 quantityFuel env source =
      some ⟨signature,function body⟩) :
    LoanClosingTyped env [] false (.initial (function body)) Term.var signature ∧
    ∃ control, LoanTyping.ResourceQuantity.projectRaw quantityFuel env [] [] (function body) = some control := by
  have expanded := LoanTyping.MixedProgram.checkDeclaration_expanded_check accepted
  unfold LoanTyping.MixedProgram.checkExpanded at expanded
  split at expanded
  · rw [sorted] at expanded
    simp only [Definitions.bodyMode,Bool.false_or] at expanded
    obtain ⟨checked,resource⟩ := Bool.and_eq_true_iff.mp expanded
    refine ⟨.initial (LoanTyping.Checker.check_sound checked),?_⟩
    cases projected : LoanTyping.ResourceQuantity.project quantityFuel env [] [] (function body) with
    | none => simp [LoanTyping.ResourceQuantity.checkResource,projected] at resource
    | some control => exact ⟨control,LoanTyping.ResourceQuantity.project_origin projected⟩
  · contradiction

/-- All contexts and the original body receipt at the actual call boundary
come from one checked mixed declaration and the literal scalar arguments.
This lemma does not restrict the body syntax or change mixed admission. -/
theorem admitted_entry
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (accepted : LoanTyping.MixedProgram.checkDeclaration 128 (resourceFuel+8) env source =
      some ⟨signature,function body⟩)
    (countBound : count < 2^64) (offsetBound : offset < 2^64)
    (fillBound : ValueReduction.signed64 fill) :
    let code := entry body count offset fill
    (run 15 (initial (program body count offset fill))).state =
      ⟨SizedBufferHeap.empty,.evaluate code,[]⟩ ∧
    eventsHeap (run 15 (initial (program body count offset fill))).events = [] ∧
    LoanClosingTyped env [] false code code.origins .i64 ∧
    ValueContext env code code.origins ∧
    OwnerSizes env SizedBufferHeap.empty code code.origins ∧
    LoanSlots code [] [] ∧ Loans.Entered code.context.length [] ∧
    ∃ control, LoanTyping.ResourceQuantity.projectRaw (resourceFuel+5) env [] code.context body = some control := by
  obtain ⟨functionTyped,control,projected⟩ := admitted_function accepted
  have firstTyped : LoanClosingTyped env [] false (first body count) (first body count).origins
      (.pi false .u64 (.pi false .i64 .i64)) := by
    have result := enter_natural_closing history functionTyped countBound (.natural count)
    simpa only [signature,function,first,Code.initial,enter,Term.subst,substArgs,Op.binders,liftSub,single] using result
  have secondTyped : LoanClosingTyped env [] false (second body count offset) (second body count offset).origins
      (.pi false .i64 .i64) := by
    have result := enter_natural_closing history firstTyped offsetBound (.natural offset)
    simpa only [second,first,enter,Term.subst,substArgs,Op.binders,liftSub] using result
  have bodyTyped : LoanClosingTyped env [] false (entry body count offset fill) (entry body count offset fill).origins .i64 := by
    have result := enter_integer_closing history secondTyped fillBound (.integer fill)
    simpa only [entry,second,first,enter,Term.subst,substArgs,Op.binders,liftSub] using result
  have firstContext := (ValueContext.initial env (function body)).enter_natural history functionTyped countBound (.natural count)
  have secondContext := firstContext.enter_natural history firstTyped offsetBound (.natural offset)
  have bodyContext := secondContext.enter_integer history secondTyped fillBound (.integer fill)
  have firstSizes := (OwnerSizes.initial env SizedBufferHeap.empty (function body)).enter_natural
    .u64 (.lam false .u64 (.lam false .i64 body)) (.natural count) count
  have secondSizes := firstSizes.enter_natural .u64 (.lam false .i64 body) (.natural offset) offset
  have bodySizes := secondSizes.enter_integer .i64 body (.integer fill) fill
  obtain ⟨mode₁,control₁,projected₁,same₁⟩ := LoanTyping.ResourceQuantity.projectRaw_lambda_body projected
  obtain ⟨mode₂,control₂,projected₂,same₂⟩ := LoanTyping.ResourceQuantity.projectRaw_lambda_body projected₁
  obtain ⟨mode₃,control₃,projected₃,same₃⟩ := LoanTyping.ResourceQuantity.projectRaw_lambda_body projected₂
  have executed := fifteen_steps body count offset fill countBound offsetBound fillBound
  refine ⟨congrArg (fun result => result.state) executed,?_,bodyTyped,bodyContext,bodySizes,?_,?_,control₃,projected₃⟩
  · rw [executed]
    rfl
  · intro index active
    cases active
  · intro frame member
    cases member

end Jihoo.NativeKernel.Environment.BindingMachine.ScalarCalls
