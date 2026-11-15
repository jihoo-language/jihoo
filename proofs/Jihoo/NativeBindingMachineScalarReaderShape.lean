import Jihoo.NativeBindingMachineLendValues

/-! Syntactic scalar-result cases for local reader handoff. This auxiliary
classification does not change the complete source grammar or the whole-kernel
completion obligations. No result-typing premise is supplied by callers. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

inductive ScalarReadShape : Term → Prop where
  | index : ScalarReadShape (.index reference offset evidence)
  | ifLt : ScalarReadShape (.ifLt left right (.index reference offset evidence) no)

theorem ScalarReadShape.substitution (shape : ScalarReadShape term) (values : Nat → Term) :
    ScalarReadShape (term.subst values) := by
  cases shape with
  | @index reference offset evidence =>
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        (show ScalarReadShape (.index (reference.subst values) (offset.subst values) (evidence.subst values)) from .index)
  | @ifLt left right reference offset evidence no =>
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        (show ScalarReadShape (.ifLt (left.subst values) (right.subst values)
          (.index (reference.subst (liftSubOne values)) (offset.subst (liftSubOne values))
            (evidence.subst (liftSubOne values))) (no.subst values)) from .ifLt)

theorem ScalarReadShape.read (shape : ScalarReadShape body) (owner : Term) :
    ScalarReadShape (Lending.read owner body) := shape.substitution (single (.borrow owner))

theorem ScalarReadShape.result_conversion (shape : ScalarReadShape term)
    (wf : UnifiedProgram.EnvWellFormed env) (typed : HasType env loans ctx mode term type) :
    Conversion.Conv env .i64 type := by
  cases shape with
  | index => exact typed.principalView
  | ifLt => exact typed.ifLt_index_result wf

/-- An actual bounded scalar can instantiate the checked read and restore,
including guarded readers. Specialized cases never assume a generic callback. -/
theorem actual_scalar_shape_finish
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env [] [] true
      (.lend owner (.lam false domain readerBody) (.lam false first (.lam false again body))) type)
    (shape : ScalarReadShape readerBody) (bounded : ValueReduction.signed64 value) :
    HasType env [] [] true (Lending.finish owner body (.integer value)) type := by
  obtain ⟨principal,origin,converted⟩ := typed.lendView
  have actual : HasType env [] [] true (.integer value) .i64 := .integer bounded.1 bounded.2
  cases origin with
  | generic ownerTyped owned outlived readerTyped continuationTyped allowed =>
      have readTyped := reader_from_generic_checks wf ownerTyped owned readerTyped
      have readConverted := (shape.read owner).result_conversion wf readTyped
      exact (continuation_from_generic_checks wf ownerTyped (actual.convert readConverted) continuationTyped).convert converted
  | dependentGhost ownerTyped owned domainTyped domainConverted readerTyped outlived firstConverted againConverted continuationTyped resultConverted removed =>
      have readConverted := (shape.read owner).result_conversion wf readerTyped
      have finished := finish_from_specialized_checks wf continuationTyped
        (actual.convert (readConverted.trans firstConverted.symm))
      exact (finished.convert (result_outside wf resultConverted removed)).convert converted

end Jihoo.NativeKernel.Environment.LoanTyping
