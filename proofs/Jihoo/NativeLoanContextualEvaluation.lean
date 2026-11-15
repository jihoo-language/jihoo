import Jihoo.NativeLoanContextualPreservation
import Jihoo.NativeLoanGenericDesugar

/-! Genuine typed contextual evaluation: specialized Lend contracts before its
untyped source callbacks are traversed. Other nodes have full child closure,
including binder annotations and dependent indices. No output typing premise
or reverse-typing/confluence assumption enters the preservation endpoint. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

 theorem raw_forward_lambda_shape (step : RawLend.Forward env input output) :
    LambdaShape env input output := by
  fun_cases LambdaShape env input output
  · rename_i erased domain body
    obtain ⟨ys,shape,kids⟩ := step.rigid_shape rfl rfl
    cases kids with
    | cons domainStep rest => cases rest with
      | cons bodyStep rest =>
        cases rest
        exact ⟨_,_,shape,domainStep.toConv,raw_forward_lambda_shape bodyStep⟩
  · trivial
termination_by sizeOf input

namespace Evaluation

inductive Steps : Term → Term → Prop where
  | atomic : Atomic.Root input output → Steps input output
  | generic (owner reader continuation : Term) : explicitCallbacks reader continuation = false →
      Steps (.lend owner reader continuation) (RawLend.desugar owner reader continuation)
  | refl : Steps term term
  | trans : Steps input middle → Steps middle output → Steps input output
  | node (op : Op) : op ≠ .lend → NativeKernel.Conversion.ListRel Steps xs ys →
      Steps (.node op xs) (.node op ys)

theorem Steps.forward (steps : Steps input output) : RawLend.Forward env input output := by
  induction steps using Steps.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (RawLend.Forward env) xs ys) with
  | atomic step => exact step.forward
  | generic owner reader continuation _ => exact .lend owner reader continuation
  | refl => exact .refl
  | trans _ _ first second => exact first.trans second
  | node op _ _ ih => exact .node op ih
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

private theorem transforms_forward
    (changes : NativeKernel.Conversion.ListRel (GhostTransform env) xs ys) :
    NativeKernel.Conversion.ListRel (RawLend.Forward env) xs ys := by
  induction changes with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.forward ih

theorem Steps.ghost_transform (wf : UnifiedProgram.EnvWellFormed env)
    (steps : Steps input output) : GhostTransform env input output := by
  induction steps using Steps.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (GhostTransform env) xs ys) with
  | atomic step =>
    exact ⟨step.forward,raw_forward_lambda_shape step.forward,fun typed => step.preserves wf typed⟩
  | generic owner reader continuation nonexplicit =>
    exact ⟨.lend owner reader continuation,raw_forward_lambda_shape (.lend owner reader continuation),
      fun typed => typed.nonexplicitLendDesugar nonexplicit⟩
  | refl => exact .refl _
  | trans _ _ first second => exact first.trans second
  | node op notLend children ih =>
    exact ⟨.node op (transforms_forward ih),raw_forward_lambda_shape (.node op (transforms_forward ih)),
      fun typed => children_preservation wf typed op _ rfl notLend _ ih⟩
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

 theorem Steps.preserves (wf : UnifiedProgram.EnvWellFormed env)
    (steps : Steps input output) (typed : HasType env loans ctx mode input type) :
    HasType env [] ctx true output type := (steps.ghost_transform wf).typed typed

 theorem Steps.typed_forward (wf : UnifiedProgram.EnvWellFormed env)
    (steps : Steps input output) (typed : HasType env loans ctx mode input type) :
    RawLend.Forward env input output ∧ HasType env [] ctx true output type :=
  ⟨steps.forward,steps.preserves wf typed⟩

end Evaluation
end Jihoo.NativeKernel.Environment.LoanTyping
