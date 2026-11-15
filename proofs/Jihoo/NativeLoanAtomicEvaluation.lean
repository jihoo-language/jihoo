import Jihoo.NativeLoanLendPreservation
import Jihoo.NativeLendRawTypedEndpoints

/-! A pure atomic evaluation relation with independently proved typing and
genuine raw computation paths. Its Lend rule performs the specialized finish
atomically; intermediate macro applications need not be typable. These are
ghost computations, not a heap or CODE substitution semantics. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.Atomic

inductive Root : Term → Term → Prop where
  | beta (erased : Bool) (domain body value : Term) :
      Root (.app (.lam erased domain body) value) (body.subst (single value))
  | lend (owner domain readerBody first again body : Term) :
      Root (.lend owner (.lam false domain readerBody) (.lam false first (.lam false again body)))
        (Lending.finish owner body (Lending.read owner readerBody))

theorem Root.forward (step : Root input output) : RawLend.Forward env input output := by
  cases step with
  | beta erased domain body value => exact .old (.acu (.compute (.beta erased domain body value)))
  | lend owner domain readerBody first again body =>
      exact RawLend.explicit_callbacks_forward owner domain readerBody first again body

theorem Root.preserves (wf : UnifiedProgram.EnvWellFormed env)
    (step : Root input output) (typed : HasType env loans ctx mode input type) :
    HasType env [] ctx true output type := by
  cases step with
  | beta => exact typed.ghostBeta wf
  | lend owner domain readerBody first again body =>
      exact typed.explicitLendFinish wf owner domain readerBody first again body rfl

inductive Steps : Term → Term → Prop where
  | refl : Steps term term
  | root : Root input output → Steps input output
  | trans : Steps input middle → Steps middle output → Steps input output

theorem Steps.forward (steps : Steps input output) : RawLend.Forward env input output := by
  induction steps with
  | refl => exact .refl
  | root step => exact step.forward
  | trans _ _ first second => exact first.trans second

theorem Steps.preserves (wf : UnifiedProgram.EnvWellFormed env)
    (steps : Steps input output) (typed : HasType env loans ctx mode input type) :
    HasType env [] ctx true output type := by
  induction steps generalizing loans mode with
  | refl => exact typed.ghost []
  | root step => exact step.preserves wf typed
  | trans _ _ first second => exact second (first typed)

theorem Steps.typed_forward (wf : UnifiedProgram.EnvWellFormed env)
    (steps : Steps input output) (typed : HasType env loans ctx mode input type) :
    RawLend.Forward env input output ∧ HasType env [] ctx true output type :=
  ⟨steps.forward, steps.preserves wf typed⟩

end Jihoo.NativeKernel.Environment.LoanTyping.Atomic
