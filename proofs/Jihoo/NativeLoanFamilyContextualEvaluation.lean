import Jihoo.NativeLoanFamilyIotaPreservation
import Jihoo.NativeLoanContextualEvaluation

/-! Actual family roots and specialized loan roots share one genuine Raw
conversion and the same safe contextual source evaluation relation. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyEvaluation

inductive Steps (env : Environment) : Term → Term → Prop where
  | pure : Evaluation.Steps input output → Steps env input output
  | iota : Environment.FamilyIota.Root env input output → Steps env input output
  | refl : Steps env term term
  | trans : Steps env input middle → Steps env middle output → Steps env input output
  | node (op : Op) : op ≠ .lend → NativeKernel.Conversion.ListRel (Steps env) xs ys →
      Steps env (.node op xs) (.node op ys)

private theorem transforms_forward
    (changes : NativeKernel.Conversion.ListRel (GhostTransform env) xs ys) :
    NativeKernel.Conversion.ListRel (RawLend.Forward env) xs ys := by
  induction changes with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.forward ih

theorem Steps.forward (steps : Steps env input output) : RawLend.Forward env input output := by
  induction steps using Steps.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (RawLend.Forward env) xs ys) with
  | pure step => exact step.forward
  | iota root => exact .old (.iota root)
  | refl => exact .refl
  | trans _ _ first second => exact first.trans second
  | node op _ _ ih => exact .node op ih
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

theorem Steps.ghost_transform
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (steps : Steps env input output) : GhostTransform env input output := by
  induction steps using Steps.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (GhostTransform env) xs ys) with
  | pure step => exact step.ghost_transform history.wellFormed
  | iota root =>
    exact ⟨.old (.iota root),raw_forward_lambda_shape (.old (.iota root)),
      fun typed => FamilyIota.Root.preserves history root typed⟩
  | refl => exact .refl _
  | trans _ _ first second => exact first.trans second
  | node op notLend children ih =>
    exact ⟨.node op (transforms_forward ih),raw_forward_lambda_shape (.node op (transforms_forward ih)),
      fun typed => children_preservation history.wellFormed typed op _ rfl notLend _ ih⟩
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

theorem Steps.preserves
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (steps : Steps env input output) (typed : HasType env loans ctx mode input type) :
    HasType env [] ctx true output type := (steps.ghost_transform history).typed typed

theorem Steps.typed_forward
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (steps : Steps env input output) (typed : HasType env loans ctx mode input type) :
    RawLend.Forward env input output ∧ HasType env [] ctx true output type :=
  ⟨steps.forward,steps.preserves history typed⟩

theorem contract_steps (accepted : Environment.FamilyIota.contract env term = some result) :
    Steps env term result := .iota (Environment.FamilyIota.contract_sound accepted)

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyEvaluation
