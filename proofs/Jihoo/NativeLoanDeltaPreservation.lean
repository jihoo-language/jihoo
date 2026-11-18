import Jihoo.NativeLoanEnvironmentExtension
import Jihoo.NativeLoanComputationPreservation

/-! Transparent globals unfold to the actual declaration checked in the
earlier mixed history. Loan64 environment extension transports that original
derivation before closed renaming and contextual preservation. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

/-- Every stored global retains its actual formation and body typing in the
current mixed environment, at the sort-derived original body mode. -/
theorem MixedProgram.History.global_typing
    (history : MixedProgram.History definitions declarations env)
    {index : Nat} {declaration : GlobalDeclaration}
    (found : env.globals[index]? = some declaration) :
    ∃ sort : SortTag, HasType env [] [] true declaration.type sort.term ∧
      HasType env [] [] (Definitions.bodyMode sort) declaration.value declaration.type := by
  obtain ⟨_,_,_,_,_,_,checked,extension⟩ := history.global_prefix found
  obtain ⟨sort,formed,body,_⟩ := checked.valid.typing
  exact ⟨sort,formed.extend extension,body.extend extension⟩

/-- The authentic delta root preserves the exact requested original type,
including under an arbitrary local context and a converted global type. -/
theorem MixedProgram.History.delta_preserves
    (history : MixedProgram.History definitions declarations env)
    {index : Nat} {declaration : GlobalDeclaration}
    (found : env.globals[index]? = some declaration)
    (typed : HasType env loans ctx mode (.node (.global index) []) type) :
    HasType env [] ctx true declaration.value type := by
  obtain ⟨selected,selectedFound,converted⟩ := typed.principalView
  have same : selected = declaration := Option.some.inj (selectedFound.symm.trans found)
  subst selected
  obtain ⟨_,_,bodyTyped⟩ := history.global_typing found
  have weakening : Ghost.Renaming [] ctx id := by
    intro index binding selected
    cases selected
  have recontextualized := bodyTyped.ghostRenaming history.wellFormed weakening
  simp only [Term.rename_id] at recontextualized
  rw [Environment.closed_rename (history.wellFormed.globals index declaration found).1] at converted
  exact recontextualized.convert converted

namespace DeltaEvaluation

/-- Delta composes with the proved computation, arithmetic, Lend and family
rules in either order beneath the existing ordinary-node context boundary. -/
inductive Steps (env : Environment) : Term → Term → Prop where
  | computation : ComputationEvaluation.Steps env input output → Steps env input output
  | delta : env.globals[index]? = some declaration → Steps env (.node (.global index) []) declaration.value
  | trans : Steps env input middle → Steps env middle output → Steps env input output
  | node (op : Op) : op ≠ .lend → NativeKernel.Conversion.ListRel (Steps env) xs ys →
      Steps env (.node op xs) (.node op ys)

private theorem transforms_forward
    (changes : NativeKernel.Conversion.ListRel (GhostTransform env) xs ys) :
    NativeKernel.Conversion.ListRel (RawLend.Forward env) xs ys := by
  induction changes with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.forward ih

theorem Steps.ghost_transform
    (history : MixedProgram.History definitions declarations env)
    (steps : Steps env input output) : GhostTransform env input output := by
  induction steps using Steps.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (GhostTransform env) xs ys) with
  | computation step => exact step.ghost_transform (ScopedProgram.History.ofLoanMixed history)
  | delta found =>
      have forward := RawLend.Forward.old (.old (.delta found))
      exact ⟨forward,raw_forward_lambda_shape forward,history.delta_preserves found⟩
  | trans _ _ first second => exact first.trans second
  | node op notLend _ ih =>
      have forward := RawLend.Forward.node op (transforms_forward ih)
      exact ⟨forward,raw_forward_lambda_shape forward,
        fun typed => children_preservation history.wellFormed typed op _ rfl notLend _ ih⟩
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

end DeltaEvaluation

/-- A complete mixed history suffices for original-type preservation along
the typed contextual evaluator, including honest global delta steps. -/
theorem MixedProgram.History.delta_computation_preservation
    (history : MixedProgram.History definitions declarations env)
    (steps : DeltaEvaluation.Steps env input output)
    (typed : HasType env loans ctx mode input type) :
    RawLend.Forward env input output ∧ HasType env [] ctx true output type := by
  have transformed := steps.ghost_transform history
  exact ⟨transformed.forward,transformed.typed typed⟩

end Jihoo.NativeKernel.Environment.LoanTyping
