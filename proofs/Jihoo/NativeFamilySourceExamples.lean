import Jihoo.NativeFamilyClosure
set_option maxUniverseOffset 40

/-! Actual native higher-kinded binders and independently interpreted families.
The signature ranges over every input/result level below32. -/
namespace Jihoo.NativeKernel.Environment.Semantics.FamilyCodes.Examples
open Jihoo.NativeKernel.Environment.Conversion

def levels (signature : Signature) : Fin 1 → Fin 32 := fun _ => signature.input
def signatures (signature : Signature) : Fin 1 → Signature := fun _ => signature

def fiber : TypeCode 1 1 := .application ⟨0,by decide⟩ (.parameter ⟨0,by decide⟩)

theorem fiber_valid (signature : Signature) : fiber.Valid (levels signature) (signatures signature) := ⟨trivial,rfl⟩

def identityExpression (signature : Signature) :
    Expression (levels signature) (signatures signature) [] (.arrow fiber fiber) :=
  .lam (fiber_valid signature) (.var .here (fiber_valid signature))

def identity (signature : Signature) : Term := .lam false signature.term
  (.lam false (.univ signature.input.val) (identityExpression signature).syntax)

def identityType (signature : Signature) : Term := .pi false signature.term
  (.pi false (.univ signature.input.val) ((TypeCode.arrow fiber fiber).syntax 0))

theorem identity_source (signature : Signature) : identity signature =
    .lam false signature.term (.lam false (.univ signature.input.val)
      (.lam false (.app (.var 1) (.var 0)) (.var 0))) := by
  simp [identity,identityExpression,Expression.syntax,fiber,TypeCode.syntax,TypeCode.instantiate]

theorem identity_typed (signature : Signature) : HasType env [] true (identity signature) (identityType signature) := by
  refine .lam (.intro (s := .type (max (signature.input.val+1) (signature.result.val+1))) signature.formed
    (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ?_
  refine .lam (.intro (s := .type (signature.input.val+1)) (.univ signature.input.isLt)
    (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ?_
  have typed := (identityExpression signature).typed (env := env)
  simpa [context,baseContext,levels,signatures,List.ofFn_succ] using typed

theorem identity_recognized (signature : Signature) :
    Recognized (levels signature) (signatures signature) 0 (identityExpression signature).syntax :=
  .lam fiber (fiber_valid signature) (.var (by decide))

theorem identity_body_fundamental (wf : UnifiedProgram.EnvWellFormed env) (signature : Signature) :
    ∃ A, ∃ expression : Expression (levels signature) (signatures signature) [] A,
      expression.syntax = (identityExpression signature).syntax ∧
      Conv env (A.syntax 0) ((TypeCode.arrow fiber fiber).syntax 0) ∧
      ∀ assignment : Assignment (levels signature) (signatures signature),
        Nonempty (Finite.Carrier (A.meaning assignment expression.valid)) :=
  closed_context_model wf (identityExpression signature).typed (identity_recognized signature)

private theorem singleton_get (value : α) : List.get [value] = (fun _ : Fin 1 => value) := by
  funext ⟨index,bound⟩
  have same : index = 0 := by simp only [List.length_cons,List.length_nil] at bound; omega
  subst index
  simp

private theorem fiber_list_valid (signature : Signature) : fiber.Valid [signature.input].get [signature].get := by
  simp [fiber,TypeCode.Valid,TypeCode.level,singleton_get]

def identityScheme (signature : Signature) : Scheme [] [] :=
  .family signature (.parameter signature.input (.body
    (.lam (fiber_list_valid signature)
      (.var .here (fiber_list_valid signature)))))

theorem identityScheme_source (signature : Signature) : (identityScheme signature).syntax = identity signature := by
  simp only [identityScheme,Scheme.syntax,identity,identityExpression,Expression.syntax]

theorem identity_closed_recognized (signature : Signature) : UniverseRecognized [] [] (identity signature) := by
  exact .family signature (.parameter signature.input (.body
    (.lam fiber (fiber_list_valid signature) (.var (by decide)))))

theorem identity_closed_fundamental (wf : UnifiedProgram.EnvWellFormed env) (signature : Signature) :
    ∃ scheme : Scheme [] [], scheme.syntax = identity signature ∧ Conv env scheme.type (identityType signature) ∧
      ∀ assignment : Assignment (List.get ([] : List (Fin 32))) (List.get ([] : List Signature)),
        Nonempty (Finite.Carrier (scheme.code assignment)) :=
  universe_fundamental wf (identity_typed signature) (identity_closed_recognized signature)

end Jihoo.NativeKernel.Environment.Semantics.FamilyCodes.Examples
