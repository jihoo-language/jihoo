import Jihoo.NativeClosingTelescope

/-! Representation and owner-consuming result guards after the actual finite
dependent closing trace. These results do not assert full CODE substitution,
operational source refinement, or heap safety. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem SemanticSpine.realizes_closed
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : SemanticSpine env ctx term kind)
    (closing : RealizedInterpretation env ctx values) : Realizes env kind (term.subst values) := by
  induction source with
  | @var index kind found => simpa only [Term.subst] using closing.arguments index kind found
  | @app function erased result argument head typed ih =>
      have indexTyped : HasType env [] true (argument.subst values) .u64 := by
        simpa only [Term.subst,substArgs] using typed.ghostSubstitution history.wellFormed closing.typed
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using ih.index indexTyped

theorem Spine.realizes_closed_in_extension (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (source : Spine before ctx term kind) (closing : RealizedInterpretation after ctx values) :
    Realizes after kind (term.subst values) :=
  (source.semantic.extend extension).realizes_closed history closing

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.ContextModes
open CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem Resolved.unrestricted_not_owned_closed
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (resolved : Resolved before ctx false domain .unrestricted)
    (closing : RealizedInterpretation after ctx values) : ¬ Owned after (domain.subst values) := by
  cases resolved with
  | head normalized known =>
      obtain ⟨op,children,rfl,unowned⟩ := head_unrestricted known
      have converted := (Conversion.normalize?_sound normalized).extend extension
      have substituted := converted.substitution values history.wellFormed.closed
      intro owned
      exact (unowned.extend extension).not_owned history.wellFormed.admissible
        (by simpa only [Term.subst] using owned.congr substituted)
  | abstract normalized spine =>
      intro owned
      have represented := spine.realizes_closed_in_extension extension history closing
      exact represented.not_owned history
        (owned.congr (((Conversion.normalize?_sound normalized).extend extension).substitution
          values history.wellFormed.closed))

end Jihoo.NativeKernel.Environment.ContextModes

namespace Jihoo.NativeKernel.Environment.CallReplay
open CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem ResultShape.closed_nonFunction_realized
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (shape : ResultShape before ctx result) (closing : RealizedInterpretation after ctx values) :
    PiSeparated after (result.subst values) := by
  cases shape with
  | @rigid op children converted head =>
      have reduced := (converted.extend extension).substitution values history.wellFormed.closed
      have witnessed : nonFunction after (result.subst values) := by
        apply EnvironmentDelta.Basis.NonFunction.of_conversion reduced
        apply EnvironmentDelta.Basis.NonFunction.ofHead
        simpa only [Term.subst,EnvironmentDelta.Basis.nonFunctionHead] using head
      intro erased domain body pi
      exact witnessed.not_pi pi history.wellFormed.admissible
  | abstract converted spine =>
      have represented := (spine.realizes_closed_in_extension extension history closing).nonFunction history
      intro erased domain body pi
      exact represented erased domain body
        (.trans (.symm ((converted.extend extension).substitution values history.wellFormed.closed)) pi)

end Jihoo.NativeKernel.Environment.CallReplay

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- The consumed source telescope's actual final call result has a nonfunction
representation whenever the source guard has an authenticated result shape. -/
theorem Telescope.close_nonFunction
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (telescope : Telescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (trace : CanonicalSteps env actualSignature arguments entries actualResult)
    (sameSignature : Conversion.Conv env (signature.subst values) actualSignature)
    (arity : arguments.length = count)
    (shape : CallReplay.ResultShape env finalContext result) : PiSeparated env actualResult := by
  obtain ⟨closedValues,completed,converted⟩ := telescope.close history closing trace sameSignature arity
  have separated := shape.closed_nonFunction_realized (Extends.refl _) history completed
  intro erased domain body pi
  exact separated erased domain body (converted.symm.trans pi)

/-- Typed substitution for all source terms follows from the actually built
closing substitution; it is deliberately stated in ghost mode. -/
theorem Telescope.close_ghostSubstitution
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (telescope : Telescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (trace : CanonicalSteps env actualSignature arguments entries actualResult)
    (sameSignature : Conversion.Conv env (signature.subst values) actualSignature)
    (arity : arguments.length = count) :
    ∃ closedValues, RealizedInterpretation env finalContext closedValues ∧
      Conversion.Conv env actualResult (result.subst closedValues) ∧
      (∀ ghost term type, HasType env finalContext ghost term type →
        HasType env [] true (term.subst closedValues) (type.subst closedValues)) := by
  obtain ⟨closedValues,completed,converted⟩ := telescope.close history closing trace sameSignature arity
  exact ⟨closedValues,completed,converted,fun _ _ _ typed =>
    typed.ghostSubstitution history.wellFormed completed.typed⟩

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open CodeKinds CallReplay
open Jihoo.Quantity
variable {control : Control}
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem app_interpreted_result_closed
    (projected : projectRaw (fuel + 1) before ctx (.app function argument) = some control)
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (closing : RealizedInterpretation after ctx values) :
    ∃ head supplied entries result signature,
      NativeQuantity.splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      ContextFormed before ctx ∧ SignatureTrace after ctx false signature supplied entries result ∧
      HasType after ctx false (applications head supplied) result ∧
      (entries.any (ownsArgument before) = false ∨ PiSeparated after (result.subst values)) := by
  obtain ⟨head,supplied,entries,result,signature,split,formed,typed,steps,applied,guarded⟩ :=
    app_authenticated projected
  refine ⟨head,supplied,entries,result,signature,split,formed,
    steps.signatureTrace.extend extension,applied.extend extension,?_⟩
  rcases guarded with noOwner | represented
  · exact Or.inl noOwner
  · exact Or.inr (represented.closed_nonFunction_realized extension history closing)

end Jihoo.NativeKernel.Environment.ContextQuantity

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem Telescope.close_checkedCall_nonFunction
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (telescope : Telescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (classified : EntriesClassified env entries)
    (arity : arguments.length = count)
    (shape : CallReplay.ResultShape env finalContext result) : PiSeparated env actualResult := by
  obtain ⟨closedValues,completed,converted⟩ := telescope.close_checkedCall history closing sourceFunction checked classified arity
  have separated := shape.closed_nonFunction_realized (Extends.refl _) history completed
  intro erased domain body pi
  exact separated erased domain body (converted.symm.trans pi)

end Jihoo.NativeKernel.Environment.CodeKinds
