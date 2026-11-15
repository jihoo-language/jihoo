import Jihoo.NativeEvaluatedClosing

/-! The same source projector's binder modes retain their actual head/metadata
certificates or semantic nonownership after dependent value computation.
This preserves source control descriptors, not native heap or loan lifetimes. -/
namespace Jihoo.NativeKernel.Environment.ContextModes
open CodeKinds Jihoo.Quantity
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}
variable {erased : Bool}

/-- Positive modes retain the exact computed head and its environment metadata.
Abstract unrestricted types instead retain their proved ownership separation. -/
inductive ModeContract (env : Environment) (domain : Term) : BinderMode → Prop where
  | erased : ModeContract env domain .erased
  | known : Conversion.Conv env domain normal → head env normal = some mode → ModeContract env domain mode
  | abstract : (¬ Owned env domain) →
      (∀ owner, ¬ Conversion.Conv env domain (.ref owner)) →
      (∀ erased owner motive, ¬ Conversion.Conv env domain (.back erased owner motive)) →
      ModeContract env domain .unrestricted

/-- Substitution can expose new heads at unknown variables, but every already
computed source head retains its actual mode and exact family metadata. -/
theorem head_substitution (accepted : head env term = some mode) (values : Nat → Term) :
    head env (term.subst values) = some mode := by
  cases term with
  | var index => simp [head,NativeQuantity.binderMode] at accepted
  | node op children =>
      cases op <;> simp_all [head,NativeQuantity.binderMode,Term.subst]
      all_goals
        cases children with
        | nil => simp_all [substArgs]
        | cons first rest =>
            cases rest with
            | nil => simp_all [substArgs]
            | cons second tail =>
                cases tail <;> simp_all [substArgs]

theorem head_extend (extension : Extends before after) (accepted : head before term = some mode) :
    head after term = some mode := by
  cases term with
  | var index => simp [head,NativeQuantity.binderMode] at accepted
  | node op children =>
      cases op <;> first | exact accepted | skip
      case «universe» level =>
        cases children <;> exact accepted
      case ind family count =>
        obtain ⟨entry,found,same⟩ := Option.map_eq_some_iff.mp accepted
        simp only [head,extension.families _ _ found,Option.map_some]
        exact congrArg some same

/-- No precomputed ownership flag is supplied: Resolved itself came from the
same real binder normalizer/kind lookup in the source resource projector. -/
theorem Resolved.modeContract
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (resolved : Resolved before ctx erased domain mode)
    (closing : RealizedInterpretation after ctx values) : ModeContract after (domain.subst values) mode := by
  cases resolved with
  | erased => exact .erased
  | head normalized known =>
      exact .known (((Conversion.normalize?_sound normalized).extend extension).substitution values history.wellFormed.closed)
        (head_substitution (head_extend extension known) values)
  | abstract normalized spine =>
      have represented := spine.realizes_closed_in_extension extension history closing
      have aligned := ((Conversion.normalize?_sound normalized).extend extension).substitution values history.wellFormed.closed
      refine .abstract (fun owned => represented.not_owned history (owned.congr aligned)) ?_ ?_
      · intro owner converted
        exact represented.not_ref history (aligned.symm.trans converted)
      · intro flag owner motive converted
        exact represented.not_back history (aligned.symm.trans converted)

theorem Resolved.evaluated_modeContract
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (resolved : Resolved before ctx erased domain mode)
    (closing : RealizedInterpretation after ctx values)
    (evaluated : ForwardValues after values finalValues) :
    ModeContract after (domain.subst finalValues) mode :=
  resolved.modeContract extension history (closing.forwardValues history evaluated)

end Jihoo.NativeKernel.Environment.ContextModes

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open CodeKinds ContextModes Jihoo.Quantity
variable {control : Control}
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}
variable {erased : Bool}

/-- Every actually emitted lambda scope keeps its exact mode's contract after
all interpreted dependent values take their observed finite forward paths. -/
theorem lam_evaluated_modeContract
    (projected : projectRaw (fuel + 1) before ctx (.lam erased domain term) = some control)
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (closing : RealizedInterpretation after ctx values)
    (evaluated : ForwardValues after values finalValues) :
    ∃ mode body sort, ContextFormed before ctx ∧ Binder before ctx erased domain sort ∧
      ModeContract after (domain.subst finalValues) mode ∧
      projectRaw fuel before (⟨domain,erased⟩ :: ctx) term = some body ∧
      control = .closure (.scope mode (NativeQuantity.functionTail term body)) := by
  obtain ⟨mode,body,sort,formed,binding,resolved,bodyProjected,same⟩ := lam_origin projected
  exact ⟨mode,body,sort,formed,binding,resolved.evaluated_modeContract extension history closing evaluated,bodyProjected,same⟩

end Jihoo.NativeKernel.Environment.ContextQuantity
