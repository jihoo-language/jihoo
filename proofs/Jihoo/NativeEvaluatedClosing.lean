import Jihoo.NativeKindValueEvaluation

/-! Transport complete dependent closing interpretations through actual finite
forward value computation. Dependent annotation coherence is proved by actual
conversion congruence; neither output safety nor CODE rechecking is assumed.
These are type/resource representation contracts, not native heap simulation. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- Every actual substituted code value has its observed forward value path.
Slots beyond the source context can be retained by the reflexive constructor. -/
def ForwardValues (env : Environment) (source target : Nat → Term) : Prop :=
  ∀ index, FamilyIota.Extended.Forward env (source index) (target index)

theorem ForwardValues.refl (values : Nat → Term) : ForwardValues env values values :=
  fun _ => .refl

theorem ForwardValues.trans (first : ForwardValues env before middle)
    (second : ForwardValues env middle after) : ForwardValues env before after :=
  fun index => .trans (first index) (second index)

theorem ForwardValues.extend (extension : Extends before after)
    (values : ForwardValues before source target) : ForwardValues after source target :=
  fun index => (values index).extend extension

/-- The existing bounded implementation supplies genuine value paths even
when it explicitly refuses: getD then retains the original value. No successful
normalization is treated as an output-normality certificate. -/
def normalizedValues (env : Environment) (fuel : Nat) (values : Nat → Term) : Nat → Term :=
  fun index => Conversion.normalize env fuel (values index)

theorem ForwardValues.normalized (values : Nat → Term) :
    ForwardValues env values (normalizedValues env fuel values) := by
  intro index
  change FamilyIota.Extended.Forward env (values index)
    ((Conversion.normalize? env fuel (values index)).getD (values index))
  cases normalized : Conversion.normalize? env fuel (values index) with
  | none => exact .refl
  | some normal => exact Conversion.normalize?_forward normalized

/-- Actual forward computation determines dependent output annotation
coherence, including every binder and arbitrary typed U64 index occurrence. -/
theorem ForwardValues.subst_congr (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (values : ForwardValues env before after) (term : Term) :
    Conversion.Conv env (term.subst before) (term.subst after) :=
  FamilyIota.Extended.Conv.subst_congr history.wellFormed.closed
    (fun index => FamilyIota.Extended.Forward.toConv (values index)) term

/-- Complete typed closing is stable for all actual forward value paths. Every
lookup's dependent type is transported by proved substitution congruence. -/
theorem RealizedInterpretation.forwardValues
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : RealizedInterpretation env ctx before)
    (values : ForwardValues env before after) : RealizedInterpretation env ctx after := by
  refine ⟨closing.formed,?_,?_⟩
  · intro index binding selected
    exact ((closing.typed index binding selected).ghostFamilyForward history (values index)).convert
      (values.subst_congr history binding.ty)
  · intro index kind found
    exact (closing.arguments index kind found).forward history (values index)

/-- Uniform executable value normalization preserves the whole dependent
interpretation; no bounded rerun of code checking is needed. -/
theorem RealizedInterpretation.normalizedValues
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : RealizedInterpretation env ctx values) :
    RealizedInterpretation env ctx (normalizedValues env fuel values) :=
  closing.forwardValues history (ForwardValues.normalized values)

/-- Actual calls construct the complete context first; every actual finite
forward evaluation of its values then preserves the context and original
result-type alignment. No caller-supplied output interpretation is an input. -/
theorem InputTelescope.close_checkedCall_evaluated
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : InputTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (inputs : source.Inputs fuel arguments) :
    ∃ sourceValues, RealizedInterpretation env finalContext sourceValues ∧
      Conversion.Conv env actualResult (result.subst sourceValues) ∧
      (∀ targetValues, ForwardValues env sourceValues targetValues →
        RealizedInterpretation env finalContext targetValues ∧
        Conversion.Conv env actualResult (result.subst targetValues)) := by
  obtain ⟨sourceValues,completed,converted⟩ := source.close_checkedCall history closing sourceFunction checked inputs
  refine ⟨sourceValues,completed,converted,?_⟩
  intro targetValues evaluated
  exact ⟨completed.forwardValues history evaluated,converted.trans (evaluated.subst_congr history result)⟩

/-- Fully instantiated, actually normalized values and their typed dependent
substitution are produced from the checked call. The normalizer may fail for
individual values, in which case those original values are retained. -/
theorem InputTelescope.close_checkedCall_normalized
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : InputTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (inputs : source.Inputs fuel arguments) (valueFuel : Nat) :
    ∃ sourceValues, RealizedInterpretation env finalContext (normalizedValues env valueFuel sourceValues) ∧
      Conversion.Conv env actualResult (result.subst (normalizedValues env valueFuel sourceValues)) ∧
      (∀ ghost term type, HasType env finalContext ghost term type →
        HasType env [] true (term.subst (normalizedValues env valueFuel sourceValues))
          (type.subst (normalizedValues env valueFuel sourceValues))) := by
  obtain ⟨sourceValues,original,converted,evaluated⟩ := source.close_checkedCall_evaluated history closing sourceFunction checked inputs
  have completed := evaluated _ (ForwardValues.normalized (fuel := valueFuel) sourceValues)
  exact ⟨sourceValues,completed.1,completed.2,fun _ _ _ typed =>
    typed.ghostSubstitution history.wellFormed completed.1.typed⟩

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open CodeKinds CallReplay
open Jihoo.Quantity
variable {control : Control}
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- The same admitted projector's owner-consuming call guard remains valid
under every actually forward-evaluated complete closing interpretation. -/
theorem app_interpreted_result_evaluated
    (projected : projectRaw (fuel + 1) before ctx (.app function argument) = some control)
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (closing : RealizedInterpretation after ctx values)
    (evaluated : ForwardValues after values finalValues) :
    ∃ head supplied entries result signature,
      NativeQuantity.splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      ContextFormed before ctx ∧ SignatureTrace after ctx false signature supplied entries result ∧
      HasType after ctx false (applications head supplied) result ∧
      (entries.any (ownsArgument before) = false ∨ PiSeparated after (result.subst finalValues)) :=
  app_interpreted_result_closed projected extension history (closing.forwardValues history evaluated)

end Jihoo.NativeKernel.Environment.ContextQuantity
