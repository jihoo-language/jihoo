import Jihoo.NativeNeutralSpineSyntax
import Jihoo.NativeFamilyIotaInjectivity

/-! Exact neutral-family spine shape under genuine enlarged finite reduction,
and consequently all-arity conversion coherence. No normal-form, strong
normalization, typing or preservation premise is assumed. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended
open NativeKernel.Conversion (ListRel)

private def SpinePath (R : Term → Term → Prop) (input result : Term) : Prop :=
  ∀ head arguments, input = neutralSpine head arguments →
    ∃ replacements, result = neutralSpine head replacements ∧ ListRel R arguments replacements

private theorem list_refl (reflexive : ∀ term, R term term) (terms : List Term) : ListRel R terms terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons (reflexive term) ih

private theorem list_trans (transitive : ∀ {a b c}, R a b → R b c → R a c)
    (first : ListRel R xs ys) (second : ListRel R ys zs) : ListRel R xs zs := by
  induction first generalizing zs with
  | nil => cases second;exact .nil
  | cons first rest ih => cases second with
    | cons next tail => exact .cons (transitive first next) (ih tail)

private theorem arithmetic_variable (step : ACU.ArithmeticRed input result) :
    ∀ head, input = .var head → result = .var head := by
  induction step using ACU.ArithmeticRed.rec (motive_2 := fun _ _ _ => True) with
  | refl => intro head same;exact same
  | trans _ _ first second => intro head same;exact second head (first head same)
  | nil => trivial
  | cons => trivial
  | _ => intro head same;cases same

private theorem arithmetic_spine (step : ACU.ArithmeticRed (neutralSpine head arguments) result) :
    ∃ replacements, result = neutralSpine head replacements ∧ ListRel ACU.ArithmeticRed arguments replacements := by
  induction arguments generalizing result with
  | nil => exact ⟨[],arithmetic_variable step head rfl,.nil⟩
  | cons argument rest ih =>
    obtain ⟨children,shaped,kids⟩ := step.rigid_shape (op := .app)
      (xs := [neutralSpine head rest,argument]) rfl rfl
    cases kids with
    | cons functionStep tail => cases tail with
      | cons argumentStep tail =>
        cases tail
        obtain ⟨replacements,functionShape,functions⟩ := ih functionStep
        refine ⟨_ :: replacements,?_,.cons argumentStep functions⟩
        simpa only [neutralSpine,Term.app,functionShape] using shaped

private theorem arithmetic_to_mixed (steps : ListRel ACU.ArithmeticRed xs ys) : ListRel ACU.MixedRed xs ys := by
  induction steps with
  | nil => exact .nil
  | cons first rest ih => exact .cons (.arithmetic first) ih

private theorem mixed_spine (step : ACU.MixedRed input result) : SpinePath ACU.MixedRed input result := by
  induction step using ACU.MixedRed.rec
    (motive_2 := fun xs ys _ => ListRel (SpinePath ACU.MixedRed) xs ys) with
  | refl term => intro head arguments same;exact ⟨arguments,same,list_refl (fun _ => .refl _) arguments⟩
  | trans first second ihfirst ihsecond =>
    intro head arguments same
    obtain ⟨middle,middleShape,firstArguments⟩ := ihfirst head arguments same
    obtain ⟨replacements,last,secondArguments⟩ := ihsecond head middle middleShape
    exact ⟨replacements,last,list_trans ACU.MixedRed.trans firstArguments secondArguments⟩
  | node op kids ih =>
    intro head arguments same
    cases arguments with
    | nil => cases same
    | cons argument rest =>
      cases same
      cases kids with
      | cons functionStep tail => cases tail with
        | cons argumentStep tail =>
          cases tail
          cases ih with
          | cons functionIH tailIH =>
            obtain ⟨replacements,functionShape,functions⟩ := functionIH head rest rfl
            exact ⟨_ :: replacements,congrArg (fun function => Term.app function _) functionShape,.cons argumentStep functions⟩
  | arithmetic original =>
    intro head arguments same
    rw [same] at original
    obtain ⟨replacements,last,arguments⟩ := arithmetic_spine original
    exact ⟨replacements,last,arithmetic_to_mixed arguments⟩
  | compute original =>
    intro head arguments same
    cases arguments with
    | nil => cases original <;> cases same
    | cons argument rest =>
      cases rest with
      | nil => cases original <;> cases same
      | cons first rest => cases original <;> cases same
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

private theorem mixed_to_old (steps : ListRel ACU.MixedRed xs ys) : ListRel (EnvironmentDelta.Forward env) xs ys := by
  induction steps with
  | nil => exact .nil
  | cons first rest ih => exact .cons (.acu first) ih

private theorem old_spine (step : EnvironmentDelta.Forward env input result) :
    SpinePath (EnvironmentDelta.Forward env) input result := by
  induction step using EnvironmentDelta.Forward.rec
    (motive_2 := fun xs ys _ => ListRel (SpinePath (EnvironmentDelta.Forward env)) xs ys) with
  | refl => intro head arguments same;exact ⟨arguments,same,list_refl (fun _ => .refl) arguments⟩
  | trans first second ihfirst ihsecond =>
    intro head arguments same
    obtain ⟨middle,middleShape,firstArguments⟩ := ihfirst head arguments same
    obtain ⟨replacements,last,secondArguments⟩ := ihsecond head middle middleShape
    exact ⟨replacements,last,list_trans EnvironmentDelta.Forward.trans firstArguments secondArguments⟩
  | node op kids ih =>
    intro head arguments same
    cases arguments with
    | nil => cases same
    | cons argument rest =>
      cases same
      cases kids with
      | cons functionStep tail => cases tail with
        | cons argumentStep tail =>
          cases tail
          cases ih with
          | cons functionIH tailIH =>
            obtain ⟨replacements,functionShape,functions⟩ := functionIH head rest rfl
            exact ⟨_ :: replacements,congrArg (fun function => Term.app function _) functionShape,.cons argumentStep functions⟩
  | delta => intro head arguments same;cases arguments <;> cases same
  | acu original =>
    intro head arguments same
    obtain ⟨replacements,last,arguments⟩ := mixed_spine original head arguments same
    exact ⟨replacements,last,mixed_to_old arguments⟩
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

private theorem old_to_extended (steps : ListRel (EnvironmentDelta.Forward env) xs ys) : ListRel (Forward env) xs ys := by
  induction steps with
  | nil => exact .nil
  | cons first rest ih => exact .cons (.old first) ih

/-- Arbitrary native arguments may compute, including genuine iota and delta;
the free family head and every argument's actual forward path are retained. -/
theorem Forward.neutralSpine_shape (step : Forward env input result) : SpinePath (Forward env) input result := by
  induction step using Forward.rec
    (motive_2 := fun xs ys _ => ListRel (SpinePath (Forward env)) xs ys) with
  | refl => intro head arguments same;exact ⟨arguments,same,list_refl (fun _ => .refl) arguments⟩
  | trans first second ihfirst ihsecond =>
    intro head arguments same
    obtain ⟨middle,middleShape,firstArguments⟩ := ihfirst head arguments same
    obtain ⟨replacements,last,secondArguments⟩ := ihsecond head middle middleShape
    exact ⟨replacements,last,list_trans Forward.trans firstArguments secondArguments⟩
  | node op kids ih =>
    intro head arguments same
    cases arguments with
    | nil => cases same
    | cons argument rest =>
      cases same
      cases kids with
      | cons functionStep tail => cases tail with
        | cons argumentStep tail =>
          cases tail
          cases ih with
          | cons functionIH tailIH =>
            obtain ⟨replacements,functionShape,functions⟩ := functionIH head rest rfl
            exact ⟨_ :: replacements,congrArg (fun function => Term.app function _) functionShape,.cons argumentStep functions⟩
  | old original =>
    intro head arguments same
    obtain ⟨replacements,last,arguments⟩ := old_spine original head arguments same
    exact ⟨replacements,last,old_to_extended arguments⟩
  | iota original => intro head arguments same;cases arguments <;> cases original <;> cases same
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
