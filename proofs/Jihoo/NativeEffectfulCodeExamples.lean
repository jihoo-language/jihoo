import Jihoo.NativeEffectfulCodeInterpretation
set_option maxUniverseOffset 40

/-! Actual checked type annotations whose Pi domain and codomain contain
Strict and Free, with a value-indexed family at every native universe level. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentFamilies.EffectfulExamples
open MultiUniverse (Mono)

private def input : Mono 1 := .parameter ⟨0,by decide⟩
private def family (result : Fin 32) : Signature 1 := ⟨input,result⟩
private def fiber : TypeCode 1 1 1 := .fiber ⟨0,by decide⟩ ⟨0,by decide⟩

private theorem fiber_valid (result : Fin 32) : fiber.Valid [family result].get [input].get := by
  simp [fiber,TypeCode.Valid,family,List.get_eq_getElem]

def effectfulPi : Annotation 1 1 1 :=
  .arrow (.strict (.natural 0) (.pure fiber))
    (.free (.alloc (.natural 0) (.integer 0)) (.pure fiber))

def source : Term :=
  .pi false (.strict (.natural 0) (.app (.var 1) (.var 0)))
    (.free (.alloc (.natural 0) (.integer 0)) (.app (.var 2) (.var 1)))

theorem effectfulPi_source : effectfulPi.syntax 0 = source := rfl

theorem source_typed (level result : Fin 32) :
    HasType env (observationContext ([level].get) [family result] [input]) true source (.univ result.val) := by
  let frame := LookupFrame.of_context (levels := [level].get) [family result] [input] []
  have domain : HasType env (observationContext ([level].get) [family result] [input]) true
      (.strict (.natural 0) (fiber.syntax 0)) (.univ result.val) :=
    .strict (.natural (by decide)) (fiber.formed_in frame (fiber_valid result))
  have body : HasType env (⟨.strict (.natural 0) (fiber.syntax 0),false⟩ ::
      observationContext ([level].get) [family result] [input]) true
      (.free (.alloc (.natural 0) (.integer 0)) (fiber.syntax 1)) (.univ result.val) :=
    .free (.alloc (.natural (by decide)) (.integer (by decide) (by decide)))
      (fiber.formed_in (frame.extend ⟨.strict (.natural 0) (fiber.syntax 0),false⟩) (fiber_valid result))
  have formed := HasType.pi (ghost := true) (s := .type result.val) (r := .type result.val)
    (.intro domain (Or.inl (by intro h; cases h))) body
  simpa only [SortTag.pi,SortTag.term,Nat.max_self,source,fiber,TypeCode.syntax,TypeCode.instantiate] using formed

theorem source_reconstructed (wf : UnifiedProgram.EnvWellFormed env) (level result : Fin 32)
    {mode type}
    (typed : HasType env (observationContext ([level].get) [family result] [input]) mode source type) :
    effectfulPi.code.Valid [family result].get [input].get ∧
      Conversion.Conv env (.univ result.val) type := by
  have recovered := effectfulPi.recover wf
    (LookupFrame.of_context (levels := [level].get) [family result] [input] [])
    (effectfulPi_source.symm ▸ typed)
  simpa only [effectfulPi,Annotation.code,TypeCode.level,fiber,family,List.get_eq_getElem,
    List.getElem_cons_zero,Nat.max_self] using recovered

theorem source_finite_meaning (wf : UnifiedProgram.EnvWellFormed env) (level result : Fin 32)
    (assignment : Assignment ([level].get) [family result].get [input].get) :
    effectfulPi.interpret_checked wf
      (LookupFrame.of_context (levels := [level].get) [family result] [input] [])
      (effectfulPi_source.symm ▸ source_typed level result) assignment =
    Finite.pi (fiber.meaning assignment (fiber_valid result)) (fiber.sort ([level].get) [family result].get)
      (fun _ => fiber.meaning assignment (fiber_valid result)) := rfl

theorem source_projects_to_dependent_fiber_pi :
    ValueErasure.project env source = .pi false (.app (.var 1) (.var 0)) (.app (.var 2) (.var 1)) := by
  rw [←effectfulPi_source,Annotation.project_syntax]
  simp only [effectfulPi,Annotation.code,fiber,TypeCode.syntax,
    TypeCode.instantiate,Term.rename]

end Jihoo.NativeKernel.Environment.Semantics.DependentFamilies.EffectfulExamples
