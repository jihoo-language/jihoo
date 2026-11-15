import Jihoo.NativeDependentFamilyClosure
set_option maxUniverseOffset 40

/-! Actual closed source examples quantify over arbitrary abstract carriers,
value-indexed families and their carrier observations at every native level. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentFamilies.Examples
open Jihoo.NativeKernel.Environment.Conversion
open MultiUniverse (Mono)

private def domain : Mono 1 := .parameter ⟨0,by decide⟩
private def signature (result : Fin 32) : Signature 1 := ⟨domain,result⟩
private def fiber : TypeCode 1 1 1 := .fiber ⟨0,by decide⟩ ⟨0,by decide⟩

private theorem fiber_valid (result : Fin 32) : fiber.Valid [signature result].get [domain].get := by
  simp [fiber,TypeCode.Valid,signature,List.get_eq_getElem]

def identityScheme (level result : Fin 32) : Scheme [] [] [] :=
  .parameter level (.family (levelList := [level]) (signature result) (.observation (levelList := [level]) domain
    (.body (.lam (fiber_valid result) (.var .here (fiber_valid result))))))

def identity (level result : Fin 32) : Term :=
  .lam false (.univ level.val) (.lam false (.pi false (.var 0) (.univ result.val))
    (.lam false (.var 1) (.lam false (.app (.var 1) (.var 0)) (.var 0))))

theorem identityScheme_source (level result : Fin 32) : (identityScheme level result).syntax = identity level result := by
  simp [identityScheme,Scheme.syntax,identity,Signature.term,signature,domain,MultiUniverse.Mono.syntax,
    MultiUniverse.Mono.instantiate,Expression.syntax,fiber,TypeCode.syntax,TypeCode.instantiate]

theorem identity_typed (level result : Fin 32) :
    HasType env [] true (identity level result) (identityScheme level result).type := by
  rw [←identityScheme_source]
  simpa only [sourceContext,observationContext,familyContext,MultiUniverse.universeContext_list,List.map_nil] using
    (identityScheme level result).typed (env := env)

theorem identity_recognized (level result : Fin 32) : UniverseRecognized [] [] [] (identity level result) := by
  have bodyRecognized : Recognized [signature result] [domain] 0
      (.lam false (fiber.syntax 0) (.var 0)) :=
    Recognized.lam (familyList := [signature result]) (observations := [domain]) (depth := 0)
      fiber
      (Recognized.var (familyList := [signature result]) (observations := [domain])
        (index := 0) (depth := 1) (by simp))
  exact .parameter level (.family (levelList := [level]) (signature result)
    (.observation (levelList := [level]) domain (.body bodyRecognized)))

theorem identity_fundamental (wf : UnifiedProgram.EnvWellFormed env) (level result : Fin 32) :
    ∃ scheme : Scheme [] [] [], scheme.syntax = identity level result ∧
      Conv env scheme.type (identityScheme level result).type ∧
      ∀ assignment : Assignment (List.get ([] : List (Fin 32)))
        (List.get ([] : List (Signature 0))) (List.get ([] : List (Mono 0))),
        Nonempty (Finite.Carrier (scheme.code assignment)) := by
  exact universe_fundamental wf (identity_typed level result) (identity_recognized level result)

def observationScheme (level result : Fin 32) : Scheme [] [] [] :=
  .parameter level (.family (levelList := [level]) (signature result) (.observation (levelList := [level]) domain (.body (.observation ⟨0,by simp⟩))))

theorem observation_typed (level result : Fin 32) :
    HasType env [] true (observationScheme level result).syntax (observationScheme level result).type := by
  simpa only [sourceContext,observationContext,familyContext,MultiUniverse.universeContext_list,List.map_nil] using
    (observationScheme level result).typed (env := env)

theorem observation_recognized (level result : Fin 32) :
    UniverseRecognized [] [] [] (observationScheme level result).syntax := by
  have bodyRecognized : Recognized [signature result] [domain] 0 (.var 0) :=
    .var (index := 0) (depth := 0) (by simp)
  exact .parameter level (.family (levelList := [level]) (signature result)
    (.observation (levelList := [level]) domain (.body bodyRecognized)))

end Jihoo.NativeKernel.Environment.Semantics.DependentFamilies.Examples
