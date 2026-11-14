import Jihoo.NativeUniverseLevelSource
import Jihoo.NativeSemanticUniverseBoundary

namespace Jihoo.NativeKernel.Environment.Semantics.UniverseContext.LevelExamples

private theorem emptyWellFormed : UnifiedProgram.EnvWellFormed empty :=
  UnifiedProgram.UnifiedProgramChecked.empty.wellFormed
private def identityBody : Expression [] (.arrow .parameter .parameter) := .lam (.var .here)
private def identity (level : Nat) : Term := .lam false (.univ level) (.lam false (.var 0) (.var 0))
private def identityType (level : Nat) : Term := .pi false (.univ level) (.pi false (.var 0) (.var 1))

private theorem identityRecognized (level : Fin 32) : UniverseRecognizedAt level (identity level.val) :=
  .lam (.lam .parameter (.var (by decide)))

theorem all_native_levels_identity_model (level : Fin 32) :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ level.val) expression.syntax = identity level.val ∧
      Conversion.Conv empty (polyTypeAt level A) (identityType level.val) ∧
      Nonempty (Finite.Carrier (polyCodeAt level A)) := by
  have typed : HasType empty [] true (identity level.val) (identityType level.val) := by
    simpa only [identityBody,identity,identityType,Expression.syntax,polyTypeAt,Mono.syntax,Mono.instantiate,
      Term.rename,List.length_nil] using identityBody.polyTypedAt (env := empty) level
  exact universe_fundamental_at emptyWellFormed level typed (identityRecognized level)

theorem highest_native_input_checked : HasType empty [] true (identity 31) (identityType 31) :=
  Checker.check_sound (by cbv : Checker.check 32 empty [] true (identity 31) (identityType 31) = true)

theorem highest_native_input_model :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ 31) expression.syntax = identity 31 ∧
      Conversion.Conv empty (polyTypeAt ⟨31,by decide⟩ A) (identityType 31) ∧
      Nonempty (Finite.Carrier (polyCodeAt ⟨31,by decide⟩ A)) :=
  universe_fundamental_at emptyWellFormed ⟨31,by decide⟩ highest_native_input_checked (identityRecognized _)

theorem administrative_sort_of_highest_identity_type :
    HasType empty [] true (identityType 31) (.univ 32) := by
  simpa only [identityType,polyTypeAt,Mono.syntax,Mono.instantiate,Term.rename] using
    (polyTypeAt_formed (env := empty) (mode := true) ⟨31,by decide⟩ (.arrow .parameter .parameter))

theorem administrative_top_still_not_input : ¬ HasType env ctx mode (.univ 32) type :=
  Semantics.administrative_top_not_input

theorem every_level_identity_acts_on_every_code (level : Fin 32)
    (parameter : Finite.Carrier (Finite.Values.codeUniverse level))
    (value : Finite.Carrier (Finite.Values.decode level parameter)) :
    (Finite.piMeaning (Finite.Values.decode level parameter) (.type ⟨level.val,by omega⟩)
      (fun _ => Finite.Values.decode level parameter)).app
        ((Finite.piMeaning (Finite.Values.codeUniverse level)
          ((Mono.arrow .parameter .parameter).semanticSort (.type ⟨level.val,by omega⟩))
          (fun parameter => (Mono.arrow .parameter .parameter).atCode (Finite.Values.decode level parameter))).app
            (identityBody.polyInterpretAt level) parameter) value = value := by
  rw [Expression.polyInterpretAt_application]
  simp only [identityBody,Expression.levelMeaning,Mono.atCode,Mono.semanticSort]
  rw [(Finite.piMeaning (Finite.Values.decode level parameter) (.type ⟨level.val,by omega⟩)
    (fun _ => Finite.Values.decode level parameter)).beta]
  rfl

theorem no_highest_level_polymorphic_bottom
    (typed : HasType empty [] mode term (polyTypeAt ⟨31,by decide⟩ .parameter))
    (recognized : UniverseRecognizedAt ⟨31,by decide⟩ term) : False :=
  no_recognized_polymorphic_bottom emptyWellFormed ⟨31,by decide⟩ typed recognized

theorem no_polymorphic_bottom_raw_representative (level : Fin 32)
    (typed : HasType empty [] mode term (.uadd (polyTypeAt level .parameter) (.natural 0)))
    (recognized : UniverseRecognizedAt level term) : False := by
  have converted : Conversion.Conv empty (.uadd (polyTypeAt level .parameter) (.natural 0))
      (polyTypeAt level .parameter) := .acu (.zero _)
  exact no_recognized_polymorphic_bottom emptyWellFormed level (typed.convert converted) recognized

end Jihoo.NativeKernel.Environment.Semantics.UniverseContext.LevelExamples
