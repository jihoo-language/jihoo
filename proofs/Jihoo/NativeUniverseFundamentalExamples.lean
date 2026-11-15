import Jihoo.NativeUniverseFundamental

/-! Checker-derived universe abstraction/application and code-coherence tests.
Model values and logical realizations are derived by the fundamental theorem. -/
namespace Jihoo.NativeKernel.Environment.Semantics.UniverseContext.Examples
open Jihoo.NativeKernel.Environment.Conversion

private theorem emptyWellFormed : UnifiedProgram.EnvWellFormed empty :=
  UnifiedProgram.UnifiedProgramChecked.empty.wellFormed

private def identity : Term := .lam false (.univ 0) (.lam false (.var 0) (.var 0))
private def identityType : Term := .pi false (.univ 0) (.pi false (.var 0) (.var 1))
private theorem identityRecognized : UniverseRecognized identity := .lam (.lam .parameter (.var (by decide)))
private def identityBody : Expression [] (.arrow .parameter .parameter) := .lam (.var .here)

theorem checked_polymorphic_identity_model :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ 0) expression.syntax = identity ∧ Conv empty (polyType A) identityType ∧
      Nonempty (Finite.Carrier (polyCode A)) ∧
      ∀ (parameter : Parameter empty) (code : Term),
        Realizes parameter A (.app identity code) (expression.meaning (carrier := parameter.carrier) .nil) := by
  have typed : HasType empty [] true identity identityType := Checker.check_sound
    (by cbv : Checker.check 32 empty [] true identity identityType = true)
  exact universe_fundamental emptyWellFormed typed identityRecognized

theorem identity_model_acts_on_every_type (carrier : Type) (value : carrier) :
    identityBody.polyInterpret.down carrier value = value := rfl

theorem identity_application_preserves_parameter_relation (parameter : Parameter env) (code : Term) {value : parameter.carrier}
    (argument : parameter.realizes term value) :
    parameter.realizes (.app (.app identity code) term) value := by
  have realized := identityBody.poly_application parameter code
  simpa only [identityBody,identity,Expression.syntax,Expression.meaning,Member.value,Mono.syntax,Mono.instantiate,List.length_nil,Realizes] using
    realized term value argument

theorem checked_universe_application_realized :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ 0) expression.syntax = identity ∧
      HasType empty [] true (.app identity .u64) (A.instantiate .u64) ∧
      Realizes (CodeValue.sourceCode (env := empty) .natural).parameter A (.app identity .u64)
        (expression.meaning (carrier := Nat) .nil) := by
  have typed : HasType empty [] true identity identityType := Checker.check_sound
    (by cbv : Checker.check 32 empty [] true identity identityType = true)
  exact universe_source_application emptyWellFormed typed identityRecognized .natural

private def higherOrder : Term :=
  .lam false (.univ 0)
    (.lam false (.pi false (.var 0) (.var 1))
      (.lam false (.var 1) (.app (.var 1) (.var 0))))
private def higherOrderType : Term :=
  .pi false (.univ 0)
    (.pi false (.pi false (.var 0) (.var 1)) (.pi false (.var 1) (.var 2)))
private theorem higherOrderRecognized : UniverseRecognized higherOrder := by
  simpa only [higherOrder,Mono.syntax,Mono.instantiate,Term.rename] using
    (UniverseRecognized.lam (Recognized.lam (.arrow .parameter .parameter)
      (Recognized.lam .parameter (Recognized.app (Recognized.var (show 1 < 2 from by decide))
        (Recognized.var (show 0 < 2 from by decide))))))

theorem checked_abstract_higher_order_model :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ 0) expression.syntax = higherOrder ∧ Conv empty (polyType A) higherOrderType ∧
      Nonempty (Finite.Carrier (polyCode A)) ∧
      ∀ (parameter : Parameter empty) (code : Term),
        Realizes parameter A (.app higherOrder code) (expression.meaning (carrier := parameter.carrier) .nil) := by
  have typed : HasType empty [] true higherOrder higherOrderType := Checker.check_sound
    (by cbv : Checker.check 40 empty [] true higherOrder higherOrderType = true)
  exact universe_fundamental emptyWellFormed typed higherOrderRecognized

private def computedCode : Term := .app (.lam false (.univ 0) (.var 0)) .u64

theorem computed_universe_code_interpreted : Nonempty (CodeValue empty computedCode) := by
  have converted : Conv empty computedCode .u64 := by
    simpa only [computedCode,Term.app,Term.lam,Term.subst,NativeKernel.single] using
      (FamilyIota.Extended.Conv.legacy (env := empty) (NativeKernel.Conversion.Conv.beta false (.univ 0) (.var 0) .u64))
  exact ⟨⟨.natural,converted⟩⟩

theorem computed_universe_code_has_actual_type : HasType empty [] true computedCode (.univ 0) :=
  Checker.check_sound (by cbv : Checker.check 32 empty [] true computedCode (.univ 0) = true)

theorem closed_code_coherence_allows_skeleton_collapse :
    Mono.parameter.code Nat = Mono.natural.code Nat := by
  let value := CodeValue.sourceCode (env := empty) Functions.SimpleType.natural
  exact CodeValue.instantiated_coherent emptyWellFormed .parameter .natural value value (.refl _)

private def declaration : GlobalDeclaration := ⟨.univ 0,.u64⟩
private def checkedEnvironment : Environment := ⟨#[declaration],#[]⟩
private theorem history : UnifiedProgram.UnifiedProgramChecked [declaration] [] checkedEnvironment :=
  UnifiedProgram.checkProgram_sound
    (by cbv : UnifiedProgram.checkProgram 32 32 [declaration] [] = some checkedEnvironment)
private def deltaCode : CodeValue checkedEnvironment (.node (.global 0) []) :=
  ⟨.natural,FamilyIota.Extended.Conv.delta (env := checkedEnvironment) (index := 0) (declaration := declaration) rfl⟩

theorem checked_delta_type_argument_realized :
    HasType checkedEnvironment [] true (.app identity (.node (.global 0) [])) (.pi false .u64 .u64) ∧
    Realizes deltaCode.parameter (.arrow .parameter .parameter) (.app identity (.node (.global 0) []))
      (fun value : Nat => value) := by
  constructor
  · exact Checker.check_sound (by cbv : Checker.check 32 checkedEnvironment [] true
      (.app identity (.node (.global 0) [])) (.pi false .u64 .u64) = true)
  · simpa only [identityBody,identity,Expression.syntax,Expression.meaning,Member.value,Mono.syntax,Mono.instantiate,List.length_nil,Realizes] using
      identityBody.poly_application deltaCode.parameter (.node (.global 0) [])

theorem checked_delta_code_coherence (other : CodeValue checkedEnvironment (.node (.global 0) [])) :
    other.source = Functions.SimpleType.natural := CodeValue.coherent history.wellFormed other deltaCode

end Jihoo.NativeKernel.Environment.Semantics.UniverseContext.Examples
