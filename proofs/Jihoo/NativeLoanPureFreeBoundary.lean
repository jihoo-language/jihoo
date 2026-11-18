import Jihoo.NativeLoanComputationPreservation
import Jihoo.NativeLoanValueProjection

/-! The conversion used by Loan64 does not yet include every pure Core
equation. Free is a value observation, while raw conversion retains its head.
This separates the resulting equality propositions even in an empty world. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.PureFreeBoundary

def owner : Term := .alloc (.natural 1) (.integer 0)

def annotation : Term :=
  .pi false .u64 (.eq (.free owner (.var 0)) (.var 0))

def body : Term := .lam false .u64 (.refl (.var 0))

theorem free_variable_not_convertible (admissible : EnvironmentDelta.Admissible env) :
    ¬ Conversion.Conv env (.var index) (.free buffer (.var index)) := by
  intro converted
  exact converted.full_variable_node_separate rfl admissible

/-- `refl x` cannot use the pure Free equation at its requested Eq type in
the current Loan64 judgment. In Core, the ghost Free yields x. -/
theorem free_reflexivity_untypable (admissible : EnvironmentDelta.Admissible env) :
    ¬ HasType env [] [] true body annotation := by
  intro typed
  obtain ⟨_,_,_,reflTyped,lambda⟩ := typed.lamView
  have result := (lambda.pi_injective admissible).2.2
  have sides := (reflTyped.principalView.trans result).eq_injective admissible
  exact free_variable_not_convertible admissible sides.1

theorem free_result_value_root : ValueReduction.Root (.free owner (.var 0)) (.var 0) :=
  .free _ _

theorem check_declaration_rejects (admissible : EnvironmentDelta.Admissible env) :
    MixedProgram.checkDeclaration fuel quantityFuel env ⟨annotation,body⟩ = none := by
  cases accepted : MixedProgram.checkDeclaration fuel quantityFuel env ⟨annotation,body⟩ with
  | none => rfl
  | some expanded =>
      have checked := MixedProgram.checkDeclaration_sound accepted
      have annotationFree : GlobalEnvironment.GlobalFree annotation :=
        (Environment.globalFree_correct annotation).mp (by cbv)
      have bodyFree : GlobalEnvironment.GlobalFree body :=
        (Environment.globalFree_correct body).mp (by cbv)
      have typeEq := (EnvironmentDelta.expansion_eq_expand (env := env) checked.typeExpansion).symm.trans
        (EnvironmentDelta.expand_globalFree annotationFree)
      have bodyEq := (EnvironmentDelta.expansion_eq_expand (env := env) checked.valueExpansion).symm.trans
        (EnvironmentDelta.expand_globalFree bodyFree)
      obtain ⟨_,_,typed,_⟩ := checked.valid.typing
      rw [typeEq,bodyEq] at typed
      exact False.elim (free_reflexivity_untypable admissible (typed.ghost []))

/-- The existing ghost value projection accounts for Free beneath the Pi and
Eq constructors. Its equality acts on projected terms. -/
theorem projected_annotation_eq (env : Environment) :
    Semantics.ValueErasure.Loan.project env annotation = .pi false .u64 (.eq (.var 0) (.var 0)) := by
  open Semantics.ValueErasure.Loan in
  simp only [annotation,project_pi,Term.eq,project_ordinary_node (op := .eq) rfl (by decide),
    List.map_cons,List.map_nil,project_free,project_variable,Semantics.ValueErasure.emit]
  rw [show Term.u64 = .node .u64 [] from rfl,
    project_ordinary_node (op := .u64) rfl (by decide)]
  rfl

end Jihoo.NativeKernel.Environment.LoanTyping.PureFreeBoundary
