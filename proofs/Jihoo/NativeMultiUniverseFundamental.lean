import Jihoo.NativeMultiUniverseModel

/-! Source reconstruction and the fundamental theorem for arbitrary finite
mixed-level universe contexts. The premises inspect source syntax and actual
HasType derivations, rather than postulate intrinsic source membership. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse
open Jihoo.NativeKernel.Environment.Conversion
variable {count : Nat} {levels : Fin count → Fin 32}

inductive Recognized (count : Nat) : Nat → Term → Prop where
  | var (bound : index < depth) : Recognized count depth (.var index)
  | natural (value : Nat) : Recognized count depth (.natural value)
  | lam (domain : Mono count) : Recognized count (depth+1) body → Recognized count depth (.lam false (domain.syntax depth) body)
  | app : Recognized count depth function → Recognized count depth argument → Recognized count depth (.app function argument)

theorem recognized_principal (wf : UnifiedProgram.EnvWellFormed env) (recognized : Recognized count depth term) :
    ∀ (Γ : List (Mono count)), Γ.length = depth → ∀ {mode type}, HasType env (context levels Γ) mode term type →
      ∃ A, ∃ expression : Expression Γ A, expression.syntax = term ∧ Conv env (A.syntax Γ.length) type := by
  induction recognized with
  | var bound =>
    intro Γ length mode type typed
    cases length
    obtain ⟨A,member⟩ := Member.at Γ _ bound
    obtain ⟨binding,found,converted⟩ := typed.principalView
    rw [member.lookup levels] at found
    cases found
    exact ⟨A,.var member,rfl,converted⟩
  | natural value =>
    intro Γ length mode type typed
    obtain ⟨bound,converted⟩ := typed.naturalView
    exact ⟨.natural,.natural value bound,rfl,converted⟩
  | lam domain recognized ih =>
    intro Γ length mode type typed
    cases length
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨B,bodyExpression,erased,bodyConversion⟩ := ih (domain :: Γ) rfl bodyTyped
    refine ⟨.arrow domain B,.lam bodyExpression,?_,?_⟩
    · simp only [Expression.syntax,erased]
    · rw [Mono.syntax_arrow]
      exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConversion .nil))) converted
  | app recognizedFunction recognizedArgument ihf iha =>
    intro Γ length mode type typed
    obtain ⟨erased,domain,codomain,functionTyped,argumentTyped,allowed,resultConverted⟩ := typed.appView
    obtain ⟨F,functionExpression,functionErasure,functionConverted⟩ := ihf Γ length functionTyped
    cases F with
    | parameter index =>
      exact False.elim (FamilyIota.Extended.Conv.full_variable_node_separate rfl functionConverted wf.admissible)
    | natural =>
      exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .u64) (op' := .pi erased) rfl rfl (by intro h; cases h) functionConverted wf.admissible)
    | arrow A B =>
      rw [Mono.syntax_arrow] at functionConverted
      have components := functionConverted.pi_injective wf.admissible
      obtain ⟨C,argumentExpression,argumentErasure,argumentConverted⟩ := iha Γ length argumentTyped
      have same : C = A := Mono.syntax_injective wf (.trans argumentConverted (.symm components.2.1))
      subst C
      refine ⟨B,.app functionExpression argumentExpression,?_,?_⟩
      · simp only [Expression.syntax,functionErasure,argumentErasure]
      · have result := components.2.2.substitution (single argumentExpression.syntax) wf.closed
        rw [Mono.syntax_instantiate,argumentErasure] at result
        exact .trans result resultConverted

theorem native_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (context levels Γ) mode term type) (recognized : Recognized count Γ.length term)
    (interpretation : Interpretation env levels) {values : Values interpretation.assignment Γ}
    (substitution : SubstitutionRealizes interpretation Γ σ values) :
    ∃ A, ∃ expression : Expression Γ A,
      expression.syntax = term ∧ Conv env (A.syntax Γ.length) type ∧
      Realizes interpretation A (term.subst σ) (expression.meaning values) := by
  obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized Γ rfl typed
  exact ⟨A,expression,erased,converted,erased ▸ expression.fundamental interpretation substitution⟩

/-- Consistency of every reconstructed value fragment in an authentic world:
independent arbitrary type parameters cannot supply an element by themselves. -/
theorem no_abstract_parameter (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized count 0 term) (index : Fin count)
    (typed : HasType env (context levels []) mode term ((Mono.parameter index).syntax 0)) : False := by
  obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized [] rfl typed
  have same : A = .parameter index := Mono.syntax_injective wf converted
  cases same
  exact expression.parameter_uninhabited levels

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse
