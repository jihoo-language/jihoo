import Jihoo.NativeMultiUniverseCodeComputations
set_option maxUniverseOffset 40

/-! Actual source reconstruction also admits computed type annotations. Its
recognizer contains only syntax; every code normal form and every source-term
conversion is constructed from the authenticated HasType derivation. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.Computed
open Jihoo.NativeKernel.Environment.Conversion
variable {count : Nat} {levels : Fin count → Fin 32}

def ValueContext (env : Environment) (Γ : List (Mono count)) (ctx : Context) : Prop :=
  ∀ {A index}, Member A Γ index → ∃ binding,
    NativeKernel.lookup ctx index = some binding ∧ binding.erased = false ∧
      Conv env binding.ty (A.syntax Γ.length)

theorem ValueContext.extend (wf : UnifiedProgram.EnvWellFormed env) (agreement : ValueContext env Γ ctx)
    (converted : Conv env original (A.syntax Γ.length)) :
    ValueContext env (A :: Γ) (⟨original,false⟩ :: ctx) := by
  intro B index member
  cases member with
  | here =>
    refine ⟨⟨original.rename Nat.succ,false⟩,rfl,rfl,?_⟩
    simpa only [Mono.syntax_shift,List.length_cons] using converted.renaming Nat.succ wf.closed
  | there previous =>
    obtain ⟨binding,found,erased,previousConverted⟩ := agreement previous
    refine ⟨⟨binding.ty.rename Nat.succ,binding.erased⟩,?_,erased,?_⟩
    · simp only [NativeKernel.lookup,found,Option.map]
    · simpa only [Mono.syntax_shift,List.length_cons] using previousConverted.renaming Nat.succ wf.closed

theorem context_values (levels : Fin count → Fin 32) (Γ : List (Mono count)) :
    ValueContext env Γ (context levels Γ) := by
  intro A index member
  exact ⟨⟨A.syntax Γ.length,false⟩,member.lookup levels,rfl,.refl _⟩

inductive Recognized (count : Nat) : Nat → Term → Prop where
  | var (bound : index < depth) : Recognized count depth (.var index)
  | natural (value : Nat) : Recognized count depth (.natural value)
  | lam (domain : Code count) : Recognized count (depth+1) body →
      Recognized count depth (.lam false (domain.syntax depth) body)
  | app : Recognized count depth function → Recognized count depth argument →
      Recognized count depth (.app function argument)

theorem recognized_principal (wf : UnifiedProgram.EnvWellFormed env) (recognized : Recognized count depth term) :
    ∀ (Γ : List (Mono count)), Γ.length = depth → ∀ {ctx mode type}, ValueContext env Γ ctx →
      HasType env ctx mode term type →
      ∃ A, ∃ expression : Expression Γ A,
        Conv env expression.syntax term ∧ Conv env (A.syntax Γ.length) type := by
  induction recognized with
  | var bound =>
    intro Γ length ctx mode type agreement typed
    cases length
    obtain ⟨A,member⟩ := Member.at Γ _ bound
    obtain ⟨binding,found,converted⟩ := typed.principalView
    obtain ⟨actual,selected,erased,canonical⟩ := agreement member
    rw [found] at selected
    cases selected
    exact ⟨A,.var member,.refl _,.trans canonical.symm converted⟩
  | natural value =>
    intro Γ length ctx mode type agreement typed
    obtain ⟨bound,converted⟩ := typed.naturalView
    exact ⟨.natural,.natural value bound,.refl _,converted⟩
  | lam domain recognized ih =>
    intro Γ length ctx mode type agreement typed
    cases length
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨B,bodyExpression,bodyErasure,bodyConversion⟩ :=
      ih (domain.normal :: Γ) rfl (agreement.extend wf (domain.normalizes _)) bodyTyped
    refine ⟨.arrow domain.normal B,.lam bodyExpression,?_,?_⟩
    · exact .node (.lam false) (.cons (domain.normalizes _).symm (.cons bodyErasure .nil))
    · rw [Mono.syntax_arrow]
      exact .trans (.node (.pi false) (.cons (domain.normalizes _).symm (.cons bodyConversion .nil))) converted
  | @app depth function argument recognizedFunction recognizedArgument ihf iha =>
    intro Γ length ctx mode type agreement typed
    obtain ⟨erased,domain,codomain,functionTyped,argumentTyped,allowed,resultConverted⟩ := typed.appView
    obtain ⟨F,functionExpression,functionErasure,functionConverted⟩ := ihf Γ length agreement functionTyped
    cases F with
    | parameter index =>
      exact False.elim (EnvironmentDelta.Basis.Conv.full_variable_node_separate rfl functionConverted wf.admissible)
    | natural =>
      exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .u64) (op' := .pi erased) rfl rfl (by intro h; cases h) functionConverted wf.admissible)
    | arrow A B =>
      rw [Mono.syntax_arrow] at functionConverted
      have components := functionConverted.pi_injective wf.admissible
      obtain ⟨C,argumentExpression,argumentErasure,argumentConverted⟩ := iha Γ length agreement argumentTyped
      have same : C = A := Mono.syntax_injective wf (.trans argumentConverted (.symm components.2.1))
      subst C
      refine ⟨B,.app functionExpression argumentExpression,?_,?_⟩
      · exact .node .app (.cons functionErasure (.cons argumentErasure .nil))
      · have result := components.2.2.substitution (single argument) wf.closed
        rw [Mono.syntax_instantiate] at result
        exact .trans result resultConverted

theorem native_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (context levels Γ) mode term type) (recognized : Recognized count Γ.length term)
    (interpretation : Interpretation env levels) {values : Values interpretation.assignment Γ}
    (substitution : SubstitutionRealizes interpretation Γ σ values) :
    ∃ A, ∃ expression : Expression Γ A,
      Conv env expression.syntax term ∧ Conv env (A.syntax Γ.length) type ∧
      Realizes interpretation A (term.subst σ) (expression.meaning values) := by
  obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized Γ rfl (context_values levels Γ) typed
  exact ⟨A,expression,erased,converted,
    (Realizes.conversion interpretation A (erased.substitution σ wf.closed) _).mp
      (expression.fundamental interpretation substitution)⟩

inductive UniverseRecognized : (levelsList : List (Fin 32)) → Term → Prop where
  | body : Recognized levelsList.length 0 termBody → UniverseRecognized levelsList termBody
  | abstract (level : Fin 32) : UniverseRecognized (level :: levelsList) termBody →
      UniverseRecognized levelsList (.lam false (.univ level.val) termBody)

theorem universe_principal (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : UniverseRecognized levelsList term) :
    ∀ {mode type}, HasType env (parameterContext levelsList) mode term type →
      ∃ scheme : Scheme levelsList, Conv env scheme.syntax term ∧ Conv env scheme.type type := by
  induction recognized with
  | @body termBody levelsList recognized =>
    intro mode type typed
    have agreement : ValueContext env ([] : List (Mono levelsList.length)) (parameterContext levelsList) := by
      intro A index member; cases member
    obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized [] rfl agreement typed
    exact ⟨.body expression,erased,converted⟩
  | abstract level recognized ih =>
    intro mode type typed
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨inner,erased,bodyConverted⟩ := ih bodyTyped
    exact ⟨.abstract level inner,
      .node (.lam false) (.cons (.refl _) (.cons erased .nil)),
      .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConverted .nil))) converted⟩

theorem universe_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (parameterContext levelsList) mode term type)
    (recognized : UniverseRecognized levelsList term) :
    ∃ scheme : Scheme levelsList, Conv env scheme.syntax term ∧ Conv env scheme.type type ∧
      ∀ assignment : Assignment levelsList.get, Nonempty (Finite.Carrier (scheme.code assignment)) := by
  obtain ⟨scheme,erased,converted⟩ := universe_principal wf recognized typed
  exact ⟨scheme,erased,converted,fun assignment => ⟨scheme.meaning assignment⟩⟩

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.Computed
