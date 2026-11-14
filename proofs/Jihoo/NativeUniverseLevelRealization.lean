import Jihoo.NativeUniverseLevelSource
set_option maxUniverseOffset 40

/-! Conversion-saturated realizability at every finite universe level. The
parameter relation interprets a context variable; realizability of the actual
source is derived by induction and reconstruction, never supplied as an oracle. -/
namespace Jihoo.NativeKernel.Environment.Semantics.UniverseContext
open Jihoo.NativeKernel.Environment.Conversion

structure LevelParameter (env : Environment) (sort : Finite.LevelSort) where
  code : Finite.Universe sort
  realizes : Term → Finite.Carrier code → Prop
  saturated : ∀ {term replacement}, Conv env term replacement →
    ∀ value, realizes term value ↔ realizes replacement value

def LevelRealizes (parameter : LevelParameter env sort) :
    (A : Mono) → Term → Finite.Carrier (A.atCode parameter.code) → Prop
  | .parameter, term, value => parameter.realizes term value
  | .natural, term, value => value.down < 2^64 ∧ Conv env term (.natural value.down)
  | .arrow A B, term, function =>
    ∀ argument value, LevelRealizes parameter A argument value →
      LevelRealizes parameter B (.app term argument)
        ((Finite.piMeaning (A.atCode parameter.code) (B.semanticSort sort)
          (fun _ => B.atCode parameter.code)).app function value)

theorem LevelRealizes.conversion (parameter : LevelParameter env sort) (A : Mono)
    (converted : Conv env term replacement) (value : Finite.Carrier (A.atCode parameter.code)) :
    LevelRealizes parameter A term value ↔ LevelRealizes parameter A replacement value := by
  induction A generalizing term replacement with
  | parameter => exact parameter.saturated converted value
  | natural =>
    constructor
    · rintro ⟨bound,proof⟩; exact ⟨bound,.trans (.symm converted) proof⟩
    · rintro ⟨bound,proof⟩; exact ⟨bound,.trans converted proof⟩
  | arrow A B ha hb =>
    constructor <;> intro proof argument argumentValue admitted
    · exact (hb (.node .app (.cons converted (.cons (.refl _) .nil))) _).mp (proof argument argumentValue admitted)
    · exact (hb (.node .app (.cons converted (.cons (.refl _) .nil))) _).mpr (proof argument argumentValue admitted)

def LevelSubstitutionRealizes (parameter : LevelParameter env sort) (Γ : List Mono) (σ : Nat → Term)
    (values : LevelValues parameter.code Γ) : Prop :=
  ∀ {A index} (member : Member A Γ index), LevelRealizes parameter A (σ index) (member.levelValue values)

theorem LevelSubstitutionRealizes.extend (substitution : LevelSubstitutionRealizes parameter Γ σ values)
    (argument : LevelRealizes parameter A term value) :
    LevelSubstitutionRealizes parameter (A :: Γ) (Functions.extendSubstitution σ term) (.cons value values) := by
  intro B index member
  cases member with
  | here => exact argument
  | there previous => exact substitution previous

theorem Expression.level_fundamental (expression : Expression Γ A) (parameter : LevelParameter env sort)
    {values : LevelValues parameter.code Γ} (substitution : LevelSubstitutionRealizes parameter Γ σ values) :
    LevelRealizes parameter A (expression.syntax.subst σ) (expression.levelMeaning values) := by
  induction expression generalizing σ with
  | var member => simpa only [Expression.syntax,Expression.levelMeaning,Term.subst] using substitution member
  | natural value bound =>
    simpa only [Expression.syntax,Expression.levelMeaning,Term.natural,Term.subst,substArgs] using
      (show LevelRealizes parameter .natural (.natural value) ⟨value⟩ from ⟨bound,.refl _⟩)
  | @lam A Γ B body ih =>
    intro argument argumentValue admitted
    have realizes := ih (LevelSubstitutionRealizes.extend substitution admitted)
    have beta : Conv env (.app ((Term.lam false (A.syntax Γ.length) body.syntax).subst σ) argument)
        (body.syntax.subst (Functions.extendSubstitution σ argument)) := by
      simp only [Term.lam,Term.subst,substArgs,Op.binders]
      exact .trans (.legacy (.beta false _ _ argument))
        (by rw [Functions.lifted_substitution_instantiation]; exact .refl _)
    simp only [Expression.levelMeaning]
    rw [(Finite.piMeaning (A.atCode parameter.code) (B.semanticSort sort)
      (fun _ => B.atCode parameter.code)).beta]
    exact (LevelRealizes.conversion parameter B beta _).mpr realizes
  | app function argument ihf iha =>
    simpa only [Expression.syntax,Expression.levelMeaning,Term.app,Term.subst,substArgs,Op.binders,liftSub] using
      ihf substitution _ _ (iha substitution)

theorem native_level_fundamental (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 32)
    (typed : HasType env (contextAt level.val Γ) mode term type) (recognized : Recognized Γ.length term)
    (parameter : LevelParameter env (.type ⟨level.val,by omega⟩))
    {values : LevelValues parameter.code Γ} (substitution : LevelSubstitutionRealizes parameter Γ σ values) :
    ∃ A, ∃ expression : Expression Γ A,
      expression.syntax = term ∧ Conv env (A.syntax Γ.length) type ∧
      LevelRealizes parameter A (term.subst σ) (expression.levelMeaning values) := by
  obtain ⟨A,expression,erased,converted⟩ :=
    recognized_in_value_context wf recognized Γ rfl (contextAt_values _ _) typed
  exact ⟨A,expression,erased,converted,erased ▸ expression.level_fundamental parameter substitution⟩

theorem Expression.level_poly_application (level : Fin 32) (expression : Expression [] A)
    (parameter : LevelParameter env (.type ⟨level.val,by omega⟩)) (code : Term) :
    LevelRealizes parameter A (.app (.lam false (.univ level.val) expression.syntax) code)
      (expression.levelMeaning (parameter := parameter.code) .nil) := by
  have substitution : LevelSubstitutionRealizes parameter [] (single code) .nil := by
    intro B index member
    cases member
  have realizes := expression.level_fundamental parameter substitution
  exact (LevelRealizes.conversion parameter A
    (.legacy (.beta false (.univ level.val) expression.syntax code)) _).mpr realizes

/-- Both a concrete finite-model value and universal contextual realizations
are derived from the actual source at every allowed native universe level. -/
theorem universe_realization_at (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 32)
    (typed : HasType env [] mode term type) (recognized : UniverseRecognizedAt level term) :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ level.val) expression.syntax = term ∧ Conv env (polyTypeAt level A) type ∧
      Nonempty (Finite.Carrier (polyCodeAt level A)) ∧
      ∀ (parameter : LevelParameter env (.type ⟨level.val,by omega⟩)) (code : Term),
        LevelRealizes parameter A (.app term code) (expression.levelMeaning (parameter := parameter.code) .nil) := by
  obtain ⟨A,expression,erased,converted,model⟩ := universe_fundamental_at wf level typed recognized
  refine ⟨A,expression,erased,converted,model,?_⟩
  intro parameter code
  simpa only [erased] using expression.level_poly_application level parameter code

theorem checked_universe_realization_at
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env) (level : Fin 32)
    (typed : HasType env [] mode term type) (recognized : UniverseRecognizedAt level term) :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ level.val) expression.syntax = term ∧ Conv env (polyTypeAt level A) type ∧
      Nonempty (Finite.Carrier (polyCodeAt level A)) ∧
      ∀ (parameter : LevelParameter env (.type ⟨level.val,by omega⟩)) (code : Term),
        LevelRealizes parameter A (.app term code) (expression.levelMeaning (parameter := parameter.code) .nil) :=
  universe_realization_at history.wellFormed level typed recognized

end Jihoo.NativeKernel.Environment.Semantics.UniverseContext
