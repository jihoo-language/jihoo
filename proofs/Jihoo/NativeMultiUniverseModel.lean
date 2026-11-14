import Jihoo.NativeMultiUniverseSyntax
set_option maxUniverseOffset 40

/-! Concrete finite-code semantics and a saturated logical relation for any
finite list of universe variables, including mixed levels. Parameter relations
are context assignments. The source expression's meaning and realizability
are reconstructed rather than accepted as input evidence. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse
open Jihoo.NativeKernel.Environment.Conversion
variable {count : Nat} {levels : Fin count → Fin 32}

def Mono.semanticSort (levels : Fin count → Fin 32) : Mono count → Finite.LevelSort
  | .parameter index => .type ⟨(levels index).val,by omega⟩
  | .natural => .type ⟨0,by decide⟩
  | .arrow A B => (A.semanticSort levels).pi (B.semanticSort levels)

structure Assignment (levels : Fin count → Fin 32) where
  codes : ∀ index, Finite.Universe (.type ⟨(levels index).val,by omega⟩)

def Mono.code (assignment : Assignment levels) : (A : Mono count) → Finite.Universe (A.semanticSort levels)
  | .parameter index => assignment.codes index
  | .natural => Finite.natural
  | .arrow A B => Finite.pi (A.code assignment) (B.semanticSort levels) (fun _ => B.code assignment)

theorem Mono.semanticSort_native (A : Mono count) (levels : Fin count → Fin 32) :
    (A.semanticSort levels).native = .type (A.nativeLevel levels) := by
  induction A with
  | parameter => rfl
  | natural => rfl
  | arrow A B ha hb => simp only [Mono.semanticSort,Mono.nativeLevel,Finite.LevelSort.pi_native,ha,hb,SortTag.pi]

theorem Mono.code_coherent (wf : UnifiedProgram.EnvWellFormed env) {A B : Mono count}
    (converted : Conv env (A.syntax offset) (B.syntax offset)) (assignment : Assignment levels) :
    HEq (A.code assignment) (B.code assignment) := by
  cases Mono.syntax_injective wf converted
  rfl

inductive Values {levels : Fin count → Fin 32} (assignment : Assignment levels) : List (Mono count) → Type 34 where
  | nil : Values assignment []
  | cons : Finite.Carrier (A.code assignment) → Values assignment Γ → Values assignment (A :: Γ)

def Member.value {A : Mono count} {Γ : List (Mono count)} {assignment : Assignment levels}
    (member : Member A Γ index) (values : Values assignment Γ) : Finite.Carrier (A.code assignment) :=
  match member, values with
  | .here, .cons value _ => value
  | .there previous, .cons _ rest => previous.value rest

inductive Expression {count : Nat} : List (Mono count) → Mono count → Type where
  | var : Member A Γ index → Expression Γ A
  | natural (value : Nat) (bound : value < 2^64) : Expression Γ .natural
  | lam : Expression (A :: Γ) B → Expression Γ (.arrow A B)
  | app : Expression Γ (.arrow A B) → Expression Γ A → Expression Γ B

def Expression.syntax : Expression Γ A → Term
  | .var (index := index) _ => .var index
  | .natural value _ => .natural value
  | .lam (A := A) (Γ := Γ) body => .lam false (A.syntax Γ.length) body.syntax
  | .app function argument => .app function.syntax argument.syntax

def Expression.meaning {A : Mono count} {Γ : List (Mono count)} {assignment : Assignment levels} :
    Expression Γ A → Values assignment Γ → Finite.Carrier (A.code assignment)
  | .var member, values => member.value values
  | .natural value _, _ => ⟨value⟩
  | .lam (A := A) (B := B) body, values =>
    (Finite.piMeaning (A.code assignment) (B.semanticSort levels) (fun _ => B.code assignment)).lam
      (fun argument => body.meaning (.cons argument values))
  | .app (A := A) (B := B) function argument, values =>
    (Finite.piMeaning (A.code assignment) (B.semanticSort levels) (fun _ => B.code assignment)).app
      (function.meaning values) (argument.meaning values)

theorem Expression.typed {A : Mono count} {Γ : List (Mono count)} (expression : Expression Γ A) (levels : Fin count → Fin 32) :
    HasType env (context levels Γ) true expression.syntax (A.syntax Γ.length) := by
  induction expression with
  | var member => exact .var (member.lookup levels) (Or.inl rfl)
  | natural value bound => exact .natural bound
  | @lam A Γ B body ih =>
    rw [Mono.syntax_arrow]
    exact .lam (.intro (s := .type (A.nativeLevel levels)) (A.formed levels)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih
  | @app Γ A B function argument ihf iha =>
    have typedFunction : HasType env (context levels Γ) true function.syntax
        (.pi false (A.syntax Γ.length) (B.syntax (Γ.length+1))) := by
      simpa only [Mono.syntax_arrow] using ihf
    change HasType env (context levels Γ) true (.app function.syntax argument.syntax) (B.syntax Γ.length)
    rw [←Mono.syntax_instantiate B Γ.length argument.syntax]
    exact .app typedFunction iha (Or.inl rfl)

def Assignment.empty (levels : Fin count → Fin 32) : Assignment levels where
  codes index := Finite.Values.empty (levels index)

/-- No expression without value assumptions can produce an arbitrary abstract
carrier element. The concrete assignment selects the empty code for every
independent parameter, including parameters at different universe levels. -/
theorem Expression.parameter_uninhabited {index : Fin count}
    (expression : Expression [] (.parameter index)) (levels : Fin count → Fin 32) : False := by
  have value : Finite.Carrier (Finite.Values.empty (levels index)) :=
    expression.meaning (assignment := Assignment.empty levels) .nil
  exact Finite.Values.empty_uninhabited (levels index) ⟨value⟩

structure Interpretation (env : Environment) (levels : Fin count → Fin 32) where
  assignment : Assignment levels
  realizes : ∀ index, Term → Finite.Carrier (assignment.codes index) → Prop
  saturated : ∀ index {term replacement}, Conv env term replacement →
    ∀ value, realizes index term value ↔ realizes index replacement value

def Realizes (interpretation : Interpretation env levels) :
    (A : Mono count) → Term → Finite.Carrier (A.code interpretation.assignment) → Prop
  | .parameter index, term, value => interpretation.realizes index term value
  | .natural, term, value => value.down < 2^64 ∧ Conv env term (.natural value.down)
  | .arrow A B, term, function =>
    ∀ argument value, Realizes interpretation A argument value →
      Realizes interpretation B (.app term argument)
        ((Finite.piMeaning (A.code interpretation.assignment) (B.semanticSort levels)
          (fun _ => B.code interpretation.assignment)).app function value)

theorem Realizes.conversion (interpretation : Interpretation env levels) (A : Mono count)
    (converted : Conv env term replacement) (value : Finite.Carrier (A.code interpretation.assignment)) :
    Realizes interpretation A term value ↔ Realizes interpretation A replacement value := by
  induction A generalizing term replacement with
  | parameter index => exact interpretation.saturated index converted value
  | natural =>
    constructor
    · rintro ⟨bound,realized⟩; exact ⟨bound,.trans (.symm converted) realized⟩
    · rintro ⟨bound,realized⟩; exact ⟨bound,.trans converted realized⟩
  | arrow A B ha hb =>
    constructor <;> intro proof argument argumentValue admitted
    · exact (hb (.node .app (.cons converted (.cons (.refl _) .nil))) _).mp (proof argument argumentValue admitted)
    · exact (hb (.node .app (.cons converted (.cons (.refl _) .nil))) _).mpr (proof argument argumentValue admitted)

def SubstitutionRealizes (interpretation : Interpretation env levels) (Γ : List (Mono count))
    (σ : Nat → Term) (values : Values interpretation.assignment Γ) : Prop :=
  ∀ {A index} (member : Member A Γ index), Realizes interpretation A (σ index) (member.value values)

theorem SubstitutionRealizes.extend (substitution : SubstitutionRealizes interpretation Γ σ values)
    (argument : Realizes interpretation A term value) :
    SubstitutionRealizes interpretation (A :: Γ) (Functions.extendSubstitution σ term) (.cons value values) := by
  intro B index member
  cases member with
  | here => exact argument
  | there previous => exact substitution previous

theorem Expression.fundamental {A : Mono count} {Γ : List (Mono count)} (expression : Expression Γ A) (interpretation : Interpretation env levels)
    {values : Values interpretation.assignment Γ} (substitution : SubstitutionRealizes interpretation Γ σ values) :
    Realizes interpretation A (expression.syntax.subst σ) (expression.meaning values) := by
  induction expression generalizing σ with
  | var member => simpa only [Expression.syntax,Expression.meaning,Term.subst] using substitution member
  | natural value bound =>
    simpa only [Expression.syntax,Expression.meaning,Term.natural,Term.subst,substArgs] using
      (show Realizes interpretation .natural (.natural value) ⟨value⟩ from ⟨bound,.refl _⟩)
  | @lam A Γ B body ih =>
    intro argument argumentValue admitted
    have realized := ih (SubstitutionRealizes.extend substitution admitted)
    have beta : Conv env (.app ((Term.lam false (A.syntax Γ.length) body.syntax).subst σ) argument)
        (body.syntax.subst (Functions.extendSubstitution σ argument)) := by
      simp only [Term.lam,Term.subst,substArgs,Op.binders]
      exact .trans (.legacy (.beta false _ _ argument))
        (by rw [Functions.lifted_substitution_instantiation]; exact .refl _)
    simp only [Expression.meaning]
    rw [(Finite.piMeaning (A.code interpretation.assignment) (B.semanticSort levels)
      (fun _ => B.code interpretation.assignment)).beta]
    exact (Realizes.conversion interpretation B beta _).mpr realized
  | app function argument ihf iha =>
    simpa only [Expression.syntax,Expression.meaning,Term.app,Term.subst,substArgs,Op.binders,liftSub] using
      ihf substitution _ _ (iha substitution)

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse
