import Jihoo.NativeFamilyCodeContexts
set_option maxUniverseOffset 40

/-! Higher-kinded source reconstruction and semantic fundamental theorem.
Only source syntax, level checks and actual native HasType are recognition
inputs; semantic values and the intrinsic source program are outputs. -/
namespace Jihoo.NativeKernel.Environment.Semantics.FamilyCodes
open Jihoo.NativeKernel.Environment.Conversion
variable {parameters families : Nat} {levels : Fin parameters → Fin 32} {signatures : Fin families → Signature}

inductive Values (assignment : Assignment levels signatures) : List (TypeCode parameters families) → Type 34 where
  | nil : Values assignment []
  | cons (valid : A.Valid levels signatures) :
      Finite.Carrier (A.meaning assignment valid) → Values assignment Γ → Values assignment (A :: Γ)

def Member.value {A : TypeCode parameters families} {Γ : List (TypeCode parameters families)}
    {assignment : Assignment levels signatures} (member : Member A Γ index)
    (values : Values assignment Γ) (valid : A.Valid levels signatures) : Finite.Carrier (A.meaning assignment valid) :=
  match member,values with
  | .here,.cons _ value _ => value
  | .there previous,.cons _ _ rest => previous.value rest valid

inductive Expression (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature) :
    List (TypeCode parameters families) → TypeCode parameters families → Type where
  | var : Member A Γ index → A.Valid levels signatures → Expression levels signatures Γ A
  | natural (value : Nat) (bound : value < 2^64) : Expression levels signatures Γ .natural
  | lam : A.Valid levels signatures → Expression levels signatures (A :: Γ) B → Expression levels signatures Γ (.arrow A B)
  | app : Expression levels signatures Γ (.arrow A B) → Expression levels signatures Γ A → Expression levels signatures Γ B

theorem Expression.valid : Expression levels signatures Γ A → A.Valid levels signatures
  | .var _ valid => valid
  | .natural _ _ => trivial
  | .lam valid body => ⟨valid,body.valid⟩
  | .app function _ => function.valid.2

def Expression.syntax : Expression levels signatures Γ A → Term
  | .var (index := index) _ _ => .var index
  | .natural value _ => .natural value
  | .lam (A := A) (Γ := Γ) _ body => .lam false (A.syntax Γ.length) body.syntax
  | .app function argument => .app function.syntax argument.syntax

def Expression.meaning {A : TypeCode parameters families} {Γ : List (TypeCode parameters families)}
    {assignment : Assignment levels signatures} :
    (expression : Expression levels signatures Γ A) → Values assignment Γ → Finite.Carrier (A.meaning assignment expression.valid)
  | .var member valid,values => member.value values valid
  | .natural value _,_ => ⟨value⟩
  | .lam (A := A) (B := B) valid body,values =>
    (Finite.piMeaning (A.meaning assignment valid) (B.sort levels signatures)
      (fun _ => B.meaning assignment body.valid)).lam (fun argument => body.meaning (.cons valid argument values))
  | .app (A := A) (B := B) function argument,values =>
    (Finite.piMeaning (A.meaning assignment argument.valid) (B.sort levels signatures)
      (fun _ => B.meaning assignment function.valid.2)).app (function.meaning values) (argument.meaning values)

theorem Expression.typed {A : TypeCode parameters families} {Γ : List (TypeCode parameters families)}
    (expression : Expression levels signatures Γ A) :
    HasType env (context levels signatures Γ) true expression.syntax (A.syntax Γ.length) := by
  induction expression with
  | var member valid => exact .var member.lookup (Or.inl rfl)
  | natural value bound => exact .natural bound
  | @lam A Γ B valid body ih =>
    rw [TypeCode.syntax_arrow]
    exact .lam (.intro (s := .type (A.level levels signatures)) (A.formed valid)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih
  | @app Γ A B function argument ihf iha =>
    have functionTyped : HasType env (context levels signatures Γ) true function.syntax
        (.pi false (A.syntax Γ.length) (B.syntax (Γ.length+1))) := by
      simpa only [TypeCode.syntax_arrow] using ihf
    change HasType env (context levels signatures Γ) true (.app function.syntax argument.syntax) (B.syntax Γ.length)
    rw [←TypeCode.syntax_instantiate B Γ.length argument.syntax]
    exact .app functionTyped iha (Or.inl rfl)

def TypeCode.Atomic : TypeCode parameters families → Prop
  | .parameter _ => True
  | .application _ _ => True
  | _ => False

structure Interpretation (env : Environment) (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature) where
  assignment : Assignment levels signatures
  realizes : ∀ (A : TypeCode parameters families) (valid : A.Valid levels signatures), A.Atomic → Term → Finite.Carrier (A.meaning assignment valid) → Prop
  saturated : ∀ A valid atomic {term replacement}, Conv env term replacement →
    ∀ value, realizes A valid atomic term value ↔ realizes A valid atomic replacement value

def Realizes (interpretation : Interpretation env levels signatures) :
    (A : TypeCode parameters families) → (valid : A.Valid levels signatures) →
      Term → Finite.Carrier (A.meaning interpretation.assignment valid) → Prop
  | .parameter index,valid,term,value => interpretation.realizes (.parameter index) valid trivial term value
  | .natural,_,term,value => value.down < 2^64 ∧ Conv env term (.natural value.down)
  | .arrow A B,valid,term,function =>
    ∀ argument value, Realizes interpretation A valid.1 argument value →
      Realizes interpretation B valid.2 (.app term argument)
        ((Finite.piMeaning (A.meaning interpretation.assignment valid.1) (B.sort levels signatures)
          (fun _ => B.meaning interpretation.assignment valid.2)).app function value)
  | .application family argument,valid,term,value => interpretation.realizes (.application family argument) valid trivial term value

theorem Realizes.conversion (interpretation : Interpretation env levels signatures) (A : TypeCode parameters families)
    (valid : A.Valid levels signatures) (converted : Conv env term replacement)
    (value : Finite.Carrier (A.meaning interpretation.assignment valid)) :
    Realizes interpretation A valid term value ↔ Realizes interpretation A valid replacement value := by
  induction A generalizing term replacement with
  | parameter index => exact interpretation.saturated _ valid trivial converted value
  | natural =>
    constructor
    · rintro ⟨bound,realized⟩; exact ⟨bound,.trans (.symm converted) realized⟩
    · rintro ⟨bound,realized⟩; exact ⟨bound,.trans converted realized⟩
  | arrow A B ha hb =>
    constructor <;> intro proof argument argumentValue admitted
    · exact (hb valid.2 (.node .app (.cons converted (.cons (.refl _) .nil))) _).mp (proof argument argumentValue admitted)
    · exact (hb valid.2 (.node .app (.cons converted (.cons (.refl _) .nil))) _).mpr (proof argument argumentValue admitted)
  | application family argument ih => exact interpretation.saturated _ valid trivial converted value

def SubstitutionRealizes (interpretation : Interpretation env levels signatures) (Γ : List (TypeCode parameters families))
    (σ : Nat → Term) (values : Values interpretation.assignment Γ) : Prop :=
  ∀ {A index} (member : Member A Γ index) valid,
    Realizes interpretation A valid (σ index) (member.value values valid)

theorem SubstitutionRealizes.extend (substitution : SubstitutionRealizes interpretation Γ σ values)
    (argument : Realizes interpretation A valid term value) :
    SubstitutionRealizes interpretation (A :: Γ) (Functions.extendSubstitution σ term) (.cons valid value values) := by
  intro B index member validB
  cases member with
  | here => exact argument
  | there previous => exact substitution previous validB

theorem Expression.fundamental {A : TypeCode parameters families} {Γ : List (TypeCode parameters families)}
    (expression : Expression levels signatures Γ A) (interpretation : Interpretation env levels signatures)
    {values : Values interpretation.assignment Γ} (substitution : SubstitutionRealizes interpretation Γ σ values) :
    Realizes interpretation A expression.valid (expression.syntax.subst σ) (expression.meaning values) := by
  induction expression generalizing σ with
  | var member valid => simpa only [Expression.syntax,Expression.meaning,Term.subst] using substitution member valid
  | natural value bound =>
    simpa only [Expression.syntax,Expression.meaning,Term.natural,Term.subst,substArgs] using
      (show Realizes interpretation .natural trivial (.natural value) ⟨value⟩ from ⟨bound,.refl _⟩)
  | @lam A Γ B valid body ih =>
    intro argument argumentValue admitted
    have realized := ih (SubstitutionRealizes.extend substitution admitted)
    have beta : Conv env (.app ((Term.lam false (A.syntax Γ.length) body.syntax).subst σ) argument)
        (body.syntax.subst (Functions.extendSubstitution σ argument)) := by
      simp only [Term.lam,Term.subst,substArgs,Op.binders]
      exact .trans (.legacy (.beta false _ _ argument))
        (by rw [Functions.lifted_substitution_instantiation]; exact .refl _)
    simp only [Expression.meaning]
    rw [(Finite.piMeaning (A.meaning interpretation.assignment valid) (B.sort levels signatures)
      (fun _ => B.meaning interpretation.assignment body.valid)).beta]
    exact (Realizes.conversion interpretation B body.valid beta _).mpr realized
  | app function argument ihf iha =>
    simpa only [Expression.syntax,Expression.meaning,Term.app,Term.subst,substArgs,Op.binders,liftSub] using
      ihf substitution _ _ (iha substitution)

inductive Recognized (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature) : Nat → Term → Prop where
  | var (bound : index < depth) : Recognized levels signatures depth (.var index)
  | natural (value : Nat) : Recognized levels signatures depth (.natural value)
  | lam (domain : TypeCode parameters families) (valid : domain.Valid levels signatures) :
      Recognized levels signatures (depth+1) body → Recognized levels signatures depth (.lam false (domain.syntax depth) body)
  | app : Recognized levels signatures depth function → Recognized levels signatures depth argument →
      Recognized levels signatures depth (.app function argument)

theorem recognized_principal (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized levels signatures depth term) :
    ∀ (Γ : List (TypeCode parameters families)), Γ.length = depth → ContextValid levels signatures Γ →
      ∀ {mode type}, HasType env (context levels signatures Γ) mode term type →
      ∃ A, ∃ expression : Expression levels signatures Γ A,
        expression.syntax = term ∧ Conv env (A.syntax Γ.length) type := by
  induction recognized with
  | var bound =>
    intro Γ length validΓ mode type typed
    cases length
    obtain ⟨A,member⟩ := Member.at Γ _ bound
    obtain ⟨binding,found,converted⟩ := typed.principalView
    rw [member.lookup] at found
    cases found
    exact ⟨A,.var member (validΓ.member member),rfl,converted⟩
  | natural value =>
    intro Γ length validΓ mode type typed
    obtain ⟨bound,converted⟩ := typed.naturalView
    exact ⟨.natural,.natural value bound,rfl,converted⟩
  | lam domain valid recognized ih =>
    intro Γ length validΓ mode type typed
    cases length
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨B,bodyExpression,erased,bodyConversion⟩ := ih (domain :: Γ) rfl (validΓ.cons valid) bodyTyped
    refine ⟨.arrow domain B,.lam valid bodyExpression,?_,?_⟩
    · simp only [Expression.syntax,erased]
    · rw [TypeCode.syntax_arrow]
      exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConversion .nil))) converted
  | app recognizedFunction recognizedArgument ihf iha =>
    intro Γ length validΓ mode type typed
    obtain ⟨erased,domain,codomain,functionTyped,argumentTyped,allowed,resultConverted⟩ := typed.appView
    obtain ⟨F,functionExpression,functionErasure,functionConverted⟩ := ihf Γ length validΓ functionTyped
    cases F with
    | parameter index =>
      exact False.elim (EnvironmentDelta.Basis.Conv.full_variable_node_separate rfl functionConverted wf.admissible)
    | natural =>
      exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .u64) (op' := .pi erased) rfl rfl (by intro h; cases h) functionConverted wf.admissible)
    | arrow A B =>
      rw [TypeCode.syntax_arrow] at functionConverted
      have components := functionConverted.pi_injective wf.admissible
      obtain ⟨C,argumentExpression,argumentErasure,argumentConverted⟩ := iha Γ length validΓ argumentTyped
      have same : C = A := TypeCode.syntax_injective wf (.trans argumentConverted (.symm components.2.1))
      subst C
      refine ⟨B,.app functionExpression argumentExpression,?_,?_⟩
      · simp only [Expression.syntax,functionErasure,argumentErasure]
      · have result := components.2.2.substitution (single argumentExpression.syntax) wf.closed
        rw [TypeCode.syntax_instantiate,argumentErasure] at result
        exact .trans result resultConverted
    | application family argument =>
      exact False.elim (EnvironmentDelta.Basis.Conv.neutralSpine_node_separate
        (arguments := [argument.syntax Γ.length]) wf.admissible rfl (by intro h; cases h) rfl functionConverted)

/-- The higher-kinded fundamental endpoint reconstructs a semantic source from
actual native typing, rather than assuming its realization or normalization. -/
theorem native_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (context levels signatures Γ) mode term type)
    (recognized : Recognized levels signatures Γ.length term) (validΓ : ContextValid levels signatures Γ)
    (interpretation : Interpretation env levels signatures) {values : Values interpretation.assignment Γ}
    (substitution : SubstitutionRealizes interpretation Γ σ values) :
    ∃ A, ∃ expression : Expression levels signatures Γ A,
      expression.syntax = term ∧ Conv env (A.syntax Γ.length) type ∧
      Realizes interpretation A expression.valid (term.subst σ) (expression.meaning values) := by
  obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized Γ rfl validΓ typed
  exact ⟨A,expression,erased,converted,erased ▸ expression.fundamental interpretation substitution⟩

/-- No interpretation or inhabitant is an input here: actual source typing
constructs a value in each independently chosen concrete family assignment. -/
theorem closed_context_model (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (context levels signatures []) mode term type)
    (recognized : Recognized levels signatures 0 term) :
    ∃ A, ∃ expression : Expression levels signatures [] A,
      expression.syntax = term ∧ Conv env (A.syntax 0) type ∧
      ∀ assignment : Assignment levels signatures,
        Nonempty (Finite.Carrier (A.meaning assignment expression.valid)) := by
  have validΓ : ContextValid levels signatures [] := by intro A member; cases member
  obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized [] rfl validΓ typed
  exact ⟨A,expression,erased,converted,fun assignment => ⟨expression.meaning (assignment := assignment) .nil⟩⟩

theorem TypeCode.atomic_empty (A : TypeCode parameters families) (valid : A.Valid levels signatures)
    (atomic : A.Atomic) : ¬ Nonempty (Finite.Carrier (A.meaning (Assignment.empty levels signatures) valid)) := by
  cases A with
  | parameter index => exact Finite.Values.empty_uninhabited (levels index)
  | natural => cases atomic
  | arrow A B => cases atomic
  | application family argument =>
    simpa only [TypeCode.meaning,Assignment.empty,TypeCode.sort,TypeCode.level,Signature.apply_emptyFamily] using
      Finite.Values.empty_uninhabited (signatures family).result

/-- A type variable or an arbitrary nested family fiber cannot supply its own
inhabitant in the authentic source fragment. The separating model assigns
empty codes to parameters and the constant empty function to every family. -/
theorem no_atomic_result {A : TypeCode parameters families} (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized levels signatures 0 term) (atomic : A.Atomic)
    (typed : HasType env (context levels signatures []) mode term (A.syntax 0)) : False := by
  have validΓ : ContextValid levels signatures [] := by intro A member; cases member
  obtain ⟨B,expression,erased,converted⟩ := recognized_principal wf recognized [] rfl validΓ typed
  have same : B = A := TypeCode.syntax_injective wf converted
  cases same
  exact A.atomic_empty expression.valid atomic ⟨expression.meaning (assignment := Assignment.empty levels signatures) .nil⟩

end Jihoo.NativeKernel.Environment.Semantics.FamilyCodes
