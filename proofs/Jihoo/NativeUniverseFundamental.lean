import Jihoo.NativeUniverseContext

/-! Actual source reconstruction in a Type0-variable context, followed by a
universe-lambda fundamental theorem. The closed theorem constructs a concrete
Tarski-model value and parametric realizations; neither is an input oracle.
Arbitrary universe-code computations are not claimed complete by this slice. -/
namespace Jihoo.NativeKernel.Environment.Semantics.UniverseContext
open Jihoo.NativeKernel.Environment.Conversion

inductive Recognized : Nat → Term → Prop where
  | var (bound : index < depth) : Recognized depth (.var index)
  | natural (value : Nat) : Recognized depth (.natural value)
  | lam (domain : Mono) : Recognized (depth+1) body → Recognized depth (.lam false (domain.syntax depth) body)
  | app : Recognized depth function → Recognized depth argument → Recognized depth (.app function argument)

theorem recognized_principal (wf : UnifiedProgram.EnvWellFormed env) (recognized : Recognized depth term) :
    ∀ (Γ : List Mono), Γ.length = depth → ∀ {mode type}, HasType env (context Γ) mode term type →
      ∃ A, ∃ expression : Expression Γ A, expression.syntax = term ∧ Conv env (A.syntax Γ.length) type := by
  induction recognized with
  | var bound =>
    intro Γ length mode type typed
    cases length
    obtain ⟨A,member⟩ := Member.at Γ _ bound
    obtain ⟨binding,found,converted⟩ := typed.principalView
    rw [member.lookup] at found
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
    | parameter =>
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
    (typed : HasType env (context Γ) mode term type) (recognized : Recognized Γ.length term)
    (parameter : Parameter env) {values : Values parameter.carrier Γ}
    (substitution : SubstitutionRealizes parameter Γ σ values) :
    ∃ A, ∃ expression : Expression Γ A,
      expression.syntax = term ∧ Conv env (A.syntax Γ.length) type ∧
      Realizes parameter A (term.subst σ) (expression.meaning values) := by
  obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized Γ rfl typed
  exact ⟨A,expression,erased,converted,erased ▸ expression.fundamental parameter substitution⟩

def polyType (A : Mono) : Term := .pi false (.univ 0) (A.syntax 0)

def polyCode (A : Mono) : Finite.Universe (.type ⟨1,by decide⟩) :=
  Finite.pi Finite.universe0 (.type ⟨0,by decide⟩) (fun parameter => A.code parameter.down)

theorem polyCode_concrete (A : Mono) :
    polyCode A = Finite.Universe.type1 ((carrier : Type) → A.Meaning carrier) := rfl

def Expression.polyInterpret (expression : Expression [] A) : Finite.Carrier (polyCode A) :=
  ⟨fun carrier => expression.meaning (carrier := carrier) .nil⟩

theorem Expression.polyTyped (expression : Expression [] A) :
    HasType env [] true (.lam false (.univ 0) expression.syntax) (polyType A) :=
  .lam (.intro (s := .type 1) (.univ (by decide))
    (Or.inl (by change SortTag.type 1 ≠ SortTag.prop; intro h; cases h))) expression.typed

theorem Expression.poly_application (expression : Expression [] A) (parameter : Parameter env) (code : Term) :
    Realizes parameter A (.app (.lam false (.univ 0) expression.syntax) code)
      (expression.meaning (carrier := parameter.carrier) .nil) := by
  have substitution : SubstitutionRealizes parameter [] (single code) .nil := by
    intro B index member
    cases member
  have realizes := expression.fundamental parameter substitution
  exact (Realizes.conversion parameter A (.legacy (.beta false (.univ 0) expression.syntax code)) _).mpr realizes

inductive UniverseRecognized : Term → Prop where
  | lam : Recognized 0 body → UniverseRecognized (.lam false (.univ 0) body)

/-- Concrete universe abstraction, including arbitrary uses of its abstract
carrier in value domains and function domains, is reconstructed from HasType. -/
theorem universe_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env [] mode term type) (recognized : UniverseRecognized term) :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ 0) expression.syntax = term ∧ Conv env (polyType A) type ∧
      Nonempty (Finite.Carrier (polyCode A)) ∧
      ∀ (parameter : Parameter env) (code : Term),
        Realizes parameter A (.app term code) (expression.meaning (carrier := parameter.carrier) .nil) := by
  cases recognized with
  | lam bodyRecognized =>
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨A,expression,erased,bodyConversion⟩ := recognized_principal wf bodyRecognized [] rfl bodyTyped
    refine ⟨A,expression,?_,?_,⟨expression.polyInterpret⟩,?_⟩
    · rw [erased]
    · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConversion .nil))) converted
    · intro parameter code
      simpa only [erased] using expression.poly_application parameter code

theorem checked_universe_fundamental
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env [] mode term type) (recognized : UniverseRecognized term) :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ 0) expression.syntax = term ∧ Conv env (polyType A) type ∧
      Nonempty (Finite.Carrier (polyCode A)) ∧
      ∀ (parameter : Parameter env) (code : Term),
        Realizes parameter A (.app term code) (expression.meaning (carrier := parameter.carrier) .nil) :=
  universe_fundamental history.wellFormed typed recognized

/-- Concrete code values are generated from the earlier source type grammar
and closed under actual conversion. This is a partial universe interpretation;
completeness for arbitrary native Type0 computations is not assumed. -/
structure CodeValue (env : Environment) (code : Term) where
  source : Functions.SimpleType
  converted : Conv env code source.syntax

def CodeValue.parameter (value : CodeValue env code) : Parameter env where
  carrier := value.source.Meaning
  realizes := Functions.Realizes env value.source
  saturated := fun converted value => Functions.Realizes.conversion converted _ value

def CodeValue.sourceCode (source : Functions.SimpleType) : CodeValue env source.syntax := ⟨source,.refl _⟩

theorem CodeValue.conversion (value : CodeValue env code) (converted : Conv env code replacement) :
    Nonempty (CodeValue env replacement) := ⟨⟨value.source,.trans (.symm converted) value.converted⟩⟩

theorem CodeValue.coherent (wf : UnifiedProgram.EnvWellFormed env) (first second : CodeValue env code) :
    first.source = second.source :=
  Functions.SimpleType.syntax_injective wf (.trans (.symm first.converted) second.converted)

theorem CodeValue.model_coherent (wf : UnifiedProgram.EnvWellFormed env) (first second : CodeValue env code) :
    first.source.code = second.source.code := by
  rw [first.coherent wf second]

theorem Mono.syntax_zero_instantiate (A : Mono) (code : Term) :
    (A.syntax 0).subst (single code) = A.instantiate code := by
  rw [Mono.syntax,Mono.instantiate_subst]
  simp only [Term.subst,NativeKernel.single]

def Mono.close (source : Functions.SimpleType) : Mono → Functions.SimpleType
  | .parameter => source
  | .natural => .natural
  | .arrow A B => .arrow (A.close source) (B.close source)

theorem Mono.close_syntax (A : Mono) (source : Functions.SimpleType) :
    A.instantiate source.syntax = (A.close source).syntax := by
  induction A with
  | parameter => rfl
  | natural => rfl
  | arrow A B ha hb =>
    simp only [Mono.instantiate,Mono.close,Functions.SimpleType.syntax]
    rw [Functions.SimpleType.syntax_rename,ha,hb]

theorem Mono.close_meaning (A : Mono) (source : Functions.SimpleType) :
    A.Meaning source.Meaning = (A.close source).Meaning := by
  induction A with
  | parameter => rfl
  | natural => rfl
  | arrow A B ha hb =>
    simp only [Mono.Meaning,Mono.close,Functions.SimpleType.Meaning]
    rw [ha,hb]

theorem Mono.close_code (A : Mono) (source : Functions.SimpleType) :
    A.code source.Meaning = (A.close source).code := congrArg Finite.Universe.type0 (A.close_meaning source)

theorem Mono.closed_code_coherent (wf : UnifiedProgram.EnvWellFormed env) (A B : Mono)
    (source replacement : Functions.SimpleType)
    (converted : Conv env (A.instantiate source.syntax) (B.instantiate replacement.syntax)) :
    A.code source.Meaning = B.code replacement.Meaning := by
  rw [Mono.close_syntax,Mono.close_syntax] at converted
  rw [Mono.close_code,Mono.close_code,Functions.SimpleType.syntax_injective wf converted]

theorem Mono.instantiate_conversion {code replacement : Term} (A : Mono) (closed : Conversion.Closed env)
    (converted : Conv env code replacement) : Conv env (A.instantiate code) (A.instantiate replacement) := by
  induction A generalizing code replacement with
  | parameter => exact converted
  | natural => exact .refl _
  | arrow A B ha hb =>
    exact .node (.pi false) (.cons (ha converted) (.cons (hb (converted.renaming Nat.succ closed)) .nil))

/-- Actual closed-code conversion may identify different open monotype
skeletons. Coherence here uses their constructed code values after closing,
so it does not assume that open skeleton injectivity survives substitution. -/
theorem CodeValue.instantiated_coherent (wf : UnifiedProgram.EnvWellFormed env) (A B : Mono)
    (first : CodeValue env code) (second : CodeValue env replacement)
    (converted : Conv env (A.instantiate code) (B.instantiate replacement)) :
    A.code first.source.Meaning = B.code second.source.Meaning := by
  apply Mono.closed_code_coherent wf A B first.source second.source
  exact .trans (.symm (A.instantiate_conversion wf.closed first.converted))
    (.trans converted (B.instantiate_conversion wf.closed second.converted))

/-- Universe application to a generated type code constructs both actual
typing and semantic realization; no membership of the application is given. -/
theorem universe_source_application (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env [] mode term type) (recognized : UniverseRecognized term)
    (source : Functions.SimpleType) :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ 0) expression.syntax = term ∧
      HasType env [] true (.app term source.syntax) (A.instantiate source.syntax) ∧
      Realizes (CodeValue.sourceCode (env := env) source).parameter A (.app term source.syntax)
        (expression.meaning (carrier := source.Meaning) .nil) := by
  obtain ⟨A,expression,erased,converted,model,realizes⟩ := universe_fundamental wf typed recognized
  have functionTyped := typed.ghost.convert (.symm converted)
  have applied : HasType env [] true (.app term source.syntax) ((A.syntax 0).subst (single source.syntax)) :=
    HasType.app (B := A.syntax 0) functionTyped source.formed (Or.inl rfl)
  rw [Mono.syntax_zero_instantiate] at applied
  exact ⟨A,expression,erased,applied,realizes _ _⟩

end Jihoo.NativeKernel.Environment.Semantics.UniverseContext
