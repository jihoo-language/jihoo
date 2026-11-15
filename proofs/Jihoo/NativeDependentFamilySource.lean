import Jihoo.NativeDependentFamilyContexts
set_option maxUniverseOffset 40

/-! Actual native source reconstruction in dependent family contexts. Ordinary
observations may be used as program values as well as in family indices. The
fundamental constructs a concrete contextual value from HasType and syntax. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
open Jihoo.NativeKernel.Environment.Conversion
open MultiUniverse (Mono)
variable {parameters familyCount observationCount : Nat} {levels : Fin parameters → Fin 32}
variable {signatures : Fin familyCount → Signature parameters} {observed : Fin observationCount → Mono parameters}

inductive Values (assignment : Assignment levels signatures observed) :
    List (TypeCode parameters familyCount observationCount) → Type 34 where
  | nil : Values assignment []
  | cons (valid : A.Valid signatures observed) :
      Finite.Carrier (A.meaning assignment valid) → Values assignment Γ → Values assignment (A :: Γ)

def Slot.value {A : TypeCode parameters familyCount observationCount}
    {Γ : List (TypeCode parameters familyCount observationCount)} {assignment : Assignment levels signatures observed}
    (slot : Slot A Γ index) (values : Values assignment Γ) (valid : A.Valid signatures observed) :
    Finite.Carrier (A.meaning assignment valid) :=
  match slot,values with
  | .here,.cons _ value _ => value
  | .there previous,.cons _ _ rest => previous.value rest valid

inductive Expression (signatures : Fin familyCount → Signature parameters)
    (observed : Fin observationCount → Mono parameters) :
    List (TypeCode parameters familyCount observationCount) → TypeCode parameters familyCount observationCount → Type where
  | var : Slot A Γ index → A.Valid signatures observed → Expression signatures observed Γ A
  | observation (index : Fin observationCount) : Expression signatures observed Γ (TypeCode.ofMono (observed index))
  | natural (value : Nat) (bound : value < 2^64) : Expression signatures observed Γ .natural
  | lam : A.Valid signatures observed → Expression signatures observed (A :: Γ) B → Expression signatures observed Γ (.arrow A B)
  | app : Expression signatures observed Γ (.arrow A B) → Expression signatures observed Γ A → Expression signatures observed Γ B

theorem Expression.valid : Expression signatures observed Γ A → A.Valid signatures observed
  | .var _ valid => valid
  | .observation index => TypeCode.ofMono_valid (observed index)
  | .natural _ _ => trivial
  | .lam valid body => ⟨valid,body.valid⟩
  | .app function _ => function.valid.2

def Expression.syntax : Expression signatures observed Γ A → Term
  | .var (index := index) _ _ => .var index
  | .observation (Γ := Γ) index => .var (Γ.length+index.val)
  | .natural value _ => .natural value
  | .lam (A := A) (Γ := Γ) _ body => .lam false (A.syntax Γ.length) body.syntax
  | .app function argument => .app function.syntax argument.syntax

def Expression.meaning {A : TypeCode parameters familyCount observationCount}
    {Γ : List (TypeCode parameters familyCount observationCount)} {assignment : Assignment levels signatures observed} :
    (expression : Expression signatures observed Γ A) → Values assignment Γ → Finite.Carrier (A.meaning assignment expression.valid)
  | .var slot valid,values => slot.value values valid
  | .observation index,_ => assignment.observationValue index
  | .natural value _,_ => ⟨value⟩
  | .lam (A := A) (B := B) valid body,values =>
    (Finite.piMeaning (A.meaning assignment valid) (B.sort levels signatures)
      (fun _ => B.meaning assignment body.valid)).lam (fun argument => body.meaning (.cons valid argument values))
  | .app (A := A) (B := B) function argument,values =>
    (Finite.piMeaning (A.meaning assignment argument.valid) (B.sort levels signatures)
      (fun _ => B.meaning assignment function.valid.2)).app (function.meaning values) (argument.meaning values)

theorem Expression.typed {familyList : List (Signature parameters)} {observations : List (Mono parameters)}
    {A : TypeCode parameters familyList.length observations.length}
    {Γ : List (TypeCode parameters familyList.length observations.length)}
    (expression : Expression familyList.get observations.get Γ A) :
    HasType env (context levels familyList observations Γ) true expression.syntax (A.syntax Γ.length) := by
  induction expression with
  | var slot valid => exact .var slot.value_lookup (Or.inl rfl)
  | @observation Γ index =>
    rw [TypeCode.ofMono_syntax]
    exact .var ((Slot.ofFin observations index).context_observation_lookup familyList Γ) (Or.inl rfl)
  | natural value bound => exact .natural bound
  | @lam A Γ B valid body ih =>
    rw [TypeCode.syntax_arrow]
    exact .lam (.intro (s := .type (A.level levels familyList.get)) (A.formed valid)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih
  | @app Γ A B function argument ihf iha =>
    have functionTyped : HasType env (context levels familyList observations Γ) true function.syntax
        (.pi false (A.syntax Γ.length) (B.syntax (Γ.length+1))) := by
      simpa only [TypeCode.syntax_arrow] using ihf
    change HasType env (context levels familyList observations Γ) true (.app function.syntax argument.syntax) (B.syntax Γ.length)
    rw [←TypeCode.syntax_instantiate B Γ.length argument.syntax]
    exact .app functionTyped iha (Or.inl rfl)

inductive Recognized (familyList : List (Signature parameters)) (observations : List (Mono parameters)) : Nat → Term → Prop where
  | var (bound : index < depth+observations.length) : Recognized familyList observations depth (.var index)
  | natural (value : Nat) : Recognized familyList observations depth (.natural value)
  | lam (domain : TypeCode parameters familyList.length observations.length) :
      Recognized familyList observations (depth+1) body →
      Recognized familyList observations depth (.lam false (domain.syntax depth) body)
  | app : Recognized familyList observations depth function → Recognized familyList observations depth argument →
      Recognized familyList observations depth (.app function argument)

theorem recognized_principal (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized familyList observations depth term) :
    ∀ (Γ : List (TypeCode parameters familyList.length observations.length)), Γ.length = depth →
      ContextValid familyList.get observations.get Γ → ∀ {mode type},
      HasType env (context levels familyList observations Γ) mode term type →
      ∃ A, ∃ expression : Expression familyList.get observations.get Γ A,
        expression.syntax = term ∧ Conv env (A.syntax Γ.length) type := by
  induction recognized with
  | @var index depth bound =>
    intro Γ length validΓ mode type typed
    cases length
    obtain ⟨binding,found,converted⟩ := typed.principalView
    by_cases isValue : index < Γ.length
    · let slot := Slot.ofFin Γ ⟨index,isValue⟩
      rw [slot.value_lookup] at found
      cases found
      exact ⟨_,.var slot (validΓ.slot slot),rfl,converted⟩
    · let observation : Fin observations.length := ⟨index-Γ.length,by omega⟩
      have same : Γ.length+observation.val = index := by dsimp only [observation]; omega
      have selected := (Slot.ofFin observations observation).context_observation_lookup (levels := levels) familyList Γ
      rw [same] at selected
      rw [selected] at found
      cases found
      refine ⟨TypeCode.ofMono (observations.get observation),.observation observation,?_,?_⟩
      · exact congrArg Term.var same
      · simpa only [TypeCode.ofMono_syntax] using converted
  | natural value =>
    intro Γ length validΓ mode type typed
    obtain ⟨bound,converted⟩ := typed.naturalView
    exact ⟨.natural,.natural value bound,rfl,converted⟩
  | lam domain recognized ih =>
    intro Γ length validΓ mode type typed
    cases length
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    have domainTyped := by cases binder with | intro formed allowed => exact formed
    have valid := domain.valid_of_typed wf domainTyped
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
    | fiber family observation =>
      exact False.elim (EnvironmentDelta.Basis.Conv.neutralSpine_node_separate
        (arguments := [.var (Γ.length+observation.val)]) wf.admissible rfl (by intro h; cases h) rfl functionConverted)

/-- Actual native HasType constructs a concrete contextual value for every
assignment of arbitrary carriers, dependent families and carrier observations. -/
theorem native_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (context levels familyList observations Γ) mode term type)
    (recognized : Recognized familyList observations Γ.length term)
    (validΓ : ContextValid familyList.get observations.get Γ) :
    ∃ A, ∃ expression : Expression familyList.get observations.get Γ A,
      expression.syntax = term ∧ Conv env (A.syntax Γ.length) type ∧
      ∀ assignment : Assignment levels familyList.get observations.get, ∀ _values : Values assignment Γ,
        Nonempty (Finite.Carrier (A.meaning assignment expression.valid)) := by
  obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized Γ rfl validΓ typed
  exact ⟨A,expression,erased,converted,fun assignment values => ⟨expression.meaning (assignment := assignment) values⟩⟩

theorem checked_fundamental
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env (context levels familyList observations Γ) mode term type)
    (recognized : Recognized familyList observations Γ.length term)
    (validΓ : ContextValid familyList.get observations.get Γ) :
    ∃ A, ∃ expression : Expression familyList.get observations.get Γ A,
      expression.syntax = term ∧ Conv env (A.syntax Γ.length) type ∧
      ∀ assignment : Assignment levels familyList.get observations.get, ∀ _values : Values assignment Γ,
        Nonempty (Finite.Carrier (A.meaning assignment expression.valid)) :=
  native_fundamental history.wellFormed typed recognized validΓ

end Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
