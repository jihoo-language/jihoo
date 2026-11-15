import Jihoo.NativeUniverseLevelModel

/-! Actual-source reconstruction and universe abstraction at every native
input level0..31. Source realization is constructed from HasType and syntax;
no same-term membership, normalization, or raw regularity principle is assumed. -/
namespace Jihoo.NativeKernel.Environment.Semantics.UniverseContext
open Jihoo.NativeKernel.Environment.Conversion

def contextAt (level : Nat) : List Mono → Context
  | [] => [⟨.univ level,false⟩]
  | A :: Γ => ⟨A.syntax Γ.length,false⟩ :: contextAt level Γ

def ValueContext (Γ : List Mono) (ctx : Context) : Prop :=
  ∀ {A index} (_member : Member A Γ index), NativeKernel.lookup ctx index = some ⟨A.syntax Γ.length,false⟩

theorem ValueContext.extend (agreement : ValueContext Γ ctx) (domain : Mono) :
    ValueContext (domain :: Γ) (⟨domain.syntax Γ.length,false⟩ :: ctx) := by
  intro A index member
  cases member with
  | here => simp only [NativeKernel.lookup,Mono.syntax_shift,List.length_cons]
  | there previous =>
    simp only [NativeKernel.lookup,agreement previous,Option.map,Mono.syntax_shift,List.length_cons]

theorem contextAt_values (level : Nat) (Γ : List Mono) : ValueContext Γ (contextAt level Γ) := by
  induction Γ with
  | nil => intro A index member; cases member
  | cons A Γ ih => exact ih.extend A

theorem contextAt_parameter (level : Nat) (Γ : List Mono) :
    NativeKernel.lookup (contextAt level Γ) Γ.length = some ⟨.univ level,false⟩ := by
  induction Γ with
  | nil => simp only [contextAt,List.length_nil,NativeKernel.lookup,Term.univ,Term.rename,renameArgs]
  | cons A Γ ih =>
    change (NativeKernel.lookup (contextAt level Γ) Γ.length).map _ = _
    rw [ih]
    simp only [Option.map,Term.univ,Term.rename,renameArgs]

theorem Mono.formed_at (A : Mono) (level : Nat) :
    HasType env (contextAt level Γ) mode (A.syntax Γ.length) (.univ (A.nativeLevel level)) := by
  induction A generalizing Γ mode with
  | parameter => exact .var (contextAt_parameter _ _) (Or.inr rfl)
  | natural => exact .u64
  | arrow A B ha hb =>
    rw [Mono.syntax_arrow]
    exact .pi (s := .type (A.nativeLevel level)) (r := .type (B.nativeLevel level))
      (.intro (ha (mode := true)) (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h)))
      (hb (Γ := A :: Γ) (mode := true))

theorem Expression.typed_at (expression : Expression Γ A) (level : Nat) :
    HasType env (contextAt level Γ) true expression.syntax (A.syntax Γ.length) := by
  induction expression with
  | var member => exact .var (contextAt_values _ _ member) (Or.inl rfl)
  | natural value bound => exact .natural bound
  | @lam A Γ B body ih =>
    rw [Mono.syntax_arrow]
    exact .lam (.intro (s := .type (A.nativeLevel level)) (A.formed_at level)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih
  | @app Γ A B function argument ihf iha =>
    have functionTyped : HasType env (contextAt level Γ) true function.syntax
        (.pi false (A.syntax Γ.length) (B.syntax (Γ.length+1))) := by
      simpa only [Mono.syntax_arrow] using ihf
    change HasType env (contextAt level Γ) true (.app function.syntax argument.syntax) (B.syntax Γ.length)
    rw [←Mono.syntax_instantiate B Γ.length argument.syntax]
    exact HasType.app (B := B.syntax (Γ.length+1)) functionTyped iha (Or.inl rfl)

/-- This reusable reconstruction premise is an exact native lookup fact for
value variables. In the universe theorem it is proved by contextAt_values. -/
theorem recognized_in_value_context (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized depth term) :
    ∀ (Γ : List Mono), Γ.length = depth → ∀ {ctx mode type}, ValueContext Γ ctx →
      HasType env ctx mode term type →
      ∃ A, ∃ expression : Expression Γ A, expression.syntax = term ∧ Conv env (A.syntax Γ.length) type := by
  induction recognized with
  | var bound =>
    intro Γ length ctx mode type agreement typed
    cases length
    obtain ⟨A,member⟩ := Member.at Γ _ bound
    obtain ⟨binding,found,converted⟩ := typed.principalView
    rw [agreement member] at found
    cases found
    exact ⟨A,.var member,rfl,converted⟩
  | natural value =>
    intro Γ length ctx mode type agreement typed
    obtain ⟨bound,converted⟩ := typed.naturalView
    exact ⟨.natural,.natural value bound,rfl,converted⟩
  | lam domain recognized ih =>
    intro Γ length ctx mode type agreement typed
    cases length
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨B,bodyExpression,erased,bodyConversion⟩ := ih (domain :: Γ) rfl (agreement.extend domain) bodyTyped
    refine ⟨.arrow domain B,.lam bodyExpression,?_,?_⟩
    · simp only [Expression.syntax,erased]
    · rw [Mono.syntax_arrow]
      exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConversion .nil))) converted
  | app recognizedFunction recognizedArgument ihf iha =>
    intro Γ length ctx mode type agreement typed
    obtain ⟨erased,domain,codomain,functionTyped,argumentTyped,allowed,resultConverted⟩ := typed.appView
    obtain ⟨F,functionExpression,functionErasure,functionConverted⟩ := ihf Γ length agreement functionTyped
    cases F with
    | parameter => exact False.elim (FamilyIota.Extended.Conv.full_variable_node_separate rfl functionConverted wf.admissible)
    | natural => exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .u64) (op' := .pi erased) rfl rfl (by intro h; cases h) functionConverted wf.admissible)
    | arrow A B =>
      rw [Mono.syntax_arrow] at functionConverted
      have components := functionConverted.pi_injective wf.admissible
      obtain ⟨C,argumentExpression,argumentErasure,argumentConverted⟩ := iha Γ length agreement argumentTyped
      have same : C = A := Mono.syntax_injective wf (.trans argumentConverted (.symm components.2.1))
      subst C
      refine ⟨B,.app functionExpression argumentExpression,?_,?_⟩
      · simp only [Expression.syntax,functionErasure,argumentErasure]
      · have result := components.2.2.substitution (single argumentExpression.syntax) wf.closed
        rw [Mono.syntax_instantiate,argumentErasure] at result
        exact .trans result resultConverted

def polyTypeAt (level : Fin 32) (A : Mono) : Term := .pi false (.univ level.val) (A.syntax 0)

theorem Expression.polyTypedAt (level : Fin 32) (expression : Expression [] A) :
    HasType env [] true (.lam false (.univ level.val) expression.syntax) (polyTypeAt level A) :=
  .lam (.intro (s := .type (level.val+1)) (.univ level.isLt)
    (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) (expression.typed_at level.val)

theorem polyTypeAt_formed (level : Fin 32) (A : Mono) :
    HasType env [] mode (polyTypeAt level A) (.univ (level.val+1)) := by
  have formed : HasType env [] mode (polyTypeAt level A)
      (.univ (max (level.val+1) (A.nativeLevel level.val))) :=
    .pi (s := .type (level.val+1)) (r := .type (A.nativeLevel level.val))
      (.intro (.univ level.isLt) (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h)))
      (A.formed_at (Γ := []) (mode := true) level.val)
  have bound : A.nativeLevel level.val ≤ level.val+1 := Nat.le_trans (A.nativeLevel_bound _) (Nat.le_succ _)
  rw [Nat.max_eq_left bound] at formed
  exact formed

theorem polyTypeAt_model_coherent (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 32) {A B : Mono}
    (converted : Conv env (polyTypeAt level A) (polyTypeAt level B)) : HEq (polyCodeAt level A) (polyCodeAt level B) := by
  have same := Mono.syntax_injective wf (converted.pi_injective wf.admissible).2.2
  cases same
  rfl

inductive UniverseRecognizedAt (level : Fin 32) : Term → Prop where
  | lam : Recognized 0 body → UniverseRecognizedAt level (.lam false (.univ level.val) body)

theorem universe_fundamental_at (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 32)
    (typed : HasType env [] mode term type) (recognized : UniverseRecognizedAt level term) :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ level.val) expression.syntax = term ∧ Conv env (polyTypeAt level A) type ∧
      Nonempty (Finite.Carrier (polyCodeAt level A)) := by
  cases recognized with
  | lam bodyRecognized =>
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨A,expression,erased,bodyConversion⟩ :=
      recognized_in_value_context wf bodyRecognized [] rfl (contextAt_values level.val []) bodyTyped
    refine ⟨A,expression,?_,?_,⟨expression.polyInterpretAt level⟩⟩
    · rw [erased]
    · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConversion .nil))) converted

theorem checked_universe_fundamental_at
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env) (level : Fin 32)
    (typed : HasType env [] mode term type) (recognized : UniverseRecognizedAt level term) :
    ∃ A, ∃ expression : Expression [] A,
      .lam false (.univ level.val) expression.syntax = term ∧ Conv env (polyTypeAt level A) type ∧
      Nonempty (Finite.Carrier (polyCodeAt level A)) :=
  universe_fundamental_at history.wellFormed level typed recognized

/-- A universe-level consistency consequence of the actual-source fundamental.
No caller-supplied model membership or normalization premise is present. -/
theorem no_recognized_polymorphic_bottom (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 32)
    (typed : HasType env [] mode term (polyTypeAt level .parameter))
    (recognized : UniverseRecognizedAt level term) : False := by
  obtain ⟨A,expression,erased,converted,model⟩ := universe_fundamental_at wf level typed recognized
  have same : A = .parameter := Mono.syntax_injective wf (converted.pi_injective wf.admissible).2.2
  subst A
  exact polyCodeAt_bottom_uninhabited level model

end Jihoo.NativeKernel.Environment.Semantics.UniverseContext
