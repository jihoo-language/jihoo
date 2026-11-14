import Jihoo.NativeFunctionFundamental

/-! A concrete universe-variable context. Monotypes may contain the abstract
Type0 value, U64, and functions. The semantic carrier of the abstract type is
any host Type0, and its values carry an arbitrary conversion-saturated relation.
This is a contextual parameter assignment, not realization of the source being
proved. Closed universe abstractions quantify over every such assignment. -/
namespace Jihoo.NativeKernel.Environment.Semantics.UniverseContext
open Jihoo.NativeKernel.Environment.Conversion

inductive Mono where
  | parameter
  | natural
  | arrow (domain codomain : Mono)
  deriving DecidableEq, Repr

def Mono.instantiate (parameter : Term) : Mono → Term
  | .parameter => parameter
  | .natural => .u64
  | .arrow A B => .pi false (A.instantiate parameter) (B.instantiate (parameter.rename Nat.succ))

def Mono.syntax (position : Nat) (mono : Mono) : Term := mono.instantiate (.var position)

@[reducible] def Mono.Meaning (carrier : Type) : Mono → Type
  | .parameter => carrier
  | .natural => Nat
  | .arrow A B => A.Meaning carrier → B.Meaning carrier

def Mono.code (carrier : Type) (mono : Mono) : Finite.Universe (.type ⟨0,by decide⟩) :=
  .type0 (mono.Meaning carrier)

theorem Mono.code_arrow (carrier : Type) (A B : Mono) :
    (Mono.arrow A B).code carrier =
      Finite.pi (A.code carrier) (.type ⟨0,by decide⟩) (fun _ => B.code carrier) := rfl

theorem shift_rename (term : Term) (ρ : Nat → Nat) :
    (term.rename Nat.succ).rename (liftRenaming 1 ρ) = (term.rename ρ).rename Nat.succ := by
  rw [Term.rename_comp,Term.rename_comp]
  rfl

theorem shift_subst (term : Term) (σ : Nat → Term) :
    (term.rename Nat.succ).subst (liftSub 1 σ) = (term.subst σ).rename Nat.succ := by
  rw [Term.subst_rename,Term.rename_subst]
  rfl

theorem Mono.instantiate_rename (mono : Mono) (parameter : Term) (ρ : Nat → Nat) :
    (mono.instantiate parameter).rename ρ = mono.instantiate (parameter.rename ρ) := by
  induction mono generalizing parameter ρ with
  | parameter => rfl
  | natural => simp only [Mono.instantiate,Term.u64,Term.rename,renameArgs]
  | arrow A B ha hb =>
    simp only [Mono.instantiate,Term.pi,Term.rename,renameArgs,Op.binders]
    rw [ha,hb,shift_rename]
    rfl

theorem Mono.instantiate_subst (mono : Mono) (parameter : Term) (σ : Nat → Term) :
    (mono.instantiate parameter).subst σ = mono.instantiate (parameter.subst σ) := by
  induction mono generalizing parameter σ with
  | parameter => rfl
  | natural => simp only [Mono.instantiate,Term.u64,Term.subst,substArgs]
  | arrow A B ha hb =>
    simp only [Mono.instantiate,Term.pi,Term.subst,substArgs,Op.binders]
    rw [ha,hb,shift_subst]
    rfl

theorem Mono.syntax_shift (mono : Mono) (position : Nat) :
    (mono.syntax position).rename Nat.succ = mono.syntax (position+1) := by
  rw [Mono.syntax,Mono.instantiate_rename]
  simp only [Term.rename]
  rfl

theorem Mono.syntax_instantiate (mono : Mono) (position : Nat) (argument : Term) :
    (mono.syntax (position+1)).subst (single argument) = mono.syntax position := by
  rw [Mono.syntax,Mono.instantiate_subst]
  simp only [Term.subst,NativeKernel.single]
  rfl

theorem Mono.syntax_arrow (A B : Mono) (position : Nat) :
    (Mono.arrow A B).syntax position = .pi false (A.syntax position) (B.syntax (position+1)) := by
  simp only [Mono.syntax,Mono.instantiate,Term.rename]

theorem Mono.syntax_injective (wf : UnifiedProgram.EnvWellFormed env) {A B : Mono}
    (converted : Conv env (A.syntax position) (B.syntax position)) : A = B := by
  induction A generalizing B position with
  | parameter =>
    cases B with
    | parameter => rfl
    | natural => exact False.elim (EnvironmentDelta.Basis.Conv.full_variable_node_separate rfl converted wf.admissible)
    | arrow B C => exact False.elim (EnvironmentDelta.Basis.Conv.full_variable_node_separate rfl converted wf.admissible)
  | natural =>
    cases B with
    | parameter => exact False.elim (EnvironmentDelta.Basis.Conv.full_variable_node_separate rfl (.symm converted) wf.admissible)
    | natural => rfl
    | arrow B C => exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .u64) (op' := .pi false) rfl rfl (by intro h; cases h) converted wf.admissible)
  | arrow A C ha hc =>
    cases B with
    | parameter => exact False.elim (EnvironmentDelta.Basis.Conv.full_variable_node_separate rfl (.symm converted) wf.admissible)
    | natural => exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .pi false) (op' := .u64) rfl rfl (by intro h; cases h) converted wf.admissible)
    | arrow B D =>
      rw [Mono.syntax_arrow,Mono.syntax_arrow] at converted
      have parts := converted.pi_injective wf.admissible
      cases ha parts.2.1
      cases hc parts.2.2
      rfl

theorem Mono.code_coherent (wf : UnifiedProgram.EnvWellFormed env) {A B : Mono}
    (converted : Conv env (A.syntax position) (B.syntax position)) (carrier : Type) :
    A.code carrier = B.code carrier := by
  cases Mono.syntax_injective wf converted
  rfl

def context : List Mono → Context
  | [] => [⟨.univ 0,false⟩]
  | A :: Γ => ⟨A.syntax Γ.length,false⟩ :: context Γ

theorem parameter_lookup (Γ : List Mono) :
    NativeKernel.lookup (context Γ) Γ.length = some ⟨.univ 0,false⟩ := by
  induction Γ with
  | nil => simp only [context,List.length_nil,NativeKernel.lookup,Term.univ,Term.rename,renameArgs]
  | cons A Γ ih =>
    change (NativeKernel.lookup (context Γ) Γ.length).map _ = _
    rw [ih]
    simp only [Option.map,Term.univ,Term.rename,renameArgs]

theorem Mono.formed (mono : Mono) : HasType env (context Γ) mode (mono.syntax Γ.length) (.univ 0) := by
  induction mono generalizing Γ mode with
  | parameter => exact .var (parameter_lookup _) (Or.inr rfl)
  | natural => exact .u64
  | arrow A B ha hb =>
    rw [Mono.syntax_arrow]
    exact .pi (s := .type 0) (r := .type 0)
      (.intro (ha (mode := true)) (Or.inl (by change SortTag.type 0 ≠ SortTag.prop; intro h; cases h)))
      (hb (Γ := A :: Γ) (mode := true))

inductive Member : Mono → List Mono → Nat → Type where
  | here : Member A (A :: Γ) 0
  | there : Member A Γ i → Member A (B :: Γ) (i+1)

theorem Member.lookup (member : Member A Γ i) :
    NativeKernel.lookup (context Γ) i = some ⟨A.syntax Γ.length,false⟩ := by
  induction member with
  | here => simp only [context,NativeKernel.lookup,Mono.syntax_shift,List.length_cons]
  | there previous ih =>
    change (NativeKernel.lookup (context _) _).map _ = _
    rw [ih]
    simp only [Option.map,Mono.syntax_shift,List.length_cons]

def Member.at (Γ : List Mono) (index : Nat) (bound : index < Γ.length) : (A : Mono) × Member A Γ index :=
  match Γ,index with
  | [],_ => by simp at bound
  | A :: _,0 => ⟨A,.here⟩
  | _ :: Γ,index+1 =>
    let ⟨A,member⟩ := Member.at Γ index (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using bound)
    ⟨A,.there member⟩

inductive Values (carrier : Type) : List Mono → Type where
  | nil : Values carrier []
  | cons : A.Meaning carrier → Values carrier Γ → Values carrier (A :: Γ)

def Member.value (member : Member A Γ i) (values : Values carrier Γ) : A.Meaning carrier :=
  match member, values with
  | .here, .cons value _ => value
  | .there previous, .cons _ rest => previous.value rest

inductive Expression : List Mono → Mono → Type where
  | var : Member A Γ i → Expression Γ A
  | natural (value : Nat) (bound : value < 2^64) : Expression Γ .natural
  | lam : Expression (A :: Γ) B → Expression Γ (.arrow A B)
  | app : Expression Γ (.arrow A B) → Expression Γ A → Expression Γ B

def Expression.syntax : Expression Γ A → Term
  | .var (i := i) _ => .var i
  | .natural value _ => .natural value
  | .lam (A := A) (Γ := Γ) body => .lam false (A.syntax Γ.length) body.syntax
  | .app function argument => .app function.syntax argument.syntax

def Expression.meaning : Expression Γ A → Values carrier Γ → A.Meaning carrier
  | .var member, values => member.value values
  | .natural value _, _ => value
  | .lam body, values => fun argument => body.meaning (.cons argument values)
  | .app function argument, values => function.meaning values (argument.meaning values)

theorem Expression.typed (expression : Expression Γ A) :
    HasType env (context Γ) true expression.syntax (A.syntax Γ.length) := by
  induction expression with
  | var member => exact .var member.lookup (Or.inl rfl)
  | natural value bound => exact .natural bound
  | @lam A Γ B body ih =>
    rw [Mono.syntax_arrow]
    exact .lam (.intro (s := .type 0) A.formed
      (Or.inl (by change SortTag.type 0 ≠ SortTag.prop; intro h; cases h))) ih
  | @app Γ A B function argument ihf iha =>
    have functionTyped : HasType env (context Γ) true function.syntax
        (.pi false (A.syntax Γ.length) (B.syntax (Γ.length+1))) := by
      simpa only [Mono.syntax_arrow] using ihf
    change HasType env (context Γ) true (.app function.syntax argument.syntax) (B.syntax Γ.length)
    rw [←Mono.syntax_instantiate B Γ.length argument.syntax]
    exact HasType.app (B := B.syntax (Γ.length+1)) functionTyped iha (Or.inl rfl)

structure Parameter (env : Environment) where
  carrier : Type
  realizes : Term → carrier → Prop
  saturated : ∀ {term replacement}, Conv env term replacement →
    ∀ value, realizes term value ↔ realizes replacement value

def Realizes (parameter : Parameter env) : (A : Mono) → Term → A.Meaning parameter.carrier → Prop
  | .parameter, term, value => parameter.realizes term value
  | .natural, term, value => value < 2^64 ∧ Conv env term (.natural value)
  | .arrow A B, term, function =>
    ∀ argument value, Realizes parameter A argument value → Realizes parameter B (.app term argument) (function value)

theorem Realizes.conversion (parameter : Parameter env) (A : Mono) (converted : Conv env term replacement)
    (value : A.Meaning parameter.carrier) : Realizes parameter A term value ↔ Realizes parameter A replacement value := by
  induction A generalizing term replacement with
  | parameter => exact parameter.saturated converted value
  | natural =>
    constructor
    · rintro ⟨bound,proof⟩; exact ⟨bound,.trans (.symm converted) proof⟩
    · rintro ⟨bound,proof⟩; exact ⟨bound,.trans converted proof⟩
  | arrow A B ha hb =>
    constructor <;> intro proof argument admittedValue admitted
    · exact (hb (.node .app (.cons converted (.cons (.refl _) .nil))) _).mp (proof argument admittedValue admitted)
    · exact (hb (.node .app (.cons converted (.cons (.refl _) .nil))) _).mpr (proof argument admittedValue admitted)

def SubstitutionRealizes (parameter : Parameter env) (Γ : List Mono) (σ : Nat → Term)
    (values : Values parameter.carrier Γ) : Prop :=
  ∀ {A i} (member : Member A Γ i), Realizes parameter A (σ i) (member.value values)

theorem SubstitutionRealizes.extend (substitution : SubstitutionRealizes parameter Γ σ values)
    (argument : Realizes parameter A term value) :
    SubstitutionRealizes parameter (A :: Γ) (Functions.extendSubstitution σ term) (.cons value values) := by
  intro B i member
  cases member with
  | here => exact argument
  | there previous => exact substitution previous

theorem Expression.fundamental (expression : Expression Γ A) (parameter : Parameter env) {values : Values parameter.carrier Γ}
    (substitution : SubstitutionRealizes parameter Γ σ values) :
    Realizes parameter A (expression.syntax.subst σ) (expression.meaning values) := by
  induction expression generalizing σ with
  | var member => simpa only [Expression.syntax,Expression.meaning,Term.subst] using substitution member
  | natural value bound =>
    simpa only [Expression.syntax,Expression.meaning,Term.natural,Term.subst,substArgs] using
      (show Realizes parameter .natural (.natural value) value from ⟨bound,.refl _⟩)
  | @lam A Γ B body ih =>
    intro argument argumentValue admitted
    have realizes := ih (SubstitutionRealizes.extend substitution admitted)
    have beta : Conv env (.app ((Term.lam false (A.syntax Γ.length) body.syntax).subst σ) argument)
        (body.syntax.subst (Functions.extendSubstitution σ argument)) := by
      simp only [Term.lam,Term.subst,substArgs,Op.binders]
      exact .trans (.legacy (.beta false _ _ argument))
        (by rw [Functions.lifted_substitution_instantiation]; exact .refl _)
    exact (Realizes.conversion parameter B beta _).mpr realizes
  | app function argument ihf iha =>
    simpa only [Expression.syntax,Expression.meaning,Term.app,Term.subst,substArgs,Op.binders,liftSub] using
      ihf substitution _ _ (iha substitution)

end Jihoo.NativeKernel.Environment.Semantics.UniverseContext
