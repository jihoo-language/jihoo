import Jihoo.NativeCoreIterationReentry

/-! Contexts whose typing premises can be transported at their original
types even when a pure value contraction is outside RawLend conversion. -/
namespace Jihoo.NativeKernel.NativeCoreValueContexts

open Environment
open NativeKernel.Conversion (ListRel)

/-- Evidence of exact source-type preservation for both the represented
syntax and the syntax obtained by expanding checked globals. -/
structure Change (env : Environment) (source result : Term) : Prop where
  raw : ∀ {ctx type}, LoanTyping.HasType env [] ctx true source type →
    LoanTyping.HasType env [] ctx true result type
  expanded : ∀ {ctx type}, LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env source) type →
    LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env result) type

theorem Change.trans (first : Change env a b) (second : Change env b c) : Change env a c :=
  ⟨fun typed => second.raw (first.raw typed), fun typed => second.expanded (first.expanded typed)⟩

theorem Change.iteration (step : NativeCoreIterationNormal.Change env a b) : Change env a b :=
  ⟨step.preserves, step.preservesExpanded⟩

theorem Change.discard : Change env (.strict a b) b := by
  constructor
  · exact LoanTyping.value_root_ghost_preservation (.strict a b)
  · simp only [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs]
    exact LoanTyping.value_root_ghost_preservation (.strict _ _)

private def StrictEffect (env : Environment) (ctx : Context) : Term → Prop
  | .strict first _ => ∃ A, LoanTyping.HasType env [] ctx true first A
  | _ => True

private theorem strict_effect (typed : LoanTyping.HasType env loans ctx mode term type) :
    StrictEffect env ctx term := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term _ _ => StrictEffect env ctx term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case strict first _ _ _ => exact ⟨_, first.ghost []⟩
  case dataElim => split <;> trivial

theorem strict_effect_typing (typed : LoanTyping.HasType env loans ctx mode (.strict effect value) type) :
    ∃ A, LoanTyping.HasType env [] ctx true effect A :=
  strict_effect typed

theorem Change.strict (first : Change env a a') (rest : Change env b b') :
    Change env (.strict a b) (.strict a' b') := by
  have rebuild {a b a' b' : Term}
      (first : ∀ {ctx type}, LoanTyping.HasType env [] ctx true a type → LoanTyping.HasType env [] ctx true a' type)
      (rest : ∀ {ctx type}, LoanTyping.HasType env [] ctx true b type → LoanTyping.HasType env [] ctx true b' type)
      {ctx type} (typed : LoanTyping.HasType env [] ctx true (.strict a b) type) :
      LoanTyping.HasType env [] ctx true (.strict a' b') type := by
    obtain ⟨_, effect⟩ := strict_effect_typing typed
    obtain ⟨_, result, converted⟩ := typed.principalView
    exact .strict (first effect) (rest (result.convert converted))
  refine ⟨rebuild first.raw rest.raw, ?_⟩
  simp only [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs]
  exact rebuild first.expanded rest.expanded

/-- Every child of these constructors is checked at the same specified
type. The result depends only on the constructor, including the declared
number of Elements. -/
def signature : Op → Option (Term × Term)
  | .array | .buffer => some (.u64, .univ 0)
  | .eq | .lt => some (.u64, .prop)
  | .arith _ => some (.i64, .i64)
  | .elements size => some (.i64, .array (.natural size))
  | .refine => some (.pi false .u64 .prop, .univ 0)
  | _ => none

private def PayloadValid : Op → Prop
  | .elements size => size < 2^64
  | _ => True

private def Premises (env : Environment) (ctx : Context) : Term → Term → Prop
  | .var _, _ => True
  | .node op xs, type =>
      match signature op with
      | none => True
      | some (arg, principal) => xs.length = op.arity ∧ PayloadValid op ∧
          (∀ operand ∈ xs, LoanTyping.HasType env [] ctx true operand arg) ∧
          LoanTyping.Conversion.Conv env principal type

private theorem Premises.convert (premises : Premises env ctx term original)
    (converted : LoanTyping.Conversion.Conv env original result) : Premises env ctx term result := by
  cases term with
  | var => trivial
  | node op args =>
      cases identified : signature op with
      | none => simp only [Premises, identified]
      | some pair =>
          cases pair
          simp only [Premises, identified] at premises ⊢
          exact ⟨premises.1, premises.2.1, premises.2.2.1, premises.2.2.2.trans converted⟩

private theorem premises (typed : LoanTyping.HasType env loans ctx mode term type) :
    Premises env ctx term type := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => Premises env ctx term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case dataElim => split <;> trivial
  case convert => exact Premises.convert (by assumption) (by assumption)
  case array typed _ =>
    exact ⟨rfl, trivial, by simpa using typed.ghost [], .refl _⟩
  case buffer typed _ =>
    exact ⟨rfl, trivial, by simpa using typed.ghost [], .refl _⟩
  case refine typed _ =>
    exact ⟨rfl, trivial, by simpa using typed.ghost [], .refl _⟩
  case lt first second _ _ =>
    exact ⟨rfl, trivial, by simpa using And.intro (first.ghost []) (second.ghost []), .refl _⟩
  case eq first second _ _ =>
    exact ⟨rfl, trivial, by simpa using And.intro (first.ghost []) (second.ghost []), .refl _⟩
  case arith first second _ _ =>
    exact ⟨rfl, trivial, by simpa using And.intro (first.ghost []) (second.ghost []), .refl _⟩
  case elements size bounded typed _ =>
    simp only [Premises, signature, PayloadValid, Op.arity]
    refine ⟨size, size ▸ bounded, fun x found => (typed x found).ghost [], ?_⟩
    rw [size]
    exact .refl _

private theorem form (found : signature op = some (arg, principal)) (arity : xs.length = op.arity)
    (valid : PayloadValid op) (operands : ∀ operand ∈ xs, LoanTyping.HasType env [] ctx true operand arg) :
    LoanTyping.HasType env [] ctx true (.node op xs) principal := by
  cases op <;> try contradiction
  case elements size =>
    cases found
    have count : xs.length = size := arity
    have typed := LoanTyping.HasType.elements (ghost := true) (loans := []) count
      (show xs.length < 2^64 from count.symm ▸ valid) operands
    rw [count] at typed
    exact typed
  all_goals cases found
  all_goals
    rcases xs with _ | ⟨first, rest⟩
    · cases arity
    · cases rest with
      | nil =>
          first
          | exact .array (operands first (by simp))
          | exact .buffer (operands first (by simp))
          | exact .refine (operands first (by simp))
          | cases arity
      | cons second rest =>
          cases rest with
          | nil =>
              first
              | exact .lt (operands first (by simp)) (operands second (by simp))
              | exact .eq (operands first (by simp)) (operands second (by simp))
              | exact .arith (operands first (by simp)) (operands second (by simp))
              | cases arity
          | cons => cases arity

private theorem move_operands {rel : Term → Term → Prop}
    (moves : ListRel rel xs ys) (profiles : ∀ a b, rel a b →
      LoanTyping.HasType env [] ctx true a arg → LoanTyping.HasType env [] ctx true b arg)
    (premises : ∀ a ∈ xs, LoanTyping.HasType env [] ctx true a arg) :
    ys.length = xs.length ∧ ∀ b ∈ ys, LoanTyping.HasType env [] ctx true b arg := by
  induction moves with
  | nil => exact ⟨rfl, by simp⟩
  | @cons x y xs ys first _ ih =>
      obtain ⟨equal, tail⟩ := ih (fun a found => premises a (List.mem_cons_of_mem _ found))
      refine ⟨congrArg Nat.succ equal, ?_⟩
      intro b included
      rcases List.mem_cons.mp included with rfl | included
      · exact profiles x _ first (premises x (by simp))
      · exact tail b included

private theorem signature_ordinary (read : signature op = some pair) :
    GlobalEnvironment.ordinary op = true := by
  cases op <;> first | rfl | contradiction

private theorem rebuild_uniform (found : signature op = some (arg, principal))
    (moves : ListRel rel xs ys) (profiles : ∀ {ctx} a b, rel a b →
      LoanTyping.HasType env [] ctx true a arg → LoanTyping.HasType env [] ctx true b arg)
    (typed : LoanTyping.HasType env [] ctx true (.node op xs) type) :
    LoanTyping.HasType env [] ctx true (.node op ys) type := by
  have inputs := premises typed
  simp only [Premises, found] at inputs
  obtain ⟨size, valid, before, converted⟩ := inputs
  obtain ⟨equal, after⟩ := move_operands moves profiles before
  exact (form found (equal.trans size) valid after).convert converted

private theorem expanded_list (moves : ListRel (Change env) xs ys) :
    ListRel (fun a b => ∀ {ctx type}, LoanTyping.HasType env [] ctx true a type →
      LoanTyping.HasType env [] ctx true b type) (EnvironmentDelta.expandArgs env xs)
      (EnvironmentDelta.expandArgs env ys) := by
  induction moves with
  | nil => simpa only [EnvironmentDelta.expandArgs] using ListRel.nil
  | cons first _ rest =>
      simp only [EnvironmentDelta.expandArgs]
      exact .cons (fun typed => first.expanded typed) rest

/-- Every well-typed covered parent is rebuilt at the original type from
its real typing premises. Child changes need no conversion hypothesis. -/
theorem Change.uniform (found : signature op = some inputs) (moves : ListRel (Change env) xs ys) :
    Change env (.node op xs) (.node op ys) := by
  cases inputs with
  | mk arg principal =>
      refine ⟨rebuild_uniform found moves (fun _ _ change => change.raw), ?_⟩
      rw [EnvironmentDelta.expand_ordinary (signature_ordinary found),
        EnvironmentDelta.expand_ordinary (signature_ordinary found)]
      exact rebuild_uniform found (expanded_list moves) (fun _ _ change => change)

end Jihoo.NativeKernel.NativeCoreValueContexts
