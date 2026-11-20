import Jihoo.NativeCoreTypedEqual

/-! The common ghost inference result, exact comparison receipt and typed
type requirement used by application and dependent constructor walks. -/
namespace Jihoo.NativeKernel.NativeCoreGhostSpineInference

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreCompare (FullyRetained)
open EnvironmentDelta (expand)

structure Inferred where
  typeRoot : Nat
  compared : List (Nat × Nat)
  deriving Repr

abbrev Visit := State → Nat → Outcome Nat
abbrev Infer := State → Nat → Outcome Inferred
private def discard (state : State) (root : Nat) : Outcome α :=
  ⟨state, .error (.outsideFragment root)⟩

/-- Core.require normalizes the inferred argument type, then the expected
domain, and uses identity on their live roots. The original argument
reference, not either type root, is later substituted into the codomain. -/
def requireTypes (normal : Visit) (limit depth : Nat) (state : State)
    (actual expected argument : Nat) : Outcome (Nat × Nat) :=
  (normal state actual).next fun afterLeft left =>
    (normal afterLeft expected).next fun afterRight right =>
      (NativeCoreTypedEqual.identify limit depth afterRight left right).next fun afterIdentity same =>
        if same then ⟨afterIdentity, .ok (left, right)⟩ else discard afterIdentity argument

theorem next_progress {before : Outcome α} {later : State → α → Outcome β}
    (prior : Progress limit state before) (room : state.steps ≤ limit)
    (following : ∀ value, before.result = .ok value → before.state.steps ≤ limit →
      Progress limit before.state (later before.state value)) :
    Progress limit state (before.next later) := by
  cases found : before.result with
  | error reason =>
      simp only [Outcome.next, found]
      exact ⟨prior.kept, prior.monotone, prior.bounded, fun _ _ impossible => by cases impossible⟩
  | ok value =>
      have within := prior.accepted room value found
      have after := following value found within
      simp only [Outcome.next, found]
      exact ⟨prior.kept.trans after.kept, Nat.le_trans prior.monotone after.monotone,
        fun _ => after.bounded within, fun _ output done => after.accepted within output done⟩

private theorem identify_progress (room : state.steps ≤ limit) :
    Progress limit state (NativeCoreTypedEqual.identify limit depth state left right) := by
  have bounds := NativeCoreIdentical.runArena_step_bounds (arena := state.arena)
    (depth := depth) (a := left) (b := right) room
  generalize found : NativeCoreIdentical.runArena state.arena limit depth state.steps left right = outcome at bounds ⊢
  rcases outcome with ⟨result, spent⟩
  simp only [NativeCoreTypedEqual.identify, found]
  refine ⟨.refl _, bounds.1, fun _ => bounds.2.1, fun _ value success => ?_⟩
  cases result with
  | error reason => simp [Except.mapError] at success
  | ok answer =>
      have found : answer = value := Except.ok.inj (by simpa only [Except.mapError] using success)
      exact bounds.2.2 value (congrArg Except.ok found)

theorem requireTypes_progress
    (metered : ∀ state root, state.steps ≤ limit → Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (requireTypes normal limit depth state actual expected argument) := by
  apply next_progress (metered _ _ room) room
  intro left _ leftRoom
  apply next_progress (metered _ _ leftRoom) leftRoom
  intro right _ rightRoom
  apply next_progress (identify_progress rightRoom) rightRoom
  intro same _ _
  cases same <;> exact Progress.atState _ _

def PairRetained (arena : Arena) (pair : Nat × Nat) : Prop :=
  ∃ first second, Represents arena pair.1 first ∧ Represents arena pair.2 second ∧
    FullyRetained first ∧ FullyRetained second

def RetainedComparisons (arena : Arena) (answer : Inferred) : Prop :=
  ∀ pair ∈ answer.compared, PairRetained arena pair

private theorem identify_true
    (left : Represents state.arena a first) (right : Represents state.arena b second)
    (success : (NativeCoreTypedEqual.identify limit depth state a b).result = .ok true) :
    (NativeCoreTypedEqual.identify limit depth state a b).state.arena = state.arena ∧
      NativeCoreCompare.project first = NativeCoreCompare.project second := by
  rcases compared : NativeCoreIdentical.runArena state.arena limit depth state.steps a b with ⟨result, steps⟩
  cases result with
  | error reason => simp [NativeCoreTypedEqual.identify, compared, Except.mapError] at success
  | ok flag =>
      simp [NativeCoreTypedEqual.identify, compared, Except.mapError] at success
      subst flag
      exact ⟨by simp [NativeCoreTypedEqual.identify, compared],
        (NativeCoreIdentical.runArena_refines left right compared).mp rfl⟩

/-- Retention is evidence about the actual two comparison outcomes.
Full syntax equality reflects their projected identity, and the normalizer
supplies conversion from each original type to its corresponding outcome. -/
theorem requireTypes_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (leftRep : Represents state.arena actual actualType) (rightRep : Represents state.arena expected expectedType)
    (success : (requireTypes normal limit depth state actual expected argument).result = .ok pair)
    (ambient : Prefix (requireTypes normal limit depth state actual expected argument).state.arena final)
    (retained : PairRetained final pair) :
    let output := requireTypes normal limit depth state actual expected argument
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      LoanTyping.Conversion.Conv env (expand env actualType) (expand env expectedType) := by
  unfold requireTypes at success ambient ⊢
  obtain ⟨a, firstOk, firstNext⟩ := Outcome.next_success success
  obtain ⟨firstKept, firstBack, first, firstRep, firstChange⟩ := normalSound onBase leftRep firstOk
  rw [firstNext] at success ambient ⊢
  obtain ⟨b, secondOk, secondNext⟩ := Outcome.next_success success
  obtain ⟨secondKept, secondBack, second, secondRep, secondChange⟩ :=
    normalSound (onBase.trans firstKept) (rightRep.frame firstKept) secondOk
  rw [secondNext] at success ambient ⊢
  obtain ⟨flag, identical, identityNext⟩ := Outcome.next_success success
  rw [identityNext] at success ambient ⊢
  cases flag with
  | false => simp [discard] at success
  | true =>
      simp at success
      subst pair
      have firstFinal := firstRep.frame secondKept
      obtain ⟨unchanged, same⟩ := identify_true firstFinal secondRep identical
      simp [unchanged] at ambient ⊢
      obtain ⟨left, right, leftRep, rightRep, leftKept, rightKept⟩ := retained
      have sameLeft := (firstFinal.frame ambient).unique leftRep
      have sameRight := (secondRep.frame ambient).unique rightRep
      have syntactic : first = second := NativeCoreCompare.project_injective_of_fully_retained
        (sameLeft.symm ▸ leftKept) (sameRight.symm ▸ rightKept) same
      refine ⟨firstKept.trans secondKept, secondBack ∘ firstBack, ?_⟩
      have converted : LoanTyping.Conversion.Conv env (expand env actualType) (expand env first) :=
        firstChange.converted
      rw [syntactic] at converted
      exact converted.trans secondChange.converted.symm

structure Refines (env : Environment) (arena : Arena) (ctx : Context) (source : Term)
    (outcome : Outcome Inferred) (answer : Inferred) : Prop where
  kept : Prefix arena outcome.state.arena
  backward : Backward arena → Backward outcome.state.arena
  inferred : ∃ type, Represents outcome.state.arena answer.typeRoot type ∧
    LoanTyping.HasType env [] ctx true (expand env source) (expand env type)

def InferSound (env : Environment) (base : Arena) (ctx : Context) (limit : Nat) (visit : Infer) : Prop :=
  ∀ {state root term answer final}, Prefix base state.arena → state.steps ≤ limit → Represents state.arena root term →
    (visit state root).result = .ok answer → Prefix (visit state root).state.arena final →
    RetainedComparisons final answer → Refines env state.arena ctx term (visit state root) answer

end Jihoo.NativeKernel.NativeCoreGhostSpineInference
