import Jihoo.NativeCorePureStructuralNormal

/-! The pure structural fragment of Core.equal normalizes the left root,
normalizes the right root in the resulting arena, and compares both returned
references in that live arena. All three share the checking counter. -/
namespace Jihoo.NativeKernel.NativeCorePureStructuralEqual

open NativeArena NativeProgramWire
open Environment.LoanTyping.MixedProgram (History)
open NativeCorePureStructuralNormal (runNested runNested_refines runNested_cost frameDefinitions)

inductive Error where
  | left (reason : NativeCorePureStructuralNormal.Error)
  | right (reason : NativeCorePureStructuralNormal.Error)
  | identity (reason : NativeCoreIdentical.Error)
  deriving Repr, DecidableEq

structure Outcome where
  arena : Arena
  result : Except Error Bool
  steps : Nat
  deriving Repr

/-- An error retains the arena and counter reached at the point of failure. -/
def run (arena : Arena) (roots : List Roots) (visible limit depth initial a b : Nat) : Outcome :=
  let left := runNested roots visible limit depth arena initial a
  match left.result with
  | .error reason => ⟨left.arena, .error (.left reason), left.steps⟩
  | .ok first =>
      let right := runNested roots visible limit depth left.arena left.steps b
      match right.result with
      | .error reason => ⟨right.arena, .error (.right reason), right.steps⟩
      | .ok second =>
          let (answer, steps) := NativeCoreIdentical.runArena right.arena limit depth right.steps first second
          ⟨right.arena, answer.mapError .identity, steps⟩

def Agrees (env : Environment) (arena : Arena) (first second : Term) (same : Bool) : Prop :=
  ∃ left right firstNormal secondNormal,
    Represents arena left firstNormal ∧ Represents arena right secondNormal ∧
    Environment.RawValue.Forward env first firstNormal ∧ Environment.RawValue.Forward env second secondNormal ∧
    (same = true ↔ NativeCoreCompare.project firstNormal = NativeCoreCompare.project secondNormal)

/-- Arena growth is charged to the shared counter. Starting within budget,
equality can overspend by only the rejecting tick. A completed comparison
stays within the same limit across both normalizations and identity. -/
theorem run_cost (within : initial ≤ limit) :
    let computed := run arena roots visible limit depth initial a b
    computed.arena.size + initial ≤ arena.size + computed.steps ∧ computed.steps ≤ limit + 1 ∧
      ∀ same, computed.result = .ok same → computed.steps ≤ limit := by
  have leftCost := runNested_cost arena roots visible limit depth initial a
  rcases leftState : runNested roots visible limit depth arena initial a with ⟨afterLeft, firstResult, leftSteps⟩
  dsimp only at leftCost
  rw [leftState] at leftCost
  cases firstResult with
  | error reason =>
      simp only [run, leftState]
      exact ⟨leftCost.1, leftCost.2.1 within, by intro _ impossible; cases impossible⟩
  | ok firstRoot =>
      have leftRoom := leftCost.2.2 firstRoot rfl
      have rightCost := runNested_cost afterLeft roots visible limit depth leftSteps b
      rcases rightState : runNested roots visible limit depth afterLeft leftSteps b with
        ⟨afterRight, secondResult, rightSteps⟩
      dsimp only at rightCost
      rw [rightState] at rightCost
      have leftGrowth : afterLeft.size + initial ≤ arena.size + leftSteps := leftCost.1
      have rightGrowth : afterRight.size + leftSteps ≤ afterLeft.size + rightSteps := rightCost.1
      cases secondResult with
      | error reason =>
          simp only [run, leftState, rightState]
          refine ⟨?_, rightCost.2.1 leftRoom, by intro _ impossible; cases impossible⟩
          change afterRight.size + initial ≤ arena.size + rightSteps
          omega
      | ok secondRoot =>
          have rightRoom := rightCost.2.2 secondRoot rfl
          have compared := NativeCoreIdentical.runArena_step_bounds (arena := afterRight) (depth := depth)
            (a := firstRoot) (b := secondRoot) rightRoom
          rcases identified : NativeCoreIdentical.runArena afterRight limit depth rightSteps firstRoot secondRoot with
            ⟨answer, spent⟩
          dsimp only at compared
          rw [identified] at compared
          simp only [run, leftState, rightState, identified]
          refine ⟨?_, compared.2.1, ?_⟩
          · have charged : rightSteps ≤ spent := compared.1
            change afterRight.size + initial ≤ arena.size + spent
            omega
          · intro _ completed
            cases answer
            · cases completed
            · exact compared.2.2 _ rfl

/-- Normalization and identity share the appended rows. Every completed
comparison decides the equality of the normalized retained shapes. -/
theorem run_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env)
    (left : Represents arena a first) (right : Represents arena b second) :
    let computed := run arena roots visible limit depth initial a b
    Prefix arena computed.arena ∧ (Backward arena → Backward computed.arena) ∧
      ∀ same, computed.result = .ok same → Agrees env computed.arena first second same := by
  have leftSound := runNested_refines (visible := visible) (limit := limit) (depth := depth)
    (initial := initial) aligned history left
  rcases leftState : runNested roots visible limit depth arena initial a with ⟨afterLeft, firstResult, leftSteps⟩
  dsimp only at leftSound
  rw [leftState] at leftSound
  obtain ⟨leftPrefix, leftBackward, leftReduced⟩ := leftSound
  cases firstResult with
  | error reason =>
      simp only [run, leftState]
      exact ⟨leftPrefix, leftBackward, by intro _ impossible; cases impossible⟩
  | ok firstRoot =>
      have rightSound := runNested_refines (visible := visible) (limit := limit) (depth := depth)
        (initial := leftSteps) (frameDefinitions aligned leftPrefix) history (right.frame leftPrefix)
      rcases rightState : runNested roots visible limit depth afterLeft leftSteps b with
        ⟨afterRight, secondResult, rightSteps⟩
      dsimp only at rightSound
      rw [rightState] at rightSound
      obtain ⟨rightPrefix, rightBackward, rightReduced⟩ := rightSound
      have kept := leftPrefix.trans rightPrefix
      have backward : Backward arena → Backward afterRight := fun before => rightBackward (leftBackward before)
      cases secondResult with
      | error reason =>
          simp only [run, leftState, rightState]
          exact ⟨kept, backward, by intro _ impossible; cases impossible⟩
      | ok secondRoot =>
          rcases identified : NativeCoreIdentical.runArena afterRight limit depth rightSteps firstRoot secondRoot
            with ⟨answer, spent⟩
          simp only [run, leftState, rightState, identified]
          refine ⟨kept, backward, ?_⟩
          intro same completed
          cases answer with
          | error reason => cases completed
          | ok result =>
              cases completed
              obtain ⟨firstNormal, firstRep, firstForward⟩ := leftReduced firstRoot rfl
              obtain ⟨secondNormal, secondRep, secondForward⟩ := rightReduced secondRoot rfl
              have firstFinal := firstRep.frame rightPrefix
              exact ⟨firstRoot, secondRoot, firstNormal, secondNormal, firstFinal, secondRep,
                firstForward, secondForward, NativeCoreIdentical.runArena_refines firstFinal secondRep identified⟩

/-- The byte admission supplies both the unchanged checked definition table
and the backward-reference invariant of the original input. -/
theorem run_checkBytes_refines
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (left : Represents snapshot.arena a first) (right : Represents snapshot.arena b second) :
    let computed := run snapshot.arena snapshot.definitions visible limit depth initial a b
    ∃ definitions families env, History definitions families env ∧
      Prefix snapshot.arena computed.arena ∧ Backward computed.arena ∧
      ∀ same, computed.result = .ok same → Agrees env computed.arena first second same := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, valid, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨kept, backward, compared⟩ := run_refines (visible := visible) (limit := limit)
    (depth := depth) (initial := initial) aligned history left right
  exact ⟨definitions, _, env, history, kept, backward valid, compared⟩

/-- The left normalization appends an equality row. The final identity reads
that row and its two children. The append survives a comparison limit error. -/
theorem appended_identity_example :
    let arena : Arena := #[.node (.natural 7) [], .node .free [0, 0], .node .eq [1, 0], .node .eq [0, 0]]
    let normalized := arena.push (.node .eq [0, 0])
    run arena [] 0 10 3 0 2 3 = ⟨normalized, .ok true, 10⟩ ∧
      run arena [] 0 9 3 0 2 3 = ⟨normalized, .error (.identity (.stepLimit 0)), 10⟩ := by
  exact ⟨rfl, rfl⟩

end Jihoo.NativeKernel.NativeCorePureStructuralEqual
