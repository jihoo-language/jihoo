import Jihoo.NativeCorePureStructuralNormal

/-! The pure structural fragment of Core.equal normalizes the left root,
normalizes the right root in the resulting arena, and compares both returned
references in that live arena. All three share the checking counter. -/
namespace Jihoo.NativeKernel.NativeCorePureStructuralEqual

open NativeArena NativeProgramWire
open Environment.LoanTyping.MixedProgram (History)
open NativeCorePureStructuralNormal (runNested runNested_refines runNested_cost frameDefinitions runNested_result_fully_retained)
open NativeCoreCompare (FullyRetained project projectArgs project_injective_of_fully_retained)
open NativeKernel.Conversion (ListRel)

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
    (same = true ↔ project firstNormal = project secondNormal)

private def RetainedAgreement (env : Environment) (arena : Arena) (first second : Term) (same : Bool) : Prop :=
  ∃ left right firstNormal secondNormal,
    Represents arena left firstNormal ∧ Represents arena right secondNormal ∧
    Environment.RawValue.Forward env first firstNormal ∧ Environment.RawValue.Forward env second secondNormal ∧
    (FullyRetained (EnvironmentDelta.expand env first) → FullyRetained firstNormal) ∧
    (FullyRetained (EnvironmentDelta.expand env second) → FullyRetained secondNormal) ∧
    (same = true ↔ project firstNormal = project secondNormal)

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

private theorem run_refines_retained (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env)
    (left : Represents arena a first) (right : Represents arena b second) :
    let computed := run arena roots visible limit depth initial a b
    Prefix arena computed.arena ∧ (Backward arena → Backward computed.arena) ∧
      ∀ same, computed.result = .ok same → RetainedAgreement env computed.arena first second same := by
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
              have firstKept (kept : FullyRetained (EnvironmentDelta.expand env first)) : FullyRetained firstNormal :=
                runNested_result_fully_retained (visible := visible) (limit := limit) (depth := depth)
                  (initial := initial) aligned history left kept
                  (by rw [leftState]) (by rw [leftState]; exact firstRep)
              have secondKept (kept : FullyRetained (EnvironmentDelta.expand env second)) : FullyRetained secondNormal :=
                runNested_result_fully_retained (visible := visible) (limit := limit) (depth := depth)
                  (initial := leftSteps) (frameDefinitions aligned leftPrefix) history
                  (right.frame leftPrefix) kept (by rw [rightState]) (by rw [rightState]; exact secondRep)
              exact ⟨firstRoot, secondRoot, firstNormal, secondNormal, firstFinal, secondRep,
                firstForward, secondForward, firstKept, secondKept,
                NativeCoreIdentical.runArena_refines firstFinal secondRep identified⟩

/-- Normalization and identity share the appended rows. Every completed
comparison decides the equality of the normalized retained shapes. -/
theorem run_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env)
    (left : Represents arena a first) (right : Represents arena b second) :
    let computed := run arena roots visible limit depth initial a b
    Prefix arena computed.arena ∧ (Backward arena → Backward computed.arena) ∧
      ∀ same, computed.result = .ok same → Agrees env computed.arena first second same := by
  obtain ⟨kept, backward, compared⟩ := run_refines_retained (visible := visible) (limit := limit)
    (depth := depth) (initial := initial) aligned history left right
  refine ⟨kept, backward, ?_⟩
  intro same success
  obtain ⟨a, b, firstNormal, secondNormal, leftRep, rightRep, leftStep, rightStep, _, _, equal⟩ :=
    compared same success
  exact ⟨a, b, firstNormal, secondNormal, leftRep, rightRep, leftStep, rightStep, equal⟩

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

/-- An accepted comparison reflects RawValue conversion for fully retained
expanded inputs. Both actual normalized results preserve that property. -/
theorem run_converts_fully_retained (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env)
    (left : Represents arena a first) (right : Represents arena b second)
    (leftKept : FullyRetained (EnvironmentDelta.expand env first))
    (rightKept : FullyRetained (EnvironmentDelta.expand env second))
    (equal : (run arena roots visible limit depth initial a b).result = .ok true) :
    Environment.RawValue.Conv env first second := by
  have compared := (run_refines_retained (visible := visible) (limit := limit) (depth := depth)
    (initial := initial) aligned history left right).2.2 true equal
  obtain ⟨_, _, _, _, _, _, forwardLeft, forwardRight, keepLeft, keepRight, matched⟩ := compared
  have same := project_injective_of_fully_retained (keepLeft leftKept) (keepRight rightKept) (matched.mp rfl)
  rw [same] at forwardLeft
  exact forwardLeft.toConv.trans forwardRight.toConv.symm

/-- Identity may discard Strict prefixes anywhere while retaining all the
evidence fields in the part of the term it actually compares. -/
inductive EvidenceRetained : Term → Prop where
  | var (index : Nat) : EvidenceRetained (.var index)
  | strict (effect : Term) : EvidenceRetained result → EvidenceRetained (.strict effect result)
  | node (ordinary : op ≠ .strict) (kept : NativeCoreCompare.conversionChildren op args = args)
      (arity : args.length = op.arity) (children : ∀ arg ∈ args, EvidenceRetained arg) :
      EvidenceRetained (.node op args)

private theorem retain_children (children : ∀ arg ∈ args, ∃ reduced,
    Environment.RawValue.Forward env arg reduced ∧ FullyRetained reduced ∧ project reduced = project arg) :
    ∃ reduced, ListRel (Environment.RawValue.Forward env) args reduced ∧ reduced.length = args.length ∧
      (∀ arg ∈ reduced, FullyRetained arg) ∧ projectArgs reduced = projectArgs args := by
  induction args with
  | nil => exact ⟨[], .nil, rfl, by simp, rfl⟩
  | cons arg args ih =>
    obtain ⟨value, first, retained, same⟩ := children arg List.mem_cons_self
    obtain ⟨rest, later, length, restRetained, restSame⟩ :=
      ih (fun child member => children child (List.mem_cons_of_mem _ member))
    refine ⟨value :: rest, .cons first later, by simp only [List.length_cons, length], ?_, ?_⟩
    · intro term member
      rcases List.mem_cons.mp member with rfl | tail
      · exact retained
      · exact restRetained term tail
    · simp only [projectArgs, same, restSame]

private theorem EvidenceRetained.reduces (evidence : EvidenceRetained term) :
    ∃ reduced, Environment.RawValue.Forward env term reduced ∧ FullyRetained reduced ∧ project reduced = project term := by
  induction evidence with
  | var index => exact ⟨.var index, .refl, .var index, rfl⟩
  | strict effect _ ih =>
    obtain ⟨output, reduced, retained, same⟩ := ih
    refine ⟨output, (Environment.RawValue.Forward.strict effect _).trans reduced, retained, same.trans ?_⟩
    simp only [Term.strict, project, projectArgs, NativeCoreCompare.syntaxView, ite_true] <;> rfl
  | @node op args ordinary kept arity _ ih =>
    obtain ⟨reduced, related, length, retained, same⟩ := retain_children ih
    have retainedFields := NativeCoreCompare.children_kept_of_length length.symm kept
    refine ⟨.node op reduced, .node op related,
      .node ordinary retainedFields (length.trans arity) retained, ?_⟩
    rw [project, project, same]

/-- Reflection uses the shaped Strict equation for discarded effects.
Every retained constructor and evidence field remains structurally equal. -/
theorem projected_identity_converts (left : EvidenceRetained first) (right : EvidenceRetained second)
    (matched : project first = project second) : Environment.RawValue.Conv env first second := by
  obtain ⟨firstNormal, leftSteps, leftKept, leftView⟩ := left.reduces (env := env)
  obtain ⟨secondNormal, rightSteps, rightKept, rightView⟩ := right.reduces (env := env)
  have same := project_injective_of_fully_retained leftKept rightKept (leftView.trans (matched.trans rightView.symm))
  rw [same] at leftSteps
  exact leftSteps.toConv.trans rightSteps.toConv.symm

theorem successful_identity_converts (left : Represents arena a first) (right : Represents arena b second)
    (leftKept : EvidenceRetained first) (rightKept : EvidenceRetained second)
    (computed : NativeCoreIdentical.runArena arena limit depth initial a b = (.ok true, steps)) :
    Environment.RawValue.Conv env first second :=
  projected_identity_converts leftKept rightKept ((NativeCoreIdentical.runArena_refines left right computed).mp rfl)

/-- A Strict prefix below an Eq constructor is ignored by actual graph
identity. The two proposition terms remain related by pure conversion. -/
theorem nested_strict_identity_example :
    Environment.RawValue.Conv env (.eq (.strict (.integer 0) (.natural 7)) (.natural 7)) (.eq (.natural 7) (.natural 7)) := by
  let arena : Arena := #[.node (.integer 0) [], .node (.natural 7) [], .node .strict [0, 1],
    .node .eq [2, 1], .node .eq [1, 1]]
  have first : Represents arena 3 (.eq (.strict (.integer 0) (.natural 7)) (.natural 7)) :=
    decode_sound (fuel := 4) rfl
  have second : Represents arena 4 (.eq (.natural 7) (.natural 7)) := decode_sound (fuel := 4) rfl
  have checked : NativeCoreIdentical.runArena arena 4 4 0 3 4 = (.ok true, 4) := by cbv
  have numeral : EvidenceRetained (.natural 7) := .node (by decide) rfl rfl (by simp)
  apply successful_identity_converts first second ?_ ?_ checked
  · refine .node (by decide) rfl rfl ?_
    intro child member
    have selected : child = .strict (.integer 0) (.natural 7) ∨ child = .natural 7 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
    rcases selected with rfl | rfl
    · exact .strict _ numeral
    · exact numeral
  · refine .node (by decide) rfl rfl ?_
    intro child member
    have selected : child = .natural 7 := by simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using member
    subst child
    exact numeral

/-- The left normalization appends an equality row. The final identity reads
that row and its two children. The append survives a comparison limit error. -/
theorem appended_identity_example :
    let arena : Arena := #[.node (.natural 7) [], .node .free [0, 0], .node .eq [1, 0], .node .eq [0, 0]]
    let normalized := arena.push (.node .eq [0, 0])
    run arena [] 0 10 3 0 2 3 = ⟨normalized, .ok true, 10⟩ ∧
      run arena [] 0 9 3 0 2 3 = ⟨normalized, .error (.identity (.stepLimit 0)), 10⟩ := by
  exact ⟨rfl, rfl⟩

end Jihoo.NativeKernel.NativeCorePureStructuralEqual
