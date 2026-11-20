import Jihoo.NativeCoreExpandedTraversal
import Jihoo.NativeCoreExpandedFamilies

/-! The pure typed fragment of Core.equal shares the live arena and clock
across the left normalization, right normalization, and final identity.
Both selected definitions retain their checked types after expansion. -/
namespace Jihoo.NativeKernel.NativeCoreTypedEqual

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreCompare (project FullyRetained project_injective_of_fully_retained
  compareArena compareArena_refines compareShape_eq)

def identify (limit depth : Nat) (state : State) (left right : Nat) : Outcome Bool :=
  let (answer, steps) := NativeCoreIdentical.runArena state.arena limit depth state.steps left right
  ⟨{state with steps}, answer.mapError .tick⟩

/-- Native Core.equal passes the same depth to both normalizations and to
identity. Each continuation receives the arena and counter of its predecessor. -/
def runWith (visit : State → Nat → Outcome Nat) (limit depth : Nat)
    (start : State) (left right : Nat) : Outcome Bool :=
  (visit start left).next fun afterLeft leftRef =>
    (visit afterLeft right).next fun afterRight rightRef =>
      identify limit depth afterRight leftRef rightRef

private theorem identify_progress (room : state.steps ≤ limit) :
    Progress limit state (identify limit depth state left right) := by
  have bounds := NativeCoreIdentical.runArena_step_bounds (arena := state.arena)
    (depth := depth) (a := left) (b := right) room
  generalize found : NativeCoreIdentical.runArena state.arena limit depth state.steps left right = outcome at bounds ⊢
  rcases outcome with ⟨result, spent⟩
  simp only [identify, found] at ⊢
  refine ⟨.refl _, bounds.1, fun _ => bounds.2.1, fun _ value success => ?_⟩
  cases result with
  | error reason => simp [Except.mapError] at success
  | ok answer =>
      have found : answer = value := Except.ok.inj (by simpa only [Except.mapError] using success)
      exact bounds.2.2 value (congrArg Except.ok found)

/-- Every failure retains the committed prefix. With an initial clock
inside the budget, only the rejecting tick can consume one extra step. -/
theorem runWith_progress
    (metered : ∀ start ref, Progress limit start (visit start ref))
    (within : state.steps ≤ limit) :
    Progress limit state (runWith visit limit depth state left right) := by
  have first := metered state left
  cases leftResult : (visit state left).result with
  | error reason =>
      simp only [runWith, Outcome.next, leftResult]
      exact ⟨first.kept, first.monotone, first.bounded, fun _ _ impossible => by cases impossible⟩
  | ok leftRef =>
      have second := metered (visit state left).state right
      have leftRoom := first.accepted within leftRef leftResult
      cases rightResult : (visit (visit state left).state right).result with
      | error reason =>
          simp only [runWith, Outcome.next, leftResult, rightResult]
          exact ⟨first.kept.trans second.kept, Nat.le_trans first.monotone second.monotone,
            fun _ => second.bounded leftRoom, fun _ _ impossible => by cases impossible⟩
      | ok rightRef =>
          have rightRoom := second.accepted leftRoom rightRef rightResult
          have compared := identify_progress (depth := depth) (left := leftRef) (right := rightRef) rightRoom
          simp only [runWith, Outcome.next, leftResult, rightResult]
          exact ⟨first.kept.trans (second.kept.trans compared.kept),
            Nat.le_trans first.monotone (Nat.le_trans second.monotone compared.monotone),
            fun _ => compared.bounded rightRoom, fun _ value done => compared.accepted rightRoom value done⟩

abbrev ExpandedTyping (env : Environment) (term : Term) (ctx : Context) (type : Term) : Prop :=
  LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env term) type

def Sound (env : Environment) (base : Arena) (visit : State → Nat → Outcome Nat) : Prop :=
  ∀ {state ref input selected}, Prefix base state.arena → Represents state.arena ref input →
    (visit state ref).result = .ok selected →
    let output := visit state ref
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧
        ∀ {ctx type}, ExpandedTyping env input ctx type → ExpandedTyping env residual ctx type

structure Refines (env : Environment) (visit : State → Nat → Outcome Nat)
    (start : State) (a b : Nat) (first second : Term)
    (output : Outcome Bool) (same : Bool) : Prop where
  kept : Prefix start.arena output.state.arena
  backward : Backward start.arena → Backward output.state.arena
  agreement : ∃ left right leftNormal rightNormal,
    (visit start a).result = .ok left ∧ (visit (visit start a).state b).result = .ok right ∧
    Represents output.state.arena left leftNormal ∧ Represents output.state.arena right rightNormal ∧
    (∀ {ctx type}, ExpandedTyping env first ctx type → ExpandedTyping env leftNormal ctx type) ∧
    (∀ {ctx type}, ExpandedTyping env second ctx type → ExpandedTyping env rightNormal ctx type) ∧
    (same = true ↔ project leftNormal = project rightNormal)

/-- A completed structural ordering on the same live roots has order zero
exactly when identity returned true. Its own work budget is independent. -/
theorem Refines.agrees_compare (refinement : Refines env visit state a b first second output same)
    (left : (visit state a).result = .ok leftRef)
    (right : (visit (visit state a).state b).result = .ok rightRef)
    (compared : compareArena output.state.arena depth work leftRef rightRef = some (order, remaining)) :
    same = true ↔ order = .eq := by
  obtain ⟨leftRoot, rightRoot, _, _, leftOk, rightOk, leftRep, rightRep, _, _, equal⟩ := refinement.agreement
  have sameLeft := Except.ok.inj (left.symm.trans leftOk)
  have sameRight := Except.ok.inj (right.symm.trans rightOk)
  subst leftRoot rightRoot
  rw [compareArena_refines leftRep rightRep compared]
  exact equal.trans (compareShape_eq _ _).symm

private theorem identify_refines (left : Represents state.arena a first) (right : Represents state.arena b second)
    (success : (identify limit depth state a b).result = .ok same) :
    (identify limit depth state a b).state.arena = state.arena ∧
      (same = true ↔ project first = project second) := by
  rcases compared : NativeCoreIdentical.runArena state.arena limit depth state.steps a b with ⟨result, steps⟩
  cases result with
  | error reason => simp [identify, compared, Except.mapError] at success
  | ok answer =>
      simp [identify, compared, Except.mapError] at success
      subst answer
      exact ⟨by simp [identify, compared], NativeCoreIdentical.runArena_refines left right compared⟩

/-- Identity observes both resulting roots in the final arena. Both
original expanded types survive independently, including when identity
returns false. -/
theorem runWith_refines (sound : Sound env base visit) (onBase : Prefix base state.arena)
    (left : Represents state.arena a first) (right : Represents state.arena b second)
    (success : (runWith visit limit depth state a b).result = .ok same) :
    Refines env visit state a b first second (runWith visit limit depth state a b) same := by
  unfold runWith at success ⊢
  obtain ⟨a', leftOk, nextLeft⟩ := Outcome.next_success success
  obtain ⟨leftKept, leftBack, leftNormal, leftRep, leftTyped⟩ := sound onBase left leftOk
  rw [nextLeft] at success ⊢
  obtain ⟨b', rightOk, nextRight⟩ := Outcome.next_success success
  obtain ⟨rightKept, rightBack, rightNormal, rightRep, rightTyped⟩ :=
    sound (onBase.trans leftKept) (right.frame leftKept) rightOk
  rw [nextRight] at success ⊢
  have leftFinal := leftRep.frame rightKept
  obtain ⟨unchanged, compared⟩ := identify_refines leftFinal rightRep success
  refine ⟨?_, ?_, a', b', leftNormal, rightNormal, leftOk, rightOk, ?_, ?_, leftTyped, rightTyped, compared⟩
  · simpa only [unchanged] using leftKept.trans rightKept
  · simpa only [unchanged] using rightBack ∘ leftBack
  · simpa only [unchanged] using leftFinal
  · simpa only [unchanged] using rightRep

def run (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots)
    (visible limit depth : Nat) (state : State) (left right : Nat) : Outcome Bool :=
  runWith (NativeCoreBinderTraversal.runThroughAliases env families roots visible limit depth) limit depth state left right

theorem run_progress {families : List NativeFamilyWire.FamilyRoots} (within : state.steps ≤ limit) :
    Progress limit state (run env families roots visible limit depth state a b) :=
  runWith_progress (NativeCoreBinderTraversal.runThroughAliases_progress env families roots visible limit depth) within

private theorem binder_sound {families : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (definitionsFit : RepresentsDefinitions base roots definitions) :
    Sound env base (NativeCoreBinderTraversal.runThroughAliases env families roots visible limit depth) := by
  intro before ref input selected kept represented done
  exact NativeCoreValueAliases.runWith_refines (visit := NativeCoreBinderTraversal.run env families limit)
    (NativeCoreNestedAliases.frame_definitions definitionsFit kept) history
    (fun source success => NativeCoreBinderTraversal.run_refines history source success) represented done

theorem run_refines {families : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (definitionsFit : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (left : Represents state.arena a first) (right : Represents state.arena b second)
    (success : (run env families roots visible limit depth state a b).result = .ok same) :
    Refines env (NativeCoreBinderTraversal.runThroughAliases env families roots visible limit depth)
      state a b first second (run env families roots visible limit depth state a b) same :=
  runWith_refines (binder_sound history definitionsFit) onBase left right success

abbrev Driver := (visible limit depth : Nat) → State → Nat → Outcome Nat

abbrev CheckedComparisons (snapshot : NativeFamilyWire.Snapshot) (env : Environment) (normalize : Driver) : Prop :=
  ∀ {firstIndex secondIndex visible limit depth initial : Nat} {firstRow secondRow : Roots},
        snapshot.definitions[firstIndex]? = some firstRow →
        snapshot.definitions[secondIndex]? = some secondRow →
        let start : State := ⟨snapshot.arena, initial⟩
        let visit := normalize visible limit depth
        let output := runWith visit limit depth start firstRow.valueRoot secondRow.valueRoot
        (initial ≤ limit → Progress limit start output) ∧
        ∀ same, output.result = .ok same →
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          ∃ (leftEntry rightEntry : GlobalDeclaration) (left right : Nat) (leftNormal rightNormal : Term),
            env.globals[firstIndex]? = some leftEntry ∧ env.globals[secondIndex]? = some rightEntry ∧
            (visit start firstRow.valueRoot).result = .ok left ∧
            (visit (visit start firstRow.valueRoot).state secondRow.valueRoot).result = .ok right ∧
            Represents output.state.arena left leftNormal ∧ Represents output.state.arena right rightNormal ∧
            ExpandedTyping env leftNormal [] leftEntry.type ∧ ExpandedTyping env rightNormal [] rightEntry.type ∧
            (same = true ↔ project leftNormal = project rightNormal) ∧
            (FullyRetained leftNormal → FullyRetained rightNormal → (same = true ↔ leftNormal = rightNormal))

/-- Admission authenticates both selected roots and the type of each
declaration. Both visits use the very same visibility bound and clock. -/
theorem admitted_program_refines_with
    (normalize : Environment → NativeFamilyWire.Snapshot → Driver)
    (metered : ∀ env snapshot visible limit depth state root,
      Progress limit state (normalize env snapshot visible limit depth state root))
    (sound : ∀ {env snapshot definitions declarations},
      LoanTyping.MixedProgram.History definitions declarations env →
      RepresentsDefinitions snapshot.arena snapshot.definitions definitions →
      ∀ visible limit depth, Sound env snapshot.arena (normalize env snapshot visible limit depth))
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      CheckedComparisons snapshot env (normalize env snapshot) := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, valid, fits, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro firstIndex secondIndex visible limit depth initial firstRow secondRow leftFound rightFound
  refine ⟨fun within => runWith_progress (metered env snapshot visible limit depth) within, ?_⟩
  intro same success
  obtain ⟨leftEntry, _, leftRead, leftRep, leftTyped⟩ :=
    NativeCoreGlobalNormal.checked_definition_at fits history leftFound
  obtain ⟨rightEntry, _, rightRead, rightRep, rightTyped⟩ :=
    NativeCoreGlobalNormal.checked_definition_at fits history rightFound
  obtain ⟨kept, backward, left, right, leftNormal, rightNormal, leftOk, rightOk, leftFinal, rightFinal,
      preservesLeft, preservesRight, matched⟩ :=
    runWith_refines (sound history fits visible limit depth) (.refl _) leftRep.2 rightRep.2 success
  exact ⟨kept, backward valid, leftEntry, rightEntry, left, right, leftNormal, rightNormal,
    leftRead, rightRead, leftOk, rightOk, leftFinal, rightFinal, preservesLeft leftTyped, preservesRight rightTyped,
    matched, fun leftRetained rightRetained => matched.trans
      ⟨project_injective_of_fully_retained leftRetained rightRetained, congrArg project⟩⟩

theorem admitted_program_refines
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      CheckedComparisons snapshot env (NativeCoreBinderTraversal.runThroughAliases env snapshot.families snapshot.definitions) :=
  admitted_program_refines_with
    (fun env snapshot => NativeCoreBinderTraversal.runThroughAliases env snapshot.families snapshot.definitions)
    (fun env snapshot => NativeCoreBinderTraversal.runThroughAliases_progress env snapshot.families snapshot.definitions)
    (fun history fits _ _ _ => binder_sound history fits) admitted

/-- Both normalizations follow transparent definitions recursively using
the same native graph and the same visibility bound. -/
theorem admitted_expanded_program_refines
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      CheckedComparisons snapshot env (NativeCoreExpandedTraversal.run env snapshot.definitions) :=
  admitted_program_refines_with (fun env snapshot => NativeCoreExpandedTraversal.run env snapshot.definitions)
    (fun env snapshot => NativeCoreExpandedTraversal.run_progress env snapshot.definitions)
    (fun history fits _ _ _ => by
      intro state root source selected kept represented done
      obtain ⟨extension, backwards, residual, held, preserves⟩ :=
        NativeCoreExpandedTraversal.run_refines history fits kept represented done
      exact ⟨extension, backwards, residual, held, preserves⟩) admitted

/-- Each normalization can revisit constructors and recursively generated
family spines before the shared native identity visit. -/
theorem admitted_family_program_refines
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      CheckedComparisons snapshot env (NativeCoreExpandedFamilies.run env snapshot.families snapshot.definitions) :=
  admitted_program_refines_with
    (fun env snapshot => NativeCoreExpandedFamilies.run env snapshot.families snapshot.definitions)
    (fun env snapshot => NativeCoreExpandedFamilies.run_progress env snapshot.families snapshot.definitions)
    (fun history fits _ _ _ => by
      intro state root source selected kept represented done
      obtain ⟨extension, backwards, residual, held, preserves⟩ :=
        NativeCoreExpandedFamilies.run_refines history fits kept represented done
      exact ⟨extension, backwards, residual, held, preserves⟩) admitted

namespace Examples

private def leftTerm : Term := .arith .mul (.arith .add (.integer 3) (.integer 4)) (.integer 6)
private def rightTerm : Term :=
  .strict (.arith .add (.integer 1) (.integer 2)) (.arith .add (.integer 40) (.integer 2))
private def entry : GlobalDeclaration := ⟨.i64, leftTerm⟩
private def alias : GlobalDeclaration := ⟨.i64, .node (.global 0) []⟩
private def rightEntry : GlobalDeclaration := ⟨.i64, rightTerm⟩
private def definitions : List GlobalDeclaration := [entry, alias, rightEntry]
private def env : Environment := ⟨#[entry, entry, rightEntry], #[]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨0, 5⟩, ⟨0, 6⟩, ⟨0, 12⟩]
  families := []
  arena := #[.node .i64 [], .node (.integer 3) [], .node (.integer 4) [], .node (.integer 6) [],
    .node (.arith .add) [1, 2], .node (.arith .mul) [4, 3], .node (.global 0) [],
    .node (.integer 1) [], .node (.integer 2) [], .node (.arith .add) [7, 8],
    .node (.integer 40) [], .node (.arith .add) [10, 8], .node .strict [9, 11]]

private def initial : State := ⟨snapshot.arena, 0⟩
private def leftArena : Arena := snapshot.arena ++ #[.node (.integer 7) [], .node (.integer 42) []]
private def finalArena : Arena := leftArena ++ #[.node (.integer 3) [], .node (.integer 42) []]
private def comparison (limit depth : Nat) := run env [] snapshot.definitions 3 limit depth initial 6 12

/-- The alias and the Strict operand each normalize before identity reads
the two independently allocated rows for 42 using the same counter. -/
theorem admitted_alias_and_strict_compare_live_results :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    NativeCoreBinderTraversal.runThroughAliases env [] snapshot.definitions 3 14 16 initial 6 =
      ⟨⟨leftArena, 6⟩, .ok 14⟩ ∧
    NativeCoreBinderTraversal.runThroughAliases env [] snapshot.definitions 3 14 16 ⟨leftArena, 6⟩ 12 =
      ⟨⟨finalArena, 13⟩, .ok 16⟩ ∧
    comparison 14 16 = ⟨⟨finalArena, 14⟩, .ok true⟩ ∧
    LoanTyping.HasType env [] [] true (.integer 42) .i64 := by
  have accepted : NativeLoanMixedAdmission.checkBytes 64 128
      (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have history : LoanTyping.MixedProgram.History definitions [] env :=
    LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
  have aligned : RepresentsDefinitions snapshot.arena snapshot.definitions definitions := decodeRoots_sound (by cbv)
  have leftRan : NativeCoreBinderTraversal.runThroughAliases env [] snapshot.definitions 3 14 16 initial 6 =
      ⟨⟨leftArena, 6⟩, .ok 14⟩ := by cbv
  have rightRan : NativeCoreBinderTraversal.runThroughAliases env [] snapshot.definitions 3 14 16 ⟨leftArena, 6⟩ 12 =
      ⟨⟨finalArena, 13⟩, .ok 16⟩ := by cbv
  have finished : comparison 14 16 = ⟨⟨finalArena, 14⟩, .ok true⟩ := by cbv
  have source : Represents snapshot.arena 6 alias.value := decode_sound (fuel := 8) (by cbv)
  have other : Represents snapshot.arena 12 rightTerm := decode_sound (fuel := 8) (by cbv)
  obtain ⟨_, _, left, _, residual, _, leftOk, _, shown, _, preserves, _, _⟩ :=
    run_refines history aligned (.refl _) source other (congrArg Outcome.result finished)
  rw [leftRan] at leftOk
  have leftIndex : 14 = left := Except.ok.inj leftOk
  subst left
  change Represents (comparison 14 16).state.arena 14 residual at shown
  rw [finished] at shown
  have exactValue : Represents finalArena 14 (.integer 42) := decode_sound (fuel := 2) (by cbv)
  obtain ⟨_, _, checked⟩ := history.global_typing (index := 1) (declaration := entry) rfl
  have expanded : EnvironmentDelta.expand env alias.value = leftTerm :=
    EnvironmentDelta.expand_global (show env.globals[0]? = some entry from rfl)
  have original : ExpandedTyping env alias.value [] .i64 := by
    unfold ExpandedTyping
    rw [expanded]
    exact checked.ghost []
  have typed := preserves original
  rw [shown.unique exactValue] at typed
  exact ⟨accepted, leftRan, rightRan, finished,
    by simpa only [ExpandedTyping, EnvironmentDelta.expand, EnvironmentDelta.expandArgs] using typed⟩

/-- A shared clock identifies the exact failing left visit, right visit,
or identity tick and keeps the rows appended by the completed phases. -/
theorem comparison_exhaustion_preserves_live_prefix :
    comparison 1 16 = ⟨⟨snapshot.arena, 2⟩, .error (.tick (.stepLimit 5))⟩ ∧
    comparison 6 16 = ⟨⟨leftArena, 7⟩, .error (.tick (.stepLimit 12))⟩ ∧
    comparison 13 16 = ⟨⟨finalArena, 14⟩, .error (.tick (.stepLimit 14))⟩ ∧
    comparison 1 0 = ⟨⟨snapshot.arena, 1⟩, .error (.tick (.depthLimit 6))⟩ ∧
    comparison 0 0 = ⟨⟨snapshot.arena, 1⟩, .error (.tick (.stepLimit 6))⟩ := by cbv

end Examples

end Jihoo.NativeKernel.NativeCoreTypedEqual
