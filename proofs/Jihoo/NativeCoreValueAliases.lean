import Jihoo.NativeCoreValueTraversal

/-! Transparent global roots enter the same native normalizer at the
definition's actual raw value reference. Each alias pays for one visit
before visibility is checked and passes a smaller depth to its destination. -/
namespace Jihoo.NativeKernel.NativeCoreValueAliases

open Environment NativeArena NativeProgramWire
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Error Progress)

private def aliasAt (arena : Arena) (root : Nat) : Option Nat :=
  match arena[root]? with
  | some (.node (.global index) []) => some index
  | _ => none

private theorem aliasAt_read (found : aliasAt arena root = some index) :
    arena[root]? = some (.node (.global index) []) := by
  unfold aliasAt at found
  split at found
  · cases found
    assumption
  · contradiction

abbrev Visitor := Nat → State → Nat → Outcome Nat

/-- Follow an initial run of globals, then pass the live arena, clock and
remaining depth to the selected ordinary value visitor. -/
def runWith (visit : Visitor) (roots : List Roots) (visible limit : Nat) : Visitor
  | 0, state, root =>
      let paid := NativeCoreUnsignedCancellation.tick state.arena limit 0 state.steps root
      let entered := {state with steps := paid.2}
      match paid.1 with
      | .error reason => ⟨entered, .error (.tick reason)⟩
      | .ok () => ⟨entered, .error (.tick (.depthLimit root))⟩
  | depth + 1, state, root =>
      match aliasAt state.arena root with
      | none => visit (depth + 1) state root
      | some index =>
          let paid := NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root
          let entered := {state with steps := paid.2}
          match paid.1 with
          | .error reason => ⟨entered, .error (.tick reason)⟩
          | .ok () =>
              if index < visible then
                match roots[index]? with
                | some row => runWith visit roots visible limit depth entered row.valueRoot
                | none => ⟨entered, .error (.outsideFragment root)⟩
              else ⟨entered, .error (.invisibleGlobal root)⟩

def run (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots)
    (visible limit : Nat) : Visitor :=
  runWith (NativeCoreValueTraversal.run env families limit) roots visible limit

private theorem tick_clock :
    (NativeCoreUnsignedCancellation.tick arena limit depth steps root).2 = steps + 1 := by
  simp only [NativeCoreUnsignedCancellation.tick]
  repeat' first | rfl | split

private theorem alias_bound (found : aliasAt arena root = some index) : root < arena.size :=
  (Array.getElem?_eq_some_iff.mp (aliasAt_read found)).1

private theorem pay_alias {state : State}
    (found : aliasAt state.arena root = some index) (room : state.steps + 1 ≤ limit) :
    NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root = (.ok (), state.steps + 1) := by
  simp [NativeCoreUnsignedCancellation.tick, Nat.not_lt.mpr room, Nat.not_le.mpr (alias_bound found)]

/-- A hidden global pays its own visit and leaves the arena intact. -/
theorem runWith_hidden (read : state.arena[root]? = some (.node (.global index) []))
    (room : state.steps + 1 ≤ limit) (hidden : visible ≤ index) :
    runWith visit roots visible limit (depth + 1) state root =
      ⟨{state with steps := state.steps + 1}, .error (.invisibleGlobal root)⟩ := by
  have found : aliasAt state.arena root = some index := by simp only [aliasAt, read]
  simp only [runWith, found, pay_alias found room, ite_eq_right (Nat.not_lt.mpr hidden)]

/-- Each recorded pair contains the visited Global node reference and the
definition index it selected. The terminal graph root is kept separately. -/
inductive Trace (arena : Arena) (roots : List Roots) (visible : Nat) :
    Nat → Nat → List (Nat × Nat) → Prop where
  | terminal : aliasAt arena root = none → Trace arena roots visible root root []
  | alias : aliasAt arena root = some index → index < visible → roots[index]? = some row →
      Trace arena roots visible row.valueRoot terminal visits →
      Trace arena roots visible root terminal ((root, index) :: visits)

/-- The prefix itself allocates no rows. The derived callback uses the
exact depth and clock remaining after each recorded alias. -/
theorem Trace.execute {terminalRef : Nat} (path : Trace arena roots visible root terminalRef visits)
    (height : visits.length < depth) (room : initial + visits.length ≤ limit) :
    runWith visit roots visible limit depth ⟨arena, initial⟩ root =
      visit (depth - visits.length) ⟨arena, initial + visits.length⟩ terminalRef := by
  induction path generalizing depth initial with
  | terminal found =>
      cases depth with
      | zero => simp at height
      | succ depth => simp only [runWith, found, List.length_nil, Nat.sub_zero, Nat.add_zero]
  | alias found seen row rest ih =>
      rename_i aliasRoot index target destination tailVisits
      cases depth with
      | zero => simp at height
      | succ depth =>
          have nextRoom : initial + 1 ≤ limit := by
            simp only [List.length_cons] at room
            omega
          have paid := pay_alias (state := ⟨arena, initial⟩) (depth := depth) found nextRoom
          simp only [runWith, found, paid, ite_eq_left seen, row, List.length_cons]
          have lower : tailVisits.length < depth := by
            simp only [List.length_cons] at height
            omega
          have remaining : (initial + 1) + tailVisits.length ≤ limit := by
            simp only [List.length_cons] at room
            omega
          have exactDepth : depth + 1 - (tailVisits.length + 1) = depth - tailVisits.length := by omega
          have exactClock : initial + (tailVisits.length + 1) = initial + 1 + tailVisits.length := by omega
          rw [exactDepth, exactClock]
          exact ih lower remaining

/-- Every successful run decomposes into its actual alias path and the
callback that ran at the terminal reference. -/
theorem runWith_trace (success : (runWith visit roots visible limit depth state root).result = .ok selected) :
    ∃ terminal visits, Trace state.arena roots visible root terminal visits ∧ visits.length < depth ∧
      runWith visit roots visible limit depth state root =
        visit (depth - visits.length) {state with steps := state.steps + visits.length} terminal := by
  induction depth generalizing state root with
  | zero =>
      cases paid : NativeCoreUnsignedCancellation.tick state.arena limit 0 state.steps root with
      | mk result clock => cases result <;> simp [runWith, paid] at success
  | succ depth ih =>
      cases found : aliasAt state.arena root with
      | none =>
          refine ⟨root, [], .terminal found, by simp, ?_⟩
          simp only [runWith, found, List.length_nil, Nat.sub_zero, Nat.add_zero]
      | some index =>
          rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root with
            ⟨answer, clock⟩
          cases answer with
          | error reason => simp [runWith, found, paid] at success
          | ok charged =>
              cases charged
              by_cases shown : index < visible
              · cases row : roots[index]? with
                | none => simp [runWith, found, paid, shown, row] at success
                | some row =>
                    simp only [runWith, found, paid, shown, ite_true, row] at success ⊢
                    obtain ⟨terminal, visits, path, height, exactRun⟩ := ih success
                    refine ⟨terminal, (root, index) :: visits, .alias found shown row path, ?_, ?_⟩
                    · simpa only [List.length_cons] using Nat.succ_lt_succ height
                    · have charged : clock = state.steps + 1 := (congrArg Prod.snd paid).symm.trans tick_clock
                      have exactDepth : depth + 1 - (visits.length + 1) = depth - visits.length := by omega
                      rw [exactRun]
                      simp only [List.length_cons, exactDepth, charged, Nat.add_assoc, Nat.add_comm 1]
              · simp [runWith, found, paid, shown] at success

private theorem paid_clock {state : State}
    (paid : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root = (answer, clock)) :
    clock = state.steps + 1 :=
  (congrArg Prod.snd paid).symm.trans tick_clock

private theorem rejected_progress (state : State) (reason : Error) :
    Progress limit state (⟨{state with steps := state.steps + 1}, .error reason⟩ : Outcome Nat) :=
  ⟨.refl _, Nat.le_succ _, fun room => Nat.succ_le_succ room, fun _ _ success => by cases success⟩

theorem runWith_progress (metered : ∀ depth state root, Progress limit state (visit depth state root)) :
    Progress limit state (runWith visit roots visible limit depth state root) := by
  induction depth generalizing state root with
  | zero =>
      rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit 0 state.steps root with ⟨answer, clock⟩
      have clockEq := paid_clock paid
      cases answer <;> simp only [runWith, paid, clockEq]
      all_goals exact rejected_progress _ _
  | succ depth ih =>
      cases alias : aliasAt state.arena root with
      | none => simpa only [runWith, alias] using metered (depth + 1) state root
      | some index =>
          rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root with
            ⟨answer, clock⟩
          have clockEq := paid_clock paid
          cases answer with
          | error reason =>
              simpa only [runWith, alias, paid, clockEq] using rejected_progress (limit := limit) state (.tick reason)
          | ok charged =>
              cases charged
              by_cases shown : index < visible
              · cases read : roots[index]? with
                | none =>
                    simpa only [runWith, alias, paid, shown, ite_true, read, clockEq] using
                      rejected_progress (limit := limit) state (.outsideFragment root)
                | some row =>
                    simp only [runWith, alias, paid, shown, ite_true, read, clockEq]
                    have room : state.steps + 1 ≤ limit := by
                      apply Nat.le_of_not_gt
                      intro over
                      simp [NativeCoreUnsignedCancellation.tick, over] at paid
                    have result := ih (state := {state with steps := state.steps + 1}) (root := row.valueRoot)
                    exact ⟨result.kept, Nat.le_trans (Nat.le_succ _) result.monotone,
                      fun _ => result.bounded room, fun _ => result.accepted room⟩
              · simpa only [runWith, alias, paid, ite_eq_right shown, clockEq] using
                  rejected_progress (limit := limit) state (.invisibleGlobal root)

theorem run_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots)
    (visible limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (run env families roots visible limit depth state root) :=
  runWith_progress (NativeCoreValueTraversal.run_progress env families limit)

private theorem represented_definition {index : Nat} (aligned : RepresentsDefinitions arena roots definitions)
    (lookup : roots[index]? = some row) :
    ∃ raw, definitions[index]? = some raw ∧ RepresentsDefinition arena row raw := by
  induction aligned generalizing index with
  | nil => simp at lookup
  | @cons _ raw _ _ represented _ ih =>
      cases index with
      | zero => cases lookup; exact ⟨raw, rfl, represented⟩
      | succ index => exact ih lookup

private theorem earlier_target (aligned : RepresentsDefinitions arena roots definitions)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (lookup : roots[index]? = some row) (alias : aliasAt arena row.valueRoot = some target) :
    target < index := by
  obtain ⟨raw, source, represented⟩ := represented_definition aligned lookup
  have targetRep : Represents arena row.valueRoot (.node (.global target) []) :=
    .node (aliasAt_read alias) rfl .nil
  exact NativeCoreGlobalNormal.admitted_alias_before history source (represented.2.unique targetRep)

private theorem Trace.before {terminalRef : Nat} (path : Trace arena roots visible root terminalRef visits)
    (aligned : RepresentsDefinitions arena roots definitions)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (lookup : roots[index]? = some row) (onRow : row.valueRoot = root) :
    ∀ hop ∈ visits, hop.2 < index := by
  induction path generalizing index row with
  | terminal => simp
  | alias found shown targetLookup rest ih =>
      have earlier := earlier_target aligned history lookup (onRow.symm ▸ found)
      intro hop selected
      rcases List.mem_cons.mp selected with rfl | tail
      · exact earlier
      · exact Nat.lt_trans (ih targetLookup rfl _ tail) earlier

theorem Trace.decreasing {terminalRef : Nat} (path : Trace arena roots visible root terminalRef visits)
    (aligned : RepresentsDefinitions arena roots definitions)
    (history : LoanTyping.MixedProgram.History definitions declarations env) :
    visits.Pairwise (fun first second => second.2 < first.2) := by
  induction path with
  | terminal => exact .nil
  | alias _ _ lookup tail ih => exact .cons (tail.before aligned history lookup rfl) ih

/-- Authentic stored definitions always reach a non-alias root through
earlier definitions alone. The number of alias visits is at most the
starting definition index, without any condition on the terminal syntax. -/
theorem admitted_chain {index : Nat} (aligned : RepresentsDefinitions arena roots definitions)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (lookup : roots[index]? = some row) (visibleBound : index ≤ visible) :
    ∃ terminal visits, Trace arena roots visible row.valueRoot terminal visits ∧ visits.length ≤ index := by
  induction index using Nat.strongRecOn generalizing row with
  | ind index ih =>
      cases alias : aliasAt arena row.valueRoot with
      | none => exact ⟨_, [], .terminal alias, by simp⟩
      | some target =>
          have earlier := earlier_target aligned history lookup alias
          have inside := Nat.lt_trans earlier (List.getElem?_eq_some_iff.mp lookup).1
          have found := List.getElem?_eq_getElem (l := roots) inside
          obtain ⟨terminal, visits, path, count⟩ := ih target earlier found (Nat.le_of_lt (Nat.lt_of_lt_of_le earlier visibleBound))
          refine ⟨terminal, (row.valueRoot, target) :: visits,
            .alias alias (Nat.lt_of_lt_of_le earlier visibleBound) found path, ?_⟩
          simp only [List.length_cons]
          omega

/-- A full alias prefix leads to a represented terminal term whose
transparent expansion is exactly that of the original graph root. -/
theorem Trace.expansion {terminalRef : Nat} (path : Trace arena roots visible root terminalRef visits)
    (aligned : RepresentsDefinitions arena roots definitions)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents arena root input) :
    ∃ term, Represents arena terminalRef term ∧
      EnvironmentDelta.expand env input = EnvironmentDelta.expand env term := by
  induction path generalizing input with
  | terminal => exact ⟨input, source, rfl⟩
  | alias found _ lookup rest ih =>
      obtain ⟨body, held, unfolded⟩ :=
        NativeCoreGlobalNormal.alias_target aligned history source (aliasAt_read found) rfl lookup
      obtain ⟨terminal, represented, equal⟩ := ih held
      exact ⟨terminal, represented, unfolded.trans equal⟩

/-- The terminal value walk preserves the type of the original expanded
term, even when a typed value contraction happens after delta dispatch. -/
theorem runWith_refines
    (aligned : RepresentsDefinitions state.arena roots definitions)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (visitor : ∀ {depth state root input selected}, Represents state.arena root input →
      (visit depth state root).result = .ok selected →
      NativeCoreValueTraversal.Refines env state input (visit depth state root) selected)
    (source : Represents state.arena root input)
    (success : (runWith visit roots visible limit depth state root).result = .ok selected) :
    let output := runWith visit roots visible limit depth state root
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧
        ∀ {ctx type}, LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env input) type →
          LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env residual) type := by
  obtain ⟨terminal, visits, path, _, exactRun⟩ := runWith_trace success
  rw [exactRun] at success ⊢
  obtain ⟨body, represented, unfolded⟩ := path.expansion aligned history source
  obtain ⟨kept, backward, residual, held, changed⟩ :=
    visitor (state := {state with steps := state.steps + visits.length}) represented success
  exact ⟨kept, backward, residual, held, fun typed => changed.expanded (unfolded ▸ typed)⟩

theorem run_refines {families : List NativeFamilyWire.FamilyRoots}
    (aligned : RepresentsDefinitions state.arena roots definitions)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root input)
    (success : (run env families roots visible limit depth state root).result = .ok selected) :
    let output := run env families roots visible limit depth state root
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧
        ∀ {ctx type}, LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env input) type →
          LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env residual) type :=
  runWith_refines (visit := NativeCoreValueTraversal.run env families limit) aligned history
    (fun input done => NativeCoreValueTraversal.run_refines history input done) source success

/-- The selected source definition runs with exactly its authenticated
earlier prefix visible and keeps its declared type after expansion. -/
theorem admitted_program_preserves
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : Roots},
        snapshot.definitions[index]? = some row →
        (run env snapshot.families snapshot.definitions index limit depth ⟨snapshot.arena, initial⟩ row.valueRoot).result =
          .ok selected →
        let output := run env snapshot.families snapshot.definitions index limit depth ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected residual ∧
          LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨snapshot, definitions, familyTerms, env, exact, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exact, history, ?_⟩
  intro index limit depth initial selected row read success
  obtain ⟨entry, _, found, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history read
  obtain ⟨kept, preserved, residual, held, preserves⟩ := run_refines aligned history source.2 success
  exact ⟨entry, residual, found, kept, preserved backward, held, preserves typed⟩

namespace Examples

private def arithmetic : Term := .arith .mul (.arith .add (.integer 3) (.integer 4)) (.integer 6)
private def entry : GlobalDeclaration := ⟨.i64, arithmetic⟩
private def alias (index : Nat) : GlobalDeclaration := ⟨.i64, .node (.global index) []⟩
private def definitions : List GlobalDeclaration := [entry, alias 0, alias 1, alias 2]
private def env : Environment := ⟨#[entry, entry, entry, entry], #[]⟩
private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨0, 5⟩, ⟨0, 6⟩, ⟨0, 7⟩, ⟨0, 8⟩]
  families := []
  arena := #[.node .i64 [], .node (.integer 3) [], .node (.integer 4) [], .node (.integer 6) [],
    .node (.arith .add) [1, 2], .node (.arith .mul) [4, 3], .node (.global 0) [],
    .node (.global 1) [], .node (.global 2) []]
private def start : State := ⟨snapshot.arena, 0⟩
private def left : Arena := snapshot.arena.push (.node (.integer 7) [])
private def computedArena : Arena := left.push (.node (.integer 42) [])
private theorem history : LoanTyping.MixedProgram.History definitions [] env :=
  LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
private theorem aligned : RepresentsDefinitions snapshot.arena snapshot.definitions definitions :=
  decodeRoots_sound (by cbv)

/-- Three admitted aliases reach the raw nested arithmetic declaration.
Each alias pays once and the terminal visit appends the two signed results. -/
theorem admitted_alias_chain_runs_value_traversal :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
      Trace snapshot.arena snapshot.definitions 3 8 5 [(8, 2), (7, 1), (6, 0)] ∧
      run env [] snapshot.definitions 3 8 12 start 8 = ⟨⟨computedArena, 8⟩, .ok 10⟩ ∧
      LoanTyping.HasType env [] [] true (.integer 42) .i64 := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have exactPath : Trace snapshot.arena snapshot.definitions 3 8 5 [(8, 2), (7, 1), (6, 0)] :=
    .alias rfl (by decide) rfl (.alias rfl (by decide) rfl (.alias rfl (by decide) rfl (.terminal rfl)))
  have finished : run env [] snapshot.definitions 3 8 12 start 8 = ⟨⟨computedArena, 8⟩, .ok 10⟩ := by cbv
  have source : Represents snapshot.arena 8 (.node (.global 2) []) := decode_sound (fuel := 4) rfl
  have typed := (history.global_typing (index := 3) (declaration := entry) rfl).choose_spec.2
  have expanded : EnvironmentDelta.expand env (.node (.global 2) []) = arithmetic :=
    EnvironmentDelta.expand_global (show env.globals[2]? = some entry from rfl)
  obtain ⟨_, _, _, held, preserves⟩ := run_refines aligned history source (congrArg Outcome.result finished)
  rw [finished] at held
  have expected : Represents computedArena 10 (.integer 42) := decode_sound (fuel := 4) rfl
  have original : LoanTyping.HasType env [] [] true arithmetic .i64 := typed.ghost []
  have aliasTyped : LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env (.node (.global 2) [])) .i64 :=
    expanded.symm ▸ original
  have kept := preserves aliasTyped
  rw [held.unique expected] at kept
  exact ⟨admitted, exactPath, finished, by simpa only [EnvironmentDelta.expand, EnvironmentDelta.expandArgs] using kept⟩

/-- Visibility, depth and work exhaustion identify the exact stopped
visit. Failure in the terminal signed walk keeps its completed left fold. -/
theorem alias_and_terminal_failures_preserve_prefix :
    run env [] snapshot.definitions 2 8 12 start 8 =
      ⟨⟨snapshot.arena, 1⟩, .error (.invisibleGlobal 8)⟩ ∧
    run env [] snapshot.definitions 3 2 12 start 8 =
      ⟨⟨snapshot.arena, 3⟩, .error (.tick (.stepLimit 6))⟩ ∧
    run env [] snapshot.definitions 3 8 3 start 8 =
      ⟨⟨snapshot.arena, 4⟩, .error (.tick (.depthLimit 5))⟩ ∧
    run env [] snapshot.definitions 3 7 12 start 8 =
      ⟨⟨left, 8⟩, .error (.tick (.stepLimit 3))⟩ := by cbv

end Examples

end Jihoo.NativeKernel.NativeCoreValueAliases
