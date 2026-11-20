import Jihoo.NativeCoreIterationReentry

/-! Array and Buffer formation transport the typed U64 length through the
joint iteration runner, including its zero-count value equation. The
parent uses the same node reuse or append as Core.normal. -/
namespace Jihoo.NativeKernel.NativeCoreIterationWordTypes

open Environment NativeArena
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Error Progress nodeResult nodeResult_exact nodeResult_progress)
open NativeCoreIterationNormal (Change)

inductive Kind where
  | array
  | buffer

def Kind.op : Kind → Op
  | .array => .array
  | .buffer => .buffer

def Kind.term (kind : Kind) (size : Term) : Term := .node kind.op [size]

private theorem Kind.arity (kind : Kind) : kind.op.arity = 1 := by
  cases kind <;> rfl

private theorem Kind.expand (kind : Kind) (env : Environment) (size : Term) :
    EnvironmentDelta.expand env (kind.term size) = kind.term (EnvironmentDelta.expand env size) := by
  simp only [Kind.term, EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs]

private def LengthPremise (env : Environment) (ctx : Context) : Term → Prop
  | .array size | .buffer size => LoanTyping.HasType env [] ctx true size .u64
  | _ => True

private theorem length_premise (typed : LoanTyping.HasType env loans ctx mode term type) :
    LengthPremise env ctx term := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term _ _ => LengthPremise env ctx term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case array size _ => exact size.ghost []
  case buffer size _ => exact size.ghost []
  case dataElim => split <;> trivial

private theorem Kind.invert (kind : Kind) (typed : LoanTyping.HasType env loans ctx mode (kind.term size) type) :
    LoanTyping.HasType env [] ctx true size .u64 ∧ LoanTyping.Conversion.Conv env (.univ 0) type := by
  cases kind
  · exact ⟨length_premise typed, typed.principalView⟩
  · exact typed.bufferView

private theorem Kind.form (kind : Kind) (sizeTyped : LoanTyping.HasType env [] ctx true size .u64) :
    LoanTyping.HasType env [] ctx true (kind.term size) (.univ 0) := by
  cases kind
  · exact .array sizeTyped
  · exact .buffer sizeTyped

def run (kind : Kind) (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  let paid := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let entered := {state with steps := paid.2}
  match paid.1 with
  | .error reason => ⟨entered, .error (.tick reason)⟩
  | .ok () =>
      match state.arena[root]? with
      | some (.node op [size]) =>
          if op = kind.op then
            (NativeCoreIterationReentry.run env families limit (depth - 1) entered size).next fun next size' =>
              nodeResult next root kind.op [size] [size']
          else ⟨entered, .error (.outsideFragment root)⟩
      | _ => ⟨entered, .error (.outsideFragment root)⟩

variable {kind : Kind} {families : List NativeFamilyWire.FamilyRoots}

theorem run_known (read : state.arena[root]? = some (.node kind.op [size]))
    (paid : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root = (.ok (), clock)) :
    run kind env families limit depth state root =
      (NativeCoreIterationReentry.run env families limit (depth - 1) {state with steps := clock} size).next
        (fun next size' => nodeResult next root kind.op [size] [size']) := by
  simp only [run, paid, read, ite_true]

theorem run_progress (kind : Kind) (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (run kind env families limit depth state root) := by
  let entered := {state with steps := state.steps + 1}
  have rejected (reason : Error) : Progress limit state (⟨entered, .error reason⟩ : Outcome Nat) :=
    ⟨.refl _, Nat.le_succ _, fun room => Nat.succ_le_succ room, fun _ _ success => by cases success⟩
  by_cases exhausted : limit < state.steps + 1
  · simpa only [run, NativeCoreUnsignedCancellation.tick, exhausted, ite_true, entered] using
      rejected (.tick (.stepLimit root))
  by_cases nesting : depth = 0
  · simpa only [run, NativeCoreUnsignedCancellation.tick, exhausted, nesting, ite_false, ite_true, entered] using
      rejected (.tick (.depthLimit root))
  by_cases invalid : state.arena.size ≤ root
  · simpa only [run, NativeCoreUnsignedCancellation.tick, exhausted, nesting, invalid, ite_false, ite_true, entered] using
      rejected (.tick (.invalidReference root))
  simp only [run, NativeCoreUnsignedCancellation.tick, exhausted, nesting, invalid, ite_false]
  split
  · rename_i op size read
    by_cases sameOp : op = kind.op
    · simp only [sameOp, ite_true]
      have child := NativeCoreIterationReentry.run_progress env families limit (depth - 1) entered size
      have completed := child.next (after := fun next size' => nodeResult next root kind.op [size] [size'])
        (fun size' => nodeResult_progress _ root kind.op [size] [size'] true)
      have room := Nat.le_of_not_gt exhausted
      exact ⟨completed.kept, Nat.le_trans (Nat.le_succ _) completed.monotone,
        fun _ => completed.bounded room, fun _ => completed.accepted room⟩
    · simp only [sameOp, ite_false]
      exact rejected (.outsideFragment root)
  · exact rejected (.outsideFragment root)

structure Refines (env : Environment) (kind : Kind) (start : State) (length : Term)
    (outcome : Outcome Nat) (selected : Nat) : Prop where
  kept : Prefix start.arena outcome.state.arena
  backward : Backward start.arena → Backward outcome.state.arena
  value : ∃ residual, Represents outcome.state.arena selected (kind.term residual) ∧ Change env length residual

/-- Exact graph shape with the retained parent and the typed length
equation produced by the child walk. -/
theorem run_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (represented : Represents state.arena root (kind.term length))
    (success : (run kind env families limit depth state root).result = .ok selected) :
    Refines env kind state length (run kind env families limit depth state root) selected := by
  rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root with ⟨status, clock⟩
  cases status with
  | error reason => simp [run, paid] at success
  | ok charged =>
      cases charged
      cases represented with
      | node read _ children =>
          cases children with
          | cons sizeRep remaining =>
              cases remaining
              rw [run_known read paid] at success ⊢
              obtain ⟨size', returned, computed⟩ := Outcome.next_success success
              rw [computed] at success ⊢
              obtain ⟨kept, backward, residual, lengthRep, changed⟩ :=
                NativeCoreIterationReentry.run_refines (state := {state with steps := clock}) history sizeRep returned
              obtain ⟨more, preserves, parent⟩ := nodeResult_exact (kept.lookup read)
                (.cons lengthRep .nil) kind.arity.symm success
              exact ⟨kept.trans more, fun old => preserves (backward old), residual, parent, changed⟩

theorem Refines.preserves (step : Refines env kind state length outcome selected)
    (typed : LoanTyping.HasType env loans ctx mode (kind.term length) type) :
    ∃ residual, Represents outcome.state.arena selected (kind.term residual) ∧
      LoanTyping.HasType env [] ctx true (kind.term residual) type := by
  obtain ⟨lengthTyped, converted⟩ := kind.invert typed
  obtain ⟨residual, held, changed⟩ := step.value
  exact ⟨residual, held, (kind.form (changed.preserves lengthTyped)).convert converted⟩

theorem Refines.preservesExpanded (step : Refines env kind state length outcome selected)
    (typed : LoanTyping.HasType env loans ctx mode (EnvironmentDelta.expand env (kind.term length)) type) :
    ∃ residual, Represents outcome.state.arena selected (kind.term residual) ∧
      LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env (kind.term residual)) type := by
  rw [kind.expand] at typed
  obtain ⟨lengthTyped, converted⟩ := kind.invert typed
  obtain ⟨residual, held, changed⟩ := step.value
  refine ⟨residual, held, ?_⟩
  rw [kind.expand]
  exact (kind.form (changed.preservesExpanded lengthTyped)).convert converted

/-- Recover the original expanded universe from any admitted declaration
whose value represents an Array or Buffer formation. -/
theorem admitted_program_preserves
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : NativeProgramWire.Roots} {kind : Kind} {length : Term},
        snapshot.definitions[index]? = some row →
        Represents snapshot.arena row.valueRoot (kind.term length) →
        (run kind env snapshot.families limit depth ⟨snapshot.arena, initial⟩ row.valueRoot).result = .ok selected →
        let output := run kind env snapshot.families limit depth ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected (kind.term residual) ∧
          LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env (kind.term residual)) entry.type := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial selected row kind length found represented success
  obtain ⟨entry, _, read, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  rw [source.2.unique represented] at typed
  have visits := run_refines history represented success
  obtain ⟨residual, held, typing⟩ := visits.preservesExpanded typed
  exact ⟨entry, residual, read, visits.kept, visits.backward backward, held, typing⟩

namespace Examples

private def motive : Term := .lam false .u64 .u64
private def step : Term := .lam false .u64 (.lam true (.lt (.var 0) (.natural 0)) (.lam false .u64 (.var 0)))
private def length : Term := .loop (.natural 0) motive (.natural 2) step
private def buffer : GlobalDeclaration := ⟨.univ 0, .buffer length⟩
private def array : GlobalDeclaration := ⟨.univ 0, .array length⟩
private def env : Environment := ⟨#[buffer, array], #[]⟩
private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨12, 10⟩, ⟨12, 11⟩]
  families := []
  arena := #[.node .u64 [], .node (.natural 0) [], .node (.natural 2) [], .node (.lam false) [0, 0],
    .var 0, .node .lt [4, 1], .node (.lam false) [0, 4], .node (.lam true) [5, 6],
    .node (.lam false) [0, 7], .node .loop [1, 3, 2, 8], .node .buffer [9], .node .array [9],
    .node (.universe 0) [], .node .buffer [2], .node .array [2]]
private def start : State := ⟨snapshot.arena, 0⟩
private theorem history : LoanTyping.MixedProgram.History [buffer, array] [] env :=
  LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)

/-- Both type formations are admitted in the same byte snapshot. The
zero Loop leaves a four-tick walk with one fresh parent row. -/
theorem checked_array_and_buffer_zero_loop_lengths :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
      run .buffer env [] 4 12 start 10 =
        ⟨⟨snapshot.arena.push (.node .buffer [2]), 4⟩, .ok 15⟩ ∧
      run .array env [] 4 12 start 11 =
        ⟨⟨snapshot.arena.push (.node .array [2]), 4⟩, .ok 15⟩ ∧
      LoanTyping.HasType env [] [] true (.buffer (.natural 2)) (.univ 0) ∧
      LoanTyping.HasType env [] [] true (.array (.natural 2)) (.univ 0) := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have bufferSource : Represents snapshot.arena 10 (Kind.buffer.term length) := decode_sound (fuel := 16) rfl
  have arraySource : Represents snapshot.arena 11 (Kind.array.term length) := decode_sound (fuel := 16) rfl
  have bufferRun : run .buffer env [] 4 12 start 10 =
      ⟨⟨snapshot.arena.push (.node .buffer [2]), 4⟩, .ok 15⟩ := by cbv
  have arrayRun : run .array env [] 4 12 start 11 =
      ⟨⟨snapshot.arena.push (.node .array [2]), 4⟩, .ok 15⟩ := by cbv
  have bufferTyped := (history.global_typing (index := 0) (declaration := buffer) rfl).choose_spec.2
  have arrayTyped := (history.global_typing (index := 1) (declaration := array) rfl).choose_spec.2
  obtain ⟨_, bufferOut, bufferResult⟩ :=
    (run_refines history bufferSource (congrArg Outcome.result bufferRun)).preserves bufferTyped
  obtain ⟨_, arrayOut, arrayResult⟩ :=
    (run_refines history arraySource (congrArg Outcome.result arrayRun)).preserves arrayTyped
  rw [bufferRun] at bufferOut
  rw [arrayRun] at arrayOut
  have bufferExpected : Represents (snapshot.arena.push (.node .buffer [2])) 15 (.buffer (.natural 2)) :=
    decode_sound (fuel := 4) rfl
  have arrayExpected : Represents (snapshot.arena.push (.node .array [2])) 15 (.array (.natural 2)) :=
    decode_sound (fuel := 4) rfl
  exact ⟨admitted, bufferRun, arrayRun, bufferOut.unique bufferExpected ▸ bufferResult,
    arrayOut.unique arrayExpected ▸ arrayResult⟩

theorem unchanged_literal_lengths_reuse_rows :
    run .buffer env [] 2 12 start 13 = ⟨⟨snapshot.arena, 2⟩, .ok 13⟩ ∧
      run .array env [] 2 12 start 14 = ⟨⟨snapshot.arena, 2⟩, .ok 14⟩ := by cbv

end Examples
end Jihoo.NativeKernel.NativeCoreIterationWordTypes
