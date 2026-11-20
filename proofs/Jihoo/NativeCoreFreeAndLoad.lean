import Jihoo.NativeCoreIterationReentry

/-! Pure Free immediately visits its continuation. Pure Load visits its
buffer, index, evidence and continuation at the same child depth and
rebuilds the memory operation with their resulting references. -/
namespace Jihoo.NativeKernel.NativeCoreFreeAndLoad

open Environment NativeArena
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Error Progress GhostNormalization Refines
  nodeResult nodeResult_exact nodeResult_progress visitOperands visitOperands_progress visitOperands_refines)

private def enter (finish : State → Node → Outcome Nat) (limit depth : Nat)
    (state : State) (root : Nat) : Outcome Nat :=
  let paid := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let entered := {state with steps := paid.2}
  match paid.1 with
  | .error reason => ⟨entered, .error (.tick reason)⟩
  | .ok () =>
      match state.arena[root]? with
      | none => ⟨entered, .error (.outsideFragment root)⟩
      | some node => finish entered node

private theorem enter_progress (metered : ∀ after node, Progress limit after (finish after node)) :
    Progress limit state (enter finish limit depth state root) := by
  let entered := {state with steps := state.steps + 1}
  have rejected (reason : Error) : Progress limit state (⟨entered, .error reason⟩ : Outcome Nat) :=
    ⟨.refl _, Nat.le_succ _, fun room => Nat.succ_le_succ room, fun _ _ success => by cases success⟩
  by_cases exhausted : limit < state.steps + 1
  · simpa only [enter, NativeCoreUnsignedCancellation.tick, exhausted, ite_true, entered] using
      rejected (.tick (.stepLimit root))
  by_cases nesting : depth = 0
  · simpa only [enter, NativeCoreUnsignedCancellation.tick, exhausted, nesting, ite_false, ite_true, entered] using
      rejected (.tick (.depthLimit root))
  by_cases invalid : state.arena.size ≤ root
  · simpa only [enter, NativeCoreUnsignedCancellation.tick, exhausted, nesting, invalid, ite_false, ite_true, entered] using
      rejected (.tick (.invalidReference root))
  simp only [enter, NativeCoreUnsignedCancellation.tick, exhausted, nesting, invalid, ite_false]
  split
  · exact rejected (.outsideFragment root)
  · rename_i node found
    have visited := metered entered node
    have room := Nat.le_of_not_gt exhausted
    exact ⟨visited.kept, Nat.le_trans (Nat.le_succ _) visited.monotone,
      fun _ => visited.bounded room, fun _ => visited.accepted room⟩

private def freeFinish (visit : State → Nat → Outcome Nat) (root : Nat) (state : State) : Node → Outcome Nat
  | .node .free [_, rest] => visit state rest
  | _ => ⟨state, .error (.outsideFragment root)⟩

def runFree (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  enter (freeFinish (NativeCoreIterationReentry.run env families limit (depth - 1)) root) limit depth state root

variable {families : List NativeFamilyWire.FamilyRoots}

theorem runFree_known (read : state.arena[root]? = some (.node .free [owner, rest]))
    (paid : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root = (.ok (), clock)) :
    runFree env families limit depth state root =
      NativeCoreIterationReentry.run env families limit (depth - 1) {state with steps := clock} rest := by
  simp only [runFree, enter, read, paid, freeFinish]

theorem runFree_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (runFree env families limit depth state root) := by
  apply enter_progress
  intro after node
  unfold freeFinish
  split
  · exact NativeCoreIterationReentry.run_progress _ _ _ _ _ _
  · exact Progress.atState _ _

/-- The immediate Free equation is a RawValue step. Its continuation may
then take a typed zero-iteration step or a retained normalization step. -/
theorem runFree_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root (.free owner rest))
    (success : (runFree env families limit depth state root).result = .ok selected) :
    NativeCoreIterationNormal.Refines env state rest (runFree env families limit depth state root) selected ∧
      RawValue.Forward env (.free owner rest) rest := by
  rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root with ⟨answer, clock⟩
  cases answer with
  | error reason => simp [runFree, enter, paid] at success
  | ok units =>
      cases units
      cases source with
      | node read _ children =>
          cases children with
          | cons ownerRep tail =>
              cases tail with
              | cons restRep done =>
                  cases done
                  rw [runFree_known read paid] at success ⊢
                  obtain ⟨kept, backward, residual, represented, change⟩ :=
                    NativeCoreIterationReentry.run_refines (state := {state with steps := clock}) history restRep success
                  exact ⟨⟨kept, backward, residual, represented, change⟩, .free owner rest⟩

theorem runFree_preserves (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root (.free owner rest))
    (typed : LoanTyping.HasType env loans ctx mode (.free owner rest) type)
    (success : (runFree env families limit depth state root).result = .ok selected) :
    ∃ residual, Represents (runFree env families limit depth state root).state.arena selected residual ∧
      LoanTyping.HasType env [] ctx true residual type := by
  obtain ⟨residual, held, changed⟩ := (runFree_refines history source success).1.value
  exact ⟨residual, held, changed.preserves (LoanTyping.value_root_ghost_preservation (.free owner rest) typed)⟩

theorem runFree_preservesExpanded (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root (.free owner rest))
    (typed : LoanTyping.HasType env loans ctx mode (EnvironmentDelta.expand env (.free owner rest)) type)
    (success : (runFree env families limit depth state root).result = .ok selected) :
    ∃ residual, Represents (runFree env families limit depth state root).state.arena selected residual ∧
      LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env residual) type := by
  obtain ⟨residual, held, changed⟩ := (runFree_refines history source success).1.value
  have original : LoanTyping.HasType env loans ctx mode
      (.free (EnvironmentDelta.expand env owner) (EnvironmentDelta.expand env rest)) type := by
    simpa only [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs] using typed
  exact ⟨residual, held, changed.preservesExpanded (LoanTyping.value_root_ghost_preservation (.free _ _) original)⟩

def walkLoad (visit : State → Nat → Outcome Nat) (state : State) (root : Nat) (refs : List Nat) : Outcome Nat :=
  (visitOperands visit state refs).next fun after normalized =>
    nodeResult after root .load refs normalized

private def loadFinish (visit : State → Nat → Outcome Nat) (root : Nat) (state : State) : Node → Outcome Nat
  | .node .load refs =>
      if refs.length = Op.load.arity then walkLoad visit state root refs
      else ⟨state, .error (.outsideFragment root)⟩
  | _ => ⟨state, .error (.outsideFragment root)⟩

def runLoad (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  enter (loadFinish (NativeCoreIterationReentry.runNested env families limit (depth - 1)) root) limit depth state root

theorem runLoad_known (read : state.arena[root]? = some (.node .load refs))
    (arity : refs.length = Op.load.arity)
    (paid : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root = (.ok (), clock)) :
    runLoad env families limit depth state root =
      walkLoad (NativeCoreIterationReentry.runNested env families limit (depth - 1))
        {state with steps := clock} root refs := by
  simp only [runLoad, enter, read, paid, loadFinish, arity, ite_true]

theorem walkLoad_progress (metered : ∀ state ref, Progress limit state (visit state ref)) :
    Progress limit state (walkLoad visit state root refs) :=
  (visitOperands_progress metered state refs).next (fun _ => nodeResult_progress _ _ _ _ _ _)

theorem runLoad_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (runLoad env families limit depth state root) := by
  apply enter_progress
  intro after node
  unfold loadFinish
  split
  · split
    · exact walkLoad_progress (NativeCoreIterationReentry.runNested_progress env families limit (depth - 1))
    · exact Progress.atState _ _
  · exact Progress.atState _ _

/-- All four operands retain their typed dependencies, including the
evidence at the normalized index and the continuation's lowered result. -/
theorem walkLoad_refines (wf : UnifiedProgram.EnvWellFormed env)
    (visitor : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → Refines env state term (visit state ref) selected)
    (read : state.arena[root]? = some (.node .load refs))
    (represented : RepresentsList state.arena refs terms) (arity : refs.length = Op.load.arity)
    (success : (walkLoad visit state root refs).result = .ok selected) :
    Refines env state (.node .load terms) (walkLoad visit state root refs) selected := by
  unfold walkLoad at success ⊢
  obtain ⟨_, visited, computed⟩ := Outcome.next_success success
  rw [computed] at success ⊢
  obtain ⟨kept, backward, size, residuals, children, changes⟩ :=
    visitOperands_refines represented visitor visited
  obtain ⟨more, preserves, held⟩ :=
    nodeResult_exact (kept.lookup read) children (size.trans arity) success
  exact ⟨kept.trans more, fun old => preserves (backward old), _, held,
    GhostNormalization.node wf (by decide) rfl changes⟩

theorem runLoad_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root (.node .load terms))
    (success : (runLoad env families limit depth state root).result = .ok selected) :
    Refines env state (.node .load terms) (runLoad env families limit depth state root) selected := by
  rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root with ⟨answer, clock⟩
  cases answer with
  | error reason => simp [runLoad, enter, paid] at success
  | ok units =>
      cases units
      cases source with
      | node read arity children =>
          rw [runLoad_known read arity paid] at success ⊢
          obtain ⟨kept, backward, value⟩ := walkLoad_refines (state := {state with steps := clock})
            history.wellFormed (fun held done => NativeCoreIterationReentry.runNested_refines history held done)
            read children arity success
          exact ⟨kept, backward, value⟩

theorem runLoad_preserves (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root (.load buffer index proof continuation))
    (typed : LoanTyping.HasType env loans ctx mode (.load buffer index proof continuation) type)
    (success : (runLoad env families limit depth state root).result = .ok selected) :
    ∃ residual, Represents (runLoad env families limit depth state root).state.arena selected residual ∧
      LoanTyping.HasType env [] ctx true residual type := by
  obtain ⟨residual, held, changed⟩ := (runLoad_refines history source success).value
  exact ⟨residual, held, changed.raw.typed typed⟩

namespace Examples

private def size : Term := .natural 2
private def zero : Term := .natural 0
private def identity : Term := .lam false .u64 (.var 0)
private def owner : Term := .alloc (.app identity size) (.integer 0)
private def buffer : Term := .alloc size (.integer 0)
private def box : Term := .node (.ind 0 0) []
private def declaration : FamilyDeclaration := ⟨true, 0, 0, [.pi false (.buffer size) box], 0⟩
private def signature : Signature := ⟨[⟨false, .buffer size, none⟩], []⟩
private def entry : CheckedFamily := ⟨declaration, [signature], true⟩
private def wrapped : Term := .node (.con 0 0 1) [.var 0]
private def continuation : Term :=
  .lam false .i64 (.lam false (.buffer size) (.node (.drop 0) [wrapped, .var 1]))
private def normalizedContinuation : Term := .lam false .i64 (.lam false (.buffer size) (.var 1))
private def proof : Term := .decide zero size
private def loaded : Term := .load buffer (.app identity zero) proof continuation
private def freed : Term := .free owner loaded
private def residual : Term := .load buffer zero proof normalizedContinuation
private def freeDefinition : GlobalDeclaration := ⟨.i64, freed⟩
private def loadDefinition : GlobalDeclaration := ⟨.i64, loaded⟩
private def env : Environment := ⟨#[freeDefinition, loadDefinition], #[entry]⟩
private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨11, 19⟩, ⟨11, 18⟩]
  families := [⟨true, 0, 0, 0, [21]⟩]
  arena := #[.node (.natural 2) [], .node (.integer 0) [], .node .alloc [0, 1],
    .var 0, .node .u64 [], .node (.lam false) [4, 3], .node .app [5, 0], .node .alloc [6, 1],
    .node (.natural 0) [], .node .app [5, 8], .node .decide [8, 0], .node .i64 [],
    .node .buffer [0], .var 1, .node (.con 0 0 1) [3], .node (.drop 0) [14, 13],
    .node (.lam false) [12, 15], .node (.lam false) [11, 16], .node .load [2, 9, 10, 17],
    .node .free [7, 18], .node (.ind 0 0) [], .node (.pi false) [12, 20]]
private def start : State := ⟨snapshot.arena, 0⟩
private def rebuilt : Arena := ((snapshot.arena.push (.node (.lam false) [12, 13])).push
  (.node (.lam false) [11, 22])).push (.node .load [2, 8, 10, 23])
private theorem checkedHistory : LoanTyping.MixedProgram.History [freeDefinition, loadDefinition] [declaration] env :=
  LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)

/-- The two source declarations pass exact-byte resource admission. Free
skips its owner and returns the same rebuilt Load with one extra tick. -/
theorem admitted_free_visits_load_at_original_type :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
      runFree env snapshot.families 23 16 start 19 = ⟨⟨rebuilt, 23⟩, .ok 24⟩ ∧
      runLoad env snapshot.families 22 15 start 18 = ⟨⟨rebuilt, 22⟩, .ok 24⟩ ∧
      LoanTyping.HasType env [] [] true residual .i64 := by
  have accepted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have freeExec : runFree env snapshot.families 23 16 start 19 = ⟨⟨rebuilt, 23⟩, .ok 24⟩ := by cbv
  have loadExec : runLoad env snapshot.families 22 15 start 18 = ⟨⟨rebuilt, 22⟩, .ok 24⟩ := by cbv
  have typed := (checkedHistory.global_typing (index := 0) (declaration := freeDefinition) rfl).choose_spec.2
  have source : Represents snapshot.arena 19 freed := decode_sound (fuel := 16) rfl
  obtain ⟨_, output, preserved⟩ := runFree_preserves checkedHistory source typed (congrArg Outcome.result freeExec)
  rw [freeExec] at output
  have expected : Represents rebuilt 24 residual := decode_sound (fuel := 12) rfl
  exact ⟨accepted, freeExec, loadExec, output.unique expected ▸ preserved⟩

/-- After the buffer and the beta-normalized index, the first rejected
tick belongs to the evidence. Its continuation and the rebuilt row wait. -/
theorem admitted_load_evidence_order :
    runLoad env snapshot.families 12 15 start 18 =
      ⟨⟨snapshot.arena, 13⟩, .error (.tick (.stepLimit 10))⟩ := by cbv

end Examples
end Jihoo.NativeKernel.NativeCoreFreeAndLoad
