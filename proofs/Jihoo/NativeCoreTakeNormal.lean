import Jihoo.NativeCoreCaseNormal

/-! The pure Take path first visits the packed term. A Give contributes
its owner and payload to two fresh App rows using the written continuation.
The child visitor then normalizes that application spine. A neutral Take
visits its continuation before the ordinary unchanged-row check. -/
namespace Jihoo.NativeKernel.NativeCoreTakeNormal

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Error Progress GhostNormalization Refines
  nodeResult nodeResult_progress nodeResult_refines normalizeOperands normalizeOperands_progress normalizeOperands_refines)
open NativeCoreCaseNormal (appendApplications appendApplications_progress appendApplications_refines)

abbrev Visit := State → Nat → Outcome Nat

private def next (outcome : Outcome Nat) (continuation : Visit) : Outcome Nat :=
  match outcome.result with
  | .error reason => ⟨outcome.state, .error reason⟩
  | .ok ref => continuation outcome.state ref

private def given (arena : Arena) (root : Nat) : Option (Bool × Nat × Nat × Nat) :=
  match arena[root]? with
  | some (.node (.give erased) [motive, owner, value]) => some (erased, motive, owner, value)
  | _ => none

private theorem given_lookup (found : given arena root = some (erased, motive, owner, value)) :
    arena[root]? = some (.node (.give erased) [motive, owner, value]) := by
  unfold given at found
  split at found
  · simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl, rfl, rfl⟩ := found
    assumption
  · contradiction

/-- The two applications are committed in order. Either failure preserves
the exact partial spine and prevents entry into the child normalizer. -/
def applyGiven (visit : Visit) (state : State) (continuation owner value : Nat) : Outcome Nat :=
  next (appendApplications state continuation [owner, value]) visit

def finish (visit : Visit) (state : State) (root : Nat) (before : List Nat)
    (packed continuation : Nat) : Outcome Nat :=
  match given state.arena packed with
  | some (_, _, owner, value) => applyGiven visit state continuation owner value
  | none => next (visit state continuation) fun after normalized =>
      nodeResult after root .take before [packed, normalized]

def walk (visit : Visit) (state : State) (root packed continuation : Nat) : Outcome Nat :=
  next (visit state packed) fun after normalized =>
    finish visit after root [packed, continuation] normalized continuation

/-- A singleton visit of the existing child normalizer. -/
def visitChild (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  let visited := normalizeOperands limit depth state [root]
  ⟨visited.state, match visited.result with
    | .error reason => .error reason
    | .ok [selected] => .ok selected
    | .ok _ => .error (.outsideFragment root)⟩

/-- Exact Take-root scheduling with the existing child normalizer. -/
def run (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  let paid := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let entered := {state with steps := paid.2}
  match paid.1 with
  | .error reason => ⟨entered, .error (.tick reason)⟩
  | .ok () =>
      match entered.arena[root]? with
      | some (.node .take [packed, continuation]) =>
          walk (visitChild limit (depth - 1)) entered root packed continuation
      | _ => ⟨entered, .error (.outsideFragment root)⟩

theorem finish_known (read : state.arena[packed]? = some (.node (.give erased) [motive, owner, value])) :
    finish visit state root before packed continuation = applyGiven visit state continuation owner value := by
  simp only [finish, given, read]

theorem finish_neutral (read : given state.arena packed = none) :
    finish visit state root before packed continuation =
      next (visit state continuation) fun after normalized =>
        nodeResult after root .take before [packed, normalized] := by
  simp only [finish, read]

private theorem next_progress (first : Progress limit state pending)
    (later : ∀ ref, Progress limit pending.state (visit pending.state ref)) :
    Progress limit state (next pending visit) := by
  cases status : pending.result with
  | error reason =>
      simp only [next, status]
      exact ⟨first.kept, first.monotone, first.bounded, fun _ _ found => by cases found⟩
  | ok ref =>
      have continuation := later ref
      simp only [next, status]
      exact ⟨first.kept.trans continuation.kept, Nat.le_trans first.monotone continuation.monotone,
        fun room => continuation.bounded (first.accepted room ref status),
        fun room output done => continuation.accepted (first.accepted room ref status) output done⟩

/-- Each Give application charges no normalization tick. If either one hits
the arena limit, the child visitor is left uncalled and the completed prefix
is retained. -/
theorem applyGiven_progress (visitor : ∀ state ref, Progress limit state (visit state ref)) :
    Progress limit state (applyGiven visit state continuation owner value) := by
  obtain ⟨kept, clock, _, _⟩ := appendApplications_progress state continuation [owner, value]
  have built : Progress limit state (appendApplications state continuation [owner, value]) :=
    ⟨kept, Nat.le_of_eq clock.symm, fun room => Nat.le.step (clock ▸ room), fun room _ _ => clock ▸ room⟩
  exact next_progress built (fun root => visitor _ root)

/-- A capacity failure leaves the exact number of application rows that
fit and returns at the original clock. -/
theorem applyGiven_term_limit
    (full : NativeCoreGraph.entryLimit - state.arena.size < 2) :
    let outcome := applyGiven visit state continuation owner value
    outcome.result = .error (.add .termLimit) ∧ Prefix state.arena outcome.state.arena ∧
      outcome.state.arena.size = state.arena.size + min 2 (NativeCoreGraph.entryLimit - state.arena.size) ∧
      outcome.state.steps = state.steps := by
  obtain ⟨kept, clock, length, capacity⟩ := appendApplications_progress state continuation [owner, value]
  have failed := capacity.mpr full
  simp only [applyGiven, next, failed]
  exact ⟨True.intro, kept, length, clock⟩

theorem walk_progress (visitor : ∀ state ref, Progress limit state (visit state ref)) :
    Progress limit state (walk visit state root packed continuation) := by
  apply next_progress (visitor _ _)
  intro normalized
  unfold finish
  split
  · exact applyGiven_progress visitor
  · exact next_progress (visitor _ _) (fun _ => nodeResult_progress _ _ _ _ _ _)

private theorem visitChild_result (success : (visitChild limit depth state root).result = .ok selected) :
    (normalizeOperands limit depth state [root]).result = .ok [selected] := by
  unfold visitChild at success
  cases found : (normalizeOperands limit depth state [root]).result with
  | error reason => simp [found] at success
  | ok refs =>
      cases refs with
      | nil => simp [found] at success
      | cons head rest =>
          cases rest with
          | nil =>
              simp only [found, Except.ok.injEq] at success
              cases success
              rfl
          | cons => simp [found] at success

theorem visitChild_progress (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (visitChild limit depth state root) := by
  have visited := normalizeOperands_progress limit depth state [root]
  exact ⟨visited.kept, visited.monotone, visited.bounded,
    fun room selected success => visited.accepted room [selected] (visitChild_result success)⟩

theorem run_progress (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (run limit depth state root) := by
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
  · rename_i packed continuation found
    have walked := walk_progress (state := entered) (visit := visitChild limit (depth - 1))
      (root := root) (packed := packed) (continuation := continuation)
      (visitChild_progress limit (depth - 1))
    have room := Nat.le_of_not_gt exhausted
    exact ⟨walked.kept, Nat.le_trans (Nat.le_succ _) walked.monotone,
      fun _ => walked.bounded room, fun _ => walked.accepted room⟩
  · exact rejected (.outsideFragment root)

abbrev VisitorSound (env : Environment) (visit : Visit) : Prop :=
  ∀ {state root term selected}, Represents state.arena root term →
    (visit state root).result = .ok selected → Refines env state term (visit state root) selected

theorem visitChild_refines (wf : UnifiedProgram.EnvWellFormed env) :
    VisitorSound env (visitChild limit depth) := by
  intro state root term selected represented success
  have raw := visitChild_result success
  obtain ⟨kept, backward, _, values, valuesRep, changes⟩ :=
    normalizeOperands_refines wf (.cons represented .nil) raw
  cases valuesRep with
  | cons value empty =>
      cases empty
      cases changes with
      | cons change tail =>
          cases tail
          exact ⟨kept, backward, _, value, change⟩

private def TakeContinuation : Term → Prop
  | .take _ continuation =>
      ∃ erased owner result body, continuation = .lam false owner (.lam erased result body)
  | _ => True

/-- Take's written continuation has the two binders required by typing. -/
theorem continuation_shape
    (typed : LoanTyping.HasType env loans ctx mode (.take packed continuation) type) :
    ∃ erased owner result body, continuation = .lam false owner (.lam erased result body) := by
  change TakeContinuation (.take packed continuation)
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term _ _ => TakeContinuation term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case dataElim => split <;> trivial
  case take => exact ⟨_, _, _, _, rfl⟩

private theorem give_represented
    (packed : Represents arena ref term)
    (givenRow : arena[ref]? = some (.node (.give erased) [motiveRef, ownerRef, valueRef])) :
    ∃ motive owner value, term = .give erased motive owner value ∧ Represents arena ownerRef owner ∧
      Represents arena valueRef value := by
  cases packed with
  | var read => rw [read] at givenRow; cases givenRow
  | node read _ children =>
      obtain ⟨rfl, rfl⟩ := Node.node.inj (Option.some.inj (read.symm.trans givenRow))
      cases children with
      | cons motive tail =>
          cases tail with
          | cons owner tail =>
              cases tail with
              | cons value empty =>
                  cases empty
                  exact ⟨_, _, _, rfl, owner, value⟩

structure Preserves (env : Environment) (start : State) (outcome : Outcome Nat) (selected : Nat)
    (ctx : Context) (type : Term) : Prop where
  kept : Prefix start.arena outcome.state.arena
  backward : Backward start.arena → Backward outcome.state.arena
  value : ∃ residual, Represents outcome.state.arena selected residual ∧ LoanTyping.HasType env [] ctx true residual type

/-- The current raw conversion preserves both rigid heads. A Take that
returns an allocation by the operational equation needs typed preservation. -/
theorem take_allocation_separate (valid : EnvironmentDelta.Admissible env) :
    ¬ RawLend.Conv env (.take packed continuation) (.alloc size init) := by
  intro related
  exact RawLend.Conv.full_rigid_disjoint (op := .take) (op' := .alloc) rfl rfl (by decide) related valid

/-- The exact native left-associated application spine receives the original
Take type. The returning visitor only sees it after both allocations. -/
theorem applyGiven_preserves (wf : UnifiedProgram.EnvWellFormed env) (visitor : VisitorSound env visit)
    (continuationRep : Represents state.arena continuationRef continuation)
    (ownerRep : Represents state.arena ownerRef owner) (valueRep : Represents state.arena valueRef value)
    (typed : LoanTyping.HasType env loans ctx mode (.take (.give erased motive owner value) continuation) type)
    (success : (applyGiven visit state continuationRef ownerRef valueRef).result = .ok selected) :
    Preserves env state (applyGiven visit state continuationRef ownerRef valueRef) selected ctx type := by
  obtain ⟨flag, binder, domain, body, rfl⟩ := continuation_shape typed
  cases emitted : (appendApplications state continuationRef [ownerRef, valueRef]).result with
  | error reason => simp [applyGiven, next, emitted] at success
  | ok spine =>
      simp only [applyGiven, next, emitted] at success ⊢
      obtain ⟨kept, backward, _, held⟩ :=
        appendApplications_refines continuationRep (.cons ownerRep (.cons valueRep .nil)) emitted
      have appTyped := LoanTyping.take_give_ghost_preservation wf typed
      obtain ⟨later, laterBackward, residual, represented, change⟩ := visitor held success
      exact ⟨kept.trans later, fun checked => laterBackward (backward checked), residual, represented,
        change.raw.typed appTyped⟩

private theorem neutral_preserves (wf : UnifiedProgram.EnvWellFormed env) (visitor : VisitorSound env visit)
    (rootRead : state.arena[root]? = some (.node .take before))
    (packedRep : Represents state.arena packed term) (continuationRep : Represents state.arena continuation body)
    (typed : LoanTyping.HasType env loans ctx mode (.take term body) type)
    (success : (next (visit state continuation) fun after normalized =>
        nodeResult after root .take before [packed, normalized]).result = .ok selected) :
    Preserves env state (next (visit state continuation) fun after normalized =>
        nodeResult after root .take before [packed, normalized]) selected ctx type := by
  cases returned : (visit state continuation).result with
  | error reason => simp [next, returned] at success
  | ok normalized =>
      simp only [next, returned] at success ⊢
      obtain ⟨kept, backward, residual, bodyRep, change⟩ := visitor continuationRep returned
      obtain ⟨later, laterBackward, rebuilt, outputRep, rebuildChange⟩ :=
        nodeResult_refines (kept.lookup rootRead) (.cons (packedRep.frame kept) (.cons bodyRep .nil)) rfl success
      have childrenChanged := GhostNormalization.node wf (op := .take) (by decide) rfl
        (.cons (.refl term) (.cons change .nil))
      exact ⟨kept.trans later, fun old => laterBackward (backward old), rebuilt, outputRep,
        (childrenChanged.trans rebuildChange).raw.typed typed⟩

theorem finish_preserves (wf : UnifiedProgram.EnvWellFormed env) (visitor : VisitorSound env visit)
    (rootRead : state.arena[root]? = some (.node .take before))
    (packedRep : Represents state.arena packed term) (continuationRep : Represents state.arena continuation body)
    (typed : LoanTyping.HasType env loans ctx mode (.take term body) type)
    (success : (finish visit state root before packed continuation).result = .ok selected) :
    Preserves env state (finish visit state root before packed continuation) selected ctx type := by
  cases inspected : given state.arena packed with
  | none =>
      rw [finish_neutral inspected] at success ⊢
      exact neutral_preserves wf visitor rootRead packedRep continuationRep typed success
  | some payload =>
      obtain ⟨erased, motive, owner, value⟩ := payload
      have read := given_lookup inspected
      rw [finish_known read] at success ⊢
      obtain ⟨_, _, _, rfl, ownerRep, valueRep⟩ := give_represented packedRep read
      exact applyGiven_preserves wf visitor continuationRep ownerRep valueRep typed success

/-- Normalize the packed operand first, and transport the exact source type
before inspecting its head. The neutral and known branches then share the
same representation and preservation endpoint. -/
theorem walk_preserves (wf : UnifiedProgram.EnvWellFormed env) (visitor : VisitorSound env visit)
    (rootRead : state.arena[root]? = some (.node .take [packed, continuation]))
    (packedRep : Represents state.arena packed term) (continuationRep : Represents state.arena continuation body)
    (typed : LoanTyping.HasType env loans ctx mode (.take term body) type)
    (success : (walk visit state root packed continuation).result = .ok selected) :
    Preserves env state (walk visit state root packed continuation) selected ctx type := by
  cases returned : (visit state packed).result with
  | error reason => simp [walk, next, returned] at success
  | ok normalized =>
      simp only [walk, next, returned] at success ⊢
      obtain ⟨kept, backward, residual, represented, packedChange⟩ := visitor packedRep returned
      have transformed := GhostNormalization.node wf (op := .take) (by decide) rfl
        (.cons packedChange (.cons (.refl body) .nil))
      obtain ⟨later, laterBackward, value⟩ := finish_preserves wf visitor
        (kept.lookup rootRead) represented (continuationRep.frame kept) (transformed.raw.typed typed) success
      exact ⟨kept.trans later, fun checked => laterBackward (backward checked), value⟩

theorem run_preserves (wf : UnifiedProgram.EnvWellFormed env) (represented : Represents state.arena root (.take packed body))
    (typed : LoanTyping.HasType env loans ctx mode (.take packed body) type)
    (success : (run limit depth state root).result = .ok selected) :
    Preserves env state (run limit depth state root) selected ctx type := by
  cases paid : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root with
  | mk result clock =>
      cases result with
      | error reason => simp [run, paid] at success
      | ok charged =>
          cases charged
          cases represented with
          | node read _ children =>
              cases children with
              | cons packedRep tail =>
                  cases tail with
                  | cons continuationRep empty =>
                      cases empty
                      simp only [run, paid, read] at success ⊢
                      obtain ⟨kept, backward, value⟩ :=
                        walk_preserves (state := {state with steps := clock}) wf (visitChild_refines wf)
                          read packedRep continuationRep typed success
                      exact ⟨kept, backward, value⟩

namespace Examples

private def bufferType : Term := .buffer (.natural 2)
private def owner : Term := .alloc (.natural 2) (.integer 0)
private def motive : Term := .lam false bufferType .u64
private def packed : Term := .give false motive owner (.natural 7)
private def exposed : Term := .app (.lam false .u64 packed) (.natural 0)
private def continuation : Term := .lam false bufferType (.lam false .u64 (.var 1))
private def source : Term := .take exposed continuation
private def originalType : Term := .buffer (.uadd (.natural 1) (.natural 1))
private def definition : GlobalDeclaration := ⟨originalType, source⟩
private def env : Environment := ⟨#[definition], #[]⟩
private def arena : Arena := #[.node (.natural 2) [], .node .buffer [0], .node .u64 [],
  .node (.lam false) [1, 2], .node (.integer 0) [], .node .alloc [0, 4], .node (.natural 7) [],
  .node (.give false) [3, 5, 6], .node (.lam false) [2, 7], .node (.natural 0) [], .node .app [8, 9],
  .var 1, .node (.lam false) [2, 11], .node (.lam false) [1, 12], .node .take [10, 13]]
private def state : State := ⟨arena, 0⟩
private def emitted : Arena := arena ++ #[.node .app [13, 5], .node .app [15, 6]]
private def resultArena : Arena := emitted.push (.node (.lam false) [2, 5])

private theorem admitted : LoanTyping.MixedProgram.History [definition] [] env :=
  LoanTyping.MixedProgram.checkProgram_sound
    (by cbv : LoanTyping.MixedProgram.checkProgram 64 128 [definition] [] = some env)

/-- The mixed checker accepts an owning result. The live packed visit
exposes Give through beta reduction, emits both applications, then returns
the existing allocation at the original converted Buffer type. -/
theorem checked_take_exposes_give_and_returns_owner :
    visitChild 96 31 ⟨arena, 1⟩ 10 = ⟨⟨arena, 32⟩, .ok 7⟩ ∧
      run 96 32 state 14 = ⟨⟨resultArena, 61⟩, .ok 5⟩ ∧
      LoanTyping.HasType env [] [] true owner originalType := by
  have packedVisit : visitChild 96 31 ⟨arena, 1⟩ 10 = ⟨⟨arena, 32⟩, .ok 7⟩ := by cbv
  have found : env.globals[0]? = some definition := rfl
  obtain ⟨_, _, typed⟩ := admitted.global_typing found
  have checked : LoanTyping.HasType env [] [] true source originalType := typed.ghost []
  have represented : Represents arena 14 source := decode_sound (fuel := 16) (by cbv)
  have evaluated : run 96 32 state 14 = ⟨⟨resultArena, 61⟩, .ok 5⟩ := by cbv
  obtain ⟨residual, held, preserved⟩ :=
    (run_preserves admitted.wellFormed represented checked (congrArg Outcome.result evaluated)).value
  rw [evaluated] at held
  have actual : Represents resultArena 5 owner := decode_sound (fuel := 16) (by cbv)
  exact ⟨packedVisit, evaluated, held.unique actual ▸ preserved⟩

theorem checked_owner_returns_through_operational_equation :
    ¬ RawLend.Conv env source owner :=
  take_allocation_separate admitted.wellFormed.admissible

/-- Exhaustion on the first reentry tick keeps both application rows.
The continuation has yet to be visited at this point. -/
theorem reentry_exhaustion_keeps_both_applications :
    run 32 32 state 14 = ⟨⟨emitted, 33⟩, .error (.tick (.stepLimit 16))⟩ := by cbv

private def neutralArena : Arena := arena ++ #[.var 0, .node .take [15, 13]]
private def neutralSource : Term := .take (.var 0) continuation
private def neutralContext : Context := [⟨.back false bufferType motive, false⟩]

/-- A neutral operand still normalizes its continuation and reuses the
original Take row when both child references remain unchanged. -/
theorem checked_neutral_take_reuses_row :
    let start : State := ⟨neutralArena, 0⟩
    run 32 16 start 16 = ⟨⟨neutralArena, 8⟩, .ok 16⟩ ∧
      Preserves env start (run 32 16 start 16) 16 neutralContext originalType := by
  have checked : LoanTyping.Checker.check 64 env [] neutralContext true neutralSource originalType = true := by cbv
  have represented : Represents neutralArena 16 neutralSource := decode_sound (fuel := 16) (by cbv)
  have evaluated : run 32 16 ⟨neutralArena, 0⟩ 16 = ⟨⟨neutralArena, 8⟩, .ok 16⟩ := by cbv
  exact ⟨evaluated, run_preserves admitted.wellFormed represented (LoanTyping.Checker.check_sound checked)
    (congrArg Outcome.result evaluated)⟩

end Examples

end Jihoo.NativeKernel.NativeCoreTakeNormal
