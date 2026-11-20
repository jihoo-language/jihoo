import Jihoo.NativeCoreSignedEvaluation
import Jihoo.NativeCoreStrictNormal
import Jihoo.NativeCoreValueContexts

/-! The typed pure traversal composes value contractions beneath parents
with independently typed operands, using the native order and clock. -/
namespace Jihoo.NativeKernel.NativeCoreValueTraversal

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCoreValueContexts (Change signature)
open NativeCorePureComputationNormal (Error Outcome Progress nodeResult nodeResult_exact nodeResult_progress
  visitOperands visitOperands_progress visitOperands_relates)
open NativeKernel.Conversion (ListRel)

inductive Frame : Op → Type where
  | strict : Frame .strict
  | arithmetic (op : Arith) : Frame (.arith op)
  | uniform : signature op = some inputs → Frame op

def frame (op : Op) : Option (Frame op) :=
  match op with
  | .strict => some .strict
  | .arith op => some (.arithmetic op)
  | op =>
      match found : signature op with
      | some _ => some (.uniform found)
      | none => none

def finish (kind : Frame op) (env : Environment) (childDepth root : Nat) (state : State)
    (before after : List Nat) : Outcome Nat :=
  match kind with
  | .strict =>
      match after with
      | [effect, rest] => NativeCoreStrictNormal.finish env childDepth root state before effect rest
      | _ => ⟨state, .error (.outsideFragment root)⟩
  | .arithmetic op =>
      match after with
      | [left, right] => NativeCoreSignedEvaluation.finish state root op before left right
      | _ => ⟨state, .error (.outsideFragment root)⟩
  | .uniform _ => nodeResult state root op before after

def walk (kind : Frame op) (visit : State → Nat → Outcome Nat) (env : Environment)
    (depth root : Nat) (state : State) (refs : List Nat) : Outcome Nat :=
  (visitOperands visit state refs).next fun state args => finish kind env depth root state refs args

private def charge (limit depth : Nat) (state : State) (root : Nat) (visit : State → Outcome Nat) : Outcome Nat :=
  let paid := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let entered := {state with steps := paid.2}
  match paid.1 with
  | .error reason => ⟨entered, .error (.tick reason)⟩
  | .ok () => visit entered

/-- An additional syntax-directed visit with access to the same recursive
driver at child depth, after the shared root tick. -/
structure Extension where
  accepts : Op → Bool
  walk : (State → Nat → Outcome Nat) → Nat → Nat → Nat → State → Op → List Nat → Outcome Nat

private def noExtension : Extension :=
  ⟨fun _ => false, fun _ _ _ root state _ _ => ⟨state, .error (.outsideFragment root)⟩⟩

def runWith (extension : Extension) (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (limit : Nat) :
    Nat → State → Nat → Outcome Nat
  | 0, state, root => NativeCoreIterationReentry.run env families limit 0 state root
  | depth + 1, state, root =>
      match state.arena[root]? with
      | some (.node op refs) =>
          let visit := runWith extension env families limit depth
          if extension.accepts op then charge limit (depth + 1) state root
            fun entered => extension.walk visit limit depth root entered op refs
          else
            match frame op with
            | some kind => charge limit (depth + 1) state root
                fun entered => walk kind visit env depth root entered refs
            | none => NativeCoreIterationReentry.run env families limit (depth + 1) state root
      | _ => NativeCoreIterationReentry.run env families limit (depth + 1) state root

/-- Recurse through covered value contexts. The underlying family walker
continues to handle dependent graph positions requiring raw conversion. -/
def run (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (limit depth : Nat)
    (state : State) (root : Nat) : Outcome Nat :=
  runWith noExtension env families limit depth state root

private theorem finish_progress (kind : Frame op) (env : Environment) (depth root : Nat)
    (state : State) (before after : List Nat) : Progress limit state (finish kind env depth root state before after) := by
  cases kind with
  | uniform => exact nodeResult_progress _ _ _ _ _ _
  | arithmetic op =>
      simp only [finish]
      split
      · exact NativeCoreSignedEvaluation.finish_progress _ _ _ _ _ _
      · exact Progress.atState _ _
  | strict =>
      simp only [finish]
      split
      · unfold NativeCoreStrictNormal.finish
        split
        · exact Progress.atState _ _
        · exact nodeResult_progress _ _ _ _ _ _
      · exact Progress.atState _ _

theorem walk_progress (visitor : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (walk kind visit env depth root state refs) :=
  (visitOperands_progress visitor state refs).next (fun args => finish_progress kind env depth root _ refs args)

private theorem charge_progress (later : ∀ state, Progress limit state (visit state)) :
    Progress limit state (charge limit depth state root visit) := by
  let entered := {state with steps := state.steps + 1}
  have rejected (reason : Error) : Progress limit state (⟨entered, .error reason⟩ : Outcome Nat) :=
    ⟨.refl _, Nat.le_succ _, fun room => Nat.succ_le_succ room, fun _ _ found => by cases found⟩
  by_cases exhausted : limit < state.steps + 1
  · simpa only [charge, NativeCoreUnsignedCancellation.tick, exhausted, ite_true, entered] using
      rejected (.tick (.stepLimit root))
  by_cases nesting : depth = 0
  · simpa only [charge, NativeCoreUnsignedCancellation.tick, exhausted, nesting, ite_false, ite_true, entered] using
      rejected (.tick (.depthLimit root))
  by_cases invalid : state.arena.size ≤ root
  · simpa only [charge, NativeCoreUnsignedCancellation.tick, exhausted, nesting, invalid, ite_false, ite_true, entered] using
      rejected (.tick (.invalidReference root))
  simp only [charge, NativeCoreUnsignedCancellation.tick, exhausted, nesting, invalid, ite_false]
  have completed := later entered
  have room := Nat.le_of_not_gt exhausted
  exact ⟨completed.kept, Nat.le_trans (Nat.le_succ _) completed.monotone,
    fun _ => completed.bounded room, fun _ => completed.accepted room⟩

def Extension.Metered (extension : Extension) : Prop :=
  ∀ {visit limit depth root state op refs}, extension.accepts op = true →
    (∀ state root, Progress limit state (visit state root)) →
    Progress limit state (extension.walk visit limit depth root state op refs)

theorem runWith_progress (metered : extension.Metered)
    (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (limit depth : Nat)
    (state : State) (root : Nat) : Progress limit state (runWith extension env families limit depth state root) := by
  induction depth generalizing state root with
  | zero => exact NativeCoreIterationReentry.run_progress _ _ _ _ _ _
  | succ depth ih =>
      simp only [runWith]
      split
      · split
        · rename_i accepted
          exact charge_progress (fun _ => metered accepted ih)
        · split
          · exact charge_progress (fun _ => walk_progress ih)
          · exact NativeCoreIterationReentry.run_progress _ _ _ _ _ _
      · exact NativeCoreIterationReentry.run_progress _ _ _ _ _ _

theorem run_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) : Progress limit state (run env families limit depth state root) :=
  runWith_progress (extension := noExtension) (by intro _ _ _ _ _ _ _ impossible; cases impossible)
    env families limit depth state root

structure Refines (env : Environment) (state : State) (input : Term)
    (output : Outcome Nat) (selected : Nat) : Prop where
  kept : Prefix state.arena output.state.arena
  backward : Backward state.arena → Backward output.state.arena
  value : ∃ residual, Represents output.state.arena selected residual ∧ Change env input residual

private theorem strict_result
    (read : state.arena[root]? = some (.node .strict before))
    (effect : Represents state.arena left a) (rest : Represents state.arena right b)
    (success : (NativeCoreStrictNormal.finish env depth root state before left right).result = .ok selected) :
    Refines env state (.strict a b) (NativeCoreStrictNormal.finish env depth root state before left right) selected := by
  by_cases discard : NativeCoreStrictNormal.discardPrefix env state.arena depth left = true
  · simp only [NativeCoreStrictNormal.finish, ite_eq_left discard, Except.ok.injEq] at success ⊢
    subst selected
    exact ⟨.refl _, id, b, rest, Change.discard⟩
  · simp only [NativeCoreStrictNormal.finish, ite_eq_right discard] at success ⊢
    obtain ⟨kept, backward, result⟩ := nodeResult_exact read (.cons effect (.cons rest .nil)) rfl success
    exact ⟨kept, backward, _, result, ⟨id, id⟩⟩

private theorem arithmetic_result
    (read : state.arena[root]? = some (.node (.arith op) before))
    (leftRep : Represents state.arena left a) (rightRep : Represents state.arena right b)
    (success : (NativeCoreSignedEvaluation.finish state root op before left right).result = .ok selected) :
    Refines env state (.arith op a b) (NativeCoreSignedEvaluation.finish state root op before left right) selected := by
  obtain ⟨kept, backward, result⟩ := NativeCoreSignedEvaluation.finish_exact read leftRep rightRep success
  refine ⟨kept, backward, _, result, ?_⟩
  cases folded : NativeCoreSignedEvaluation.foldAt state.arena op left right with
  | none => exact ⟨id, id⟩
  | some word =>
      obtain ⟨x, y, rfl, rfl⟩ := NativeCoreSignedEvaluation.foldAt_literals leftRep rightRep folded
      have checked {ctx type} (typed : LoanTyping.HasType env [] ctx true (.arith op (.integer x) (.integer y)) type) :
          LoanTyping.HasType env [] ctx true (.integer word.toInt) type := by
        have computes := NativeCoreSignedEvaluation.foldAt_refines leftRep rightRep typed
        have branch : ValueReduction.contract (.arith op (.integer x) (.integer y)) = some (.integer word.toInt) :=
          by simpa only [folded, Option.map_some] using computes.symm
        exact LoanTyping.value_root_ghost_preservation (ValueReduction.contract_sound branch) typed
      refine ⟨fun typed => checked typed, ?_⟩
      simp only [Option.map_some, Option.getD_some, EnvironmentDelta.expand_node_cons,
        EnvironmentDelta.expand, EnvironmentDelta.expandArgs]
      exact fun typed => checked typed

private theorem pair_operands (represented : RepresentsList arena refs after)
    (count : refs.length = 2) (moves : ListRel (Change env) before after) :
    ∃ x y a b a' b', refs = [x, y] ∧ before = [a, b] ∧ after = [a', b'] ∧
      Represents arena x a' ∧ Represents arena y b' ∧ Change env a a' ∧ Change env b b' := by
  cases represented with
  | nil => simp at count
  | cons left more =>
      cases more with
      | nil => simp at count
      | cons right more =>
          cases more with
          | cons => simp at count
          | nil =>
              cases moves with
              | cons first more =>
                  cases more with
                  | cons second remaining =>
                      cases remaining
                      exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, left, right, first, second⟩

/-- A native root rebuild or value contraction preserves the type of its
original syntax after the ordinary recursive child visits. -/
theorem walk_refines (kind : Frame op)
    (visitor : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → Refines env state term (visit state ref) selected)
    (read : state.arena[root]? = some (.node op refs)) (represented : RepresentsList state.arena refs before)
    (arity : refs.length = op.arity)
    (success : (walk kind visit env depth root state refs).result = .ok selected) :
    Refines env state (.node op before) (walk kind visit env depth root state refs) selected := by
  unfold walk at success ⊢
  obtain ⟨found, visited, branch⟩ := Outcome.next_success success
  rw [branch] at success ⊢
  obtain ⟨kept, backward, length, after, represented, moves⟩ :=
    visitOperands_relates (relation := Change env) represented
      (fun input done => by
        obtain ⟨kept, backward, value⟩ := visitor input done
        exact ⟨kept, backward, value⟩) visited
  have count := length.trans arity
  have current := kept.lookup read
  cases kind with
  | uniform sig =>
      obtain ⟨more, backed, held⟩ := nodeResult_exact current represented count success
      exact ⟨kept.trans more, fun old => backed (backward old), _, held, Change.uniform sig moves⟩
  | strict =>
      obtain ⟨x, y, a, b, a', b', rfl, rfl, rfl, left, right, effect, value⟩ := pair_operands represented count moves
      obtain ⟨more, backed, residual, held, reduced⟩ := strict_result current left right success
      exact ⟨kept.trans more, fun old => backed (backward old), residual, held, (Change.strict effect value).trans reduced⟩
  | arithmetic op =>
      obtain ⟨x, y, a, b, a', b', rfl, rfl, rfl, left, right, first, second⟩ := pair_operands represented count moves
      obtain ⟨more, backed, residual, held, reduced⟩ := arithmetic_result current left right success
      have changed := Change.uniform (op := .arith op) rfl (.cons first (.cons second .nil))
      exact ⟨kept.trans more, fun old => backed (backward old), residual, held, changed.trans reduced⟩

def Extension.Sound (extension : Extension) (env : Environment) : Prop :=
  ∀ {visit limit depth root state op refs args selected},
    extension.accepts op = true → state.arena[root]? = some (.node op refs) →
    RepresentsList state.arena refs args → refs.length = op.arity →
    (∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → Refines env state term (visit state ref) selected) →
    (extension.walk visit limit depth root state op refs).result = .ok selected →
    Refines env state (.node op args) (extension.walk visit limit depth root state op refs) selected

theorem runWith_refines {families : List NativeFamilyWire.FamilyRoots}
    (sound : extension.Sound env)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (represented : Represents state.arena root input)
    (success : (runWith extension env families limit depth state root).result = .ok selected) :
    Refines env state input (runWith extension env families limit depth state root) selected := by
  have base {state root input selected depth} (represented : Represents state.arena root input)
      (success : (NativeCoreIterationReentry.run env families limit depth state root).result = .ok selected) :
      Refines env state input (NativeCoreIterationReentry.run env families limit depth state root) selected := by
    obtain ⟨kept, backward, residual, held, changed⟩ :=
      NativeCoreIterationReentry.run_refines history represented success
    exact ⟨kept, backward, residual, held, Change.iteration changed⟩
  induction depth generalizing state root input selected with
  | zero => exact base represented success
  | succ depth ih =>
      cases represented with
      | var read =>
          simp only [runWith, read] at success ⊢
          exact base (.var read) success
      | @node _ op refs args read arity children =>
          by_cases accepted : extension.accepts op = true
          ·
              rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root with
                ⟨status, clock⟩
              cases status with
              | error reason => simp [runWith, read, accepted, charge, paid] at success
              | ok charged =>
                  cases charged
                  simp only [runWith, read, ite_eq_left accepted, charge, paid] at success ⊢
                  obtain ⟨kept, backward, value⟩ :=
                    sound (state := {state with steps := clock}) accepted read children arity
                      (fun source done => ih source done) success
                  exact ⟨kept, backward, value⟩
          · cases chosen : frame op with
            | none =>
                simp only [runWith, read, ite_eq_right accepted, chosen] at success ⊢
                exact base (.node read arity children) success
            | some kind =>
                rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root with
                  ⟨status, clock⟩
                cases status with
                | error reason => simp [runWith, read, accepted, chosen, charge, paid] at success
                | ok charged =>
                    cases charged
                    simp only [runWith, read, ite_eq_right accepted, chosen, charge, paid] at success ⊢
                    obtain ⟨kept, backward, value⟩ :=
                      walk_refines (state := {state with steps := clock}) kind
                        (fun source done => ih source done) read children arity success
                    exact ⟨kept, backward, value⟩

theorem run_refines {families : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (represented : Represents state.arena root input)
    (success : (run env families limit depth state root).result = .ok selected) :
    Refines env state input (run env families limit depth state root) selected :=
  runWith_refines (extension := noExtension)
    (by intro _ _ _ _ _ _ _ _ _ impossible; cases impossible) history represented success

/-- A covered stored declaration keeps the type from its exact-byte mixed
admission through the combined recursive visitor. -/
theorem admitted_program_preserves
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : NativeProgramWire.Roots},
        snapshot.definitions[index]? = some row →
        (run env snapshot.families limit depth ⟨snapshot.arena, initial⟩ row.valueRoot).result = .ok selected →
        let output := run env snapshot.families limit depth ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected residual ∧
          LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial selected row found success
  obtain ⟨entry, _, read, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  obtain ⟨kept, preserved, residual, held, change⟩ := run_refines history source.2 success
  exact ⟨entry, residual, read, kept, preserved backward, held, change.expanded (typed.ghost [])⟩

namespace Examples

private def smallSum : Term := .arith .add (.integer 1) (.integer 2)
private def sum : Term := .arith .add (.integer 3) (.integer 4)
private def strictProduct : Term := .arith .mul (.strict smallSum sum) (.integer 6)
private def overflow : Term := .arith .add (.integer (2^63-1)) (.integer 1)
private def motive : Term := .lam false .u64 .u64
private def step : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (.natural 0)) (.lam false .u64 (.var 0)))
private def length : Term := .loop (.natural 0) motive (.natural 2) step
private def elements : GlobalDeclaration := ⟨.array (.natural 2), .elements 2 [strictProduct, .integer 2]⟩
private def buffer : GlobalDeclaration := ⟨.univ 0, .buffer (.strict overflow length)⟩
private def env : Environment := ⟨#[elements, buffer], #[]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨26, 25⟩, ⟨2, 24⟩]
  families := []
  arena := #[.node .u64 [], .node .i64 [], .node (.universe 0) [],
    .node (.integer 1) [], .node (.integer 2) [], .node (.integer 3) [], .node (.integer 4) [],
    .node (.integer 6) [], .node (.arith .add) [3, 4], .node (.arith .add) [5, 6],
    .node .strict [8, 9], .node (.arith .mul) [10, 7], .node (.integer (2^63-1)) [],
    .node (.arith .add) [12, 3], .node (.natural 0) [], .node (.natural 2) [], .var 0,
    .node (.lam false) [0, 0], .node .lt [16, 14], .node (.lam false) [0, 16],
    .node (.lam true) [18, 19], .node (.lam false) [0, 20], .node .loop [14, 17, 15, 21],
    .node .strict [13, 22], .node .buffer [23], .node (.elements 2) [11, 4], .node .array [15]]

private def start : State := ⟨snapshot.arena, 0⟩
private def arithmeticRows : Arena := #[.node (.integer 3) [], .node (.integer 7) [], .node (.integer 42) []]
private def arrayResult := (snapshot.arena ++ arithmeticRows).push (.node (.elements 2) [29, 4])
private def bufferResult := (snapshot.arena.push (.node .strict [13, 15])).push (.node .buffer [27])
private theorem checkedHistory : LoanTyping.MixedProgram.History [elements, buffer] [] env :=
  LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)

/-- Both signed child contractions precede Strict's discard decision. The
parent product then folds to 42 inside the Elements declaration. -/
theorem checked_nested_strict_arithmetic :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run env [] 11 20 start 25 = ⟨⟨arrayResult, 11⟩, .ok 30⟩ ∧
    run env [] 10 20 start 25 = ⟨⟨snapshot.arena ++ arithmeticRows, 11⟩, .error (.tick (.stepLimit 4))⟩ ∧
    LoanTyping.HasType env [] [] true (.elements 2 [.integer 42, .integer 2]) elements.type := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have computed : run env [] 11 20 start 25 = ⟨⟨arrayResult, 11⟩, .ok 30⟩ := by cbv
  have source : Represents start.arena 25 elements.value := decode_sound (fuel := 12) rfl
  have typed := (checkedHistory.global_typing (index := 0) (declaration := elements) rfl).choose_spec.2
  obtain ⟨_, _, _, held, change⟩ := run_refines checkedHistory source (congrArg Outcome.result computed)
  rw [computed] at held
  have expected : Represents arrayResult 30 (.elements 2 [.integer 42, .integer 2]) := decode_sound (fuel := 4) rfl
  exact ⟨admitted, computed, by cbv, held.unique expected ▸ change.raw (typed.ghost [])⟩

/-- An overflowing Strict prefix remains live while the Buffer's nested
zero Loop returns its initializer without visiting the callback. -/
theorem checked_buffer_retains_overflow_and_skips_loop :
    run env [] 8 20 start 24 = ⟨⟨bufferResult, 8⟩, .ok 28⟩ ∧
    LoanTyping.HasType env [] [] true (.buffer (.strict overflow (.natural 2))) buffer.type := by
  have computed : run env [] 8 20 start 24 = ⟨⟨bufferResult, 8⟩, .ok 28⟩ := by cbv
  have source : Represents start.arena 24 buffer.value := decode_sound (fuel := 12) rfl
  have typed := (checkedHistory.global_typing (index := 1) (declaration := buffer) rfl).choose_spec.2
  obtain ⟨_, _, _, held, change⟩ := run_refines checkedHistory source (congrArg Outcome.result computed)
  rw [computed] at held
  have expected : Represents bufferResult 28 (.buffer (.strict overflow (.natural 2))) :=
    decode_sound (fuel := 8) rfl
  exact ⟨computed, held.unique expected ▸ change.raw (typed.ghost [])⟩

end Examples

end Jihoo.NativeKernel.NativeCoreValueTraversal
