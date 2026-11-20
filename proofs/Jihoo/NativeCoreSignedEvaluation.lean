import Jihoo.NativeCoreArithmeticMachine
import Jihoo.NativeCorePureComputationNormal

/-! The native signed operation after its two recursive child visits. The
Int128/Int64 arithmetic proof supplies the exact literal decision, while
nodeResult implements ordinary reuse and rebuilding for retained arithmetic. -/
namespace Jihoo.NativeKernel.NativeCoreSignedEvaluation

open Environment NativeArena
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Error Progress GhostNormalization nodeResult
  nodeResult_exact nodeResult_progress normalizeOperands normalizeOperands_refines
  normalizeOperands_progress)
open NativeKernel.Conversion (ListRel)
open ValueReduction (contract foldArithmetic signed64)

private def numberAt (arena : Arena) (root : Nat) : Option Int :=
  match arena[root]? with
  | some (.node (.integer value) []) => some value
  | _ => none

private def integerValue : Term → Option Int
  | .integer value => some value
  | _ => none

def foldAt (arena : Arena) (op : Arith) (left right : Nat) : Option Int64 := do
  let first ← numberAt arena left
  let second ← numberAt arena right
  foldArithmetic op (Int64.ofInt first) (Int64.ofInt second)

def finish (state : State) (root : Nat) (op : Arith) (before : List Nat) (left right : Nat) : Outcome Nat :=
  match foldAt state.arena op left right with
  | none => nodeResult state root (.arith op) before [left, right]
  | some folded =>
      match NativeCoreGraph.addNode state.arena (.node (.integer folded.toInt) []) with
      | .error reason => ⟨state, .error (.add reason)⟩
      | .ok (arena, result) => ⟨{state with arena}, .ok result⟩

def walk (visit : State → List Nat → Outcome (List Nat)) (state : State)
    (root : Nat) (op : Arith) (left right : Nat) : Outcome Nat :=
  (visit state [left, right]).next fun visited refs =>
    match refs with
    | [first, second] => finish visited root op [left, right] first second
    | _ => ⟨visited, .error (.outsideFragment root)⟩

def run (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  let paid := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let entered := {state with steps := paid.2}
  match paid.1 with
  | .error reason => ⟨entered, .error (.tick reason)⟩
  | .ok () =>
      match state.arena[root]? with
      | some (.node (.arith op) [left, right]) =>
          walk (normalizeOperands limit (depth - 1)) entered root op left right
      | _ => ⟨entered, .error (.outsideFragment root)⟩

private def InputFacts (env : Environment) (ctx : Context) : Term → Prop
  | .integer value => signed64 value
  | .arith _ left right => LoanTyping.HasType env [] ctx true left .i64 ∧ LoanTyping.HasType env [] ctx true right .i64
  | _ => True

private theorem input_facts (typed : LoanTyping.HasType env [] ctx true term type) : InputFacts env ctx term := by
  have initial : ∀ loans mode, LoanTyping.HasType env loans ctx mode term type → InputFacts env ctx term := by
    intro loans mode h
    apply LoanTyping.HasType.rec (t := h)
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun _ context _ term _ _ => InputFacts env context term)
      (motive_3 := fun _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ => True)
    all_goals intros
    all_goals first | trivial | assumption | skip
    case arith left right _ _ => exact ⟨left.ghost [], right.ghost []⟩
    case dataElim => split <;> trivial
  exact initial [] true typed

private theorem number_matches (represented : Represents arena root term) :
    numberAt arena root = integerValue term := by
  cases represented with
  | var read => simp only [numberAt, read, integerValue]
  | @node _ op refs terms read arity children =>
      simp only [numberAt, read]
      cases op <;> try rfl
      case integer value =>
        cases children with
        | nil => rfl
        | cons => cases arity

private theorem integerValue_eq (read : integerValue term = some value) :
    term = .integer value := by
  fun_cases integerValue term <;> simp_all [integerValue]

private theorem contract_literal_pair (op : Arith) (left right : Term) :
    contract (.arith op left right) =
      match integerValue left, integerValue right with
      | some a, some b => contract (.arith op (.integer a) (.integer b))
      | _, _ => none := by
  fun_cases integerValue left <;> fun_cases integerValue right <;> simp_all [contract]

/-- Typed children supply the I64 bounds required to interpret the raw
integer rows. The graph decision then agrees exactly with the contractor. -/
theorem foldAt_refines
    (leftRep : Represents arena left first) (rightRep : Represents arena right second)
    (typed : LoanTyping.HasType env [] ctx true (.arith op first second) type) :
    (foldAt arena op left right).map (fun word => Term.integer word.toInt) = contract (.arith op first second) := by
  have ⟨leftTyped, rightTyped⟩ := show InputFacts env ctx (.arith op first second) from input_facts typed
  simp only [foldAt, number_matches leftRep, number_matches rightRep]
  rw [contract_literal_pair]
  cases a : integerValue first with
  | none => rfl
  | some firstInt =>
      cases b : integerValue second with
      | none => rfl
      | some secondInt =>
          have leftBound : signed64 firstInt := by
            rw [integerValue_eq a] at leftTyped
            exact input_facts leftTyped
          have rightBound : signed64 secondInt := by
            rw [integerValue_eq b] at rightTyped
            exact input_facts rightTyped
          change (foldArithmetic op (Int64.ofInt firstInt) (Int64.ofInt secondInt)).map _ = _
          simpa only [Int64.toInt_ofInt_of_le leftBound.1 leftBound.2,
            Int64.toInt_ofInt_of_le rightBound.1 rightBound.2] using
            ValueReduction.foldArithmetic_refines op (Int64.ofInt firstInt) (Int64.ofInt secondInt)

theorem finish_retains (failed : foldAt state.arena op left right = none) :
    finish state root op before left right = nodeResult state root (.arith op) before [left, right] := by
  simp only [finish, failed]

theorem finish_progress (state : State) (root : Nat) (op : Arith) (before : List Nat) (left right : Nat) :
    Progress limit state (finish state root op before left right) := by
  cases folded : foldAt state.arena op left right with
  | none => exact finish_retains folded ▸ nodeResult_progress state root (.arith op) before [left, right] true
  | some word =>
      simp only [finish, folded]
      cases added : NativeCoreGraph.addNode state.arena (.node (.integer word.toInt) []) with
      | error reason => exact Progress.atState _ _
      | ok pair =>
          obtain ⟨arena, root⟩ := pair
          exact ⟨(NativeCoreGraph.addNode_commits added).1, Nat.le_refl _, Nat.le.step, fun room _ _ => room⟩

theorem walk_progress (visitor : ∀ state refs, Progress limit state (visit state refs)) :
    Progress limit state (walk visit state root op left right) := by
  unfold walk
  apply (visitor _ _).next
  intro refs
  split
  · exact finish_progress _ _ _ _ _ _
  · exact Progress.atState _ _

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
  · rename_i op left right found
    have walked := walk_progress (state := entered) (visit := normalizeOperands limit (depth - 1))
      (root := root) (op := op) (left := left) (right := right)
      (normalizeOperands_progress limit (depth - 1))
    have room := Nat.le_of_not_gt exhausted
    exact ⟨walked.kept, Nat.le_trans (Nat.le_succ _) walked.monotone,
      fun _ => walked.bounded room, fun _ => walked.accepted room⟩
  · exact rejected (.outsideFragment root)

theorem foldAt_literals
    (leftRep : Represents arena left first) (rightRep : Represents arena right second)
    (folded : foldAt arena op left right = some number) :
    ∃ a b, first = .integer a ∧ second = .integer b := by
  simp only [foldAt, number_matches leftRep, number_matches rightRep] at folded
  cases firstValue : integerValue first with
  | none => simp [firstValue] at folded
  | some a =>
      cases secondValue : integerValue second with
      | none => simp [firstValue, secondValue] at folded
      | some b => exact ⟨a, b, integerValue_eq firstValue, integerValue_eq secondValue⟩

/-- The exact represented result is determined by the native fold attempt.
The graph fact also applies to untyped inputs. -/
theorem finish_exact
    (read : state.arena[root]? = some (.node (.arith op) before))
    (leftRep : Represents state.arena left first) (rightRep : Represents state.arena right second)
    (success : (finish state root op before left right).result = .ok selected) :
    let output := finish state root op before left right
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      Represents output.state.arena selected
        (((foldAt state.arena op left right).map (fun value => Term.integer value.toInt)).getD (.arith op first second)) := by
  cases folded : foldAt state.arena op left right with
  | none =>
      rw [finish_retains folded] at success ⊢
      exact nodeResult_exact read (.cons leftRep (.cons rightRep .nil)) rfl success
  | some word =>
      simp only [finish, folded] at success ⊢
      cases added : NativeCoreGraph.addNode state.arena (.node (.integer word.toInt) []) with
      | error reason => simp [added] at success
      | ok pair =>
          obtain ⟨arena, result⟩ := pair
          simp only [added, Except.ok.injEq] at success
          subst result
          obtain ⟨kept, _, _, _, _, row⟩ := NativeCoreGraph.addNode_commits added
          exact ⟨kept, fun backward => NativeCoreGraph.addNode_preserves_backward backward added (by simp [Node.references]),
            .node row rfl .nil⟩

/-- The retained row or emitted literal denotes precisely the existing
signed value contraction, including its refusal to fold overflow. -/
theorem finish_refines
    (read : state.arena[root]? = some (.node (.arith op) before))
    (leftRep : Represents state.arena left first) (rightRep : Represents state.arena right second)
    (typed : LoanTyping.HasType env [] ctx true (.arith op first second) type)
    (success : (finish state root op before left right).result = .ok selected) :
    let output := finish state root op before left right
    let source := Term.arith op first second
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      Represents output.state.arena selected ((contract source).getD source) ∧
      LoanTyping.HasType env [] ctx true ((contract source).getD source) type := by
  have exactFold := foldAt_refines leftRep rightRep typed
  obtain ⟨kept, backward, result⟩ := finish_exact read leftRep rightRep success
  rw [exactFold] at result
  refine ⟨kept, backward, result, ?_⟩
  cases found : contract (.arith op first second) with
  | none => exact typed
  | some value => exact LoanTyping.value_root_ghost_preservation (ValueReduction.contract_sound found) typed

private theorem binary_visit
    (represented : RepresentsList arena refs terms) (length : refs.length = 2) :
    ∃ first second a b, refs = [first, second] ∧ terms = [a, b] ∧
      Represents arena first a ∧ Represents arena second b := by
  cases represented with
  | nil => contradiction
  | cons left more =>
      cases more with
      | nil => simp at length
      | cons right more =>
          cases more with
          | nil => exact ⟨_, _, _, _, rfl, rfl, left, right⟩
          | cons => simp at length

abbrev VisitSound (env : Environment) (visit : State → List Nat → Outcome (List Nat)) : Prop :=
  ∀ {state refs terms selected}, RepresentsList state.arena refs terms →
    (visit state refs).result = .ok selected →
    let output := visit state refs
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      selected.length = refs.length ∧
      ∃ residuals, RepresentsList output.state.arena selected residuals ∧ ListRel (GhostNormalization env) terms residuals

/-- The two visited operands produce the contractor's exact residual in the
shared arena. A typed visitor supplies the input and result bounds. -/
theorem walk_preserves (wf : UnifiedProgram.EnvWellFormed env) (visitor : VisitSound env visit)
    (read : state.arena[root]? = some (.node (.arith op) [leftRef, rightRef]))
    (leftRep : Represents state.arena leftRef left) (rightRep : Represents state.arena rightRef right)
    (typed : LoanTyping.HasType env loans ctx mode (.arith op left right) type)
    (success : (walk visit state root op leftRef rightRef).result = .ok selected) :
    let output := walk visit state root op leftRef rightRef
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧ LoanTyping.HasType env [] ctx true residual type := by
  simp only [walk, Outcome.next] at success ⊢
  cases visited : (visit state [leftRef, rightRef]).result with
  | error reason => simp [visited] at success
  | ok refs =>
      obtain ⟨kept, backward, count, _, residuals, changes⟩ := visitor (.cons leftRep (.cons rightRep .nil)) visited
      obtain ⟨first, second, a, b, rfl, rfl, firstRep, secondRep⟩ := binary_visit residuals count
      simp only [visited] at success ⊢
      have changed := GhostNormalization.node wf (op := .arith op) (by intro same; cases same) rfl changes
      obtain ⟨later, laterBackward, held, keptType⟩ :=
        finish_refines (kept.lookup read) firstRep secondRep (changed.raw.typed typed) success
      exact ⟨kept.trans later, fun old => laterBackward (backward old), _, held, keptType⟩

/-- Every successful arithmetic root over supported recursive operands
retains the exact input type and all previously committed graph rows. -/
theorem run_preserves (wf : UnifiedProgram.EnvWellFormed env)
    (represented : Represents state.arena root (.arith op left right))
    (typed : LoanTyping.HasType env loans ctx mode (.arith op left right) type)
    (success : (run limit depth state root).result = .ok selected) :
    let output := run limit depth state root
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧ LoanTyping.HasType env [] ctx true residual type := by
  rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root with ⟨status, clock⟩
  cases status with
  | error reason => simp [run, paid] at success
  | ok charged =>
      cases charged
      cases represented with
      | @node _ _ refs _ read arity children =>
          obtain ⟨leftRef, rightRef, _, _, rfl, inputs, leftRep, rightRep⟩ := binary_visit children arity
          simp only [List.cons.injEq, and_true] at inputs
          obtain ⟨rfl, rfl⟩ := inputs
          simp only [run, paid, read] at success ⊢
          exact walk_preserves (state := {state with steps := clock}) (visit := normalizeOperands limit (depth - 1))
            wf (fun source solved => normalizeOperands_refines wf source solved) read leftRep rightRep typed success

namespace Examples

private def env : Environment := Environment.empty
private theorem wellFormed : UnifiedProgram.EnvWellFormed env := UnifiedProgram.EnvWellFormed.empty
private def identity : Term := .lam false .i64 (.var 0)
private def maximum : Term := .integer 9223372036854775807
private def overflowSource : Term := .arith .add (.app identity maximum) (.integer 1)
private def overflowResult : Term := .arith .add maximum (.integer 1)
private def productSource : Term := .arith .mul (.app identity (.integer 6)) (.integer 7)
private def arena : Arena := #[.node .i64 [], .var 0, .node (.lam false) [0, 1],
  .node (.integer 9223372036854775807) [], .node (.integer 1) [], .node .app [2, 3],
  .node (.arith .add) [5, 4], .node (.integer 6) [], .node .app [2, 7], .node (.integer 7) [],
  .node (.arith .mul) [8, 9]]
private def state : State := ⟨arena, 0⟩

/-- The left beta redex changes the operand reference. Overflow retains
the arithmetic and requires a fresh row because that reference changed. -/
theorem checked_beta_exposes_retained_overflow :
    run 32 16 state 6 = ⟨⟨arena.push (.node (.arith .add) [3, 4]), 10⟩, .ok 11⟩ ∧
      contract overflowResult = none ∧ LoanTyping.HasType env [] [] true overflowResult .i64 := by
  have accepted : LoanTyping.Checker.check 48 env [] [] true overflowSource .i64 = true := by cbv
  have represented : Represents arena 6 overflowSource := decode_sound (fuel := 8) (by cbv)
  have evaluated : run 32 16 state 6 = ⟨⟨arena.push (.node (.arith .add) [3, 4]), 10⟩, .ok 11⟩ := by cbv
  obtain ⟨_, _, value, held, typed⟩ := run_preserves wellFormed represented
    (LoanTyping.Checker.check_sound accepted) (congrArg Outcome.result evaluated)
  rw [evaluated] at held
  have output : Represents (arena.push (.node (.arith .add) [3, 4])) 11 overflowResult :=
    decode_sound (fuel := 8) (by cbv)
  exact ⟨evaluated, by cbv, held.unique output ▸ typed⟩

theorem checked_beta_exposes_literal_product :
    run 32 16 state 10 = ⟨⟨arena.push (.node (.integer 42) []), 10⟩, .ok 11⟩ ∧
      LoanTyping.HasType env [] [] true (.integer 42) .i64 := by
  have accepted : LoanTyping.Checker.check 48 env [] [] true productSource .i64 = true := by cbv
  have represented : Represents arena 10 productSource := decode_sound (fuel := 8) (by cbv)
  have evaluated : run 32 16 state 10 = ⟨⟨arena.push (.node (.integer 42) []), 10⟩, .ok 11⟩ := by cbv
  obtain ⟨_, _, value, held, typed⟩ := run_preserves wellFormed represented
    (LoanTyping.Checker.check_sound accepted) (congrArg Outcome.result evaluated)
  rw [evaluated] at held
  have output : Represents (arena.push (.node (.integer 42) [])) 11 (.integer 42) :=
    decode_sound (fuel := 8) (by cbv)
  exact ⟨evaluated, held.unique output ▸ typed⟩

private def elements : Term := .elements 2 [.integer (-4), .integer 7]
private def index : Term := .app (.lam false .u64 (.var 0)) (.natural 1)
private def evidence : Term := .decide (.natural 1) (.natural 2)
private def indexSource : Term := .index elements index evidence
private def indexResult : Term := .index elements (.natural 1) evidence
private def indexArena : Arena := #[.node .i64 [], .node (.natural 1) [], .node (.natural 2) [],
  .node (.integer (-4)) [], .node (.integer 7) [], .node (.elements 2) [3, 4], .node .u64 [], .var 0,
  .node (.lam false) [6, 7], .node .app [8, 1], .node .decide [1, 2], .node .index [5, 9, 10]]

/-- Core.normal visits all three operands and retains Index. The abstract
array read separately selects the second value using the same typed inputs. -/
theorem checked_literal_index_is_retained :
    NativeCorePureComputationNormal.runWithConditionals 32 16 ⟨indexArena, 0⟩ 11 =
      ⟨⟨indexArena.push (.node .index [5, 1, 10]), 15⟩, .ok 12⟩ ∧
      LoanTyping.HasType env [] [] true indexResult .i64 ∧
      ACU.Computes indexResult (.integer 7) := by
  have accepted : LoanTyping.Checker.check 48 env [] [] true indexSource .i64 = true := by cbv
  have represented : Represents indexArena 11 indexSource := decode_sound (fuel := 8) (by cbv)
  have evaluated : NativeCorePureComputationNormal.runWithConditionals 32 16 ⟨indexArena, 0⟩ 11 =
      ⟨⟨indexArena.push (.node .index [5, 1, 10]), 15⟩, .ok 12⟩ := by cbv
  obtain ⟨_, _, value, held, _, typed⟩ := NativeCorePureComputationNormal.runWithConditionals_preserves
    wellFormed represented (LoanTyping.Checker.check_sound accepted) (congrArg Outcome.result evaluated)
  rw [evaluated] at held
  have output : Represents (indexArena.push (.node .index [5, 1, 10])) 12 indexResult :=
    decode_sound (fuel := 8) (by cbv)
  exact ⟨evaluated, held.unique output ▸ typed, .read 2 [.integer (-4), .integer 7] 1 evidence (.integer 7) rfl⟩

end Examples

end Jihoo.NativeKernel.NativeCoreSignedEvaluation
