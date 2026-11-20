import Jihoo.NativeCoreArithmeticMachine
import Jihoo.NativeCorePureStructuralNormal

/-! The signed arithmetic branch of pure Core.normal visits its operands
from left to right, with the same depth and a shared counter. It widens two
I64 literals and appends their narrowed result only when it fits. Otherwise
it retains arithmetic over the normalized operand references. -/
namespace Jihoo.NativeKernel.NativeCoreSignedNormal

open NativeArena NativeProgramWire
open NativeCorePureStructuralNormal (Error Outcome)
open NativeCoreGlobalNormal (runPure runPure_refines checked_definition_at)
open Environment
open Environment.LoanTyping.MixedProgram (History)
open Environment.ValueReduction (contract foldArithmetic signed64)

private def integerRow : Node → Option Int
  | .node (.integer value) [] => some value
  | _ => none

private def integerTerm : Term → Option Int
  | .integer value => some value
  | _ => none

private def fold (arena : Arena) (op : Arith) (left right : Nat) : Option Int64 := do
  let first ← arena[left]?.bind integerRow
  let second ← arena[right]?.bind integerRow
  foldArithmetic op (Int64.ofInt first) (Int64.ofInt second)

private def write (arena : Arena) (root : Nat) (before candidate : Node) (steps : Nat) : Outcome Nat :=
  if candidate = before then ⟨arena, .ok root, steps⟩ else
  match NativeCoreGraph.addNode arena candidate with
  | .error reason => ⟨arena, .error (.add reason), steps⟩
  | .ok (extended, result) => ⟨extended, .ok result, steps⟩

private def finish (arena : Arena) (root : Nat) (op : Arith) (beforeLeft beforeRight left right steps : Nat) :
    Outcome Nat :=
  let candidate := match fold arena op left right with
    | some computed => .node (.integer computed.toInt) []
    | none => .node (.arith op) [left, right]
  write arena root (.node (.arith op) [beforeLeft, beforeRight]) candidate steps

private def operands (visit : Arena → Nat → Nat → Outcome Nat) (arena : Arena)
    (root : Nat) (op : Arith) (left right steps : Nat) : Outcome Nat :=
  let first := visit arena steps left
  match first.result with
  | .error reason => ⟨first.arena, .error reason, first.steps⟩
  | .ok leftValue =>
      let second := visit first.arena first.steps right
      match second.result with
      | .error reason => ⟨second.arena, .error reason, second.steps⟩
      | .ok rightValue => finish second.arena root op left right leftValue rightValue second.steps

private def leaf (arena : Arena) (roots : List Roots) (visible limit depth steps root : Nat) : Outcome Nat :=
  let (result, spent) := runPure arena roots visible limit depth steps root
  ⟨arena, result.mapError .normal, spent⟩

/-- Arithmetic may nest in either operand. Other branches use the existing
allocation-free traversal through Free, Drop and global paths to atoms.
Errors keep any already appended rows. -/
def run (roots : List Roots) (visible limit : Nat) : Nat → Arena → Nat → Nat → Outcome Nat
  | 0, arena, steps, root => leaf arena roots visible limit 0 steps root
  | depth + 1, arena, steps, root =>
      let next := steps + 1
      if limit < next then ⟨arena, .error (.normal (.stepLimit root)), next⟩ else
      match arena[root]? with
      | some (.node (.arith op) [left, right]) =>
          operands (run roots visible limit depth) arena root op left right next
      | _ => leaf arena roots visible limit (depth + 1) steps root

/-- The existing Pure conversion supplies leaf reductions. Signed arithmetic
normalizes both operands and uses the specified value contractor, retaining
the rebuilt arithmetic on overflow or a neutral operand. -/
inductive Reduction (env : Environment) : Term → Term → Prop where
  | leaf : Environment.RawValue.Forward env source output → Reduction env source output
  | arith (op : Arith) : Reduction env left left' → Reduction env right right' →
      Reduction env (.arith op left right) ((contract (.arith op left' right')).getD (.arith op left' right'))

private def Inputs (env : Environment) (loans : Environment.Loans.Stack) (ctx : Context) (mode : Bool) : Term → Prop
  | .arith _ left right => LoanTyping.HasType env loans ctx mode left .i64 ∧ LoanTyping.HasType env loans ctx mode right .i64
  | .integer value => signed64 value
  | _ => True

private theorem inputView (typed : LoanTyping.HasType env loans ctx mode term type) : Inputs env loans ctx mode term := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun stack context ghost term _ _ => Inputs env stack context ghost term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case dataElim => split <;> trivial

private theorem integerRow_refines (represented : Represents arena root term) :
    (arena[root]?.bind integerRow) = integerTerm term := by
  cases represented with
  | var read => simp [read, integerRow, integerTerm]
  | @node _ op refs inputs read arity children =>
      rw [read, Option.bind_some]
      cases op <;> try rfl
      case integer value =>
        cases children with
        | nil => rfl
        | cons => cases arity

private theorem contract_arith (op : Arith) (left right : Term) :
    contract (.arith op left right) =
      match integerTerm left, integerTerm right with
      | some a, some b => contract (.arith op (.integer a) (.integer b))
      | _, _ => none := by
  fun_cases integerTerm left <;> fun_cases integerTerm right <;> simp_all [contract]

private theorem integerTerm_eq (literal : integerTerm term = some value) : term = .integer value := by
  fun_cases integerTerm term <;> simp_all [integerTerm]

private theorem fold_refines (leftRep : Represents arena left first) (rightRep : Represents arena right second)
    (leftTyped : LoanTyping.HasType env [] ctx true first .i64) (rightTyped : LoanTyping.HasType env [] ctx true second .i64) :
    (fold arena op left right).map (fun word => Term.integer word.toInt) = contract (.arith op first second) := by
  simp only [fold, integerRow_refines leftRep, integerRow_refines rightRep]
  rw [contract_arith]
  cases a : integerTerm first with
  | none => simp
  | some aValue =>
      cases b : integerTerm second with
      | none => simp
      | some bValue =>
          have firstBound : signed64 aValue := by
            rw [integerTerm_eq a] at leftTyped
            exact inputView leftTyped
          have secondBound : signed64 bValue := by
            rw [integerTerm_eq b] at rightTyped
            exact inputView rightTyped
          change (foldArithmetic op (Int64.ofInt aValue) (Int64.ofInt bValue)).map _ = _
          simpa only [Int64.toInt_ofInt_of_le firstBound.1 firstBound.2,
            Int64.toInt_ofInt_of_le secondBound.1 secondBound.2] using
            Environment.ValueReduction.foldArithmetic_refines op (Int64.ofInt aValue) (Int64.ofInt bValue)

private structure Refines (before : Arena) (computed : Outcome Nat) (valid : Arena → Nat → Prop) : Prop where
  kept : Prefix before computed.arena
  backward : Backward before → Backward computed.arena
  success : ∀ selected, computed.result = .ok selected → valid computed.arena selected

private abbrev TypedResult (env : Environment) (ctx : Context) (source type : Term)
    (arena : Arena) (selected : Nat) : Prop :=
  ∃ normalized, Represents arena selected normalized ∧ Reduction env source normalized ∧
    LoanTyping.HasType env [] ctx true normalized type

private theorem error_refines (kept : Prefix arena current) (backward : Backward arena → Backward current) :
    Refines arena (⟨current, .error reason, steps⟩ : Outcome Nat) valid :=
  ⟨kept, backward, by simp⟩

private theorem represented_index (represented : Represents arena root term) : root < arena.size := by
  cases represented with
  | var valid | node valid => exact (Array.getElem?_eq_some_iff.mp valid).1

private theorem write_refines (read : arena[root]? = some before) (arity : refs.length = op.arity)
    (children : RepresentsList arena refs terms) (known : ∀ child ∈ refs, child < arena.size) :
    Refines arena (write arena root before (.node op refs) steps)
      (fun extended selected => Represents extended selected (.node op terms)) := by
  unfold write
  split
  · rename_i same
    refine ⟨Prefix.refl _, id, ?_⟩
    intro selected found
    cases found
    exact .node (same.symm ▸ read) arity children
  · cases added : NativeCoreGraph.addNode arena (.node op refs) with
    | error reason =>
        exact error_refines (Prefix.refl _) id
    | ok result =>
        obtain ⟨after, index⟩ := result
        obtain ⟨kept, fresh, _, _, _, lookup⟩ := NativeCoreGraph.addNode_commits added
        refine ⟨kept, fun backward => NativeCoreGraph.addNode_preserves_backward backward added ?_, ?_⟩
        · rw [fresh]
          exact known
        · intro selected found
          cases found
          exact .node lookup arity (children.frame kept)

private theorem finish_refines (read : arena[root]? = some (.node (.arith op) [oldLeft, oldRight]))
    (leftRep : Represents arena left first) (rightRep : Represents arena right second)
    (leftTyped : LoanTyping.HasType env [] ctx true first .i64) (rightTyped : LoanTyping.HasType env [] ctx true second .i64)
    (converted : Environment.RawLend.Conv env .i64 type)
    (firstReduction : Reduction env originalLeft first) (secondReduction : Reduction env originalRight second) :
    Refines arena (finish arena root op oldLeft oldRight left right steps)
      (TypedResult env ctx (.arith op originalLeft originalRight) type) := by
  have equation := fold_refines (op := op) leftRep rightRep leftTyped rightTyped
  have derived : LoanTyping.HasType env [] ctx true (.arith op first second) type :=
    (LoanTyping.HasType.arith leftTyped rightTyped).convert converted
  unfold finish
  cases folded : fold arena op left right with
  | none =>
      have residual : contract (.arith op first second) = none := by simpa only [folded, Option.map_none] using equation.symm
      have represented : RepresentsList arena [left, right] [first, second] := .cons leftRep (.cons rightRep .nil)
      have known : ∀ child ∈ [left, right], child < arena.size := by
        intro child member
        rcases (show child = left ∨ child = right from by simpa using member) with rfl | rfl
        · exact represented_index leftRep
        · exact represented_index rightRep
      have written := write_refines (op := .arith op) (steps := steps) read rfl represented known
      refine ⟨written.kept, written.backward, ?_⟩
      intro selected successful
      refine ⟨_, written.success selected successful, ?_, derived⟩
      simpa only [residual, Option.getD_none] using Reduction.arith op firstReduction secondReduction
  | some computed =>
      have foldedSpec : contract (.arith op first second) = some (.integer computed.toInt) := by
        simpa only [folded, Option.map_some] using equation.symm
      have written := write_refines (steps := steps) read (op := .integer computed.toInt) rfl .nil (by simp)
      refine ⟨written.kept, written.backward, ?_⟩
      intro selected successful
      refine ⟨_, written.success selected successful, ?_,
        Environment.LoanTyping.value_root_ghost_preservation (Environment.ValueReduction.contract_sound foldedSpec) derived⟩
      simpa only [foldedSpec, Option.getD_some] using Reduction.arith op firstReduction secondReduction

private theorem frameDefinitions (aligned : RepresentsDefinitions arena roots definitions)
    (kept : Prefix arena current) : RepresentsDefinitions current roots definitions := by
  induction aligned with
  | nil => exact .nil
  | cons first _ ih => exact .cons ⟨first.1.frame kept, first.2.frame kept⟩ ih

private theorem leaf_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions declarations env) (source : Represents arena root term)
    (typed : LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env term) type) :
    Refines arena (leaf arena roots visible limit depth steps root) (TypedResult env ctx term type) := by
  rcases ran : runPure arena roots visible limit depth steps root with ⟨result, spent⟩
  cases result with
  | error reason =>
      simp only [leaf, ran, Except.mapError]
      exact error_refines (Prefix.refl _) id
  | ok result =>
      simp only [leaf, ran, Except.mapError]
      refine ⟨Prefix.refl _, id, ?_⟩
      intro selected found
      cases found
      obtain ⟨normalized, _, represented, changed, preserves, _, _⟩ := runPure_refines aligned history source typed ran
      exact ⟨normalized, represented, .leaf changed, preserves⟩

private theorem expand_arith (env : Environment) (op : Arith) (left right : Term) :
    EnvironmentDelta.expand env (.arith op left right) =
      .arith op (EnvironmentDelta.expand env left) (EnvironmentDelta.expand env right) := by
  simp only [Term.arith, EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs]

private theorem operands_refine (aligned : RepresentsDefinitions arena roots definitions)
    (read : arena[root]? = some (.node (.arith op) [left, right]))
    (leftRep : Represents arena left first) (rightRep : Represents arena right second)
    (typed : LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env (.arith op first second)) type)
    (visitRefines : ∀ {current step root term type}, RepresentsDefinitions current roots definitions →
      Represents current root term → LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env term) type →
      Refines current (visit current step root) (TypedResult env ctx term type)) :
    Refines arena (operands visit arena root op left right steps) (TypedResult env ctx (.arith op first second) type) := by
  rw [expand_arith] at typed
  obtain ⟨firstTyped, secondTyped⟩ := inputView typed
  have firstRun := visitRefines (step := steps) aligned leftRep firstTyped
  cases leftResult : (visit arena steps left).result with
  | error reason =>
      simp only [operands, leftResult]
      exact error_refines firstRun.kept firstRun.backward
  | ok leftValue =>
      have secondRun := visitRefines (step := (visit arena steps left).steps)
        (frameDefinitions aligned firstRun.kept) (rightRep.frame firstRun.kept) secondTyped
      cases rightResult : (visit (visit arena steps left).arena (visit arena steps left).steps right).result with
      | error reason =>
          simp only [operands, leftResult, rightResult]
          exact error_refines (firstRun.kept.trans secondRun.kept) (fun h => secondRun.backward (firstRun.backward h))
      | ok rightValue =>
          obtain ⟨newLeft, leftRead, leftChanged, leftTyped⟩ := firstRun.success leftValue leftResult
          obtain ⟨newRight, rightRead, rightChanged, rightTyped⟩ := secondRun.success rightValue rightResult
          have keeps := firstRun.kept.trans secondRun.kept
          have written := finish_refines (steps := (visit (visit arena steps left).arena
            (visit arena steps left).steps right).steps) (keeps.lookup read)
            (leftRead.frame secondRun.kept) rightRead leftTyped rightTyped typed.principalView leftChanged rightChanged
          simp only [operands, leftResult, rightResult]
          exact ⟨keeps.trans written.kept, fun h => written.backward (secondRun.backward (firstRun.backward h)), written.success⟩

private theorem run_refines_aux (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions declarations env) (source : Represents arena root term)
    (typed : LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env term) type) :
    Refines arena (run roots visible limit depth arena steps root) (TypedResult env ctx term type) := by
  induction depth generalizing arena root term steps type with
  | zero => exact leaf_refines aligned history source typed
  | succ depth ih =>
      by_cases exceeded : limit < steps + 1
      · simp only [run, exceeded, ite_true]
        exact error_refines (Prefix.refl _) id
      cases source with
      | var read =>
          simpa only [run, ite_eq_right exceeded, read] using leaf_refines aligned history (.var read) typed
      | @node _ op refs terms read arity children =>
          cases op <;> try
            simpa only [run, ite_eq_right exceeded, read] using leaf_refines aligned history (.node read arity children) typed
          case arith op =>
            cases children with
            | nil => cases arity
            | cons left rest =>
                cases rest with
                | nil => cases arity
                | cons right rest =>
                    cases rest with
                    | nil =>
                        simp only [run, ite_eq_right exceeded, read]
                        exact operands_refine aligned read left right typed (fun a rep ty => ih a rep ty)
                    | cons => cases arity

/-- A complete supported visit retains earlier rows and their backward
references. Success computes a specified pure reduction whose result has
the exact admitted Loan64 type, including on retained signed overflow. -/
theorem run_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions declarations env) (source : Represents arena root term)
    (typed : LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env term) type) :
    let computed := run roots visible limit depth arena steps root
    Prefix arena computed.arena ∧ (Backward arena → Backward computed.arena) ∧
      ∀ selected, computed.result = .ok selected →
        ∃ normalized, Represents computed.arena selected normalized ∧ Reduction env term normalized ∧
          LoanTyping.HasType env [] ctx true normalized type := by
  let proof := run_refines_aux (visible := visible) (limit := limit) (depth := depth) (steps := steps)
    aligned history source typed
  exact ⟨proof.kept, proof.backward, proof.success⟩

/-- The original result type and body come from the selected definition in
the admitted exact snapshot bytes. No output typing premise is required. -/
theorem run_admitted_definition_refines {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some definition) :
    let computed := run snapshot.definitions visible limit depth snapshot.arena steps definition.valueRoot
    ∃ definitions families env entry raw,
      History definitions families env ∧ env.globals[index]? = some entry ∧
        RepresentsDefinition snapshot.arena definition raw ∧ Prefix snapshot.arena computed.arena ∧
        Backward computed.arena ∧ ∀ selected, computed.result = .ok selected →
          ∃ normalized, Represents computed.arena selected normalized ∧ Reduction env raw.value normalized ∧
            LoanTyping.HasType env [] [] true normalized entry.type := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, backwards, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨entry, raw, found, represented, typed⟩ := checked_definition_at aligned history row
  obtain ⟨kept, preserves, checked⟩ := run_refines (visible := visible) (limit := limit) (depth := depth)
    (steps := steps) aligned history represented.2 typed
  exact ⟨definitions, _, env, entry, raw, history, found, represented, kept, preserves backwards, checked⟩

/-- Shared arithmetic operands are each normalized. A shortage at the
last right operand retains the left fold, and signed overflow reuses the
original row when its operands already normalize to themselves. -/
theorem fold_order_and_overflow_example :
    let arena : Arena := #[.node (.integer 7) [], .node (.integer 3) [], .node (.arith .sub) [0, 1],
      .node (.arith .mul) [2, 2], .node (.integer 9223372036854775807) [], .node (.arith .add) [4, 1]]
    let left := arena.push (.node (.integer 4) [])
    run [] 0 7 3 arena 0 3 =
      ⟨(left.push (.node (.integer 4) [])).push (.node (.integer 16) []), .ok 8, 7⟩ ∧
    run [] 0 6 3 arena 0 3 = ⟨left, .error (.normal (.stepLimit 1)), 7⟩ ∧
    run [] 0 3 2 arena 0 5 = ⟨arena, .ok 5, 3⟩ := by
  exact ⟨rfl, rfl, rfl⟩

end Jihoo.NativeKernel.NativeCoreSignedNormal
