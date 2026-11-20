import Jihoo.NativeCoreRecursiveCase
import Jihoo.NativeCoreCaseStrict
import Jihoo.NativeCoreTrapAnalysis

/-! Pure Strict normalizes its two operands in order. It discards a lambda
value or a prefix classified as nontrapping. Otherwise it keeps the Strict
row, with the same operand references or an appended replacement. -/
namespace Jihoo.NativeKernel.NativeCoreStrictNormal

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress GhostNormalization nodeResult nodeResult_refines)
open NativeCoreTrapAnalysis (graphMayTrap termMayTrap graphMayTrap_refines)

private def lambdaRow : Node → Bool
  | .node (.lam _) _ => true
  | _ => false

private def lambdaTerm : Term → Bool
  | .node (.lam _) _ => true
  | _ => false

def discardPrefix (env : Environment) (arena : Arena) (depth effect : Nat) : Bool :=
  (arena[effect]?.map lambdaRow).getD false || !graphMayTrap env false arena depth effect

/-- The native decision uses the normalized lambda head and the pure
depth-limited trap analysis of the represented term. -/
theorem discardPrefix_refines (backward : Backward arena) (effect : Represents arena ref term) :
    discardPrefix env arena depth ref = (lambdaTerm term || !termMayTrap env false depth term) := by
  unfold discardPrefix
  rw [graphMayTrap_refines backward effect]
  cases effect with
  | var read => simp [read, lambdaRow, lambdaTerm]
  | @node _ op _ _ read _ _ =>
      rw [read]
      cases op <;> rfl

def finish (env : Environment) (depth root : Nat) (state : State)
    (before : List Nat) (effect result : Nat) : Outcome Nat :=
  if discardPrefix env state.arena depth effect then ⟨state, .ok result⟩
  else nodeResult state root .strict before [effect, result]

private def visitOperands (env : Environment) (limit depth root : Nat)
    (state : State) (effect result : Nat) : Outcome Nat :=
  let first := NativeCoreRecursiveCase.run env limit depth state effect
  match first.result with
  | .error reason => ⟨first.state, .error reason⟩
  | .ok effectRef =>
      let second := NativeCoreRecursiveCase.run env limit depth first.state result
      match second.result with
      | .error reason => ⟨second.state, .error reason⟩
      | .ok resultRef => finish env depth root second.state [effect, result] effectRef resultRef

def run (env : Environment) (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  let tried := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let entered := {state with steps := tried.2}
  match tried.1, depth with
  | .error reason, _ => ⟨entered, .error (.tick reason)⟩
  | .ok (), 0 => ⟨entered, .error (.tick (.depthLimit root))⟩
  | .ok (), childDepth + 1 =>
      match state.arena[root]? with
      | some (.node .strict [effect, result]) => visitOperands env limit childDepth root entered effect result
      | _ => ⟨entered, .error (.outsideFragment root)⟩

structure Refines (env : Environment) (before after : Arena) (selected : Nat) (ctx : Context)
    (input type : Term) : Prop where
  kept : Prefix before after
  backward : Backward before → Backward after
  value : ∃ output, Represents after selected output ∧ RawValue.Forward env input output ∧
    LoanTyping.HasType env [] ctx true output type

private theorem finish_preserves
    (read : state.arena[root]? = some (.node .strict before))
    (effect : Represents state.arena effectRef prefixTerm) (result : Represents state.arena resultRef resultTerm)
    (typed : LoanTyping.HasType env [] ctx true (.strict prefixTerm resultTerm) type)
    (success : (finish env depth root state before effectRef resultRef).result = .ok selected) :
    Refines env state.arena (finish env depth root state before effectRef resultRef).state.arena
      selected ctx (.strict prefixTerm resultTerm) type := by
  by_cases discard : discardPrefix env state.arena depth effectRef = true
  · simp only [finish, ite_eq_left discard, Except.ok.injEq] at success ⊢
    subst selected
    exact ⟨.refl _, id, resultTerm, result, .strict prefixTerm resultTerm,
      LoanTyping.value_root_ghost_preservation (.strict prefixTerm resultTerm) typed⟩
  · simp only [finish, ite_eq_right discard] at success ⊢
    obtain ⟨kept, backward, residual, represented, changes⟩ :=
      nodeResult_refines read (.cons effect (.cons result .nil)) rfl success
    exact ⟨kept, backward, residual, represented, .old changes.raw.forward, changes.raw.typed typed⟩

private theorem visitOperands_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (read : state.arena[root]? = some (.node .strict [effect, result]))
    (effectRep : Represents state.arena effect prefixTerm)
    (resultRep : Represents state.arena result resultTerm)
    (typed : LoanTyping.HasType env loans ctx mode (.strict prefixTerm resultTerm) type)
    (success : (visitOperands env limit depth root state effect result).result = .ok selected) :
    Refines env state.arena (visitOperands env limit depth root state effect result).state.arena
      selected ctx (.strict prefixTerm resultTerm) type := by
  unfold visitOperands at success ⊢
  cases first : (NativeCoreRecursiveCase.run env limit depth state effect).result with
  | error reason => simp [first] at success
  | ok effectRef =>
      simp only [first] at success ⊢
      obtain ⟨kept, backward, prefixNormal, prefixRep, prefixChange⟩ :=
        NativeCoreRecursiveCase.run_refines history effectRep first
      let afterEffect := (NativeCoreRecursiveCase.run env limit depth state effect).state
      cases second : (NativeCoreRecursiveCase.run env limit depth afterEffect result).result with
      | error reason =>
          simp [afterEffect] at second
          simp [second] at success
      | ok resultRef =>
          have resultRead : (NativeCoreRecursiveCase.run env limit depth
              (NativeCoreRecursiveCase.run env limit depth state effect).state result).result = .ok resultRef := second
          simp only [resultRead] at success ⊢
          obtain ⟨later, preserves, resultNormal, outputRep, resultChange⟩ :=
            NativeCoreRecursiveCase.run_refines history (resultRep.frame kept) second
          have both := GhostNormalization.node (op := .strict) history.wellFormed
            (by intro same; cases same) rfl (.cons prefixChange (.cons resultChange .nil))
          obtain ⟨last, lastBackward, output, represented, reduction, retained⟩ :=
            finish_preserves ((kept.trans later).lookup read) (prefixRep.frame later) outputRep
              (both.raw.typed typed) success
          exact ⟨kept.trans (later.trans last), fun old => lastBackward (preserves (backward old)),
            output, represented, (RawValue.Forward.old both.raw.forward).trans reduction, retained⟩

/-- Both operands normalize using the family-aware visitor. The selected
Strict root result retains the exact original Loan64 type. -/
theorem run_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root (.strict prefixTerm resultTerm))
    (typed : LoanTyping.HasType env loans ctx mode (.strict prefixTerm resultTerm) type)
    (success : (run env limit depth state root).result = .ok selected) :
    Refines env state.arena (run env limit depth state root).state.arena
      selected ctx (.strict prefixTerm resultTerm) type := by
  rcases ticked : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root with ⟨answer, spent⟩
  cases answer
  · simp [run, ticked] at success
  case ok charged =>
    cases charged
    cases depth
    · simp [run, ticked] at success
    case succ depth =>
      cases source with
      | node read size operands =>
          cases operands with
          | cons first rest =>
              cases rest with
              | cons second tail =>
                  cases tail with
                  | nil =>
                      simp only [run, ticked, read] at success ⊢
                      exact visitOperands_preserves (state := {state with steps := spent}) history read
                        first second typed success

/-- If the scrutinee of Case retained a strict prefix, the appended inner
Case can use the joint recursive driver through nested family eliminations. -/
theorem case_reentry_preserves {sort : SortTag}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (motiveRep : Represents state.arena motiveRef motive) (armsRep : RepresentsList state.arena armsRefs arms)
    (prefixRep : Represents state.arena prefixRef prefixTerm) (valueRep : Represents state.arena valueRef value)
    (typed : LoanTyping.HasType env loans ctx mode
      (FamilyIota.caseTerm family motive arms (.strict prefixTerm value)) type)
    (formed : LoanTyping.HasType env [] ctx true type sort.term)
    (success : (NativeCoreCaseStrict.run (NativeCoreRecursiveCase.run env limit depth)
      state family motiveRef armsRefs prefixRef valueRef).result = .ok selected) :
    let output := NativeCoreCaseStrict.run (NativeCoreRecursiveCase.run env limit depth)
      state family motiveRef armsRefs prefixRef valueRef
    NativeCoreCaseStrict.Refines env state.arena output.state.arena selected ctx
      (FamilyIota.caseTerm family motive arms (.strict prefixTerm value)) type := by
  apply NativeCoreCaseStrict.run_preserves _ motiveRep armsRep prefixRep valueRep typed formed success
  intro child root count terms childType result represented checked computed
  obtain ⟨kept, backward, value, valueRep, change⟩ := NativeCoreRecursiveCase.run_refines history represented computed
  exact ⟨kept, backward, value, valueRep, change.raw.forward, change.raw.typed checked⟩

theorem case_reentry_progress :
    Progress limit state (NativeCoreCaseStrict.run (NativeCoreRecursiveCase.run env limit depth)
      state family motive arms effect value) :=
  NativeCoreCaseStrict.run_progress (NativeCoreRecursiveCase.run_progress env limit depth)

namespace Examples

private def allocation : Term := .alloc (.natural 2) (.integer 0)
private def seven : Term := .natural 7
private def source : Term := .strict allocation (.app (.lam false .u64 (.var 0)) seven)
private def arena : Arena := #[.node (.natural 2) [], .node (.integer 0) [], .node .alloc [0, 1],
  .node .u64 [], .node (.lam false) [3, 2], .node (.natural 7) [],
  .node .strict [4, 5], .node .strict [2, 5], .var 0, .node (.lam false) [3, 8],
  .node .app [9, 5], .node .strict [2, 10]]
private def rebuilt : Arena := arena.push (.node .strict [2, 5])

/-- A lambda hides its body from the native discard decision. The actual
allocation prefix is retained and only the changed Strict row is appended. -/
theorem checked_strict_discard_and_rebuild :
    run .empty 7 8 ⟨arena, 0⟩ 6 = ⟨⟨arena, 7⟩, .ok 5⟩ ∧
    run .empty 5 8 ⟨arena, 0⟩ 7 = ⟨⟨arena, 5⟩, .ok 7⟩ ∧
    run .empty 12 8 ⟨arena, 0⟩ 11 = ⟨⟨rebuilt, 12⟩, .ok 12⟩ ∧
    LoanTyping.HasType .empty [] [] true (.strict allocation seven) .u64 := by
  have history : LoanTyping.MixedProgram.History [] [] Environment.empty := .empty
  have typed : LoanTyping.HasType .empty [] [] true source .u64 :=
    LoanTyping.Checker.check_sound (fuel := 64) (by cbv)
  have input : Represents arena 11 source := decode_sound (fuel := 6) rfl
  have computed : run .empty 12 8 ⟨arena, 0⟩ 11 = ⟨⟨rebuilt, 12⟩, .ok 12⟩ := rfl
  obtain ⟨_, _, residual, represented, _, retained⟩ :=
    run_preserves history input typed (congrArg Outcome.result computed)
  rw [computed] at represented
  have expected : Represents rebuilt 12 (.strict allocation seven) := decode_sound (fuel := 6) rfl
  rw [represented.unique expected] at retained
  exact ⟨rfl, rfl, computed, retained⟩

end Examples

end Jihoo.NativeKernel.NativeCoreStrictNormal
