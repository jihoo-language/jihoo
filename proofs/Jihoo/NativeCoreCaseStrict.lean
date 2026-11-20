import Jihoo.NativeCoreCaseEvaluation
import Jihoo.NativeLoanPureTyping

/-! The Strict scrutinee arm of Core.normal after operand normalization.
The inner Case is appended and reentered before the Strict wrapper is
appended. The caller provides the recursive visit at the child depth. -/
namespace Jihoo.NativeKernel.NativeCoreCaseStrict

open NativeArena Environment NativeCoreGraph
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open FamilyIota (caseTerm)

def append (state : State) (op : Op) (refs : List Nat) : Outcome Nat :=
  match addNode state.arena (.node op refs) with
  | .error reason => ⟨state, .error (.add reason)⟩
  | .ok (arena, root) => ⟨{state with arena}, .ok root⟩

def run (visit : State → Nat → Outcome Nat) (state : State) (family : Nat)
    (motive : Nat) (cases : List Nat) (effect value : Nat) : Outcome Nat :=
  let inner := append state (.caseOf family cases.length) (motive :: (cases ++ [value]))
  match inner.result with
  | .error reason => ⟨inner.state, .error reason⟩
  | .ok root =>
      let reduced := visit inner.state root
      match reduced.result with
      | .error reason => ⟨reduced.state, .error reason⟩
      | .ok residual => append reduced.state .strict [effect, residual]

private theorem children_valid (children : RepresentsList arena refs terms) :
    ∀ child ∈ refs, child < arena.size := by
  induction children using RepresentsList.rec (motive_1 := fun root _ _ => root < arena.size) with
  | var read | node read => exact (Array.getElem?_eq_some_iff.mp read).1
  | nil => simp
  | cons _ _ head tail =>
      intro child member
      rcases List.mem_cons.mp member with rfl | rest
      · exact head
      · exact tail child rest

theorem append_refines (children : RepresentsList state.arena refs terms)
    (shape : refs.length = op.arity) (success : (append state op refs).result = .ok selected) :
    let after := (append state op refs).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (.node op terms) := by
  cases added : addNode state.arena (.node op refs) with
  | error reason => simp [append, added] at success
  | ok answer =>
      obtain ⟨arena, root⟩ := answer
      simp [append, added] at success
      subst selected
      obtain ⟨kept, index, _, _, _, read⟩ := addNode_commits added
      simp only [append, added]
      refine ⟨kept, ?_, .node read shape (children.frame kept)⟩
      intro backward
      apply addNode_preserves_backward backward added
      rw [index]
      exact children_valid children

private theorem frame_append (children : RepresentsList arena refs terms) (last : Represents arena ref term) :
    RepresentsList arena (refs ++ [ref]) (terms ++ [term]) := by
  induction children using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => exact .cons last .nil
  | cons head _ _ ih => exact .cons head ih

theorem append_progress (state : State) (op : Op) (refs : List Nat) :
    Progress limit state (append state op refs) := by
  cases added : addNode state.arena (.node op refs) with
  | error reason =>
      simp only [append, added]
      exact ⟨.refl _, Nat.le_refl _, Nat.le.step, fun room _ _ => room⟩
  | ok answer =>
      obtain ⟨arena, root⟩ := answer
      simp only [append, added]
      exact ⟨(addNode_commits added).1, Nat.le_refl _, Nat.le.step, fun room _ _ => room⟩

/-- Both appends preserve the clock. Failure, including a rejecting recursive
visit or a full arena at the final wrapper, retains the emitted prefix. -/
theorem run_progress (visitProgress : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (run visit state family motive cases effect value) := by
  unfold run
  generalize built : append state (.caseOf family cases.length) (motive :: (cases ++ [value])) = inner
  have first := append_progress (limit := limit) state (.caseOf family cases.length) (motive :: (cases ++ [value]))
  rw [built] at first
  cases ready : inner.result with
  | error reason =>
      simp only [ready]
      exact ⟨first.kept, first.monotone, first.bounded, fun _ _ found => by cases found⟩
  | ok root =>
      simp only [ready]
      have middle := visitProgress inner.state root
      cases computed : (visit inner.state root).result with
      | error reason =>
          exact ⟨first.kept.trans middle.kept, Nat.le_trans first.monotone middle.monotone,
            fun room => middle.bounded (first.accepted room root ready), fun _ _ found => by cases found⟩
      | ok residual =>
          have last := append_progress (limit := limit) (visit inner.state root).state .strict [effect, residual]
          have roomAfter (room : state.steps ≤ limit) : (visit inner.state root).state.steps ≤ limit :=
            middle.accepted (first.accepted room root ready) residual computed
          exact ⟨first.kept.trans (middle.kept.trans last.kept),
            Nat.le_trans first.monotone (Nat.le_trans middle.monotone last.monotone),
            fun room => last.bounded (roomAfter room), fun room => last.accepted (roomAfter room)⟩

structure Refines (env : Environment) (before after : Arena) (root : Nat) (ctx : Context)
    (input type : Term) : Prop where
  frame : Prefix before after
  backward : Backward before → Backward after
  result : ∃ output, Represents after root output ∧ RawValue.Conv env input output ∧
    LoanTyping.PureTyping.HasType env ctx output type

private theorem discard_scrutinee_prefix (arms : List Term) :
    NativeKernel.Conversion.ListRel (RawValue.Conv env) (arms ++ [.strict effect value]) (arms ++ [value]) := by
  induction arms with
  | nil => exact .cons (.strict effect value) .nil
  | cons _ _ ih => exact .cons (.refl _) ih

/-- The original typing supplies the inner dependent Case type and the
effect typing. Reentry keeps the inner type. The final wrapper is inferred
at that type and converted to the independently formed original type. -/
theorem run_preserves {sort : SortTag}
    (visitor : ∀ {state root count terms type selected},
      Represents state.arena root (.node (.caseOf family count) terms) →
      LoanTyping.HasType env [] ctx true (.node (.caseOf family count) terms) type →
      (visit state root).result = .ok selected →
      NativeCoreCaseNormal.Refines env state.arena (visit state root).state.arena selected ctx
        (.node (.caseOf family count) terms) type)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (prefixRep : Represents state.arena prefixRef effect)
    (valueRep : Represents state.arena valueRef value)
    (typed : LoanTyping.HasType env loans ctx mode (caseTerm family motive cases (.strict effect value)) type)
    (formed : LoanTyping.HasType env [] ctx true type sort.term)
    (success : (run visit state family motiveRef caseRefs prefixRef valueRef).result = .ok selected) :
    Refines env state.arena (run visit state family motiveRef caseRefs prefixRef valueRef).state.arena selected ctx
      (caseTerm family motive cases (.strict effect value)) type := by
  obtain ⟨prefixType, innerType, prefixTyped, innerTyped, typeConversion⟩ :=
    LoanTyping.FamilyIota.strict_case_inputs typed
  have armCount : caseRefs.length = cases.length := NativeCoreIdentical.represented_length caseRep
  let built := append state (.caseOf family caseRefs.length) (motiveRef :: (caseRefs ++ [valueRef]))
  have order : run visit state family motiveRef caseRefs prefixRef valueRef =
      (match built.result with
      | .error reason => ⟨built.state, .error reason⟩
      | .ok root =>
        let reduced := visit built.state root
        match reduced.result with
        | .error reason => ⟨reduced.state, .error reason⟩
        | .ok residual => append reduced.state .strict [prefixRef, residual]) := rfl
  rw [order] at success ⊢
  cases ready : built.result with
  | error reason => simp only [ready] at success; cases success
  | ok root =>
      simp only [ready] at success ⊢
      have children := RepresentsList.cons motiveRep (frame_append caseRep valueRep)
      obtain ⟨first, firstBackward, selectedCase⟩ := append_refines children
        (op := .caseOf family caseRefs.length) (by simp [Op.arity]) ready
      have innerRep : Represents built.state.arena root (caseTerm family motive cases value) := by
        unfold caseTerm
        rw [← armCount]
        exact selectedCase
      cases computed : (visit built.state root).result with
      | error reason => rw [computed] at success; cases success
      | ok residual =>
          rw [computed] at success
          obtain ⟨middle, middleBackward, normalized, normalizedRep, forward, innerPreserved⟩ :=
            visitor innerRep innerTyped computed
          have pair := RepresentsList.cons (prefixRep.frame (first.trans middle))
            (.cons normalizedRep .nil)
          obtain ⟨last, lastBackward, output⟩ := append_refines pair (op := .strict) rfl success
          have remove :
              RawValue.Conv env (caseTerm family motive cases (.strict effect value))
                (caseTerm family motive cases value) := by
            exact .node _ (.cons (.refl _) (discard_scrutinee_prefix cases))
          have equivalent := remove.trans
            ((RawValue.Conv.old forward.toConv).trans (.symm (.strict effect normalized)))
          have retained := LoanTyping.PureTyping.convert_native
            (LoanTyping.HasType.strict prefixTyped innerPreserved) formed typeConversion
          exact ⟨first.trans (middle.trans last), fun old => lastBackward (middleBackward (firstBackward old)),
            _, output, equivalent, retained⟩

/-- The post-operand branch composes with the checked Case driver for a
constructor or neutral value exposed under the Strict wrapper. -/
theorem run_case_preserves {sort : SortTag}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (prefixRep : Represents state.arena prefixRef effect)
    (valueRep : Represents state.arena valueRef value)
    (typed : LoanTyping.HasType env loans ctx mode (caseTerm family motive cases (.strict effect value)) type)
    (formed : LoanTyping.HasType env [] ctx true type sort.term)
    (success : (run (NativeCoreCaseEvaluation.run env limit depth) state family motiveRef
      caseRefs prefixRef valueRef).result = .ok selected) :
    Refines env state.arena (run (NativeCoreCaseEvaluation.run env limit depth) state family motiveRef
      caseRefs prefixRef valueRef).state.arena selected ctx (caseTerm family motive cases (.strict effect value)) type :=
  run_preserves (fun represented checked computed =>
    NativeCoreCaseEvaluation.run_preserves history represented checked computed)
    motiveRep caseRep prefixRep valueRep typed formed success

namespace Examples

private def familyType : Term := .node (.ind 0 0) []
private def bufferType : Term := .buffer (.natural 2)
private def allocation : Term := .alloc (.natural 2) (.integer 0)
private def motive : Term := .lam false familyType bufferType
private def branch : Term := .lam false bufferType (.var 0)
private def constructor : Term := .node (.con 0 0 1) [allocation]
private def declaration : FamilyDeclaration := ⟨true, 0, 0, [.pi false bufferType familyType], 0⟩
private def signature : Signature := ⟨[⟨false, bufferType, none⟩], []⟩
private def env : Environment := ⟨#[], #[⟨declaration, [signature], true⟩]⟩
private def requested : Term := .buffer (.uadd (.natural 1) (.natural 1))
private def arena : Arena := #[.node (.natural 2) [], .node (.integer 0) [], .node .alloc [0, 1],
  .node (.ind 0 0) [], .node .buffer [0], .node (.lam false) [3, 4], .var 0,
  .node (.lam false) [4, 6], .node (.con 0 0 1) [2], .node .strict [2, 8]]
private def emittedCase : Node := .node (.caseOf 0 1) [5, 7, 8]
private def finalArena : Arena :=
  ((arena.push emittedCase).push (.node .app [7, 2])).push (.node .strict [2, 2])

/-- Reentry contracts the checked constructor inside Strict and preserves the
original converted Buffer type. The graph still contains the original effect. -/
theorem checked_strict_scrutinee_keeps_prefix :
    run (NativeCoreCaseEvaluation.run env 28 16) ⟨arena, 0⟩ 0 5 [7] 2 8 =
      ⟨⟨finalArena, 28⟩, .ok 12⟩ ∧
    LoanTyping.PureTyping.HasType env [] (.strict allocation allocation) requested := by
  have installed : LoanTyping.MixedProgram.checkProgram 64 128 [] [declaration] = some env := by cbv
  have checked : LoanTyping.HasType env [] [] true
      (caseTerm 0 motive [branch] (.strict allocation constructor)) requested :=
    LoanTyping.Checker.check_sound (fuel := 64) (by cbv)
  have formed : LoanTyping.HasType env [] [] true requested (SortTag.type 0).term :=
    .buffer (.uadd (.natural (by decide)) (.natural (by decide)))
  have computed : run (NativeCoreCaseEvaluation.run env 28 16) ⟨arena, 0⟩ 0 5 [7] 2 8 =
      ⟨⟨finalArena, 28⟩, .ok 12⟩ := rfl
  obtain ⟨_, _, residual, represented, _, kept⟩ :=
    run_case_preserves (LoanTyping.MixedProgram.checkProgram_sound installed) (decode_sound (fuel := 8) rfl)
      (.cons (decode_sound (fuel := 8) rfl) .nil) (decode_sound (fuel := 8) rfl)
      (decode_sound (fuel := 8) rfl) checked formed (congrArg Outcome.result computed)
  rw [computed] at represented
  have expected : Represents finalArena 12 (.strict allocation allocation) := decode_sound (fuel := 8) rfl
  rw [represented.unique expected] at kept
  exact ⟨computed, kept⟩

/-- Exhausting the shared clock at reentry leaves the new inner Case intact. -/
theorem reentry_limit_keeps_inner_case :
    run (NativeCoreCaseEvaluation.run env 9 16) ⟨arena, 9⟩ 0 5 [7] 2 8 =
      ⟨⟨arena.push emittedCase, 10⟩, .error (.tick (.stepLimit 10))⟩ := rfl

end Examples

end Jihoo.NativeKernel.NativeCoreCaseStrict
