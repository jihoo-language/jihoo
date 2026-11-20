import Jihoo.NativeCoreGraph
import Jihoo.NativeCoreArithmeticMachine

/-! Core.natural_sum builds a balanced graph for wide ghost constants.
It appends the left half first and reuses that reference for equal halves. -/
namespace Jihoo.NativeKernel.NativeCoreNaturalSum

open NativeArena NativeCoreGraph
open NativeConstantAccumulator (naturalSum naturalSum_correct)

structure Outcome where
  arena : Arena
  result : Except Error Nat
  deriving Repr

private def append (arena : Arena) (node : Node) : Outcome :=
  match addNode arena node with
  | .ok (next, ref) => ⟨next, .ok ref⟩
  | .error reason => ⟨arena, .error reason⟩

/-- Appending a failed parent preserves any child rows already committed.
This operation has its own node limit and does not tick the checker. -/
def run (value : Nat) (arena : Arena) : Outcome :=
  if value < 2^64 then append arena (.node (.natural value) [])
  else
    let half := value / 2
    let left := run half arena
    match left.result with
    | .error _ => left
    | .ok leftRef =>
        if value - half = half then append left.arena (.node .uadd [leftRef, leftRef])
        else
          let right := run (value - half) left.arena
          match right.result with
          | .error _ => right
          | .ok rightRef => append right.arena (.node .uadd [leftRef, rightRef])
termination_by value
decreasing_by all_goals omega

private theorem append_prefix (arena : Arena) (node : Node) : Prefix arena (append arena node).arena := by
  unfold append
  split
  · rename_i after root added
    exact (addNode_commits added).1
  · exact .refl _

theorem run_prefix (value : Nat) (arena : Arena) : Prefix arena (run value arena).arena := by
  rw [run]
  split
  · exact append_prefix ..
  · simp only
    have left := run_prefix (value / 2) arena
    split
    · exact left
    · split
      · exact left.trans (append_prefix ..)
      · have right := run_prefix (value - value / 2) ((run (value / 2) arena).arena)
        split
        · exact left.trans right
        · exact left.trans (right.trans (append_prefix ..))
termination_by value
decreasing_by all_goals omega

private theorem represented_bounds (children : RepresentsList arena refs terms) :
    ∀ ref ∈ refs, ref < arena.size := by
  induction children using RepresentsList.rec (motive_1 := fun ref _ _ => ref < arena.size) with
  | var selected | node selected => exact (Array.getElem?_eq_some_iff.mp selected).1
  | nil => simp
  | cons _ _ head tail =>
      intro ref member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail ref member

private theorem append_refines (children : RepresentsList arena refs terms) (arity : refs.length = op.arity)
    (built : (append arena (.node op refs)).result = .ok root) :
    let after := (append arena (.node op refs)).arena
    Represents after root (.node op terms) ∧ (Backward arena → Backward after) ∧ root < after.size := by
  unfold append at built ⊢
  split at built
  · rename_i next ref added
    cases built
    obtain ⟨frame, index, _, size, _, read⟩ := addNode_commits added
    refine ⟨.node read arity (children.frame frame), ?_, by dsimp only; omega⟩
    intro old
    apply addNode_preserves_backward old added
    rw [index]
    exact represented_bounds children
  · cases built

/-- The result has the independently defined balanced tree meaning, with
each output edge pointing back into the committed graph. -/
theorem run_refines (value : Nat) (arena : Arena) (built : (run value arena).result = .ok root) :
    let after := (run value arena).arena
    Represents after root (naturalSum value) ∧ (Backward arena → Backward after) ∧ root < after.size := by
  rw [run] at built ⊢
  rw [naturalSum]
  by_cases small : value < 2^64
  · simp only [small, ite_true] at built ⊢
    exact append_refines .nil rfl built
  · simp only [small, ite_false] at built ⊢
    generalize leftRun : run (value / 2) arena = left at built ⊢
    cases leftResult : left.result with
    | error reason => simp [leftResult] at built
    | ok leftRef =>
        have leftComputed : (run (value / 2) arena).result = .ok leftRef := by
          rw [leftRun, leftResult]
        have leftFacts := run_refines (value / 2) arena leftComputed
        rw [leftRun] at leftFacts
        have leftHeld := leftFacts.1
        simp only [leftResult] at built ⊢
        by_cases even : value - value / 2 = value / 2
        · simp only [even, ite_true] at built ⊢
          obtain ⟨represented, back, inRange⟩ := append_refines (op := .uadd)
            (.cons leftHeld (.cons leftHeld .nil)) rfl built
          exact ⟨represented, fun old => back (leftFacts.2.1 old), inRange⟩
        · simp only [even, ite_false] at built ⊢
          generalize rightRun : run (value - value / 2) left.arena = right at built ⊢
          cases rightResult : right.result with
          | error reason => simp [rightResult] at built
          | ok rightRef =>
              have rightComputed : (run (value - value / 2) left.arena).result = .ok rightRef := by
                rw [rightRun, rightResult]
              have rightFacts := run_refines (value - value / 2) left.arena rightComputed
              have rightPrefix := run_prefix (value - value / 2) left.arena
              rw [rightRun] at rightFacts rightPrefix
              have rightHeld := rightFacts.1
              have leftHeld := leftHeld.frame rightPrefix
              simp only [rightResult] at built ⊢
              obtain ⟨represented, back, inRange⟩ := append_refines (op := .uadd)
                (.cons leftHeld (.cons rightHeld .nil)) rfl built
              exact ⟨represented, fun old => back (rightFacts.2.1 (leftFacts.2.1 old)), inRange⟩
termination_by value
decreasing_by all_goals omega

/-- Every committed constant represents the exact unsigned mathematical
value and has the original U64 type, even above a single word. -/
theorem run_value (value : BitVec 128) (arena : Arena) (built : (run value.toNat arena).result = .ok root) :
    ∃ term, Represents (run value.toNat arena).arena root term ∧
      EnvironmentDelta.NumeralForward.Represents term value.toNat ∧
      Environment.LoanTyping.HasType env loans ctx mode term .u64 :=
  ⟨_, (run_refines _ _ built).1, naturalSum_correct _⟩

/-- At the term limit the first literal append fails and all recursive
callers retain the original arena. -/
theorem run_at_limit (value : Nat) (arena : Arena) (full : entryLimit ≤ arena.size) :
    run value arena = ⟨arena, .error .termLimit⟩ := by
  rw [run]
  by_cases small : value < 2^64
  · simp [small, append, addNode, Nat.not_lt.mpr full]
  · simp only [small, ite_false]
    rw [run_at_limit (value / 2) arena full]
termination_by value
decreasing_by omega

theorem ghost_word_boundary_shares :
    run (2^64) #[] =
      ⟨#[.node (.natural (2^63)) [], .node .uadd [0, 0]], .ok 1⟩ := by
  have half : (2^64 : Nat) / 2 = 2^63 := by decide
  have even : (2^64 : Nat) - (2^64 : Nat) / 2 = (2^64 : Nat) / 2 := by decide
  rw [run, ite_eq_right (Nat.lt_irrefl _)]
  simp only [half, even, ite_true]
  rw [run, ite_eq_left (by decide : (2^63 : Nat) < 2^64)]
  rfl

end Jihoo.NativeKernel.NativeCoreNaturalSum
