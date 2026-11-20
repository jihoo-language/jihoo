import Jihoo.NativeCoreNaturalSum
import Jihoo.NativeCoreUnsignedOrder

/-! Core.canonical retains one balanced constant and folds the stable
variable and atom ordering into live UAdd nodes from the left. -/
namespace Jihoo.NativeKernel.NativeCoreUnsignedCanonical

open NativeArena NativeCoreGraph
open NativeConstantAccumulator (naturalSum naturalSum_correct)
open NativeCoreUnsignedOrder (orderedTerms orderedTerms_perm)
open Environment

inductive Error where
  | order
  | graph (reason : NativeCoreGraph.Error)
  deriving Repr, DecidableEq

structure Outcome where
  arena : Arena
  result : Except Error (Option Nat)
  remaining : Nat
  deriving Repr

private def fold (arena : Arena) (first : Nat) : List Nat → NativeCoreNaturalSum.Outcome
  | [] => ⟨arena, .ok first⟩
  | ref :: rest =>
      match addNode arena (.node .uadd [first, ref]) with
      | .error reason => ⟨arena, .error reason⟩
      | .ok (next, sum) => fold next sum rest

private def emit (arena : Arena) (constant : Nat) : List Nat → NativeCoreNaturalSum.Outcome
  | [] => NativeCoreNaturalSum.run constant arena
  | first :: rest =>
      if constant = 0 then fold arena first rest
      else
        let emitted := NativeCoreNaturalSum.run constant arena
        match emitted.result with
        | .error _ => emitted
        | .ok number => fold emitted.arena first (rest ++ [number])

/-- An oversized runtime constant is rejected before sorting or appending.
For ghost computation the same word is emitted as a balanced sum. -/
def run (runtime : Bool) (arena : Arena) (atoms : List Nat) (constant : BitVec 128) (work : Nat) : Outcome :=
  if runtime && decide (2^64 ≤ constant.toNat) then ⟨arena, .ok none, work⟩
  else match NativeCoreUnsignedOrder.run runtime arena atoms work with
    | none => ⟨arena, .error .order, 0⟩
    | some (ordered, remaining) =>
        let emitted := emit arena constant.toNat ordered
        ⟨emitted.arena, (emitted.result.map some).mapError .graph, remaining⟩

private def emitTree (constant : Nat) : List Term → Term
  | [] => naturalSum constant
  | first :: rest =>
      (rest ++ if constant = 0 then [] else [naturalSum constant]).foldl Term.uadd first

def canonicalTerm (runtime : Bool) (atoms : List Term) (constant : Nat) : Term :=
  emitTree constant (orderedTerms runtime atoms)

private theorem represented_bound (held : Represents arena ref term) : ref < arena.size := by
  cases held with
  | var lookup | node lookup => exact (Array.getElem?_eq_some_iff.mp lookup).1

private theorem append_refines (left : Represents arena a first) (right : Represents arena b second)
    (added : addNode arena (.node .uadd [a, b]) = .ok (next, root)) :
    Prefix arena next ∧ Represents next root (.uadd first second) ∧ (Backward arena → Backward next) := by
  obtain ⟨frame, index, _, _, _, row⟩ := addNode_commits added
  refine ⟨frame, .node row rfl (.cons (left.frame frame) (.cons (right.frame frame) .nil)), ?_⟩
  intro backward
  apply addNode_preserves_backward backward added
  rw [index]
  intro ref
  simp only [Node.references, List.mem_cons, List.mem_nil_iff, or_false]
  rintro (rfl | rfl)
  · exact represented_bound left
  · exact represented_bound right

private theorem fold_refines (head : Represents arena first initial) (tail : RepresentsList arena refs terms)
    (built : (fold arena first refs).result = .ok root) :
    let after := (fold arena first refs).arena
    Prefix arena after ∧ Represents after root (terms.foldl Term.uadd initial) ∧
      (Backward arena → Backward after) := by
  induction refs generalizing arena first initial terms with
  | nil =>
      cases tail
      cases built
      exact ⟨.refl _, head, fun held => held⟩
  | cons ref refs ih =>
      cases tail with
      | cons right rest =>
          unfold fold at built ⊢
          cases added : addNode arena (.node .uadd [first, ref]) with
          | error reason => simp [added] at built
          | ok node =>
              obtain ⟨next, sum⟩ := node
              simp only [added] at built ⊢
              obtain ⟨frame, represented, backward⟩ := append_refines head right added
              have nextFacts := ih represented (rest.frame frame) built
              exact ⟨frame.trans nextFacts.1, nextFacts.2.1, fun old => nextFacts.2.2 (backward old)⟩

private theorem represented_snoc (held : RepresentsList arena refs terms) (last : Represents arena ref term) :
    RepresentsList arena (refs ++ [ref]) (terms ++ [term]) := by
  induction refs generalizing terms with
  | nil =>
      cases held
      exact .cons last .nil
  | cons first rest ih =>
      cases held with
      | cons head tail => exact .cons head (ih tail)

private theorem emit_refines (held : RepresentsList arena refs terms)
    (built : (emit arena constant refs).result = .ok root) :
    let after := (emit arena constant refs).arena
    Prefix arena after ∧ Represents after root (emitTree constant terms) ∧ (Backward arena → Backward after) := by
  cases held with
  | nil =>
      obtain ⟨represented, backward, _⟩ := NativeCoreNaturalSum.run_refines constant arena built
      exact ⟨NativeCoreNaturalSum.run_prefix constant arena, represented, backward⟩
  | @cons first initial refs terms head tail =>
      unfold emit at built ⊢
      unfold emitTree
      by_cases zero : constant = 0
      · simp only [zero, ite_true, List.append_nil] at *
        exact fold_refines head tail built
      · simp only [zero, ite_false] at built ⊢
        cases emitted : (NativeCoreNaturalSum.run constant arena).result with
        | error reason =>
            simp only [emitted] at built
            cases built
        | ok number =>
            simp only [emitted] at built ⊢
            obtain ⟨numeric, backwards, _⟩ := NativeCoreNaturalSum.run_refines constant arena emitted
            have frame := NativeCoreNaturalSum.run_prefix constant arena
            have folded := fold_refines (head.frame frame) (represented_snoc (tail.frame frame) numeric) built
            exact ⟨frame.trans folded.1, folded.2.1, fun old => folded.2.2 (backwards old)⟩

theorem run_runtime_overflow (wide : 2^64 ≤ constant.toNat) :
    run true arena refs constant work = ⟨arena, .ok none, work⟩ := by
  simp [run, wide]

/-- The result represents the canonical left fold of all original atom
occurrences and the exact balanced constant. All previously represented
references and backwardness survive the append sequence. -/
theorem run_refines (source : RepresentsList arena refs terms)
    (computed : (run runtime arena refs constant work).result = .ok (some root)) :
    let after := (run runtime arena refs constant work).arena
    Prefix arena after ∧ Represents after root (canonicalTerm runtime terms constant.toNat) ∧
      (Backward arena → Backward after) := by
  unfold run at computed ⊢
  split at computed
  · cases computed
  · rename_i guard
    simp only [guard]
    cases ordered : NativeCoreUnsignedOrder.run runtime arena refs work with
    | none => simp [ordered] at computed
    | some result =>
        obtain ⟨atomRefs, remaining⟩ := result
        simp only [ordered] at computed ⊢
        have represented := NativeCoreUnsignedOrder.run_refines source ordered
        cases built : (emit arena constant.toNat atomRefs).result with
        | error reason => simp [built, Except.map, Except.mapError] at computed
        | ok reference =>
            simp only [built, Except.map, Except.mapError, Except.ok.injEq, Option.some.injEq] at computed
            subst reference
            exact emit_refines represented built

private theorem fold_typed {terms : List Term} (head : LoanTyping.HasType env loans ctx mode first .u64)
    (tail : ∀ t ∈ terms, LoanTyping.HasType env loans ctx mode t .u64) :
    LoanTyping.HasType env loans ctx mode (terms.foldl Term.uadd first) .u64 := by
  induction terms generalizing first with
  | nil => exact head
  | cons next rest ih =>
      exact ih (.uadd head (tail next List.mem_cons_self))
        (fun term member => tail term (List.mem_cons_of_mem _ member))

/-- The emitted term keeps U64 typing in the original context and mode,
uniformly for both ordering modes. -/
theorem canonicalTerm_typed {terms : List Term} (atoms : ∀ t ∈ terms, LoanTyping.HasType env loans ctx mode t .u64) :
    LoanTyping.HasType env loans ctx mode (canonicalTerm runtime terms constant) .u64 := by
  have available : ∀ t ∈ orderedTerms runtime terms, LoanTyping.HasType env loans ctx mode t .u64 :=
    fun t member => atoms t ((orderedTerms_perm runtime terms).mem_iff.mp member)
  have number := (naturalSum_correct (env := env) (loans := loans) (ctx := ctx) (mode := mode) constant).2
  unfold canonicalTerm
  cases ordered : orderedTerms runtime terms with
  | nil => exact number
  | cons head tail =>
      rw [ordered] at available
      apply fold_typed (available head List.mem_cons_self)
      intro term member
      rcases List.mem_append.mp member with earlier | later
      · exact available term (List.mem_cons_of_mem _ earlier)
      · by_cases zero : constant = 0
        · simp [zero] at later
        · simp only [zero, ite_false, List.mem_singleton] at later
          subst term
          exact number

end Jihoo.NativeKernel.NativeCoreUnsignedCanonical
